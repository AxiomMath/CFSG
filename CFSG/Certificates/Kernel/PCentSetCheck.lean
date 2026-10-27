module

public import Certificates.Data.Kernel.PCentSet
public import CFSG.Certificates.Kernel.PCentCheck

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.BfsPin (PP)
open scoped Pointwise

variable {n w : Nat}

@[expose] def ptsM (n m : Nat) : Set (Fin n) := {i | Nat.testBit m i = true}

theorem shiftLeft_one (a : Nat) : Nat.shiftLeft 1 a = 2 ^ a := by
  change 1 <<< a = 2 ^ a
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_imgMT {g : Nat} (m j : Nat) : ∀ t,
    (Nat.testBit (imgMT w g m t) j = true ↔
      ∃ i < t, Nat.testBit m i = true ∧ pg w (mask w) g i = j)
  | 0 => by simp [imgMT]
  | t + 1 => by
    have ih := testBit_imgMT (g := g) m j t
    have e : imgMT w g m (t + 1) = cond (Nat.testBit m t)
        (Nat.lor (imgMT w g m t) (Nat.shiftLeft 1 (pg w (mask w) g t))) (imgMT w g m t) := rfl
    rw [e]
    cases hb : Nat.testBit m t
    · rw [cond_false, ih]
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        exact ⟨i, by omega, h1, h2⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h1, h2⟩
        · rw [hb] at h1
          exact absurd h1 (by simp)
    · rw [cond_true, shiftLeft_one]
      change Nat.testBit (imgMT w g m t ||| 2 ^ pg w (mask w) g t) j = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, h1, h2⟩ | h)
        · exact ⟨i, by omega, h1, h2⟩
        · exact ⟨t, by omega, hb, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h1, h2⟩
        · exact Or.inr h2

theorem imgMT_lt {g : Nat} (hg : PP n w g) (m : Nat) : ∀ t, t ≤ n → imgMT w g m t < 2 ^ n
  | 0, _ => Nat.two_pow_pos n
  | t + 1, ht => by
    have ih := imgMT_lt hg m t (by omega)
    have e : imgMT w g m (t + 1) = cond (Nat.testBit m t)
        (Nat.lor (imgMT w g m t) (Nat.shiftLeft 1 (pg w (mask w) g t))) (imgMT w g m t) := rfl
    rw [e]
    cases Nat.testBit m t
    · exact ih
    · rw [cond_true, shiftLeft_one]
      exact Nat.or_lt_two_pow ih (Nat.pow_lt_pow_right (by norm_num) (hg.2.1 t (by omega)))

theorem ptsM_imgM {g : Nat} (hg : PP n w g) (m : Nat) :
    ptsM n (imgM n w g m) = toPerm n w g • ptsM n m := by
  ext j
  rw [Set.mem_smul_set]
  change Nat.testBit (imgMT w g m n) j = true ↔ _
  rw [testBit_imgMT]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    refine ⟨⟨i, hi⟩, h1, Fin.ext ?_⟩
    rw [Equiv.Perm.smul_def, toPerm_apply hg, h2]
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, i.2, h1, ?_⟩
    rw [← h2, Equiv.Perm.smul_def, toPerm_apply hg]

theorem ptsM_inj {x y : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : ptsM n x = ptsM n y) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have e := congrArg (fun S : Set (Fin n) => (⟨i, hi⟩ : Fin n) ∈ S) h
    simp only [ptsM, Set.mem_setOf_eq, eq_iff_iff] at e
    exact Bool.eq_iff_iff.2 e
  · have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem reach_set {G : Nat → Nat} {ngen m : Nat} (hG : ∀ k < ngen, PP n w (G k))
    (hm : m < 2 ^ n) {y : Nat} (h : Reach (fun k y => imgM n w (G k) y) ngen m y) :
    y < 2 ^ n ∧ ∃ g ∈ Subgroup.closure (gens n w G ngen), g • ptsM n m = ptsM n y := by
  induction h with
  | root => exact ⟨hm, 1, Subgroup.one_mem _, one_smul _ _⟩
  | step k hk _ ih =>
    obtain ⟨-, g, hg, he⟩ := ih
    refine ⟨imgMT_lt (hG k hk) _ n le_rfl, toPerm n w (G k) * g,
      Subgroup.mul_mem _ (gen_mem hk) hg, ?_⟩
    rw [mul_smul, he, ptsM_imgM (hG k hk)]

theorem card_stab_le_of_setOrbK {G : Nat → Nat} {ngen m : Nat} {R : List Rec}
    {H : Subgroup (Equiv.Perm (Fin n))} (hG : ∀ k < ngen, PP n w (G k))
    (hGH : ∀ k < ngen, toPerm n w (G k) ∈ H) (h : setOrbK n w G ngen m R = true) :
    R.length * Nat.card (H ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) (ptsM n m) :
      Subgroup (Equiv.Perm (Fin n))) ≤ Nat.card H := by
  classical
  unfold setOrbK at h
  rw [Bool.and_eq_true, Nat.blt_eq, Nat.pow_eq] at h
  obtain ⟨hm, h⟩ := h
  obtain ⟨hs, hr⟩ := orbRecK_sound h
  have hcl : Subgroup.closure (gens n w G ngen) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hGH k hk
  have hR : ∀ r ∈ R, r.1 < 2 ^ n ∧ ∃ g ∈ H, g • ptsM n m = ptsM n r.1 := fun r hr' => by
    obtain ⟨hlt, g, hg, he⟩ := reach_set hG hm (hr r hr')
    exact ⟨hlt, g, hcl hg, he⟩
  have hnd : (R.map Prod.fst).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  have hnd' : (R.map fun r => ptsM n r.1).Nodup := by
    have e : (R.map fun r => ptsM n r.1) = (R.map Prod.fst).map (ptsM n) := by
      rw [List.map_map]
      rfl
    rw [e]
    refine hnd.map_on fun x hx y hy hxy => ?_
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hy
    exact ptsM_inj (hR r hr').1 (hR q hq').1 hxy
  have hc := card_mul_card_stab_le (H := H) (x := ptsM n m) (R.map fun r => ptsM n r.1).toFinset
    (fun s hs' => by
      obtain ⟨r, hr', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs')
      exact (hR r hr').2)
  rwa [List.toFinset_card_of_nodup hnd', List.length_map] at hc

theorem card_stab_le_of_pointOrbK {G : Nat → Nat} {ngen x : Nat} {R : List Rec}
    {H : Subgroup (Equiv.Perm (Fin n))} (hG : ∀ k < ngen, PP n w (G k))
    (hGH : ∀ k < ngen, toPerm n w (G k) ∈ H) (h : pointOrbK n w G ngen x R = true) :
    ∃ hx : x < n, R.length * Nat.card (H ⊓ MulAction.stabilizer (Equiv.Perm (Fin n))
      (⟨x, hx⟩ : Fin n) : Subgroup (Equiv.Perm (Fin n))) ≤ Nat.card H := by
  obtain ⟨hx, hcard, hS, -⟩ := pointOrbK_sound hG h
  have hcl : Subgroup.closure (gens n w G ngen) ≤ H := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hGH k hk
  refine ⟨hx, ?_⟩
  have hc := card_mul_card_stab_le (H := H) (x := (⟨x, hx⟩ : Fin n)) (ptsOf n R) fun s hs => by
    obtain ⟨g, hg, he⟩ := hS s hs
    exact ⟨g, hcl hg, he⟩
  rwa [hcard] at hc

theorem reach_mul {G : Nat → Nat} {ngen : Nat} (hsz : CFSG.KS.Raw.szOK n w = true)
    (hG : ∀ k < ngen, PP n w (G k)) {y : Nat}
    (h : Reach (fun k y => pcomp n w (mask w) (G k) y) ngen (pidn n w) y) :
    PP n w y ∧ toPerm n w y ∈ Subgroup.closure (gens n w G ngen) := by
  induction h with
  | root => exact ⟨PP.id hsz, by rw [toPerm_pidn hsz]; exact Subgroup.one_mem _⟩
  | step k hk _ ih =>
    refine ⟨(hG k hk).mul ih.1, ?_⟩
    rw [toPerm_mul (hG k hk) ih.1]
    exact Subgroup.mul_mem _ (gen_mem hk) ih.2

theorem mulRecK_sound {G : Nat → Nat} {ngen : Nat} {R : List Rec}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k))
    (h : mulRecK n w G ngen R = true) :
    (∀ r ∈ R, PP n w r.1 ∧ toPerm n w r.1 ∈ Subgroup.closure (gens n w G ngen)) ∧
      (R.map fun r => toPerm n w r.1).Nodup := by
  obtain ⟨hs, hr⟩ := orbRecK_sound h
  have hR : ∀ r ∈ R, PP n w r.1 ∧ toPerm n w r.1 ∈ Subgroup.closure (gens n w G ngen) :=
    fun r hr' => reach_mul hsz hG (hr r hr')
  refine ⟨hR, ?_⟩
  have hnd : (R.map Prod.fst).Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  have e : (R.map fun r => toPerm n w r.1) = (R.map Prod.fst).map (toPerm n w) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine hnd.map_on fun x hx y hy hxy => ?_
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
  obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hy
  exact toPerm_injective (hR r hr').1 (hR q hq').1 hxy

theorem card_finset_le {S : Finset (Equiv.Perm (Fin n))} {H : Subgroup (Equiv.Perm (Fin n))}
    (h : ∀ x ∈ S, x ∈ H) : S.card ≤ Nat.card H := by
  classical
  have e : Nat.card H = (Finset.univ.filter fun x => x ∈ H).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [e]
  exact Finset.card_le_card fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, h x hx⟩

theorem le_card_of_mulRecK {G : Nat → Nat} {ngen : Nat} {R : List Rec}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k))
    (h : mulRecK n w G ngen R = true) :
    R.length ≤ Nat.card (Subgroup.closure (gens n w G ngen)) := by
  classical
  obtain ⟨hR, hnd⟩ := mulRecK_sound hsz hG h
  have hc := card_finset_le (S := (R.map fun r => toPerm n w r.1).toFinset)
    (H := Subgroup.closure (gens n w G ngen)) fun x hx => by
      obtain ⟨r, hr', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
      exact (hR r hr').2
  rwa [List.toFinset_card_of_nodup hnd, List.length_map] at hc

theorem mem_of_mulRecK {G : Nat → Nat} {ngen : Nat} {R : List Rec}
    (hsz : CFSG.KS.Raw.szOK n w = true) (hG : ∀ k < ngen, PP n w (G k))
    (h : mulRecK n w G ngen R = true)
    (hcard : Nat.card (Subgroup.closure (gens n w G ngen)) ≤ R.length) :
    ∀ x ∈ Subgroup.closure (gens n w G ngen), ∃ r ∈ R, PP n w r.1 ∧ toPerm n w r.1 = x := by
  classical
  obtain ⟨hR, hnd⟩ := mulRecK_sound hsz hG h
  intro x hx
  by_contra hne
  push Not at hne
  set T := (R.map fun r => toPerm n w r.1).toFinset
  have hxT : x ∉ T := fun hxT => by
    obtain ⟨r, hr', e⟩ := List.mem_map.1 (List.mem_toFinset.1 hxT)
    exact hne r hr' (hR r hr').1 e
  have hc := card_finset_le (S := insert x T) (H := Subgroup.closure (gens n w G ngen))
    fun y hy => by
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hx
      · obtain ⟨r, hr', rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
        exact (hR r hr').2
  rw [Finset.card_insert_of_notMem hxT, List.toFinset_card_of_nodup hnd, List.length_map] at hc
  omega

end CFSG.KC.PCent

end
