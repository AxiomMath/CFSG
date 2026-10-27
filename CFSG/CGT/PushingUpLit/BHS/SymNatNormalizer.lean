module

public import CFSG.CGT.PushingUpLit.BHS.SymNatBasic

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6

variable {n : ℕ}

theorem sum_ite_ne_eq (hn : Odd n) (i : Fin n) :
    ∑ j : Fin n, (if j = i then (0 : ZMod 2) else 1) = 0 := by
  have h0 : ∀ j : Fin n, (if j = i then (0 : ZMod 2) else 1) = if j ≠ i then 1 else 0 := by
    intro j
    by_cases hj : j = i <;> simp [hj]
  simp_rw [h0, Finset.sum_boole]
  rw [Finset.filter_ne' Finset.univ i, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin]
  have : Even (n - 1) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  exact this.natCast_zmod_two

@[expose] def uvec (hn : Odd n) (i : Fin n) : ↥(coreMod n) :=
  mkEven (fun j => if j = i then 0 else 1) (sum_ite_ne_eq hn i)

theorem vcoord_uvec (hn : Odd n) (i j : Fin n) :
    vcoord (uvec hn i) j = if j = i then 0 else 1 := rfl

theorem coreAct_uvec (hn : Odd n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    coreAct n σ (uvec hn i) = uvec hn (σ i) := by
  apply vcoord_ext
  intro j
  rw [vcoord_coreAct, vcoord_uvec, vcoord_uvec]
  simp only [Equiv.Perm.inv_eq_iff_eq]

theorem uvec_injective (hn : Odd n) : Function.Injective (uvec hn) := by
  intro i j h
  by_contra hij
  have := congrArg (fun v => vcoord v i) h
  simp [vcoord_uvec, hij] at this


theorem vcoord_prod (S : Finset (Fin n)) (f : Fin n → ↥(coreMod n)) (j : Fin n) :
    vcoord (∏ i ∈ S, f i) j = ∑ i ∈ S, vcoord (f i) j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [vcoord_one]
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, vcoord_mul, ih]

theorem zmod_two_eq_ite (x : ZMod 2) : x = if x = 1 then 1 else 0 := by
  revert x
  decide

theorem even_card_support (d : ↥(coreMod n)) :
    Even (Finset.univ.filter (fun i => vcoord d i = 1)).card := by
  classical
  have h : ((Finset.univ.filter (fun i => vcoord d i = 1)).card : ZMod 2) = 0 := by
    rw [← Finset.sum_boole]
    have := sum_vcoord d
    calc ∑ i : Fin n, (if vcoord d i = 1 then (1 : ZMod 2) else 0) = ∑ i, vcoord d i :=
          Finset.sum_congr rfl fun i _ => (zmod_two_eq_ite _).symm
      _ = 0 := this
  exact (ZMod.natCast_eq_zero_iff_even).mp h

theorem eq_prod_uvec (hn : Odd n) (d : ↥(coreMod n)) :
    d = ∏ i ∈ Finset.univ.filter (fun i => vcoord d i = 1), uvec hn i := by
  classical
  set S := Finset.univ.filter (fun i => vcoord d i = 1) with hS
  apply vcoord_ext
  intro j
  rw [vcoord_prod]
  simp_rw [vcoord_uvec]
  have h0 : ∀ i : Fin n, (if j = i then (0 : ZMod 2) else 1) = if i ≠ j then 1 else 0 := by
    intro i
    by_cases h : j = i <;> simp [h, eq_comm]
  simp_rw [h0, Finset.sum_boole]
  have hev := even_card_support d
  rw [← hS] at hev
  by_cases hj : vcoord d j = 1
  · have hjS : j ∈ S := by simp [hS, hj]
    have : S.filter (fun i => i ≠ j) = S.erase j := Finset.filter_ne' S j
    rw [this, Finset.card_erase_of_mem hjS, hj]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j, hjS⟩
    obtain ⟨k, hk⟩ := hev
    have : Odd (S.card - 1) := ⟨k - 1, by omega⟩
    exact (this.natCast_zmod_two).symm
  · have hjS : j ∉ S := by simp [hS, hj]
    have : S.filter (fun i => i ≠ j) = S := Finset.filter_true_of_mem fun i hi h => hjS (h ▸ hi)
    rw [this]
    have : vcoord d j = 0 := by
      have := zmod_two_eq_ite (vcoord d j)
      simpa [hj] using this
    rw [this]
    exact hev.natCast_zmod_two.symm

theorem closure_uvec (hn : Odd n) : Subgroup.closure (Set.range (uvec hn)) = ⊤ := by
  rw [eq_top_iff]
  intro d _
  rw [eq_prod_uvec hn d]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.subset_closure ⟨i, rfl⟩


@[expose] def altOrb (n : ℕ) (d : ↥(coreMod n)) : Set ↥(coreMod n) :=
  {w | ∃ σ ∈ alternatingGroup (Fin n), w = coreAct n σ d}

theorem exists_alt_apply_eq (h3 : 3 ≤ n) (i j : Fin n) :
    ∃ σ ∈ alternatingGroup (Fin n), σ i = j := by
  by_cases hij : i = j
  · exact ⟨1, Subgroup.one_mem _, by simp [hij]⟩
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  refine ⟨Equiv.swap i k * Equiv.swap i j, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (fun h => hk.1 h.symm), Equiv.Perm.sign_swap hij]
    decide
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) (fun h => hk.2 h.symm)]

theorem altOrb_uvec (hn : Odd n) (h3 : 3 ≤ n) (i : Fin n) :
    altOrb n (uvec hn i) = Set.range (uvec hn) := by
  ext w
  constructor
  · rintro ⟨σ, -, rfl⟩
    exact ⟨σ i, (coreAct_uvec hn σ i).symm⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨σ, hσ, hσi⟩ := exists_alt_apply_eq h3 i j
    exact ⟨σ, hσ, by rw [coreAct_uvec, hσi]⟩

theorem ncard_range_uvec (hn : Odd n) : (Set.range (uvec hn)).ncard = n := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ (uvec_injective hn), Set.ncard_univ]
  simp


theorem vcoord_swap3 (d : ↥(coreMod n)) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (i : Fin n) :
    vcoord (coreAct n (Equiv.swap a b * Equiv.swap b c) d) i =
      if i = a then vcoord d c else if i = b then vcoord d a else if i = c then vcoord d b
        else vcoord d i := by
  rw [vcoord_coreAct]
  have hinv : (Equiv.swap a b * Equiv.swap b c)⁻¹ = Equiv.swap b c * Equiv.swap a b := by
    rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  rw [hinv, Equiv.Perm.mul_apply]
  by_cases h1 : i = a
  · subst h1
    simp [Equiv.swap_apply_left]
  by_cases h2 : i = b
  · subst h2
    simp only [h1, ite_false, ite_true, Equiv.swap_apply_right]
    rw [Equiv.swap_apply_of_ne_of_ne hab hac]
  by_cases h3 : i = c
  · subst h3
    simp only [h1, h2, ite_false, ite_true]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_right]
  simp only [h1, h2, h3, ite_false]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h2 h3]


theorem vcoord_swap3_eq_one_iff (d : ↥(coreMod n)) {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (ha : vcoord d a = 1) (hb : vcoord d b = 0) (hc : vcoord d c = 0) (i : Fin n) :
    vcoord (coreAct n (Equiv.swap a b * Equiv.swap b c) d) i = 1 ↔
      (i ≠ a ∧ vcoord d i = 1) ∨ i = b := by
  rw [vcoord_swap3 d hab hac hbc]
  by_cases h1 : i = a
  · subst h1
    simp [hc, hab]
  by_cases h2 : i = b
  · subst h2
    simp [ha, h1]
  by_cases h3 : i = c
  · subst h3
    simp [h1, h2, hb, hc]
  simp [h1, h2, h3]


theorem eq_one_or_exists_uvec_of_ncard_le (hn : Odd n) (h5 : 5 ≤ n) (d : ↥(coreMod n))
    (hd : (altOrb n d).ncard ≤ n) : d = 1 ∨ ∃ i, d = uvec hn i := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hd1, hdu⟩ := hcon
  set S : Finset (Fin n) := Finset.univ.filter (fun i => vcoord d i = 1) with hS
  set Sc : Finset (Fin n) := Finset.univ.filter (fun i => ¬ vcoord d i = 1) with hSc
  have hsum : S.card + Sc.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => vcoord d i = 1)
    simpa [hS, hSc] using this
  have hev : Even S.card := even_card_support d
  have hS0 : S.card ≠ 0 := by
    intro h0
    apply hd1
    apply vcoord_ext
    intro i
    have hi : ¬ vcoord d i = 1 := by
      intro hi
      have : i ∈ S := by simp [hS, hi]
      rw [Finset.card_eq_zero] at h0
      simp [h0] at this
    rw [vcoord_one]
    have := zmod_two_eq_ite (vcoord d i)
    simpa [hi] using this
  have hS2 : 2 ≤ S.card := by
    obtain ⟨k, hk⟩ := hev
    omega
  have hScodd : Odd Sc.card := by
    obtain ⟨k, hk⟩ := hn
    obtain ⟨l, hl⟩ := hev
    exact ⟨k - l, by omega⟩
  have hSc1 : Sc.card ≠ 1 := by
    intro h1
    obtain ⟨i0, hi0⟩ := Finset.card_eq_one.mp h1
    apply hdu i0
    apply vcoord_ext
    intro j
    rw [vcoord_uvec]
    by_cases hj : j = i0
    · subst hj
      have : j ∈ Sc := by simp [hi0]
      have h' : ¬ vcoord d j = 1 := by simpa [hSc] using this
      have := zmod_two_eq_ite (vcoord d j)
      simpa [h'] using this
    · have : j ∉ Sc := by simp [hi0, hj]
      have h' : vcoord d j = 1 := by simpa [hSc] using this
      simp [h', hj]
  have hSc3 : 3 ≤ Sc.card := by
    obtain ⟨k, hk⟩ := hScodd
    have := Nat.pos_of_ne_zero (by rintro h0; rw [h0] at hk; omega : Sc.card ≠ 0)
    omega
  have hz : ∀ t : Fin n, ∃ z : Fin n, t ∈ Sc → z ∈ Sc ∧ z ≠ t := by
    intro t
    by_cases ht : t ∈ Sc
    · obtain ⟨z, hz, hzt⟩ := Finset.exists_mem_ne (by omega : 1 < Sc.card) t
      exact ⟨z, fun _ => ⟨hz, hzt⟩⟩
    · exact ⟨t, fun h => absurd h ht⟩
  choose zf hzf using hz
  let F : Fin n × Fin n → ↥(coreMod n) := fun p =>
    coreAct n (Equiv.swap p.1 p.2 * Equiv.swap p.2 (zf p.2)) d
  have hmemS : ∀ i, i ∈ S ↔ vcoord d i = 1 := fun i => by simp [hS]
  have hmemSc : ∀ i, i ∈ Sc ↔ ¬ vcoord d i = 1 := fun i => by simp [hSc]
  have hF_orb : ∀ p ∈ S ×ˢ Sc, F p ∈ altOrb n d := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have hne1 : p.1 ≠ p.2 := fun h => (hmemSc _).mp hp2 ((hmemS _).mp (h ▸ hp1))
    have hne2 : p.2 ≠ zf p.2 := (hzf p.2 hp2).2.symm
    refine ⟨_, ?_, rfl⟩
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne1,
      Equiv.Perm.sign_swap hne2]
    decide
  have hF_inj : Set.InjOn F (↑(S ×ˢ Sc) : Set (Fin n × Fin n)) := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    have hpa : vcoord d p.1 = 1 := (hmemS _).mp hp1
    have hpb : ¬ vcoord d p.2 = 1 := (hmemSc _).mp hp2
    have hqa : vcoord d q.1 = 1 := (hmemS _).mp hq1
    have hqb : ¬ vcoord d q.2 = 1 := (hmemSc _).mp hq2
    have hpz := (hmemSc _).mp (hzf p.2 hp2).1
    have hqz := (hmemSc _).mp (hzf q.2 hq2).1
    have hz0 : ∀ x : Fin n, ¬ vcoord d x = 1 → vcoord d x = 0 := by
      intro x hx
      have := zmod_two_eq_ite (vcoord d x)
      simpa [hx] using this
    have hne1 : p.1 ≠ p.2 := fun h => hpb (h ▸ hpa)
    have hne1' : q.1 ≠ q.2 := fun h => hqb (h ▸ hqa)
    have hne3 : p.1 ≠ zf p.2 := fun h => hpz (h ▸ hpa)
    have hne3' : q.1 ≠ zf q.2 := fun h => hqz (h ▸ hqa)
    have hne2 : p.2 ≠ zf p.2 := (hzf p.2 hp2).2.symm
    have hne2' : q.2 ≠ zf q.2 := (hzf q.2 hq2).2.symm
    have hiff : ∀ i, ((i ≠ p.1 ∧ vcoord d i = 1) ∨ i = p.2) ↔
        ((i ≠ q.1 ∧ vcoord d i = 1) ∨ i = q.2) := by
      intro i
      rw [← vcoord_swap3_eq_one_iff d hne1 hne3 hne2 hpa (hz0 _ hpb) (hz0 _ hpz) i,
        ← vcoord_swap3_eq_one_iff d hne1' hne3' hne2' hqa (hz0 _ hqb) (hz0 _ hqz) i]
      have := congrArg (fun w => vcoord w i) hpq
      simp only [F] at this
      rw [this]
    have h2 : p.2 = q.2 := by
      have := (hiff p.2).mp (Or.inr rfl)
      rcases this with ⟨-, h⟩ | h
      · exact absurd h hpb
      · exact h
    have h1 : p.1 = q.1 := by
      by_contra hne
      have hh : (p.1 ≠ q.1 ∧ vcoord d p.1 = 1) ∨ p.1 = q.2 := Or.inl ⟨hne, hpa⟩
      have := (hiff p.1).mpr hh
      rcases this with ⟨h, -⟩ | h
      · exact h rfl
      · exact hne1 (by simpa [h2] using h)
    exact Prod.ext h1 h2
  have hcard1 : (S ×ˢ Sc).card ≤ (altOrb n d).ncard := by
    have hsub : (↑((S ×ˢ Sc).image F) : Set ↥(coreMod n)) ⊆ altOrb n d := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      exact hF_orb p hp
    calc (S ×ˢ Sc).card = ((S ×ˢ Sc).image F).card := (Finset.card_image_of_injOn hF_inj).symm
      _ = (↑((S ×ˢ Sc).image F) : Set ↥(coreMod n)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ (altOrb n d).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Finset.card_product] at hcard1
  have hge : n + 1 ≤ S.card * Sc.card := by
    have h4 : 2 * Sc.card ≤ S.card * Sc.card := Nat.mul_le_mul_right _ hS2
    have h4' : S.card * 3 ≤ S.card * Sc.card := Nat.mul_le_mul_left _ hSc3
    omega
  omega


theorem exists_perm_of_normalizes_alt (hn : Odd n) (h5 : 5 ≤ n) (y : MulAut ↥(coreMod n))
    (hy : ∀ σ ∈ alternatingGroup (Fin n), ∃ σ' ∈ alternatingGroup (Fin n),
      ∀ d, y (coreAct n σ d) = coreAct n σ' (y d))
    (hy' : ∀ σ' ∈ alternatingGroup (Fin n), ∃ σ ∈ alternatingGroup (Fin n),
      ∀ d, y (coreAct n σ d) = coreAct n σ' (y d)) :
    ∃ π : Equiv.Perm (Fin n), ∀ d, y d = coreAct n π d := by
  classical
  have h3 : 3 ≤ n := by omega
  have horb : ∀ d, altOrb n (y d) = y '' altOrb n d := by
    intro d
    ext w
    constructor
    · rintro ⟨σ', hσ', rfl⟩
      obtain ⟨σ, hσ, hσσ'⟩ := hy' σ' hσ'
      exact ⟨coreAct n σ d, ⟨σ, hσ, rfl⟩, hσσ' d⟩
    · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
      obtain ⟨σ', hσ', h⟩ := hy σ hσ
      exact ⟨σ', hσ', h d⟩
  have hne1 : ∀ i, uvec hn i ≠ 1 := by
    intro i h
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_contra hall
      push Not at hall
      have : Subsingleton (Fin n) := ⟨fun a b => (hall a).trans (hall b).symm⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr this
      simp at this
      omega
    have := congrArg (fun v => vcoord v j) h
    simp [vcoord_uvec, hj, vcoord_one] at this
  have huv : ∀ i, ∃ j, y (uvec hn i) = uvec hn j := by
    intro i
    have hcard : (altOrb n (y (uvec hn i))).ncard ≤ n := by
      rw [horb, Set.ncard_image_of_injective _ y.injective, altOrb_uvec hn h3,
        ncard_range_uvec hn]
    rcases eq_one_or_exists_uvec_of_ncard_le hn h5 _ hcard with h | ⟨j, hj⟩
    · exfalso
      apply hne1 i
      apply y.injective
      rw [h, map_one]
    · exact ⟨j, hj⟩
  choose π hπ using huv
  have hinj : Function.Injective π := by
    intro i j h
    apply uvec_injective hn
    apply y.injective
    rw [hπ i, hπ j, h]
  let πe : Equiv.Perm (Fin n) := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj)
  refine ⟨πe, fun d => ?_⟩
  have hagree : Set.EqOn (y : ↥(coreMod n) →* ↥(coreMod n))
      ((coreAct n πe : MulAut ↥(coreMod n)) : ↥(coreMod n) →* ↥(coreMod n))
      (Set.range (uvec hn)) := by
    rintro _ ⟨i, rfl⟩
    show y (uvec hn i) = coreAct n πe (uvec hn i)
    rw [coreAct_uvec]
    exact hπ i
  have := MonoidHom.eqOn_closure hagree
  rw [closure_uvec hn] at this
  exact this (Set.mem_univ _)

end CFSG.CGT.PushingUpLit.BHS
