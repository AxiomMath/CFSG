module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApi
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

private theorem cbtf_exists_perm {n : ℕ} (hn : 7 ≤ n) {F : Finset (Fin n)} (hF : F.card ≤ 3)
    {i j : Fin n} (hi : i ∉ F) (hj : j ∉ F) :
    ∃ σ : alternatingGroup (Fin n), (∀ f ∈ F, (σ : Equiv.Perm (Fin n)) f = f) ∧
      (σ : Equiv.Perm (Fin n)) i = j := by
  classical
  by_cases hij : i = j
  · exact ⟨1, fun f _ => rfl, hij⟩
  have hcard : 1 < (insert i (insert j F))ᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h1 := Finset.card_insert_le i (insert j F)
    have h2 := Finset.card_insert_le j F
    omega
  obtain ⟨l, hl, n', hn', hln⟩ := Finset.one_lt_card.mp hcard
  simp only [Finset.mem_compl, Finset.mem_insert, not_or] at hl hn'
  refine ⟨⟨Equiv.swap i j * Equiv.swap l n', ?_⟩, fun f hf => ?_, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hij, hln]
  · have hfi : f ≠ i := fun h => hi (h ▸ hf)
    have hfj : f ≠ j := fun h => hj (h ▸ hf)
    have hfl : f ≠ l := fun h => hl.2.2 (h ▸ hf)
    have hfn : f ≠ n' := fun h => hn'.2.2 (h ▸ hf)
    show (Equiv.swap i j) ((Equiv.swap l n') f) = f
    rw [Equiv.swap_apply_of_ne_of_ne hfl hfn, Equiv.swap_apply_of_ne_of_ne hfi hfj]
  · show (Equiv.swap i j) ((Equiv.swap l n') i) = j
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hl.1) (Ne.symm hn'.1), Equiv.swap_apply_left]

private abbrev cbtfCrd {n : ℕ} (c : ↥(G6.coreMod n)) (i : Fin n) : ZMod 2 :=
  Multiplicative.toAdd (c : G6.PermMod n) i

private theorem cbtfCrd_ext {n : ℕ} {c c' : ↥(G6.coreMod n)}
    (h : ∀ i, cbtfCrd c i = cbtfCrd c' i) : c = c' :=
  Subtype.ext (Multiplicative.toAdd.injective (funext h))

private theorem cbtfCrd_mul {n : ℕ} (c c' : ↥(G6.coreMod n)) (i : Fin n) :
    cbtfCrd (c * c') i = cbtfCrd c i + cbtfCrd c' i := rfl

private theorem cbtf_sum {n : ℕ} (c : ↥(G6.coreMod n)) (F : Finset (Fin n)) (l : ZMod 2)
    (h : ∀ i ∉ F, cbtfCrd c i = l) :
    ∑ i ∈ F, cbtfCrd c i + ((n - F.card : ℕ) : ZMod 2) * l = 0 := by
  classical
  have h0 : ∑ i, cbtfCrd c i = 0 := G6.mem_coreMod.mp c.2
  rw [← Finset.sum_compl_add_sum F,
    Finset.sum_congr rfl (fun i hi => h i (Finset.mem_compl.mp hi)), Finset.sum_const,
    Finset.card_compl, Fintype.card_fin, nsmul_eq_mul] at h0
  rw [add_comm]
  exact h0

private theorem cbtf_beta (D : CbData Y t m X) :
    ∃ β : ↥(commV X) →* ↥(G6.coreMod (m + 2)), Function.Injective β ∧
      ∀ (x : ↥X) (e : ↥(commV X)) (i : Fin (m + 2)),
        cbtfCrd (β ⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩) i =
          cbtfCrd (β e) (((D.θ x : alternatingGroup (Fin (m + 2))) :
            Equiv.Perm (Fin (m + 2)))⁻¹ i) := by
  obtain ⟨-, β, -, hker, hβ⟩ := D.hnat
  refine ⟨β, ?_, fun x e i => ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, hker, Subgroup.bot_subgroupOf]
  · exact congrArg (fun z : ↥(G6.coreMod (m + 2)) => cbtfCrd z i)
      (hβ x e (commV_invariant x.2 e.2))

private theorem cbtf_fix_ab (D : CbData Y t m X) (hYX : Y ≤ X) (y : MulAut V) (hy : y ∈ Y) :
    (D.θ ⟨y, hYX hy⟩ : Equiv.Perm (Fin (m + 2))) D.a = D.a ∧
      (D.θ ⟨y, hYX hy⟩ : Equiv.Perm (Fin (m + 2))) D.b = D.b := by
  have h : D.θ ⟨y, hYX hy⟩ ∈ altStabilizer (m + 2) {D.a, D.b} := by
    rw [← D.hstab]
    exact ⟨⟨y, hYX hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  rw [mem_altStabilizer_iff] at h
  exact ⟨h D.a (by simp), h D.b (by simp)⟩

private theorem cbtf_mem_Y (D : CbData Y t m X) (x : ↥X)
    (hx : ∀ f ∈ ({D.a, D.b} : Finset (Fin (m + 2))),
      ((D.θ x : alternatingGroup (Fin (m + 2))) : Equiv.Perm (Fin (m + 2))) f = f) :
    (x : MulAut V) ∈ Y := by
  have h : D.θ x ∈ altStabilizer (m + 2) {D.a, D.b} := mem_altStabilizer_iff.mpr hx
  rw [← D.hstab] at h
  obtain ⟨z, hz, hzx⟩ := h
  have hzx' : z = x := D.θ.injective hzx
  subst hzx'
  exact Subgroup.mem_subgroupOf.mp hz

private theorem cbtf_const (D : CbData Y t m X) {β : ↥(commV X) →* ↥(G6.coreMod (m + 2))}
    (hβ : ∀ (x : ↥X) (e : ↥(commV X)) (i : Fin (m + 2)),
      cbtfCrd (β ⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩) i =
        cbtfCrd (β e) (((D.θ x : alternatingGroup (Fin (m + 2))) :
          Equiv.Perm (Fin (m + 2)))⁻¹ i))
    (hm : 7 ≤ m) {F : Finset (Fin (m + 2))} (hF : F.card ≤ 3) (e : ↥(commV X))
    (hfix : ∀ x : ↥X,
      (∀ f ∈ F, ((D.θ x : alternatingGroup (Fin (m + 2))) : Equiv.Perm (Fin (m + 2))) f = f) →
        (x : MulAut V) (e : V) = (e : V))
    {i j : Fin (m + 2)} (hi : i ∉ F) (hj : j ∉ F) :
    cbtfCrd (β e) i = cbtfCrd (β e) j := by
  obtain ⟨σ, hσF, hσ⟩ := cbtf_exists_perm (by omega : 7 ≤ m + 2) hF hi hj
  let x : ↥X := D.θ.symm σ
  have hx : D.θ x = σ := D.θ.apply_symm_apply σ
  have h1 := hβ x e j
  have h2 : (⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩ : ↥(commV X)) = e :=
    Subtype.ext (hfix x (fun f hf => by rw [hx]; exact hσF f hf))
  have h3 : ((σ : Equiv.Perm (Fin (m + 2)))⁻¹ j) = i := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact hσ.symm
  rw [h2, hx, h3] at h1
  exact h1.symm

private theorem cbtf_w (D : CbData Y t m X) (hm : 7 ≤ m) (hodd : Odd m)
    {β : ↥(commV X) →* ↥(G6.coreMod (m + 2))} (hβinj : Function.Injective β)
    (hβ : ∀ (x : ↥X) (e : ↥(commV X)) (i : Fin (m + 2)),
      cbtfCrd (β ⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩) i =
        cbtfCrd (β e) (((D.θ x : alternatingGroup (Fin (m + 2))) :
          Equiv.Perm (Fin (m + 2)))⁻¹ i))
    (p i : Fin (m + 2)) :
    cbtfCrd (β ⟨D.w p, (D.hwmem p).1⟩) i = if i = p then 0 else 1 := by
  classical
  set e : ↥(commV X) := ⟨D.w p, (D.hwmem p).1⟩ with he
  have hfixp : ∀ x : ↥X, (∀ f ∈ ({p} : Finset (Fin (m + 2))),
      ((D.θ x : alternatingGroup (Fin (m + 2))) : Equiv.Perm (Fin (m + 2))) f = f) →
        (x : MulAut V) (e : V) = (e : V) := by
    intro x hx
    show (x : MulAut V) (D.w p) = D.w p
    rw [D.hwact x x.2 p, hx p (Finset.mem_singleton_self p)]
  obtain ⟨j, hj⟩ := exists_ne p
  have hconst : ∀ k, k ≠ p → cbtfCrd (β e) k = cbtfCrd (β e) j := fun k hk =>
    cbtf_const D hβ hm (F := {p}) (by simp) e hfixp (by simpa using hk) (by simpa using hj)
  have hs := cbtf_sum (β e) {p} (cbtfCrd (β e) j) (fun k hk => hconst k (by simpa using hk))
  rw [Finset.sum_singleton, Finset.card_singleton, show m + 2 - 1 = m + 1 by omega] at hs
  have hev : ((m + 1 : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.2 (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
  rw [hev, zero_mul, add_zero] at hs
  have hlam : cbtfCrd (β e) j = 1 := by
    by_contra hne
    have h0 : cbtfCrd (β e) j = 0 := (by decide : ∀ z : ZMod 2, z ≠ 1 → z = 0) _ hne
    have h1 : e = 1 := by
      apply hβinj
      rw [map_one]
      apply cbtfCrd_ext
      intro k
      by_cases hk : k = p
      · rw [hk, hs]
        rfl
      · rw [hconst k hk, h0]
        rfl
    exact (D.hwmem p).2 (congrArg Subtype.val h1)
  by_cases hip : i = p
  · rw [hip]
    simpa using hs
  · rw [hconst i hip, hlam]
    simp [hip]

private theorem cbtf_fixY (D : CbData Y t m X) (hm : 7 ≤ m) (hodd : Odd m)
    {β : ↥(commV X) →* ↥(G6.coreMod (m + 2))}
    (hβ : ∀ (x : ↥X) (e : ↥(commV X)) (i : Fin (m + 2)),
      cbtfCrd (β ⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩) i =
        cbtfCrd (β e) (((D.θ x : alternatingGroup (Fin (m + 2))) :
          Equiv.Perm (Fin (m + 2)))⁻¹ i))
    (e : ↥(commV X)) (hfix : ∀ y ∈ Y, (y : MulAut V) (e : V) = (e : V))
    (i : Fin (m + 2)) (ha : i ≠ D.a) (hb : i ≠ D.b) :
    cbtfCrd (β e) i = cbtfCrd (β e) D.a + cbtfCrd (β e) D.b := by
  classical
  have hF : ({D.a, D.b} : Finset (Fin (m + 2))).card ≤ 3 := by
    have := Finset.card_le_two (a := D.a) (b := D.b)
    omega
  have hfixF : ∀ x : ↥X, (∀ f ∈ ({D.a, D.b} : Finset (Fin (m + 2))),
      ((D.θ x : alternatingGroup (Fin (m + 2))) : Equiv.Perm (Fin (m + 2))) f = f) →
        (x : MulAut V) (e : V) = (e : V) := fun x hx => hfix _ (cbtf_mem_Y D x hx)
  have hconst : ∀ k, k ≠ D.a → k ≠ D.b → cbtfCrd (β e) k = cbtfCrd (β e) i := fun k hka hkb =>
    cbtf_const D hβ hm hF e hfixF (by simp [hka, hkb]) (by simp [ha, hb])
  have hs := cbtf_sum (β e) {D.a, D.b} (cbtfCrd (β e) i)
    (fun k hk => hconst k (by simp_all) (by simp_all))
  rw [Finset.sum_pair D.hab, Finset.card_pair D.hab, show m + 2 - 2 = m by omega,
    Odd.natCast_zmod_two hodd, one_mul] at hs
  generalize cbtfCrd (β e) D.a = x at hs ⊢
  generalize cbtfCrd (β e) D.b = y at hs ⊢
  generalize cbtfCrd (β e) i = z at hs ⊢
  revert x y z
  decide

private theorem cbtf_eq (D : CbData Y t m X) (hm : 7 ≤ m) (hodd : Odd m)
    {β : ↥(commV X) →* ↥(G6.coreMod (m + 2))} (hβinj : Function.Injective β)
    (hβ : ∀ (x : ↥X) (e : ↥(commV X)) (i : Fin (m + 2)),
      cbtfCrd (β ⟨(x : MulAut V) (e : V), commV_invariant x.2 e.2⟩) i =
        cbtfCrd (β e) (((D.θ x : alternatingGroup (Fin (m + 2))) :
          Equiv.Perm (Fin (m + 2)))⁻¹ i))
    {e e' : ↥(commV X)} (he : ∀ y ∈ Y, (y : MulAut V) (e : V) = (e : V))
    (he' : ∀ y ∈ Y, (y : MulAut V) (e' : V) = (e' : V))
    (h1 : cbtfCrd (β e) D.a = cbtfCrd (β e') D.a) (h2 : cbtfCrd (β e) D.b = cbtfCrd (β e') D.b) :
    e = e' := by
  apply hβinj
  apply cbtfCrd_ext
  intro i
  by_cases ha : i = D.a
  · rw [ha]
    exact h1
  by_cases hb : i = D.b
  · rw [hb]
    exact h2
  rw [cbtf_fixY D hm hodd hβ e he i ha hb, cbtf_fixY D hm hodd hβ e' he' i ha hb, h1, h2]

theorem cbtFixY_mem (D : CbData Y t m X) (hm : 7 ≤ m) (hodd : Odd m) (hYX : Y ≤ X) {u : V}
    (hu : u ∈ commV X) (hfix : ∀ y ∈ Y, y u = u) :
    u = 1 ∨ u = D.w D.a ∨ u = D.w D.b ∨ u = D.w D.a * D.w D.b := by
  classical
  obtain ⟨β, hβinj, hβ⟩ := cbtf_beta D
  let ea : ↥(commV X) := ⟨D.w D.a, (D.hwmem D.a).1⟩
  let eb : ↥(commV X) := ⟨D.w D.b, (D.hwmem D.b).1⟩
  have hYa : ∀ y ∈ Y, (y : MulAut V) (ea : V) = (ea : V) := by
    intro y hy
    show y (D.w D.a) = D.w D.a
    rw [D.hwact y (hYX hy) D.a, (cbtf_fix_ab D hYX y hy).1]
  have hYb : ∀ y ∈ Y, (y : MulAut V) (eb : V) = (eb : V) := by
    intro y hy
    show y (D.w D.b) = D.w D.b
    rw [D.hwact y (hYX hy) D.b, (cbtf_fix_ab D hYX y hy).2]
  have hYab : ∀ y ∈ Y, (y : MulAut V) ((ea * eb : ↥(commV X)) : V) =
      ((ea * eb : ↥(commV X)) : V) := by
    intro y hy
    show y (D.w D.a * D.w D.b) = D.w D.a * D.w D.b
    rw [map_mul, show y (D.w D.a) = D.w D.a from hYa y hy, show y (D.w D.b) = D.w D.b from hYb y hy]
  have hY1 : ∀ y ∈ Y, (y : MulAut V) (((1 : ↥(commV X))) : V) = (((1 : ↥(commV X))) : V) := by
    intro y hy
    exact map_one y
  have ea_a : cbtfCrd (β ea) D.a = 0 := by
    rw [cbtf_w D hm hodd hβinj hβ]
    simp
  have ea_b : cbtfCrd (β ea) D.b = 1 := by
    rw [cbtf_w D hm hodd hβinj hβ]
    simp [D.hab.symm]
  have eb_a : cbtfCrd (β eb) D.a = 1 := by
    rw [cbtf_w D hm hodd hβinj hβ]
    simp [D.hab]
  have eb_b : cbtfCrd (β eb) D.b = 0 := by
    rw [cbtf_w D hm hodd hβinj hβ]
    simp
  let e : ↥(commV X) := ⟨u, hu⟩
  have hYe : ∀ y ∈ Y, (y : MulAut V) (e : V) = (e : V) := hfix
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases (cbtfCrd (β e) D.a) with h1 | h1 <;>
    rcases hcases (cbtfCrd (β e) D.b) with h2 | h2
  · left
    have := cbtf_eq D hm hodd hβinj hβ hYe hY1 (e' := 1) (by rw [h1, map_one]; rfl)
      (by rw [h2, map_one]; rfl)
    exact congrArg Subtype.val this
  · right; left
    have := cbtf_eq D hm hodd hβinj hβ hYe hYa (e' := ea) (by rw [h1, ea_a]) (by rw [h2, ea_b])
    exact congrArg Subtype.val this
  · right; right; left
    have := cbtf_eq D hm hodd hβinj hβ hYe hYb (e' := eb) (by rw [h1, eb_a]) (by rw [h2, eb_b])
    exact congrArg Subtype.val this
  · right; right; right
    have := cbtf_eq D hm hodd hβinj hβ hYe hYab (e' := ea * eb)
      (by rw [h1, map_mul, cbtfCrd_mul, ea_a, eb_a]; decide)
      (by rw [h2, map_mul, cbtfCrd_mul, ea_b, eb_b]; decide)
    exact congrArg Subtype.val this

end CFSG.CGT.PushingUpLit.CGT6
