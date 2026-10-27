module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoWr

import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

section D8

@[expose] def Form (β : Finset (Fin 6)) (w : Wr 6) : Prop :=
  (∀ i ∈ β, w.perm i = i) ∧ ∃ k : ZMod 2, ∀ i ∈ β, w.vec i = k

theorem form_of_centralizes {β : Finset (Fin 6)} (hβ : β.card = 4) (w : Wr 6)
    (h : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) : Form β w := by
  obtain ⟨c, e, hw, he, hc⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w h
  have hcv : ∀ x ∈ β, c.vec x = 0 ∧ c.perm x = x := by
    intro x hx
    apply hc
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hx
  have hwp : w.perm = c.perm := by
    rw [hw, mul_perm]
    rcases he with rfl | rfl
    · rw [one_perm, mul_one]
    · rw [zOf_perm, mul_one]
  refine ⟨fun i hi => by rw [hwp]; exact (hcv i hi).2, ?_⟩
  have hcs : ∀ x ∈ β, c.perm.symm x = x := by
    intro x hx
    apply c.perm.injective
    rw [Equiv.apply_symm_apply, (hcv x hx).2]
  have hwv : ∀ x ∈ β, w.vec x = e.vec x := by
    intro x hx
    rw [hw, mul_vec, (hcv x hx).1, zero_add, hcs x hx]
  rcases he with rfl | rfl
  · exact ⟨0, fun i hi => by rw [hwv i hi]; rfl⟩
  · refine ⟨1, fun i hi => ?_⟩
    rw [hwv i hi, zOf_vec_apply, if_pos (by rw [range_emb]; exact hi)]

theorem mkQ_eq_one_of_centralizes (w : Wr 6)
    (h : ∀ x ∈ TwinThinPf8.Hn 6, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) : mkQ 6 w = 1 := by
  classical
  have hp : w.perm = 1 := perm_eq_one_of_centralizes w h
  have key : ∀ i j : Fin 6, w.vec i = w.vec j := by
    intro i j
    obtain ⟨α, hsub, hα⟩ := Finset.exists_superset_card_eq (s := ({i, j} : Finset (Fin 6))) (n := 4)
      (Finset.card_le_two.trans (by norm_num)) (by simp)
    obtain ⟨-, k, hk⟩ := form_of_centralizes hα w
      (fun b x hx => h x (TwinThinPf8.memBar_le_Hn α hα b hx))
    rw [hk i (hsub (by simp)), hk j (hsub (by simp))]
  exact mkQ_eq_one_of_const w hp (w.vec 0) fun i => key i 0

theorem mkQ_eq_of_invariants {β : Finset (Fin 6)} {p q b₀ : Fin 6} (hout : ∀ i, i ∉ β → i = p ∨ i = q)
    (hb₀ : b₀ ∈ β) {w w' : Wr 6} (hw : Form β w) (hw' : Form β w')
    (h1 : w.vec p + w.vec b₀ = w'.vec p + w'.vec b₀) (h2 : w.vec q + w.vec b₀ = w'.vec q + w'.vec b₀)
    (h3 : w.perm = w'.perm) : mkQ 6 w = mkQ 6 w' := by
  obtain ⟨-, k, hk⟩ := hw
  obtain ⟨-, k', hk'⟩ := hw'
  have hadd : ∀ a b c d : ZMod 2, a + b = c + d → a + c = b + d := by decide
  have hconst : ∀ j, w.vec j + w'.vec j = w.vec b₀ + w'.vec b₀ := by
    intro j
    by_cases hj : j ∈ β
    · rw [hk j hj, hk b₀ hb₀, hk' j hj, hk' b₀ hb₀]
    · rcases hout j hj with rfl | rfl
      · exact hadd _ _ _ _ h1
      · exact hadd _ _ _ _ h2
  have hvec : ∀ i, (w⁻¹ * w').vec i = w.vec b₀ + w'.vec b₀ := by
    intro i
    rw [mul_vec, inv_vec, inv_perm, Equiv.Perm.inv_def, Equiv.symm_symm]
    exact hconst _
  have hperm : (w⁻¹ * w').perm = 1 := by rw [mul_perm, inv_perm, h3, inv_mul_cancel]
  rw [mkQ_eq_iff]
  rcases (by decide : ∀ κ : ZMod 2, κ = 0 ∨ κ = 1) (w.vec b₀ + w'.vec b₀) with hκ | hκ
  · left
    refine Wr.ext (funext fun i => ?_) hperm
    rw [hvec, hκ]
    rfl
  · right
    refine Wr.ext (funext fun i => ?_) hperm
    rw [hvec, hκ]
    rfl

theorem vec_eq_of_sq {β : Finset (Fin 6)} {p q b₀ : Fin 6} (hb₀ : b₀ ∈ β) {w : Wr 6} (hw : Form β w)
    (hperm : w.perm = Equiv.swap p q) (hsq : mkQ 6 (w * w) = 1) : w.vec p = w.vec q := by
  obtain ⟨hpβ, -⟩ := hw
  have hmem : w * w ∈ piSub 6 := (QuotientGroup.eq_one_iff _).mp hsq
  have hb : (w * w).vec b₀ = 0 := by
    rw [mul_vec]
    have : w.perm.symm b₀ = b₀ := by
      apply w.perm.injective
      rw [Equiv.apply_symm_apply, hpβ b₀ hb₀]
    rw [this]
    exact zmod_two_add_self _
  rcases hmem with h1 | h1
  · have h2 := congrFun (congrArg Wr.vec h1) p
    rw [mul_vec, hperm, Equiv.symm_swap, Equiv.swap_apply_left, one_vec, Pi.zero_apply] at h2
    exact (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) _ _ h2
  · exfalso
    have h2 := congrFun (congrArg Wr.vec h1) b₀
    rw [hb] at h2
    exact absurd (show (0 : ZMod 2) = 1 from h2) (by decide)

theorem perm_eq_of_iff {β : Finset (Fin 6)} {p q : Fin 6} (hpq : p ≠ q) (hp : p ∉ β) (hq : q ∉ β)
    (hout : ∀ i, i ∉ β → i = p ∨ i = q) {w w' : Wr 6} (hw : Form β w) (hw' : Form β w')
    (h : w.perm = Equiv.swap p q ↔ w'.perm = Equiv.swap p q) : w.perm = w'.perm := by
  have hsw : Equiv.swap p q ≠ 1 := fun h' => hpq (by
    have := congrArg (fun σ : Equiv.Perm (Fin 6) => σ p) h'
    simpa using this.symm)
  rcases perm_dichotomy hpq hp hq hout _ hw.1 with e1 | e1 <;>
    rcases perm_dichotomy hpq hp hq hout _ hw'.1 with e2 | e2
  · rw [e1, e2]
  · exact absurd (e1.symm.trans (h.mpr e2)).symm hsw
  · exact absurd (e2.symm.trans (h.mp e1)).symm hsw
  · rw [e1, e2]

theorem card_le_four {β : Finset (Fin 6)} (hβ : β.card = 4) {G : Type*} [Group G] [Finite G]
    (hG : ∀ x : G, x * x = 1) (f : G → AEQ 6) (hf : Function.Injective f) (hsq : ∀ x, f x * f x = 1)
    (hc : ∀ x, ∀ b : Bool, ∀ y ∈ memBar β hβ b, f x * y * (f x)⁻¹ = y) : Nat.card G ≤ 4 := by
  classical
  obtain ⟨p, q, hpq, hp, hq, hout⟩ := exists_compl_pair hβ
  obtain ⟨b₀, hb₀⟩ : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
  choose w hw using fun x : G => (QuotientGroup.mk'_surjective (piSub 6) (f x) : ∃ a, mkQ 6 a = f x)
  have hform : ∀ x, Form β (w x) := fun x =>
    form_of_centralizes hβ (w x) fun b y hy => by rw [hw x]; exact hc x b y hy
  let inv : G → ZMod 2 × ZMod 2 × Bool := fun x =>
    ((w x).vec p + (w x).vec b₀, (w x).vec q + (w x).vec b₀, decide ((w x).perm = Equiv.swap p q))
  let T6 : Finset (ZMod 2 × ZMod 2 × Bool) :=
    Finset.univ.filter fun v => v.2.2 = true → v.1 = v.2.1
  have hT6 : T6.card = 6 := by decide
  have hinj : Function.Injective inv := by
    intro x x' h
    apply hf
    rw [← hw x, ← hw x']
    simp only [inv, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact mkQ_eq_of_invariants hout hb₀ (hform x) (hform x') h1 h2
      (perm_eq_of_iff hpq hp hq hout (hform x) (hform x') h3)
  have hmem : ∀ x, inv x ∈ T6 := by
    intro x
    simp only [T6, Finset.mem_filter, Finset.mem_univ, true_and, inv]
    intro h
    have hperm : (w x).perm = Equiv.swap p q := of_decide_eq_true h
    have hv := vec_eq_of_sq hb₀ (hform x) hperm (by rw [map_mul, hw x]; exact hsq x)
    rw [hv]
  have hle : Nat.card G ≤ 6 := by
    have hι : Function.Injective fun x => (⟨inv x, hmem x⟩ : T6) := fun x x' h =>
      hinj (congrArg Subtype.val h)
    have h1 := Nat.card_le_card_of_injective _ hι
    have h2 : Nat.card ↥T6 = 6 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT6]
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpg : IsPGroup 2 G := fun g => ⟨1, by rw [pow_one, pow_two]; exact hG g⟩
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rw [hk] at hle ⊢
  by_contra hcon
  have hk3 : 3 ≤ k := by
    by_contra h'
    have h'' : k < 3 := not_le.mp h'
    interval_cases k <;> simp at hcon
  have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
  omega

end D8

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
