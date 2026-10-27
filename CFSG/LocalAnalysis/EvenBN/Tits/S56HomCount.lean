module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Additive

theorem mem_zpowers_eq_one_or_self {E : Type*} [CommGroup E] (hE : ∀ e : E, e * e = 1)
    {z : E} (hz : z ≠ 1) {x : E} (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := by rw [sq]; exact hE z
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hk : z ^ k = z ^ (k % 2) := by
    have h := zpow_mod_orderOf z k
    rw [hord] at h
    simpa using h.symm
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · exact Or.inl (by rw [hk, h, zpow_zero])
  · exact Or.inr (by rw [hk, h, zpow_one])

theorem apply_eq_or_mul {E : Type*} [CommGroup E] (hE : ∀ e : E, e * e = 1)
    {z : E} (hz : z ≠ 1) (α : MulAut E) (hα : ∀ e : E, α e * e⁻¹ ∈ Subgroup.zpowers z)
    (e : E) : α e = e ∨ α e = z * e := by
  rcases mem_zpowers_eq_one_or_self hE hz (hα e) with h | h
  · exact Or.inl (mul_inv_eq_one.1 h)
  · exact Or.inr (mul_inv_eq_iff_eq_mul.1 h)

theorem apply_z_eq {E : Type*} [CommGroup E] (hE : ∀ e : E, e * e = 1)
    {z : E} (hz : z ≠ 1) (α : MulAut E) (hα : ∀ e : E, α e * e⁻¹ ∈ Subgroup.zpowers z) :
    α z = z := by
  rcases apply_eq_or_mul hE hz α hα z with h | h
  · exact h
  · exfalso
    have h1 : α z = 1 := by rw [h, hE z]
    exact hz ((map_eq_one_iff α (EquivLike.injective α)).1 h1)

theorem ind_mul_eq {E : Type*} [CommGroup E] [DecidableEq E] (hE : ∀ e : E, e * e = 1)
    {z : E} (hz : z ≠ 1) (α : MulAut E) (hα : ∀ e : E, α e = e ∨ α e = z * e) (a b : E) :
    (if α (a * b) = a * b then (0 : ZMod 2) else 1) =
      (if α a = a then (0 : ZMod 2) else 1) + (if α b = b then (0 : ZMod 2) else 1) := by
  have hne : ∀ x : E, z * x ≠ x := fun x h => hz (mul_eq_right.1 h)
  have hne2 : ∀ x y : E, x * (z * y) ≠ x * y := fun x y h => hne y (mul_left_cancel h)
  have hne3 : ∀ x y : E, z * x * y ≠ x * y := fun x y h => hne x (mul_right_cancel h)
  have hsq : ∀ x y : E, z * x * (z * y) = x * y := fun x y => by
    calc z * x * (z * y) = (z * z) * (x * y) := by ac_rfl
      _ = x * y := by rw [hE z, one_mul]
  rw [map_mul]
  rcases hα a with ha | ha <;> rcases hα b with hb | hb <;> rw [ha, hb] <;>
    simp only [hne, hne2, hne3, hsq, if_true, if_false, eq_self_iff_true, ↓reduceIte] <;>
    decide

theorem ite_zmod_two_eq_iff {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then (0 : ZMod 2) else 1) = (if q then 0 else 1)) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem card_mul_card_le_of_injective {K : Type*} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [Finite V] {t : V} (ht : t ≠ 0) {G : Type*}
    (φ : G → Module.Dual K V) (hφ : Function.Injective φ) (hφt : ∀ g, φ g t = 0) :
    Nat.card G * Nat.card K ≤ Nat.card V := by
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule K V, W = Submodule.span K {t} := ⟨_, rfl⟩
  have hW : Module.finrank K W = 1 := by
    rw [hWdef]
    exact finrank_span_singleton ht
  have hsum : Module.finrank K W + Module.finrank K W.dualAnnihilator
      = Module.finrank K V := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hmem : ∀ g, φ g ∈ W.dualAnnihilator := by
    intro g
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    rw [hWdef, Submodule.mem_span_singleton] at hw
    obtain ⟨a, rfl⟩ := hw
    rw [map_smul, hφt, smul_zero]
  let ψ : G → W.dualAnnihilator := fun g => ⟨φ g, hmem g⟩
  have hψ : Function.Injective ψ := fun g g' h => hφ (congrArg Subtype.val h)
  haveI : Finite W.dualAnnihilator := Module.finite_of_finite (R := K)
  have h1 : Nat.card G ≤ Nat.card W.dualAnnihilator := Nat.card_le_card_of_injective ψ hψ
  have hA : Nat.card W.dualAnnihilator = Nat.card K ^ Module.finrank K W.dualAnnihilator :=
    Module.natCard_eq_pow_finrank (K := K) (V := W.dualAnnihilator)
  have hV : Nat.card V = Nat.card K ^ Module.finrank K V :=
    Module.natCard_eq_pow_finrank (K := K) (V := V)
  have hfin : Module.finrank K V = 1 + Module.finrank K W.dualAnnihilator := by
    omega
  calc Nat.card G * Nat.card K ≤ Nat.card W.dualAnnihilator * Nat.card K :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card K ^ (1 + Module.finrank K W.dualAnnihilator) := by
        rw [hA, pow_add, pow_one]
        ring
    _ = Nat.card V := by rw [hV, hfin]

theorem card_le_of_trivial_on_quotient {E : Type*} [CommGroup E] [Finite E]
    (hE : ∀ e : E, e * e = 1) (z : E) (hz : z ≠ 1)
    (S : Subgroup (MulAut E)) (hS : ∀ α ∈ S, ∀ e : E, α e * e⁻¹ ∈ Subgroup.zpowers z) :
    Nat.card S ≤ Nat.card E / 2 := by
  classical
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) (fun v => by
    rw [two_nsmul]
    exact hE (toMul v))
  have hne : ∀ x : E, z * x ≠ x := fun x h => hz (mul_eq_right.1 h)
  have hfix : ∀ α : S, ∀ e : E, α.1 e = e ∨ α.1 e = z * e :=
    fun α e => apply_eq_or_mul hE hz α.1 (hS α.1 α.2) e
  let ind : S → Additive E →+ ZMod 2 := fun α =>
    AddMonoidHom.mk' (fun v => if α.1 (toMul v) = toMul v then (0 : ZMod 2) else 1)
      (fun v w => ind_mul_eq hE hz α.1 (hfix α) (toMul v) (toMul w))
  let φ : S → Module.Dual (ZMod 2) (Additive E) := fun α => (ind α).toZModLinearMap 2
  have hφ : Function.Injective φ := by
    intro α β h
    apply Subtype.ext
    apply MulEquiv.ext
    intro e
    have h' : (if α.1 e = e then (0 : ZMod 2) else 1)
        = (if β.1 e = e then (0 : ZMod 2) else 1) :=
      congrArg (fun L : Module.Dual (ZMod 2) (Additive E) => L (ofMul e)) h
    have hiff := ite_zmod_two_eq_iff h'
    rcases hfix α e with ha | ha
    · have hb : β.1 e = e := hiff.1 ha
      rw [ha, hb]
    · have hb : β.1 e ≠ e := fun hb => hne e (ha.symm.trans (hiff.2 hb))
      rcases hfix β e with hb' | hb'
      · exact absurd hb' hb
      · rw [ha, hb']
  have hφt : ∀ α : S, φ α (ofMul z) = 0 := fun α => by
    show (if α.1 z = z then (0 : ZMod 2) else 1) = 0
    rw [apply_z_eq hE hz α.1 (hS α.1 α.2)]
    simp
  have key := card_mul_card_le_of_injective (K := ZMod 2) (t := ofMul z) (fun h => hz h) φ hφ hφt
  rw [Nat.card_zmod] at key
  exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2 key

end CFSG.LocalAnalysis.EvenBN.Tits.S56
