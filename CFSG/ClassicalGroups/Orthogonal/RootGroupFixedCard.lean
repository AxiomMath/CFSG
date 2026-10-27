module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusFixedCard
public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusFixedCard

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

universe uV uM

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type uV} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

@[expose] noncomputable def HypPair.ofSingular {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0) : HypPair Q where
  e := u
  f := (polar Q u u')⁻¹ • u'
  Q_e := hu
  Q_f := by rw [map_smul_eq_sq, hu', mul_zero]
  polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ huu']

theorem HypPair.ofSingular_Lom {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0) :
    Lom Q (HypPair.ofSingular hu hu' huu').f = Lom Q u' :=
  Lom_smul (inv_ne_zero huu')

theorem stroth_2_1_ii_omegaMinus {m : ℕ} (hm : 2 ≤ m) (h : IsMinus Q m) {M : Type uM}
    [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0) [DistribMulAction (Gom Q) M] {u u' : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  refine omegaMinus_card_eq_pow_aux m hm Q h h2 (HypPair.ofSingular hu hu' huu') ?_
  rw [HypPair.ofSingular_Lom]
  exact hdec

theorem stroth_2_1_ii_omegaPlus {m : ℕ} (hm : 3 ≤ m) (h : IsPlus Q m) {M : Type uM}
    [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0) [DistribMulAction (Gom Q) M] {u u' : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ (m - 1) * n) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine omegaPlus_card_eq_pow_aux k (by omega) Q h h2 (HypPair.ofSingular hu hu' huu') ?_
  rw [HypPair.ofSingular_Lom]
  exact hdec

@[expose] def Gom.NonA2 (x : Gom Q) : Prop := ∃ y : V, polar Q y (x.app y) ≠ 0

theorem exists_eichler_of_nonA2 {v : V} (hv : Q v = 0) {x : Gom Q} (hx : x ∈ Lom Q v)
    (hn : x.NonA2) : ∃ w, polar Q v w = 0 ∧ Q w ≠ 0 ∧ x = Eom Q v w := by
  obtain ⟨w, hw, hxw⟩ := mem_rootGroup.mp hx
  have hx' : x = Eom Q v w := Subtype.ext hxw.symm
  refine ⟨w, hw, ?_, hx'⟩
  intro hQw
  obtain ⟨y, hy⟩ := hn
  apply hy
  have := polar_apply_eichler_self hv hw y
  rw [hx']
  show polar Q y (eichler Q v w y) = 0
  rw [this, hQw, zero_mul, sub_zero, CharTwo.two_eq_zero, zero_mul]

theorem stroth_2_1_ii_omega_fixed (hQ : (polarBilin Q).Nondegenerate) {M : Type*}
    [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0) [DistribMulAction (Gom Q) M] {u u' : V}
    (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) {g : Gom Q} (hg : g.app u = u')
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q))))
    {x : Gom Q} (hx : x ∈ Lom Q u') (hn : x.NonA2) :
    fixedSub M {x} = fixedSub M (Lom Q u' : Set (Gom Q)) ∧
      (comm M x).range = fixedSub M (Lom Q u' : Set (Gom Q)) ∧
      Nat.card M = Nat.card (fixedSub M (Lom Q u' : Set (Gom Q))) ^ 2 := by
  obtain ⟨w, hw, hQw, rfl⟩ := exists_eichler_of_nonA2 hu' hx hn
  have hcard : Nat.card (fixedSub M (Lom Q u : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q u' : Set (Gom Q))) := by
    have := card_fixedSub_Lom (M := M) g u
    rw [hg] at this
    exact this.symm
  exact pair_facts h2 (L₁ := Lom Q u) (L₂ := Lom Q u') hx (Eom_mul_self hw)
    (closure_Lom_insert_Eom hQ hu hu' huu' hw hQw) hdec hcard

end CFSG.ClassicalGroups.Orthogonal
