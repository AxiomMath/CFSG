module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinOffender
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinSylow7

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.FieldFour

section Generic

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : List (List ℤ)} (hPD : PosData τ R)
  (hc0 : 0 < τ.cartan.det) {k : Type*} [Field k] [Finite k]
include hPD hc0

theorem card_le_of_conj_abelian (U : Subgroup (hV.minGroup k)) (hU : U = posUnip hV k)
    (hconj : ∀ A : Subgroup (hV.minGroup k), (∀ a ∈ A, a ^ 2 = 1) →
      ∃ g : hV.minGroup k, A.map (MulAut.conj g).toMonoidHom ≤ U) (N : ℕ)
    (hab : ∀ X : Finset (Fin τ.rank → ℤ), (∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ) →
      (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot τ (γ + δ)) → X.card ≤ N)
    (A : Subgroup (hV.minGroup k)) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ Nat.card k ^ N := by
  obtain ⟨g, hg⟩ := hconj A hel
  have hel' : ∀ b ∈ A.map (MulAut.conj g).toMonoidHom, b ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hel a ha, map_one]
  have hAU : A.map (MulAut.conj g).toMonoidHom ≤ lvlU hV k (fWt τ.rank) 1 := by
    rw [lvlU_one_eq hV hPD k, ← hU]; exact hg
  obtain ⟨X, Y, hXr, hXX, -, hcard, -, -⟩ := exists_leading_data (hV := hV) (k := k) hc0
    (fun γ δ hγ hδ h => hPD.inj γ δ hγ hδ h) hAU (comm_of_exp_two hel')
  have hXP : ∀ γ ∈ X, IsRoot τ γ ∧ 0 < ht γ := fun γ hγ =>
    ⟨(hXr γ hγ).1, (hPD.pos γ (hXr γ hγ).1).1 (hXr γ hγ).2⟩
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  rw [← natCard_map_conj' hV k A g]
  exact hcard.trans (Nat.pow_le_pow_right hq (hab X hXP hXX))

end Generic

section E7

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem e7_abelian_card_bound (A : Subgroup (e7Data_valid.minGroup K)) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ≤ Nat.card K ^ 27 := by
  have := finite_minGroup7 K
  exact card_le_of_conj_abelian e7Data_valid posData_E7 (MinData.det_cartan_pos posDef_cartan_E7)
    (posU7 K) (by unfold posU7 posUnip; simp only [one_mul])
    (fun B hB => e7_conj_into_posU7 K B (isPGroup_of_sq B hB)) 27
    (fun X hXP hXX => e7_abelian_card_le X hXP hXX) A hel

theorem e7Isogeny_injective : Function.Injective (e7Isogeny K) := by
  intro x y hxy
  have h : x⁻¹ * y ∈ MonoidHom.ker (e7Isogeny K) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  rw [MonoidHom.mem_ker] at h
  exact inv_mul_eq_one.1 (two_group_inf_ker7 K h)

theorem e7_adjoint_abelian_card_bound (A : Subgroup (adjointGroup Tag.E7 K))
    (hel : ∀ a ∈ A, a ^ 2 = 1) : Nat.card A ≤ Nat.card K ^ 27 := by
  have hinj := e7Isogeny_injective K
  have hsurj := e7Isogeny_surjective K
  set A' := A.comap (e7Isogeny K) with hA'
  have hel' : ∀ a ∈ A', a ^ 2 = 1 := by
    intro a ha
    apply hinj
    rw [map_pow, map_one]
    exact hel _ ha
  have hmap : A'.map (e7Isogeny K) = A := Subgroup.map_comap_eq_self_of_surjective hsurj A
  have hcard : Nat.card A' = Nat.card A := by
    rw [← hmap]
    exact (Nat.card_congr (A'.equivMapOfInjective _ hinj).toEquiv)
  rw [← hcard]
  exact e7_abelian_card_bound K A' hel'

end E7

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
