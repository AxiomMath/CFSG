module

public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSU3
public import CFSG.ClassicalInvolution.Q3.Q3T8B17Fin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19M (involutionsConj_su3)

section SU3

theorem su3_sup_centralizer_eq_top {r r' : SU3} (hr : r * r = 1) (hr' : r' * r' = 1)
    (hr1 : r ≠ 1) (hr'1 : r' ≠ 1) (hne : r ≠ r') (hc : r * r' = r' * r) :
    Subgroup.centralizer ({r} : Set SU3) ⊔ Subgroup.centralizer ({r'} : Set SU3) = ⊤ := by
  have hK : Nat.card F9 = (3 ^ 1) ^ 2 := card_F9
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 : (2 : F9) ≠ 0 := two_ne_zero_F9
  have hn : 2 ≤ 3 := by norm_num
  have hconj := involutionsConj_su3 (p := 3) (f := 1) hK h2
  obtain ⟨g₁, hg₁⟩ := hconj rootInvSU₃ r rootInvSU₃_mul_self hr rootInvSU₃_ne_one hr1
  obtain ⟨g₂, hg₂⟩ := hconj rootInvSU₃ r' rootInvSU₃_mul_self hr' rootInvSU₃_ne_one hr'1
  have h₁ : IsLongRootSU2 F9 3 1 hn ((rootSU2 F9 3 1 hn).map (MulAut.conj g₁).toMonoidHom) r :=
    ⟨g₁, rfl, hg₁.symm⟩
  have h₂ : IsLongRootSU2 F9 3 1 hn ((rootSU2 F9 3 1 hn).map (MulAut.conj g₂).toMonoidHom) r' :=
    ⟨g₂, rfl, hg₂.symm⟩
  rcases inf_eq_bot_or_exists_conj_su hK hp (le_refl 3) h₁ h₂ (show Commute r r' from hc) hne with
    hV | ⟨g, e₁, e₂, hi₁, hi₂⟩
  · exfalso
    have d₁ := h₁.finrank_minusSpaceSU h2
    have d₂ := h₂.finrank_minusSpaceSU h2
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (minusSpaceSU r) (minusSpaceSU r')
    have hle : Module.finrank F9 ↥(minusSpaceSU r ⊔ minusSpaceSU r') ≤ 3 := by
      have := Submodule.finrank_le (minusSpaceSU r ⊔ minusSpaceSU r')
      simpa using this
    rw [hV, d₁, d₂] at hsum
    simp at hsum
    omega
  · have hLL : (blockEmb F9 3 1 3 2 0 (by omega)).range.map (MulAut.conj g).toMonoidHom ⊔
        (blockEmb F9 3 1 3 2 1 (by omega)).range.map (MulAut.conj g).toMonoidHom = ⊤ := by
      obtain ⟨θ, hinj, hrange, -⟩ := exists_injective_hom_of_su_frame hK hp (le_refl 3) g rfl rfl
      have hsurj : Function.Surjective θ := Finite.injective_iff_surjective.mp hinj
      rw [← hrange]
      exact MonoidHom.range_eq_top.mpr hsurj
    have hcomm : ∀ j : ℕ, ∀ hj : j + 2 ≤ 3, ∀ A : Su F9 3 1 2,
        blockEmb F9 3 1 3 2 j hj A * blockEmb F9 3 1 3 2 j hj (negOneSU F9 3 1) =
          blockEmb F9 3 1 3 2 j hj (negOneSU F9 3 1) * blockEmb F9 3 1 3 2 j hj A := by
      intro j hj A
      rw [← map_mul, ← map_mul, negOneSU_comm]
    have hsub : ∀ (j : ℕ) (hj : j + 2 ≤ 3) (i : SU3),
        i = g * blockEmb F9 3 1 3 2 j hj (negOneSU F9 3 1) * g⁻¹ →
        (blockEmb F9 3 1 3 2 j hj).range.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.centralizer ({i} : Set SU3) := by
      intro j hj i hi x hx
      obtain ⟨y, ⟨A, rfl⟩, rfl⟩ := hx
      rw [Subgroup.mem_centralizer_singleton_iff, hi]
      set a : SU3 := blockEmb F9 3 1 3 2 j hj A with ha
      set b : SU3 := blockEmb F9 3 1 3 2 j hj (negOneSU F9 3 1) with hb
      have hab : a * b = b * a := hcomm j hj A
      show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
      calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [hab]
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
    rw [eq_top_iff, ← hLL]
    exact sup_le_sup (hsub 0 (by omega) r hi₁) (hsub 1 (by omega) r' hi₂)

theorem linkModelFacts_su3 : LinkModelFacts SU3 := by
  refine ⟨fun u v hu hu1 hv hv1 =>
    involutionsConj_su3 (p := 3) (f := 1) card_F9 two_ne_zero_F9 u v hu hv hu1 hv1, ?_⟩
  intro u v hu hu1 hv hv1 huv hcomm
  rw [eq_top_iff, ← su3_sup_centralizer_eq_top hu hv hu1 hv1 huv hcomm]
  exact le_sup_left

end SU3

section Model


theorem linkModelFacts_psu3_model : LinkModelFacts (CompData.model .PSU 3).G := by
  obtain ⟨e, -⟩ := RouteD.psu_model_equiv (p := 3) (f := 1) (by norm_num) statedLieAdmissible_psu3
  exact LinkModelFacts.of_mulEquiv e linkModelFacts_su3

end Model

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
