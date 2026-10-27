module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LS8Core
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXTri
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.Burgoyne.DX
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
open CFSG.LocalAnalysis.ComponentInitial (orthogonal_model_isometry_abelianization_order_bound)
open scoped commutatorElement Pointwise


theorem spin8CentreFixedOutAbelian : Spin8CentreFixedOutAbelian := by
  intro K _ _ f hK α β hα hβ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hK, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      hf hK
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  set ρ := Tri.rhoT K with hρdef
  have hρ : IsTriality ρ := Tri.isTriality_rhoT K
  have h2K : (2 : K) ≠ 0 := two_ne_zero8 K hp2
  set F := projectivePointFamily (Q8 K) with hF
  set ρb := descend8 K ρ with hρb
  set Y := ρb • F with hY
  have hmemA : ∀ γ : MulAut (Sp8 K), (∀ c ∈ Subgroup.center (Sp8 K), γ c = c) →
      descend8 K γ ∈ projectivePointFamilyAut (Q8 K) := by
    intro γ hγ
    refine (liftAut_negOne8_iff K hp2 hρ _).1 ?_
    rw [liftAut_descend8]
    exact hγ _ (negOne8_mem_center K)
  have hρbF : ρb • F ≠ F := by
    intro h
    have h1 := (liftAut_negOne8_iff K hp2 hρ ρb).2 h
    rw [hρb, liftAut_descend8] at h1
    exact triality_moves_negOne8 h2K hρ h1
  have hYorb : Y ∈ MulAction.orbit (MulAut (P8 K)) F := ⟨ρb, rfl⟩
  have hYY : Y = plusCX 4 K ∨ Y = plusCXstar 4 K (by norm_num) := by
    rcases coordinate_plus_pointFamily_orbit_subset (K := K) (n := 4) rfl hYorb with h | h | h
    · exact absurd h hρbF
    · exact Or.inl h
    · exact Or.inr h
  have hρc : ρ (negOne8 K) ∈ Subgroup.center (Sp8 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := ρ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (negOne8_mem_center K) g']
  have hfixY : ∀ γ : MulAut (Sp8 K), (∀ c ∈ Subgroup.center (Sp8 K), γ c = c) →
      descend8 K γ • Y = Y := by
    intro γ hγ
    have h1 : liftAut K hp2 (ρb⁻¹ * descend8 K γ * ρb) (negOne8 K) = negOne8 K := by
      rw [map_mul, map_mul, map_inv, hρb, liftAut_descend8, liftAut_descend8, MulAut.mul_apply,
        MulAut.mul_apply, hγ _ hρc, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    have h2 : (ρb⁻¹ * descend8 K γ * ρb) • F = F := (liftAut_negOne8_iff K hp2 hρ _).1 h1
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
    exact h2
  obtain ⟨f', hcard, hmod⟩ := exists_model8 K (p := 3)
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus hmod K hcard (MulEquiv.refl _)
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hab0 := orthogonal_model_isometry_abelianization_order_bound _ .POmegaPlus
    (.inr (.inl rfl)) 4 3 f' hmod K hcard (quadPlus 4 K) (coe_quadPlus 4 K) (MulEquiv.refl _)
  have hab : Nat.card (Abelianization (matrixIsometries (coordinateQuadPlus 4 K))) ≤ 4 :=
    CFSG.RankThree.Automorphisms.card_abelianization_le_four_of_bound (plusIndexEquiv 4)
      (quadPlus 4 K) hab0
  have hE : projectivePointFamilyAut (Q8 K) = matrixProjectiveImage (Q8 K) :=
    coordinate_plus_family_eq_matrixImage hmod K hcard (MulEquiv.refl _)
  have h2 : ringChar K ≠ 2 := by
    rw [hchar]
    norm_num
  have hαE : descend8 K α ∈ matrixProjectiveImage (Q8 K) := hE ▸ hmemA α hα
  have hβE : descend8 K β ∈ matrixProjectiveImage (Q8 K) := hE ▸ hmemA β hβ
  obtain ⟨p, hp⟩ := S8.commutator_mem_inner_of_smul_eq K h2 hnd hQ hab hYY hαE (hfixY α hα) hβE
    (hfixY β hβ)
  obtain ⟨s, rfl⟩ := pi8_surjective K p
  refine ⟨s, ?_⟩
  have hl : liftAut K hp2 ⁅descend8 K α, descend8 K β⁆ = α * β * α⁻¹ * β⁻¹ := by
    rw [map_commutatorElement, liftAut_descend8, liftAut_descend8, commutatorElement_def]
  rw [← hl, ← hp]
  symm
  refine liftAut_unique K hp2 fun x => ?_
  rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

end CFSG.ComponentClassification.HarrisLit.T1
