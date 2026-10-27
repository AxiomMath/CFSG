module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatEvenOuterClassical

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical

section Component

variable {X : Type} [Group X]

theorem isComponent_top_of_lieModel_PSp {m f : ℕ} (h : LieModel X .PSp m 2 f) :
    IsComponent (⊤ : Subgroup X) ∧ LieModel (⊤ : Subgroup X) .PSp m 2 f := by
  have hs : IsSimpleGroup X := F4Pilot.isSimpleGroup_of_lieModel_PSp h
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
    have hp : (Nat.card X).Prime := IsSimpleGroup.prime_card
    have h8 := two_pow_eight_dvd_card_of_lieModel_PSp h
    rcases (Nat.dvd_prime hp).1 h8 with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp
  have hq : IsQuasisimple X := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  exact ⟨⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩,
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv Subgroup.topEquiv.symm h⟩

theorem isPComponent_top_of_lieModel_PSp [Finite X] {m f : ℕ} (h : LieModel X .PSp m 2 f) :
    IsPComponent 2 (⊤ : Subgroup X) :=
  isPComponent_of_isComponent_lieModel_PSp_two (isComponent_top_of_lieModel_PSp h).1
    (isComponent_top_of_lieModel_PSp h).2

end Component

section NormalForm

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_eq_symmetryAut_of_lieModel_PSp {f n : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    {v : Fin (2 * n) → K} (hv : Q v = 1) (α : MulAut (matrixProjectiveDerived Q))
    (hα2 : α * α = 1) (hout : α ∉ inner (matrixProjectiveDerived Q)) {m f' : ℕ}
    (hfix : LieModel (fixedSubgroup α) .PSp m 2 f') :
    ∃ Ψ : MulAut (matrixProjectiveDerived Q), α = Ψ * symmetryAut Q v * Ψ⁻¹ := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  obtain ⟨β, hβ⟩ := hconj α hα2
  set γ := β⁻¹ * α * β with hγdef
  have hc : MulAut.congr β⁻¹ α = γ := MulEquiv.ext fun _ => rfl
  have hγo : γ ∉ inner (matrixProjectiveDerived Q) := by
    rw [← hc, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  have hγ1 : γ ≠ 1 := fun h1 => hγo (h1 ▸ one_mem _)
  have hγγ : γ * γ = 1 := by
    rw [hγdef]
    calc β⁻¹ * α * β * (β⁻¹ * α * β) = β⁻¹ * (α * α) * β := by group
      _ = 1 := by rw [hα2]; group
  have hγ2 : orderOf γ = 2 := orderOf_eq_prime (by rw [_root_.sq]; exact hγγ) hγ1
  have hγfix : LieModel (fixedSubgroup γ) .PSp m 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))) hfix
  have hP : IsPComponent 2 (⊤ : Subgroup (fixedSubgroup γ)) :=
    isPComponent_top_of_lieModel_PSp hγfix
  have hPm : LieModel (⊤ : Subgroup (fixedSubgroup γ)) .PSp m 2 f' :=
    (isComponent_top_of_lieModel_PSp hγfix).2
  obtain ⟨S, hS, hSγ⟩ := exists_unit_rep hβ
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = γ := hs.trans hSγ
    have hss : s * s = 1 := by
      apply isometryKappa_injective hQ hT hE
      rw [map_mul, map_one]
      change matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) *
        matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) = 1
      rw [hs', hγγ]
    have hs1 : (s : GL (Fin (2 * n)) K) ≠ 1 := by
      intro h
      have h1 : s = 1 := Subtype.ext h
      rw [h1, map_one, map_one] at hs'
      exact hγ1 hs'.symm
    by_cases hr : 2 ≤ (((s : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) - 1).rank
    · exfalso
      have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
        hQ hT hE
      have hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2 := by
        rw [hs']
        exact hγ2
      have hch := LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
        (fixedInnerEquiv hcj _).symm
        (CatLeafProof.isCharacteristicP_inner_centralizer_of_two_le_rank hQ hT hE s hs2 hr)
      rw [hs'] at hch
      exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch _ hP
    · obtain ⟨w, hw, hsw⟩ :=
        exists_symmetry_of_rank_le_one hQ s.2 (congrArg Subtype.val hss) hs1 (by omega)
      have hsym : s = symmetryIsometry Q w := Subtype.ext hsw
      obtain ⟨g, hgv⟩ := F4Pilot.exists_isometry_mulVec_eq hn hQ hv hw
      refine ⟨β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g), ?_⟩
      have h1 : γ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) *
          symmetryAut Q v * (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g))⁻¹ := by
        rw [F4Pilot.conj_symmetryAut, hgv, ← hs', hsym]
      calc α = β * γ * β⁻¹ := by rw [hγdef]; group
        _ = _ := by rw [h1]; group
  · exfalso
    obtain ⟨t', n', f'', ht', hadm', hm'⟩ :=
      LinearPilot.omega_field_pComponents hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ _ hP
    exact false_of_lieModel_ne_PSp (sp2mEvenTypeDetClassical m) hPm
      (Or.inl (by rcases ht' with rfl | rfl <;> decide)) (by rcases ht' with rfl | rfl <;> decide)
      hadm' hm'

end NormalForm

end CFSG.SeitzReduction.SymplecticPilot
