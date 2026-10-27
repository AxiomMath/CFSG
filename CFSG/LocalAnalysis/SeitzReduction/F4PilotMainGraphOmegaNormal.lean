module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusNormal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalOmega

public section

namespace CFSG.SeitzReduction.F4Pilot

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

variable {K : Type} [Field K]

theorem conj_symmetryAut {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (g : matrixIsometries Q)
    (v : Fin d → K) :
    matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) * symmetryAut Q v *
        (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g))⁻¹ =
      symmetryAut Q (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) := by
  have h : g * symmetryIsometry Q v * g⁻¹ =
      symmetryIsometry Q (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) :=
    Subtype.ext (conj_symmetryGL g.2)
  unfold symmetryAut
  rw [← h, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]

variable [Finite K]

theorem exists_isometry_mulVec_eq [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    {v w : Fin (2 * n) → K} (hv : Q v = 1) (hw : Q w = 1) :
    ∃ g : matrixIsometries Q, ((g : GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) *ᵥ v
      = w := by
  obtain ⟨-, -, -, -, -, h6⟩ := finite_even_regular_quadratic_normal_forms Q hQ
  obtain ⟨P₁, P₂, -, h12, -, -⟩ := h6 n (by rw [Module.finrank_fin_fun]) hn
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hw
    exact zero_ne_one hw
  obtain ⟨g, hg, hgv⟩ := exists_mem_elementaryGroup_apply_eq hQ h12 hv0 hw0 (hv.trans hw.symm)
  refine ⟨⟨matrixLinearIso.symm g, ?_⟩, ?_⟩
  · change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rw [MulEquiv.apply_symm_apply]
    exact elementaryGroup_le_orthogonalGroup Q hg
  · change matrixLinearIso (matrixLinearIso.symm g) v = w
    rw [MulEquiv.apply_symm_apply, hgv]


theorem exists_conj_eq_symmetryAut {f n : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    {v : Fin (2 * n) → K} (hv : Q v = 1) (α : MulAut (matrixProjectiveDerived Q))
    (hα2 : α * α = 1) (hout : α ∉ inner (matrixProjectiveDerived Q)) {f' : ℕ}
    (hfix : LieModel (fixedSubgroup α) .PSp 3 2 f') :
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
  have hγfix : LieModel (fixedSubgroup γ) .PSp 3 2 f' :=
    LieType.CurtisTits.lieModel_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))) hfix
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
      exact graphNormal_false_of_notSp6Components hγfix (notSp6Components_of_isCharacteristicP hch)
    · obtain ⟨w, hw, hsw⟩ :=
        exists_symmetry_of_rank_le_one hQ s.2 (congrArg Subtype.val hss) hs1 (by omega)
      have hsym : s = symmetryIsometry Q w := Subtype.ext hsw
      obtain ⟨g, hgv⟩ := exists_isometry_mulVec_eq hn hQ hv hw
      refine ⟨β * matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g), ?_⟩
      have h1 : γ = matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g) *
          symmetryAut Q v * (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q g))⁻¹ := by
        rw [conj_symmetryAut, hgv, ← hs', hsym]
      calc α = β * γ * β⁻¹ := by rw [hγdef]; group
        _ = _ := by rw [h1]; group
  · exact (graphNormal_false_of_notSp6Components hγfix
      (notSp6Components_omega_field hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)).elim

end CFSG.SeitzReduction.F4Pilot
