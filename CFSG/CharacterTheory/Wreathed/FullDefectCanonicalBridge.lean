module

public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalBlockExistence
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralNormalizerProjection

public section

open scoped Classical

namespace CFSG.FullDefectCanonical

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.BlockBasics CFSG.BrauerThirdMainTheorem.Helpers

variable {G : Type} [Group G] [Fintype G]

@[expose] noncomputable def ofCoeffFun (z : G → ℂ) : MonoidAlgebra ℂ G :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm z)

omit [Group G] in
theorem ofCoeffFun_coeff (z : G → ℂ) (g : G) : (ofCoeffFun z).coeff g = z g := rfl

theorem ofCoeffFun_mem (m : Ideal BlocksAlgInt) [m.IsMaximal] {z : G → ℂ}
    (hz : BlocksIsCentralR m z) :
    ofCoeffFun z ∈ centralCoefficientSubring (G := G) (localizedComplexIntegerRing m) := by
  refine Subring.mem_inf.mpr ⟨fun g => ?_, Subring.mem_center_iff.mpr fun o => ?_⟩
  · rw [ofCoeffFun_coeff, mem_localizedComplexIntegerRing_iff]
    exact hz.1 g
  · have hc := groupAlgebra_central_of_coeff_conjugation (ofCoeffFun z) (by
      intro g h
      rw [ofCoeffFun_coeff, ofCoeffFun_coeff]
      exact hz.2 g h) o
    exact hc.eq.symm

theorem brauerCorr_of_residue_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup G) (hP : IsPGroup p P)
    (H : Subgroup G) (hCH : Subgroup.centralizer (P : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (P : Set G)) (lb : FiniteIrreducibleCharacterBasis H)
    (θ : lb.index) (χ : basis.index)
    (h : brauerNormalizerCharacterResidueHom ideal p P hP H hCH hHN lb θ =
      centralCharacterResidueHom basis ideal χ) :
    BlocksBrauerCorr ideal P H (BlocksBlockOf ideal H (lb.representation θ).character)
      (BlocksBlockOf ideal G (basis.representation χ).character) := by
  have hm : ideal.IsMaximal := inferInstance
  apply brauerCorr_of_scalar_congr ideal hm G P H hHN
    ⟨_, basis_character_mem_irr basis χ, rfl⟩ ⟨_, basis_character_mem_irr lb θ, rfl⟩
    (mem_blockOf_self ideal (basis_character_mem_irr basis χ))
    (mem_blockOf_self ideal (basis_character_mem_irr lb θ))
  intro z hz
  let w : centralCoefficientSubring (G := G) (localizedComplexIntegerRing ideal) :=
    ⟨ofCoeffFun z, ofCoeffFun_mem ideal hz⟩
  have hw := congrArg (fun f => f w) h
  let a := localCentralCharacterHom basis ideal χ w
  let b := localCentralCharacterHom lb ideal θ
    (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal) P H hCH hHN w)
  have hab : localizedComplexIntegerResidue ideal (a - b) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hw.symm
  rw [localizedComplexIntegerResidue_eq_zero_iff] at hab
  have ha : (a : ℂ) = BlocksCentralChar (basis.representation χ).character z := by
    change centralCharacterScalar basis (ofCoeffFun z) χ = _
    rw [centralCharacterScalar_eq]
    rfl
  have hb : (b : ℂ) = BlocksCentralChar (lb.representation θ).character
      (BlocksBrauerProj P H z) := by
    change centralCharacterScalar lb (centralNormalizerCoefficientProjection
      (localizedComplexIntegerRing ideal) P H hCH hHN w).val θ = _
    rw [centralCharacterScalar_eq]
    congr 1
    funext k
    rw [centralNormalizerCoefficientProjection_coeff, brauerProj_apply]
    rfl
  have hsub : ((a - b : localizedComplexIntegerRing ideal) : ℂ) = (a : ℂ) - b := rfl
  rw [hsub, ha, hb] at hab
  exact hab

end CFSG.FullDefectCanonical
