module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallGammaCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAut
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallGamma

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

omit [Finite K] in
theorem eq_one_of_smul_eq {x : ProjectiveSpecialUnitaryMatrixGroup J} (hx : x ∈ rootGroup J hJ)
    {β : IsoPoint J} (hβ : β ≠ pinf J hJ) (hfix : x • β = β) : x = 1 := by
  obtain ⟨r0, -, huniq⟩ := rootGroup_regular J hJ β β hβ hβ
  have h1 := huniq ⟨x, hx⟩ hfix
  have h2 := huniq 1 (one_smul _ _)
  exact congrArg Subtype.val (h1.trans h2.symm)

omit [Finite K] in
theorem normalizer_le_stabilizer {Q : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hQR : Q ≤ rootGroup J hJ) (hQ : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  by_contra hne
  obtain ⟨q, hq⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
  have hqR : (q : ProjectiveSpecialUnitaryMatrixGroup J) ∈ rootGroup J hJ := hQR q.2
  have hy : g * (q : ProjectiveSpecialUnitaryMatrixGroup J) * g⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.1 hg q).1 q.2
  have hq' : (q : ProjectiveSpecialUnitaryMatrixGroup J) • pinf J hJ = pinf J hJ :=
    MulAction.mem_stabilizer_iff.1 (rootGroup_le_stabilizer J hJ hqR)
  have hyfix : (g * (q : ProjectiveSpecialUnitaryMatrixGroup J) * g⁻¹) • (g • pinf J hJ) =
      g • pinf J hJ := by
    rw [smul_smul, show g * (q : ProjectiveSpecialUnitaryMatrixGroup J) * g⁻¹ * g =
      g * q by group, mul_smul, hq']
  have h1 := eq_one_of_smul_eq J hJ (hQR hy) hne hyfix
  apply hq
  apply Subtype.ext
  calc (q : ProjectiveSpecialUnitaryMatrixGroup J)
      = g⁻¹ * (g * (q : ProjectiveSpecialUnitaryMatrixGroup J) * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

variable {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2)
  (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem smallGammaData_rootGroup [Fact p.Prime] (hq : 2 < p ^ f) :
    SmallGammaData (ProjectiveSpecialUnitaryMatrixGroup J) (rootGroup J hJ) := by
  have hN := UnitaryModel.normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq
  refine ⟨fun Q hQR hQ => ?_, ?_⟩
  · rw [hN]
    exact normalizer_le_stabilizer J hJ hQR hQ
  · rw [hN]
    exact UnitaryModel.isSolvable_stabilizer_pinf J hJ hK hfix

end Model

theorem smallGammaData_unitary {L : Type} [Group L] [Finite L] {p : ℕ}
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow p L) : SmallGammaData L (U : Subgroup L) := by
  obtain ⟨hp, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  exact SmallGammaData.of_equiv_map e' (he'.trans hS) (smallGammaData_rootGroup J hJ hK hfix hq)

theorem smallGammaData_isSmallUnitary {K : Type} [Group K] [Finite K] (h : IsSmallUnitary 3 K)
    (T : Sylow 3 K) : SmallGammaData K (T : Subgroup K) := by
  obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ := h
  exact smallGammaData_unitary ⟨q, hqp, hdq⟩ ⟨e⟩ T

end CFSG.AGLEmbedding.KFactProofs.SmallGamma
