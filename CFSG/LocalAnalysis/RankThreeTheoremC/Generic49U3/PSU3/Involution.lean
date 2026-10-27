module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

namespace U3InvolutionCentral

open CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model CFSG.AGLEmbedding

private theorem model_central {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hfix : Nat.card {x : F // J.conj x = x} = p ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 < p ^ f) (h2 : (2 : F) ≠ 0)
    {t z : ProjectiveSpecialUnitaryMatrixGroup J} (htR : t ∈ rootGroup J hJ) (ht1 : t ≠ 1)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hzt : z * t = t * z) :
    t ∈ Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have htfix : t • pinf J hJ = pinf J hJ :=
    MulAction.mem_stabilizer_iff.mp (rootGroup_le_stabilizer J hJ htR)
  have hzpinf : z • pinf J hJ = pinf J hJ := by
    by_contra hne
    have e1 : ((⟨t, htR⟩ : rootGroup J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) •
        (z • pinf J hJ) = z • pinf J hJ := by
      show t • (z • pinf J hJ) = z • pinf J hJ
      rw [← mul_smul, ← hzt, mul_smul, htfix]
    have e2 : ((1 : rootGroup J hJ) : ProjectiveSpecialUnitaryMatrixGroup J) •
        (z • pinf J hJ) = z • pinf J hJ := by
      rw [Subgroup.coe_one, one_smul]
    have hu := (rootGroup_regular J hJ (z • pinf J hJ) (z • pinf J hJ) hne hne).unique e1 e2
    exact ht1 (congrArg Subtype.val hu)
  have hzN : z ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [UnitaryModel.normalizer_rootGroup_eq_stabilizer_pinf J hJ hF hfix hq]
    exact MulAction.mem_stabilizer_iff.mpr hzpinf
  have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  obtain ⟨u, hu, hzu⟩ := UnitaryModel.exists_conj_invol J hJ hF hfix hp hp2 hq h2 hzN hord
  have hcomm : (u⁻¹ * t * u) * UnitaryModel.invol J hJ =
      UnitaryModel.invol J hJ * (u⁻¹ * t * u) := by
    calc (u⁻¹ * t * u) * UnitaryModel.invol J hJ = u⁻¹ * (t * z) * u := by rw [hzu]; group
      _ = u⁻¹ * (z * t) * u := by rw [hzt]
      _ = UnitaryModel.invol J hJ * (u⁻¹ * t * u) := by rw [hzu]; group
  have hwR : u⁻¹ * t * u ∈ rootGroup J hJ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) htR) hu
  have hwC : u⁻¹ * t * u ∈ Subgroup.centralizer
      ({UnitaryModel.invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hmem : u⁻¹ * t * u ∈ rootGroup J hJ ⊓ Subgroup.centralizer
      ({UnitaryModel.invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    ⟨hwR, hwC⟩
  rw [UnitaryModel.rootGroup_inf_centralizer_invol J hJ hF hfix h2] at hmem
  have hwCR := (Subgroup.mem_inf.mp hmem).2
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hs : u⁻¹ * r * u ∈ rootGroup J hJ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hr) hu
  have hsw : (u⁻¹ * r * u) * (u⁻¹ * t * u) = (u⁻¹ * t * u) * (u⁻¹ * r * u) :=
    Subgroup.mem_centralizer_iff.mp hwCR _ hs
  calc r * t = (u * (u⁻¹ * r * u) * u⁻¹) * t := by group
    _ = u * ((u⁻¹ * r * u) * (u⁻¹ * t * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * t * u) * (u⁻¹ * r * u)) * u⁻¹ := by rw [hsw]
    _ = t * r := by group

end U3InvolutionCentral

open CFSG.AGLEmbedding
open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem u3_involution_central {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (T : Sylow p K) {z t : K} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (htT : t ∈ (T : Subgroup K)) (ht1 : t ≠ 1) (hzt : z * t = t * z) :
    t ∈ Subgroup.centralizer ((T : Subgroup K) : Set K) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨q, hqp, -, hv, ⟨e0⟩⟩ := hK
  have hd : IsUnitaryIndex p (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) :=
    ⟨q, hqp, rfl⟩
  have hLd : Nonempty (K ≃* CatGroup (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) :=
    ⟨e0⟩
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hF, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd hLd)
  have : CharP F p := UnitaryModel.charP_of_card Fact.out hF
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff F p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hF hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e T S
  have hT : (T : Subgroup K).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have htR : e' t ∈ rootGroup J hJ := by
    rw [← hT]
    exact (UnitaryModel.mem_map_iff e' _ t).2 htT
  have hz'1 : e' z ≠ 1 := fun h => hz1 (e'.injective (h.trans (map_one e').symm))
  have ht'1 : e' t ≠ 1 := fun h => ht1 (e'.injective (h.trans (map_one e').symm))
  have hz'2 : e' z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hz't : e' z * e' t = e' t * e' z := by rw [← map_mul, ← map_mul, hzt]
  have key := U3InvolutionCentral.model_central J hJ hF hfix hp hp2 hq h2 htR ht'1 hz'1 hz'2 hz't
  apply (UnitaryModel.mem_centralizer_map_iff e' (T : Subgroup K) t).1
  rw [hT]
  exact key

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
