module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6ThreeCardA2
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup chainRoot13_mem_parabolicRoots
  chainRoot56_mem_parabolicRoots torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer)
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus twistedFixedPoints
  mem_twistedFixedPoints)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Lattice (e6T3W toMat lget)
open scoped Matrix MatrixGroups Pointwise

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

private theorem dvd_card_of_layerEquiv {K : Type} [Field K] [Finite K] {p : ℕ}
    {P : Subgroup (ModGL Tag.E6 Ω)} (h : Nonempty (↥P ≃* SL(3, K)))
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) : p ∣ Nat.card P := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.RankThree.PartOne.KE6.NonsplitLayers.dvd_card_SL_three_of_dvd_phiThree hpq

theorem phi3_A2A2_layer_equivs {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {S₁ S₂ : Set (Fin Tag.E6.rank → ℤ)} (hS₁roots : ∀ α ∈ S₁, IsRoot Tag.E6 α)
    (hvS₁ : ∀ α ∈ S₁, e6T3W • α ∈ S₁) {w : WeylGroup Tag.E6}
    (hw₁ : (w • ·) '' S₁ = parabolicRoots Tag.E6 support13)
    (hS₂roots : ∀ α ∈ S₂, IsRoot Tag.E6 α)
    (hvS₂ : ∀ α ∈ S₂, e6T3W • α ∈ S₂)
    (hw₂ : (w • ·) '' S₂ = parabolicRoots Tag.E6 support56)
    {p : ℕ} (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    Nonempty (↥(rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints (phi3N Ω)
      (Units.map (entrywiseHom Fr))) ≃* SL(3, K)) ∧
    Nonempty (↥(rootSpan Tag.E6 Ω S₂ ⊓ twistedFixedPoints (phi3N Ω)
      (Units.map (entrywiseHom Fr))) ≃* SL(3, K)) ∧
    p ∣ Nat.card ↥(rootSpan Tag.E6 Ω S₁ ⊓ twistedFixedPoints (phi3N Ω)
      (Units.map (entrywiseHom Fr))) ∧
    p ∣ Nat.card ↥(rootSpan Tag.E6 Ω S₂ ⊓ twistedFixedPoints (phi3N Ω)
      (Units.map (entrywiseHom Fr))) := by
  obtain ⟨-, -, -, -, -, -, hne₁, -⟩ :=
    phi3_A2_layer_equiv (Ω := Ω) (Fr := Fr) hf hK hFr hS₁roots hvS₁ hw₁
  obtain ⟨-, -, -, -, -, -, hne₂, -⟩ :=
    phi3_A2_layer_equiv₂ (Ω := Ω) (Fr := Fr) hf hK hFr hS₂roots hvS₂ hw₂
  exact ⟨hne₁, hne₂, dvd_card_of_layerEquiv hne₁ hpq, dvd_card_of_layerEquiv hne₂ hpq⟩

theorem exists_layer_of_centralizing {K : Type} [Group K] {p : ℕ} {z : K} {J : Subgroup K}
    (hJ : CFSG.IsQuasisimple ↥J) (hpJ : p ∣ Nat.card J)
    (hzJ : J ≤ Subgroup.centralizer ({z} : Set K)) :
    ∃ Q : Subgroup K, Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set K) ∧
      (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set K))).Normal ∧
      CFSG.IsQuasisimple ↥Q ∧ p ∣ Nat.card Q := by
  have hJle : J ≤ J ⊓ Subgroup.centralizer ({z} : Set K) := le_inf le_rfl hzJ
  refine ⟨J, le_rfl, hzJ, ?_, hJ, hpJ⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJle).2
    (inf_le_left.trans Subgroup.le_normalizer)

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
