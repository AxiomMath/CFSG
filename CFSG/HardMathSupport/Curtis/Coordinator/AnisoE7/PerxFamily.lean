module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.UnitaryHyperRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KE.E7FourPerX
public import CFSG.RankThree.PartOne.KE.E7ThreeFrame

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

set_option linter.unusedSectionVars false


theorem e7_perx_of_family {K : Type} [Field K] [Finite K] {ℓ f p : ℕ} [Fact ℓ.Prime]
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (F : E7ThreeFrame K L ℓ f p (-1)) (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    {x : adjointGroup .E7 K} (hx : orderOf x = p) (c : adjointGroup .E7 K)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p)
    (hh : F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {b : Fin Tag.E7.rank → Lˣ}
    (hbh : rootDiagUnit .E7 b = F.g0⁻¹ * adjEmb .E7 K L (c * x * c⁻¹) * F.g0)
    {ι' : Type} (P : ι' → Subgroup (ModGL .E7 L))
    (hfam : IsSigmaFamily F.n (iterateFrobenius L ℓ f) (rootCharKernel b) P) :
    ∃ ψ : Subgroup.centralizer ({x} : Set (adjointGroup .E7 K)) →* ModGL .E7 L,
      Function.Injective ψ ∧
      (∀ y, ψ y = F.g0⁻¹ * adjEmb .E7 K L (c * (y : adjointGroup .E7 K) * c⁻¹) * F.g0) ∧
      (∀ y, ψ y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel b)) ∧
      (∀ y, F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (ψ y) * F.n⁻¹ = ψ y) ∧
      (∀ i, P i ≤ ψ.range) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hS : ∀ α ∈ rootCharKernel b, IsRoot Tag.E7 α := fun α hα => hα.1
  have hSn : ∀ α ∈ rootCharKernel b, -α ∈ rootCharKernel b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨hcS, hkerZ⟩ := e7_perx_hc_hkerZ (K := K) Fr F.g0 hbh hh (S := rootCharKernel b) rfl
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hψadj, hPψ, hψV⟩ := sigma_embedding_data_of_stab
    (adjEmb .E7 K L) adjEmb_injective adjEmb_mem (Units.map (entrywiseHom Fr))
    (adjEmb_frobenius Fr hFr) F.n F.g0 F.hg0C F.hg0 F.hperf hp
    (fun a hap ha1 haT => hstab a hap ha1 haT) hS hSn P hPfin hPq hPQ hPR hPadj hPnorm hPcent hx c
    hcS hkerZ
  exact ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
