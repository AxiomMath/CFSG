module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFRest
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1Abs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFCo1Sound
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212
public import Certificates.Certificate40100
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding CFSG.Blueprint Subgroup
open CFSG.SectionRank CFSG.SectionRank.Native

namespace FongKFCo1

theorem gen_of_check_seeds (D : Co1Gen.Data) {s₁ s₂ : String} (h₁ : D.seedA = s₁)
    (h₂ : D.seedB = s₂) (h : (ops2 24).co1GenCheck D = true) :
    ∃ (P₀ : Subgroup (NativeSporadic.seedMonoid 2 24 1 s₁ s₂)ˣ)
      (Sg : Fin 2 → Subgroup (NativeSporadic.seedMonoid 2 24 1 s₁ s₂)ˣ)
      (N : Fin 2 → Set (NativeSporadic.seedMonoid 2 24 1 s₁ s₂)ˣ),
      IsPGroup 5 P₀ ∧ (∀ i, Sg i ≤ P₀) ∧
      (∀ i, ∃ E : Subgroup (NativeSporadic.seedMonoid 2 24 1 s₁ s₂)ˣ,
        E ≤ Sg i ∧ IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2) ∧
      (∀ i, ∀ n ∈ N i, n ∈ Subgroup.normalizer (Sg i : Set _)) ∧
      Subgroup.closure (⋃ i, N i) = ⊤ := by
  subst h₁ h₂
  exact OpsSpec.co1Gen_of_check (spec2 24) D h

theorem co1Gen_witness :
    ∃ (P₀ : Subgroup NativeSporadic.Co1) (Sg : Fin 2 → Subgroup NativeSporadic.Co1)
      (N : Fin 2 → Set NativeSporadic.Co1),
      IsPGroup 5 P₀ ∧ (∀ i, Sg i ≤ P₀) ∧
      (∀ i, ∃ E : Subgroup NativeSporadic.Co1, E ≤ Sg i ∧ IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2) ∧
      (∀ i, ∀ n ∈ N i, n ∈ Subgroup.normalizer (Sg i : Set NativeSporadic.Co1)) ∧
      Subgroup.closure (⋃ i, N i) = ⊤ :=
  gen_of_check_seeds Co1Gen.dataFive rfl rfl Certificates.certificate40100

end FongKFCo1

theorem kdL64I246Co1Case_holds :
    KDL64I246Co1Case := by
  intro Z _ _ _ hpc L hL hCo P hPL hPp hPidx _ Y hY2 _
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hLq : Open.IsQuasisimple ↥L := hL.2.2
  have hZp : IsPGroup 5 (center ↥L) :=
    CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_center_component hpc hL
  obtain ⟨φ'⟩ := hCo
  haveI : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hker : (QuotientGroup.mk' (center ↥L)).ker = ⊥ :=
    CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_co1_five ↥L (↥L ⧸ center ↥L)
      (QuotientGroup.mk' (center ↥L)) ⟨φ'⟩ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']) (by rw [QuotientGroup.ker_mk']; exact hZp)
  have hZ : center ↥L = ⊥ := by rwa [QuotientGroup.ker_mk'] at hker
  let ψ : ↥L ≃* (↥L ⧸ center ↥L) :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let φ : ↥L ≃* NativeSporadic.Co1 := ψ.trans φ'
  haveI : Finite NativeSporadic.Co1 := Finite.of_equiv ↥L φ.toEquiv
  obtain ⟨P₀, Sg, N, hP₀, hSg, hSr, hN, hgen⟩ := FongKFCo1.co1Gen_witness
  exact @FongKFCo1.le_of_normalizers_generate 5 _ Z NativeSporadic.Co1 _ _
    (inferInstance : Group NativeSporadic.Co1) _ L φ P hPL hPp hPidx Y hY2 P₀ hP₀ (Fin 2) Sg hSg hSr
    N hN hgen

theorem kdL64I246Rest_holds :
    KDL64I246Rest :=
  kdL64I246Rest_of_co1 kdL64I246Co1Case_holds

theorem kdL64I246_holds :
    KDL64I246 :=
  kdL64I246_of_rest kdL64I246Rest_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
