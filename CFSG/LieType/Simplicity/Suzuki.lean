module

public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCentralCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6

public section

namespace CFSG.LieType.Simplicity

open CFSG.Blueprint CFSG.BenderSuzuki.MatrixGroups

theorem exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel {G : Type} [Group G] {p f : ℕ}
    (h : SuzukiModel G p f) : ∃ a : ℕ, 1 ≤ a ∧ Nonempty (G ≃* SuzukiMatrixGroup a) := by
  obtain ⟨rfl, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  exact ⟨a, ha, ⟨e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    ((CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard).trans
      (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)))⟩⟩

theorem finite_suzukiGroup (a : ℕ) (K : Type) [Field K] [Finite K] :
    Finite (suzukiGroup a K) :=
  inferInstance

theorem fam_suzuki_finiteness (G : Type) [Group G] (p f : ℕ) (h : SuzukiModel G p f) :
    Finite G := by
  obtain ⟨-, a, -, K, _, _, -, -, ⟨e⟩⟩ := h
  exact Finite.of_equiv _ e.symm.toEquiv

theorem fam_2b2_simplicity (G : Type) [Group G] (p f : ℕ) (h : SuzukiModel G p f) :
    Nontrivial G ∧ IsSimpleGroup G := by
  obtain ⟨a, ha, ⟨e⟩⟩ := exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
  have := (CFSG.BenderSuzuki.External.huppert_blackburn_XI_3_6 a (by omega)).1
  have hG : IsSimpleGroup G := e.isSimpleGroup
  exact ⟨hG.toNontrivial, hG⟩

end CFSG.LieType.Simplicity
