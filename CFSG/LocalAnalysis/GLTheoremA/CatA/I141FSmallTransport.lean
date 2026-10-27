module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem i141f_induces_chevAut {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} {L : Subgroup Γ}
    {R : Type} [Group R] (θ : PSimple p L ≃* R) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (L : Set Γ)) {φ : MulAut R}
    (hφ : GLAInduces θ (S10.indRel p L g) φ) (s : PSimple p L) :
    φ (θ s) = θ (chevAut p L ⟨g⁻¹, inv_mem hg⟩ s) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hval : ((L.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩ l : ↥L) : Γ) = g⁻¹ * (l : Γ) * g := by
    rw [chev_coe_normalizerMonoidHom]
    simp
  have h1 := hφ (QuotientGroup.mk l) (QuotientGroup.mk (L.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩ l))
    ⟨l, L.normalizerMonoidHom ⟨g⁻¹, inv_mem hg⟩ l, rfl, rfl, hval⟩
  have h2 := chevAut_chevQuotHom p L ⟨g⁻¹, inv_mem hg⟩ l
  exact h1.trans (congrArg θ h2.symm)

end CFSG.LocalAnalysis.GLTheoremA.I141F
