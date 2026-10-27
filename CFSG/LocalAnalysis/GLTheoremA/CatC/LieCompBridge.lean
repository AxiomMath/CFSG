module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Fi22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.Yardstones.Md42047359a2a

theorem lieCompsExport_isChevSimple {p q : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    {β : MulAut S} (h : LieComp.LieCompsExport q β) {J : Subgroup S}
    (hJ : GLAPComponent p (fixSubgroup β) J) : IsChevSimple q (PSimple p J) := by
  have hperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hle : J ≤ GLALayer (fixSubgroup β) := h.layer J hJ.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hJ hle
  have hq : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hO : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J := by
    by_cases htop : GLAPPrimeCore p ↥J = ⊤
    · exfalso
      haveI := isQuasisimple_nontrivial hq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot p J)
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (QuotientGroup.eq.2 (htop ▸ Subgroup.mem_top _))
    · exact le_center_of_normal_of_isQuasisimple hcomp.2.2 inferInstance htop
  obtain ⟨X, _, _, hX, f, hf, hfk⟩ := h.comps J hcomp
  let π : ↥J →* PQuot p J := QuotientGroup.mk' (GLAPPrimeCore p ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact hO
  have hk : (π.comp f).ker ≤ Subgroup.center X := by
    intro x hx
    have h1 : f x ∈ Subgroup.center ↥J := hπk hx
    have h2 : x ∈ (Subgroup.center ↥J).comap f := h1
    rwa [comap_center_of_surjective hX.perfect f hf hfk] at h2
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect (π.comp f) (hπ.comp hf) hk
  exact isChevSimple_congr e hX.chev

end CFSG.LocalAnalysis.GLTheoremA
