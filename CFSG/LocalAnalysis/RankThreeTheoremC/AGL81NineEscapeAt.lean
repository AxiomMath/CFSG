module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPoszAux
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_d1Escape_of_three_le {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {N R : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    (hRM : R ≤ M) (hR : CFSG.Quasithin.IsSylowIn p R N) (h3 : 3 ≤ CFSG.Open.pRank p R) :
    ∃ P' : Sylow p G, D1Escape p P' M N R := by
  classical
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := he.sylow_le
  obtain ⟨S, hS⟩ := (hR.isPGroup.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) S
  set P' : Sylow p G := (m : G) • P with hP'
  have hP'coe : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj (m : G)).toMonoidHom := by
    ext x
    rw [hP', Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'coe]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hPM hy)) (M.inv_mem m.2)
  have hRP' : R ≤ P' := by
    intro t ht
    have h1 : (⟨t, hRM ht⟩ : M) ∈ (S : Subgroup M) := hS (Subgroup.mem_subgroupOf.mpr ht)
    rw [← hm, Sylow.coe_subgroup_smul, Sylow.coe_subtype,
      Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, hy, hyt⟩ := h1
    rw [hP'coe]
    refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
    have := congrArg Subtype.val hyt
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hW : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'coe]
    exact weakCore_conj_le hp he.weakCore_le m.2
  refine ⟨P', ⟨hp, he.ne_two, hP'M, hW, he.maxTwoLocal_M, hN, hR.le, hRP',
    ⟨hR.toSylow, ?_⟩, h3, hNM⟩⟩
  rw [CFSG.Quasithin.IsSylowIn.coe_toSylow]
  exact Subgroup.map_subgroupOf_eq_of_le hR.le

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
