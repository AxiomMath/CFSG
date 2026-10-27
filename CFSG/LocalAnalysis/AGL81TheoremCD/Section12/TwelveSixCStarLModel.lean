module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneModel

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

namespace TwelveCtx

private theorem cStarL_normal (hp : p.Prime) (H : Subgroup G) : (cStarL p H).Normal := by
  haveI hchar : (CFSG.layer (StarGroup p H)).Characteristic :=
    CFSG.LocalCores.layer_characteristic
  rw [cStarL_eq_centralizer_layer hp H]
  infer_instance

private theorem pCore_cStarL_eq (hp : p.Prime) (H : Subgroup G) :
    CFSG.pCore p ↥(cStarL p H) = (CFSG.pCore p (StarGroup p H)).subgroupOf (cStarL p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (cStarL p H).Normal := cStarL_normal hp H
  exact pCore_eq_subgroupOf_pCore (p := p) (X := StarGroup p H) (cStarL p H)

private theorem centralizer_pCore_cStarL_le (hp : p.Prime) (H : Subgroup G) :
    Subgroup.centralizer (CFSG.pCore p ↥(cStarL p H) : Set ↥(cStarL p H)) ≤
      CFSG.pCore p ↥(cStarL p H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [pCore_cStarL_eq hp H]
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  refine cStarL_inf_centralizer_le_pCore hp H ⟨x.2, ?_⟩
  change (x : StarGroup p H) ∈
    Subgroup.centralizer (CFSG.pCore p (StarGroup p H) : Set (StarGroup p H))
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hx
  rw [Subgroup.mem_centralizer_iff] at h
  exact congrArg Subtype.val
    (h ⟨y, pCore_le_cStarL hp H hy⟩ (Subgroup.mem_subgroupOf.mpr hy))

private theorem pRank_pCore_cStarL_le_three (h : TwelveCtx G M p Q H) :
    CFSG.Open.pRank p (CFSG.pCore p ↥(cStarL p H)) ≤ 3 := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  rw [pCore_cStarL_eq h.p_prime H]
  have hp1 : 1 < p := h.p_prime.one_lt
  have h1 : CFSG.Open.pRank p ((CFSG.pCore p (StarGroup p H)).subgroupOf (cStarL p H)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥(cStarL p H)) :=
    CFSG.SectionRank.pRank_mono hp1 le_top
  have h2 : CFSG.Open.pRank p (⊤ : Subgroup ↥(cStarL p H)) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) :=
    CFSG.SectionRank.pRank_top_le_of_injective hp1 (cStarL p H).subtype
      (cStarL p H).subtype_injective
  have h3 : CFSG.Open.pRank p (⊤ : Subgroup (StarGroup p H)) ≤ 3 := by
    obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
    have hpσ : p ∉ CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM G M := by
      simpa only [CFSG.LocalAnalysis.AGL81TheoremCD.sigmaSet,
        CFSG.LocalAnalysis.RankThreeUC.S15.sigmaM] using h.p_not_mem_sigma
    exact (nineSettingGen h hEQ hE hEc hΓ).pRank_star_le_three h.H_mem_H2Star.1 hpσ
  exact h1.trans (h2.trans h3)

theorem exists_cStarL_model (h : TwelveCtx G M p Q H) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (_ : Module.Finite (ZMod p) W)
      (φ : ↥(cStarL p H) →* (Module.End (ZMod p) W)ˣ),
      φ.ker ≤ CFSG.pCore p ↥(cStarL p H) ∧ Module.finrank (ZMod p) W ≤ 4 := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨W, hWac, hWmod, hWfin, φ, hker, hdim⟩ :=
    S631.exists_commutatorModel h.p_odd (centralizer_pCore_cStarL_le h.p_prime H)
      (pRank_pCore_cStarL_le_three h)
  refine ⟨W, hWac, hWmod, hWfin, φ, hker, ?_⟩
  rcases hdim with h3 | ⟨h4, -⟩
  · exact h3.trans (by norm_num)
  · exact h4.le

end TwelveCtx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
