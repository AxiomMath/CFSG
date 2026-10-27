module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_of_le {p : ℕ} (hp : p.Prime) {H K : Subgroup G} (h : H ≤ K) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p K := by
  obtain ⟨E, hE, hEA, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  exact CFSG.SectionRank.le_pRank hp.one_lt (hE.trans h) hEA hcard

theorem pRank_sylow {p : ℕ} (hp : p.Prime) {P M : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P M) : CFSG.Open.pRank p P = CFSG.Open.pRank p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := hP
  refine le_antisymm ?_ ?_
  · refine pRank_le_of_le hp ?_
    rw [← hQ]; exact Subgroup.map_subtype_le _
  · obtain ⟨E, hEM, hEA, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
    have hpE : IsPGroup p (E.subgroupOf M) := by
      intro x
      refine ⟨1, ?_⟩
      rw [pow_one]
      exact Subtype.ext (Subtype.ext (hEA.2 (x.1 : G) x.2))
    obtain ⟨Q', hQ'⟩ := hpE.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q Q'
    let f : G →* G := (MulAut.conj ((g : G)⁻¹)).toMonoidHom
    have hf : Function.Injective f := (MulAut.conj ((g : G)⁻¹)).injective
    have hle : E.map f ≤ P := by
      rintro _ ⟨y, hy, rfl⟩
      have hyM : y ∈ M := hEM hy
      have h1 : (⟨y, hyM⟩ : M) ∈ (Q' : Subgroup M) := hQ' (by simpa [Subgroup.mem_subgroupOf] using hy)
      rw [← hg] at h1
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
      rw [← hQ]
      refine ⟨(MulAut.conj g)⁻¹ • ⟨y, hyM⟩, h1, ?_⟩
      simp [f, MulAut.conj_apply, mul_assoc]
    have hAb : IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hEA f
    have hc : Nat.card (E.map f) = p ^ CFSG.Open.pRank p M := by
      rw [Subgroup.card_map_of_injective hf, hcard]
    exact CFSG.SectionRank.le_pRank hp.one_lt hle hAb hc

end CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport
