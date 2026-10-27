module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBParts

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem normalizer_tP_le_normalizer_L_sup_V (hB : d.CaseBHyp) :
    normalizer (d.tP : Set G) ≤ normalizer ((d.L ⊔ d.V : Subgroup G) : Set G) := by
  have hd : d.Hyp := hB.hyp
  obtain ⟨-, -, -, -, -, -, hB4, -, -⟩ := hd.sec3_3_one hB.gms
  obtain ⟨-, -, -, -, -, -, -, hfac⟩ := hd.sec3_2
  have hB₂tP : d.B₂ ≤ d.tP := (hd.B₂_spec).2.1
  have hNV : normalizer (d.tP : Set G) ≤ normalizer (d.V : Set G) :=
    d.normalizer_tP_le_normalizer_ZtP.trans (hd.normalizer_ZtP_le_normalizer_V hB.gms)
  have htN : d.t ∈ normalizer (d.L : Set G) := Subgroup.centralizer_le_normalizer _ hd.t_mem
  have htPL : d.tP ≤ normalizer (d.L : Set G) :=
    sup_le (Subgroup.zpowers_le.2 htN) (d.P_le_L.trans Subgroup.le_normalizer)
  have hB₂N : d.B₂ ≤ normalizer ((d.L ⊔ d.V : Subgroup G) : Set G) :=
    (le_inf (hB₂tP.trans htPL)
      (hB₂tP.trans ((Subgroup.le_normalizer : d.tP ≤ normalizer (d.tP : Set G)).trans hNV))).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hVN : d.V ≤ normalizer ((d.L ⊔ d.V : Subgroup G) : Set G) :=
    (le_sup_right : d.V ≤ d.L ⊔ d.V).trans Subgroup.le_normalizer
  have hB₄N : d.B₄ ≤ normalizer ((d.L ⊔ d.V : Subgroup G) : Set G) := by
    rw [hB4]
    exact sup_le hVN hB₂N
  intro g hg
  obtain ⟨x, hx, c, hc, rfl⟩ := hfac _ hg
  have hcP : c ∈ normalizer (d.tP : Set G) := by
    have h := mul_mem (inv_mem (hd.B₄_le_normalizer_tP hx)) hg
    simpa using h
  have hcN : c ∈ normalizer (d.L : Set G) ⊓ normalizer (d.V : Set G) :=
    ⟨hd.centralizer_le_normalizer hc.2, hNV hcP⟩
  exact mul_mem (hB₄N hx) (Subgroup.inf_normalizer_le_normalizer_sup _ _ hcN)

end Data

namespace CaseBParts

theorem normalizerTP : NormalizerTPStatement :=
  fun _ _ _ _ _ _ _ _ hB => Data.normalizer_tP_le_normalizer_L_sup_V hB

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
