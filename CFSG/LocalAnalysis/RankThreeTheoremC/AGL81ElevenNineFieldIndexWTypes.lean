module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenNineWTransfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormW
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree Subgroup
open scoped commutatorElement

@[expose] def OddInnW (X : Type) [Group X] : Prop :=
  ∀ α : MulAut X, Odd (orderOf α) → ∃ w ∈ wSup X, ∀ x ∈ wSup X, α x = w * x * w⁻¹

theorem OddInnW.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : OddInnW X') : OddInnW X := by
  intro α hα
  have hβ : Odd (orderOf (MulAut.congr e α)) := by
    rw [MulEquiv.orderOf_eq]
    exact hα
  obtain ⟨w', hw', hw'x⟩ := h _ hβ
  have hW : (wSup X').map e.symm.toMonoidHom = wSup X := map_wSup_eq e.symm
  have hW' : (wSup X).map e.toMonoidHom = wSup X' := map_wSup_eq e
  refine ⟨e.symm w', hW ▸ mem_map_of_mem _ hw', fun x hx => ?_⟩
  have hex : e x ∈ wSup X' := hW' ▸ mem_map_of_mem _ hx
  have h1 := hw'x (e x) hex
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_inner_wPre_of_oddInnW {Y : Type} [Group Y] {J : Subgroup Y}
    (hJ : OddInnW (↥J ⧸ CFSG.pCore 2 ↥J)) {a : Y} (ha : a ∈ normalizer (J : Set Y))
    (hodd : Odd (orderOf a)) :
    ∃ v ∈ wPre J, ∀ w ∈ wPre J, ⁅a * v, w⁆ ∈ pCoreOf 2 J := by
  set ψ : normalizer (J : Set Y) →* MulAut (↥J ⧸ CFSG.pCore 2 ↥J) :=
    (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 ↥J)).comp J.normalizerMonoidHom with hψ
  set n : normalizer (J : Set Y) := ⟨a, ha⟩
  have hn : Odd (orderOf n) := by
    rw [Subgroup.orderOf_mk]
    exact hodd
  obtain ⟨w₀, hw₀, hw₀x⟩ := hJ (ψ n) (hn.of_dvd_nat (orderOf_map_dvd ψ n))
  obtain ⟨j₀, rfl⟩ := QuotientGroup.mk_surjective w₀
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥J)
  have hj₀ : mk j₀⁻¹ ∈ wSup (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [map_inv]
    exact inv_mem hw₀
  refine ⟨(j₀ : Y)⁻¹, ⟨j₀⁻¹, hj₀, rfl⟩, ?_⟩
  rintro _ ⟨j, hj, rfl⟩
  have hjW : mk j ∈ wSup (↥J ⧸ CFSG.pCore 2 ↥J) := hj
  set x' : ↥J := j₀⁻¹ * j * j₀
  have hx' : mk x' ∈ wSup (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem hj₀ hjW) (by simpa using inv_mem hj₀)
  set y : ↥J := J.normalizerMonoidHom n x'
  have hy : (y : Y) = a * ((j₀ : Y)⁻¹ * j * j₀) * a⁻¹ := rfl
  have h1 : mk y = mk j := by
    have h2 : ψ n (mk x') = mk y := rfl
    rw [← h2, hw₀x _ hx']
    show mk j₀ * mk x' * (mk j₀)⁻¹ = mk j
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    show j₀ * (j₀⁻¹ * j * j₀) * j₀⁻¹ = j
    group
  have h3 : y * j⁻¹ ∈ CFSG.pCore 2 ↥J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact mul_inv_eq_one.mpr h1
  refine ⟨_, h3, ?_⟩
  rw [Subgroup.coe_subtype, Subgroup.coe_mul, hy, Subgroup.coe_inv, commutatorElement_def]
  group

end CFSG.LocalAnalysis.RankThreeTheoremC
