module

public import CFSG.LocalAnalysis.OddStandard.ONanIdStd
public import CFSG.LocalAnalysis.OddStandard.ONanIdCM
public import CFSG.LocalAnalysis.OddStandard.ONanCMCard
public import CFSG.LocalAnalysis.OddStandard.ONanFusFinal
public import Certificates.Data.ONanCMChain

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.OddStandard.ChengHeldData

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0
local notation "𝐉" => centralizer ({xel v1 v2 v3} : Set G)

@[expose] noncomputable def jqEquiv (hone : OneClass G) (hbal : Balanced G) : 𝐉 ≃* Jhat 𝐉 :=
  MulEquiv.ofBijective (jq 𝐉) ⟨D.jq_injective hone hbal, jq_surjective 𝐉⟩

theorem jqEquiv_symm_jq (hone : OneClass G) (hbal : Balanced G) (j : 𝐉) :
    (D.jqEquiv hone hbal).symm (jq 𝐉 j) = j :=
  (D.jqEquiv hone hbal).symm_apply_apply j

theorem st_notMem_Cx : s * t ∉ 𝐉 := by
  intro h
  have h1 := D.st_inv_x
  rw [mem_centralizer_singleton_iff.1 h, mul_inv_cancel_right] at h1
  have h3 : 𝔵 * 𝔵 = 1 := by
    nth_rewrite 2 [h1]
    exact mul_inv_cancel 𝔵
  rw [D.xel_sq] at h3
  exact D.rep_ne_one 0 h3

theorem card_Cx
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) : Nat.card 𝐉 = 80640 := by
  obtain ⟨q, l, hq, -⟩ := D.exists_frame hF hone hbal
  have hrange : q.range = S := by
    ext y
    exact ⟨fun ⟨e, he⟩ => he ▸ hq.qS e, fun hy => hq.qsurj y hy⟩
  rw [Nat.card_congr (D.jqEquiv hone hbal).toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv, hrange, card_S, hq.ker,
    D.card_center_jhat hF hone hbal]

theorem card_Cz
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    Nat.card (centralizer ({𝔷} : Set G)) = 161280 := by
  rw [← Subgroup.card_mul_index ((centralizer ({𝔵} : Set G)).subgroupOf
      (centralizer ({𝔷} : Set G))), D.index_centralizer_x hone hbal,
    Nat.card_congr (subgroupOfEquivOfLe D.Cx_le_Cz).toEquiv, D.card_Cx hF hone hbal]

theorem nonempty_mulEquiv_CModel
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    Nonempty (centralizer ({𝔷} : Set G) ≃* CModel) := by
  obtain ⟨q, l, hU, hκ⟩ := D.exists_std hF hone hbal
  set ι := (D.jqEquiv hone hbal).symm with hι
  set Φ : Cover →* G := 𝐉.subtype.comp (ι.toMonoidHom.comp l) with hΦ
  have hΦe : ∀ c, Φ c = ((ι (l c) : 𝐉) : G) := fun c => rfl
  have hu : s * t * (s * t) = 1 := D.st_sq
  have hstinv : (s * t)⁻¹ = s * t := inv_eq_of_mul_eq_one_right hu
  have hα : ∀ w, Φ (cv (alphaU w)) = s * t * Φ (cv w) * (s * t) := by
    intro w
    rw [hΦe, hΦe, ← hU.beta_cv w]
    obtain ⟨j, hj⟩ := jq_surjective 𝐉 (l (cv w))
    rw [← hj, betaHat_jq, hι, D.jqEquiv_symm_jq, D.jqEquiv_symm_jq, coe_conjJ, hstinv]
  have hK : ∀ p q r : ℕ, inK (kapOf 0) (p : ZMod 4) (q : ZMod 4) → Φ (cv (zword p q r)) = 1 := by
    intro p q r hpq
    have h1 : l (cv (zword p q r)) = 1 := by
      rw [cv_zword, map_mul, map_mul, map_pow, map_pow, map_pow, hU.lam_z₃', one_pow, mul_one,
        ← zz_ofNat]
      exact (hκ _ _).2 hpq
    rw [hΦe, h1, map_one]
    rfl
  obtain ⟨ψ, hψof, hΦψ, huψ⟩ := IdCM.exists_cmHom hu hα hK
  have hΦz : ∀ c, Φ c ∈ centralizer ({𝔷} : Set G) := fun c => D.Cx_le_Cz (ι (l c)).2
  have hgen : ∀ i, IdCM.genG Φ (s * t) i ∈ centralizer ({𝔷} : Set G) := by
    intro i
    refine mul_mem (hΦz _) ?_
    unfold IdCM.upow
    split_ifs
    · exact D.st_mem_Cz
    · exact one_mem _
  have hrange : ψ.range ≤ centralizer ({𝔷} : Set G) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hψof i]
    exact hgen i
  set ψ' : CModel →* centralizer ({𝔷} : Set G) :=
    ψ.codRestrict (centralizer ({𝔷} : Set G)) (fun x => hrange ⟨x, rfl⟩) with hψ'
  have hsurj : Function.Surjective ψ' := by
    intro y
    suffices h : (y : G) ∈ ψ.range by
      obtain ⟨x, hx⟩ := h
      exact ⟨x, Subtype.ext hx⟩
    have hJ : ∀ g : G, g ∈ 𝐉 → g ∈ ψ.range := by
      intro g hg
      obtain ⟨c, hc⟩ := hU.lsurj (jq 𝐉 ⟨g, hg⟩)
      refine hΦψ ⟨c, ?_⟩
      rw [hΦe, hc, D.jqEquiv_symm_jq]
    by_cases hy : (y : G) ∈ 𝐉
    · exact hJ _ hy
    · have hidx := D.index_centralizer_x hone hbal
      have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := y)
        (b := ⟨s * t, D.st_mem_Cz⟩)).2 (iff_of_false (by rwa [mem_subgroupOf])
          (by rw [mem_subgroupOf]; exact D.st_notMem_Cx))
      rw [mem_subgroupOf] at hmem
      have h1 := hJ _ hmem
      have e : (y : G) = (y : G) * (s * t) * (s * t)⁻¹ := by group
      rw [e]
      exact mul_mem h1 (inv_mem huψ)
  have hcard : Nat.card CModel = Nat.card (centralizer ({𝔷} : Set G)) := by
    rw [CM.card_CModel_cert, D.card_Cz hF hone hbal]
  have : Finite CModel := Nat.finite_of_card_ne_zero (by rw [CM.card_CModel_cert]; norm_num)
  exact ⟨(MulEquiv.ofBijective ψ' (hsurj.bijective_of_nat_card_le hcard.le)).symm⟩

end FusCtx

theorem stageB1Ident_of_thmC
    (hF : ThmC.ThmCFull) : StageB1Ident := by
  intro G _ _ _ hna hbal hone v1 v2 v3 s t hfr hz hSyl
  obtain ⟨P, hP⟩ := hSyl
  let D := FusCtx.ofStage hna hfr hz P hP
  have hz' : invRep v1 v2 v3 s t 0 = v1 ^ 2 * v3 ^ 2 := by rw [D.z_eq, AlpEmb.φ_zc]
  obtain ⟨e⟩ := D.nonempty_mulEquiv_CModel hF hone hbal
  rw [hz'] at e
  exact ⟨e⟩

end CFSG.OddStandard.ONanRec
