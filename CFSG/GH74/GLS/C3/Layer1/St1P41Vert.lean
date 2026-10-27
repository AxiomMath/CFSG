module

public import CFSG.GH74.GLS.C3.Layer1.St1P41Cls
public import CFSG.GH74.GLS.C3.Layer1.Th2IV26

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpVert

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open CFSG.GH74.GLS.Stage1.Thm3.Sec4
open CFSG.GH74.GLS.C3.Layer1.PumpCalc
open CFSG.GH74.GLS.C3.Layer1.PumpL42

variable {G : Type} [Group G] [Finite G]

@[expose] def VertConfig (x y : G) (K : Subgroup G) : Prop :=
  ∃ (Q : Subgroup G) (u : G) (K' Λ : Subgroup G), IsSylowOf 2 Q (CxK x K) ∧
    y ∈ normalizer (Q : Set G) ∧ u ∈ Q ∧ orderOf u = 2 ∧ ¬ (u * y = y * u) ∧
    PumpUpLT 2 x K u K' ∧ IsLam x u K Λ ∧ x ∈ normalizer (K' : Set G) ∧
    VerticalPumpup x u K K' Λ

theorem vertical_of_nontrivial (T : Rank4Tables) (hG : IsKProperSimple G) (hB2 : B_B2)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts)
    {x u : G} {K K' : Subgroup G} (hlt : PumpUpLT 2 x K u K')
    (hU2 : InU2 (kBar K)) (hno : ¬ IsL34Quotient (kBar K)) (hs : IsSimpleGroup (kBar K))
    (hnt : ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K))) :
    ∃ Λ : Subgroup G, IsLam x u K Λ ∧ x ∈ normalizer (K' : Set G) ∧ VerticalPumpup x u K K' Λ := by
  obtain ⟨Λ, hΛ⟩ := exists_isLam hlt.2.1.1 hlt.1.2.2 hlt.2.2.2.1
  obtain ⟨hzH, hdich⟩ := pumpup_rank4 T hG hB2 hr4 hgen4 T7 hC2 hU2 hno hs hlt hΛ
  rcases hdich with htrv | hvert
  · exact absurd ⟨hzH, htrv.1⟩ hnt
  · exact ⟨Λ, hΛ, hzH, hvert⟩

theorem vertConfig_of_nontrivial (T : Rank4Tables) (hG : IsKProperSimple G) (hB2 : B_B2)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts)
    {x y : G} {K Q : Subgroup G} (hyQ : y ∈ normalizer (Q : Set G)) (hQ : IsSylowOf 2 Q (CxK x K))
    (hU2 : InU2 (kBar K)) (hno : ¬ IsL34Quotient (kBar K)) (hs : IsSimpleGroup (kBar K))
    (htriv : ∀ t : G, orderOf t = 2 → t ∈ CxK x K → t * y = y * t →
      ∀ K' : Subgroup G, PumpUpLT 2 x K t K' →
        x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K))
    {u : G} (hu : u ∈ Q) (hu2 : orderOf u = 2) {K' : Subgroup G} (hlt : PumpUpLT 2 x K u K')
    (hnt : ¬ (x ∈ normalizer (K' : Set G) ∧ Nonempty (kBar K' ≃* kBar K))) :
    VertConfig x y K := by
  obtain ⟨Λ, hΛ, hzH, hv⟩ := vertical_of_nontrivial T hG hB2 hr4 hgen4 T7 hC2 hlt hU2 hno hs hnt
  refine ⟨Q, u, K', Λ, hQ, hyQ, hu, hu2, fun hc => hnt (htriv u hu2 (hQ.le hu) hc K' hlt), hlt, hΛ,
    hzH, hv⟩

theorem hyp4B_vertConfig (T : Rank4Tables) (hG : IsKProperSimple G) (hB2 : B_B2)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts)
    (hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)))
    {x y : G} {K : Subgroup G} (hP : IsILo 2 x K) (hx : Hyp4B x y K)
    (hU2 : InU2 (kBar K)) (hno : ¬ IsL34Quotient (kBar K)) (hs : IsSimpleGroup (kBar K)) :
    VertConfig x y K := by
  have hterm : IsTerminallyUnbalancing x y K :=
    ⟨hx.unbalancing, hx.trivialPumpups, hx.sylow⟩
  obtain ⟨Q, hQ, hyQ, u, hu, hu2, K', hlt, hnt, hncomm⟩ :=
    exists_noncommuting_pumpup_of_terminallyUnbalancing hR hP hterm hx.notTerminal
  obtain ⟨Λ, hΛ, hzH, hv⟩ :=
    vertical_of_nontrivial T hG hB2 hr4 hgen4 T7 hC2 hlt hU2 hno hs hnt
  exact ⟨Q, u, K', Λ, hQ, hyQ, hu, hu2, hncomm, hlt, hΛ, hzH, hv⟩

theorem hyp4A_vertConfig (T : Rank4Tables) (hG : IsKProperSimple G) (hB2 : B_B2)
    (hr4 : pRank 2 G = 4) (hgen4 : CFSG.GH74.Gen4 G) (T7 : St1Thm7 G) (hC2 : C2Facts)
    {x y : G} {K : Subgroup G} (hx : Hyp4A x y K)
    (hU2 : InU2 (kBar K)) (hno : ¬ IsL34Quotient (kBar K)) (hs : IsSimpleGroup (kBar K)) :
    VertConfig x y K := by
  have hy2 : orderOf y = 2 := hx.unbalancing.2.1
  have hyN : y ∈ NxK x K := Subgroup.mem_inf.mpr ⟨hx.unbalancing.2.2.1, hx.unbalancing.2.2.2.1⟩
  obtain ⟨Q, hQ, hyQ⟩ := exists_yinv_sylow hy2 hyN
  obtain ⟨t, K₀, hlt₀, hnt₀⟩ := hx.nontrivial
  obtain ⟨u, hu, hu2, K', hlt, hnt⟩ := exists_nontrivial_in_sylow hQ hlt₀ hnt₀
  exact vertConfig_of_nontrivial T hG hB2 hr4 hgen4 T7 hC2 hyQ hQ hU2 hno hs hx.trivialPumpups
    hu hu2 hlt hnt

end CFSG.GH74.GLS.C3.Layer1.PumpVert
