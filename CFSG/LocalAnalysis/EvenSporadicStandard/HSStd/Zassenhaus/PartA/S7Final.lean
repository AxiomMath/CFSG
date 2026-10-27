module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7AbsMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7M1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7TB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7TC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7TD
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7TE
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7TG
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S11Plane
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Layer

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

theorem s7
    (hHs : Harris311) (hU : U43Config) (hL : HarrisL39L43NoD8) (hCov : U43CoverOrbit)
    (hSimp : LieModelSimpleU43) (h15 : CFSG.EvenSporadicStandard.Induction.FS79Lemma15Hered) :
    StepS7 := by
  intro G _ _ L t E W z hG hb a
  classical
  have ht2 : a.s7_tT hb * a.s7_tT hb = 1 := Subtype.ext hb.t_mul_t
  obtain ⟨hord, ⟨e⟩⟩ := a.toPA5.s7_cent_xhat hb
  have hinv := a.toPA5.s7_hinv hb
  have hyL : a.s7_κ (a.s7_yT hb) ∈ centralizerDerived (a.s7_κ (a.s7_tT hb)) :=
    a.toPA5.s7_JT_map_le hb ⟨_, a.toPA5.s7_yT_mem_JT hb, rfl⟩
  obtain ⟨c, k, hc, hk, hS⟩ := a.toPA5.s7_exists_ckT hb hinv hyL
  obtain ⟨D₁, hD₁, hBD⟩ := a.toPA5.s7_hB hb c k hc hk
  have hKT : CFSG.SectionRank.IsKGroupCat ↥a.s7_N₁ :=
    (hb.setting.1.isKGroupCat_centralizer a.toPA5.s7_ub_ne_one).of_injective
      (Subgroup.inclusion (inf_le_right : a.s7_N₁ ≤ Cen a.ub)) (Subgroup.inclusion_injective _)
  obtain ⟨E', hEn, hEp, hJE, hEF, -, htE, f, hf, hker, hswap⟩ :=
    s7_abstract hHs hU hL hCov hSimp (a.toPA5.s7_κ) (xhatMap_surjective _) hKT
      (fusionOddCore_xhat _) (t := a.s7_tT hb) ht2 hord e (y := a.s7_yT hb) (c := c) (k := k)
      (a.toPA5.s7_yT_ord hb) hS a.s7_F (Open.fusionOddCore ↥a.s7_N₁)
      (a.toPA5.s7_ker_le hb) (a.toPA5.s7_F_card_le hb)
      (fun f hf => mem_centralizer_iff.2 fun x hx => (a.toPA5.s7_F_comm_core hb f hf x hx).symm)
      (a.toPA5.s7_core_comm hb) hinv a.toPA5.s7_JT (a.toPA5.s7_JT_perfect hb)
      (a.toPA5.s7_yT_mem_JT hb) (a.toPA5.s7_JT_map_le hb) ⟨D₁, hD₁, hBD⟩
  haveI := hEn
  have hF : a.s7_F.map a.s7_N₁.subtype = a.F₀ :=
    Subgroup.map_subgroupOf_eq_of_le (a.toPA5.s7_F₀_le_N₁ hb)
  have hEperf := s7tg_map_perfect a.s7_N₁ E' hEp
  have hEcent : E'.map a.s7_N₁.subtype ≤ centralizer (a.F₀ : Set G) := by
    have := s7tg_map_le_centralizer a.s7_N₁ E' a.s7_F hEF
    rwa [hF] at this
  obtain ⟨f', hf', hker'⟩ := s7tg_map_cover a.s7_N₁ E' f hf hker
  have hn : ∀ x ∈ centralizer (a.F₀ : Set G), ∀ e ∈ E'.map a.s7_N₁.subtype,
      x * e * x⁻¹ ∈ E'.map a.s7_N₁.subtype := fun x hx e he =>
    s7tg_conj_mem_map a.s7_N₁ E' (PA5.s7_cent_F₀_le_N₁ hb a.toPA5 hx) he
  have hO := s7tg_oddCore_bot (PA5.s7_simple hb) hb.t_ord
  have hlayer := le_componentLayer_of_balance (h15.sec hG) hb.setting.1.kProper hO a.ub a.F₀
    (a.toPA5.s7_F₀_isPGroup hb) (a.toPA5.s7_ub_mem_F₀ hb) _ hEperf hEcent hn f' hf' hker'
  obtain ⟨M, hMle, hMperf, ⟨f₁, hf₁, hker₁⟩, hMcomm⟩ :=
    exists_M1 E' hEp (a.s7_tT hb) ht2 htE f hf hker hswap
  obtain ⟨f₂, hf₂, hker₂⟩ := s7tg_map_cover a.s7_N₁ M f₁ hf₁ hker₁
  refine ⟨{ toPA6 := a
            E₁ := E'.map a.s7_N₁.subtype
            E₁_le := hlayer
            E₁_perf := hEperf
            J_E₁ := ?_
            E₁_cent_F₀ := hEcent
            E₁_cover := ⟨f', hf', hker'⟩
            E₁_swap := s7tg_map_conj a.s7_N₁ E' (a.s7_tT hb) ht2 htE
            M₁ := M.map a.s7_N₁.subtype
            M₁_le := s7tg_map_mono a.s7_N₁ hMle
            M₁_perf := s7tg_map_perfect a.s7_N₁ M hMperf
            M₁_cover := ⟨f₂, hf₂, hker₂⟩
            M₁_comm := s7tg_map_comm a.s7_N₁ M (a.s7_tT hb) hMcomm }⟩
  rw [← a.toPA5.s7_JT_map_eq hb]
  exact Subgroup.map_mono hJE

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
