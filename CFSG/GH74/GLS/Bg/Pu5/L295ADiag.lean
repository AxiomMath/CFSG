module

public import CFSG.GH74.GLS.Bg.Pu5.L295AAbs
public import CFSG.GH74.GLS.Bg.Pu5.LPTPBasic

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Bg.Iii2.CMEngine
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem barMk_eq_one_of_mem_pPrimeCoreOf_self {Y : Subgroup G} {o : G} (ho : o ∈ pPrimeCoreOf 2 Y)
    (hoY : o ∈ Y) : barMk ↥Y ⟨o, hoY⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o', ho', rfl⟩ := ho
  exact (QuotientGroup.eq_one_iff _).mpr ho'

theorem bar_commutator_eq_bot {t : G} {K K' : Subgroup G}
    (hK : IsPCompIn 2 (centralizer ({t} : Set G)) K) (hK' : IsPCompIn 2 (centralizer ({t} : Set G)) K')
    (hne : K ≠ K') : ⁅bar t K, bar t K'⁆ = ⊥ := by
  rw [← le_bot_iff, Subgroup.commutator_le]
  rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
  have hmK : (m : G) ∈ K := Subgroup.mem_subgroupOf.mp hm
  have hm'K' : (m' : G) ∈ K' := Subgroup.mem_subgroupOf.mp hm'
  have hcs : K' ≤ cSec K := le_cSec_of_ne hK' hK hne.symm
  have h1 : ⁅(m : G), (m' : G)⁆ ∈ pPrimeCoreOf 2 K := (hcs hm'K').2.2 _ hmK
  have hcY : ⁅(m : G), (m' : G)⁆ ∈ centralizer ({t} : Set G) := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem m.2 m'.2) (inv_mem m.2)) (inv_mem m'.2)
  have hKsub : (K.subgroupOf (centralizer ({t} : Set G))).IsSubnormal := by
    obtain ⟨_, _, hsub, _⟩ := hK.2
    exact hsub
  have h2 := barMk_eq_one_of_mem_pPrimeCoreOf hK.1 hKsub h1 hcY
  rw [Subgroup.mem_bot]
  change ⁅barMk _ m, barMk _ m'⁆ = 1
  rw [← map_commutatorElement]
  exact h2


theorem cSec_of_commutators {t v g : G} {L Λ : Subgroup G} (hv : orderOf v = 2)
    (hvt : v ∈ centralizer ({t} : Set G)) (hL : IsRigidRankOneComp t L)
    (hvL : v ∉ normalizer (L : Set G)) (hgt : g ∈ centralizer ({t} : Set G))
    (hgv : g ∈ centralizer ({v} : Set G)) (hgL : g ∈ normalizer (L : Set G))
    (hΛt : Λ ≤ centralizer ({t} : Set G))
    (hcov : ∀ k ∈ L, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({t} : Set G)),
      l = k * (v * k * v⁻¹) * o)
    (hcomm : ∀ l ∈ Λ, ⁅l, g⁆ ∈ pPrimeCoreOf 2 (centralizer ({v} : Set G))) : g ∈ cSec L := by
  set Y := centralizer ({t} : Set G) with hY
  have hs2 : orderOf (sbar v hvt) = 2 := orderOf_sbar hv hvt
  have hsinv : (sbar v hvt)⁻¹ = sbar v hvt := inv_eq_self_of_orderOf_eq_two hs2
  have hLc : CFSG.IsComponent (bar t L) := isComponent_bar (rr_pcomp hL)
  have hL' : IsRigidRankOneComp t (cmap v L) := isRigidRankOneComp_cmap hL hvt
  have hne : L ≠ cmap v L := fun h => hvL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hbarL' : bar t (cmap v L) = conjSub (sbar v hvt)⁻¹ (bar t L) := by
    rw [bar_cmap hvt, hsinv]
  have hAB : ⁅bar t L, conjSub (sbar v hvt)⁻¹ (bar t L)⁆ = ⊥ := by
    rw [← hbarL']
    exact bar_commutator_eq_bot (rr_pcomp hL) (rr_pcomp hL') hne
  have hDΛ : ∀ q ∈ (swapDiag hAB).range, q ∈ bar t Λ := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨m, hm, rfl⟩ := hx
    have hmL : (m : G) ∈ L := Subgroup.mem_subgroupOf.mp hm
    obtain ⟨l, hlΛ, o, ho, hlo⟩ := hcov (m : G) hmL
    have hlY : l ∈ Y := hΛt hlΛ
    have hoY : o ∈ Y := pPrimeCoreOf_le Y ho
    refine ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hlΛ, ?_⟩
    have ho1 : barMk ↥Y ⟨o, hoY⟩ = 1 := barMk_eq_one_of_mem_pPrimeCoreOf_self ho hoY
    have hl : (⟨l, hlY⟩ : ↥Y) = m * (⟨v, hvt⟩ * m * ⟨v, hvt⟩⁻¹) * ⟨o, hoY⟩ := Subtype.ext hlo
    have hsinv' : (barMk ↥Y ⟨v, hvt⟩)⁻¹ = barMk ↥Y ⟨v, hvt⟩ := hsinv
    rw [swapDiag_apply]
    show barMk ↥Y ⟨l, hlY⟩ = barMk ↥Y m * ((sbar v hvt)⁻¹ * barMk ↥Y m * sbar v hvt)
    rw [hl, map_mul, map_mul, map_mul, map_mul, map_inv, ho1, mul_one, hsinv', hsinv]
    rfl
  have hMq : Odd (Nat.card ↥(bar t (pPrimeCoreOf 2 (centralizer ({v} : Set G))))) :=
    odd_card_bar_pPrimeCoreOf t (centralizer ({v} : Set G))
  have hcomm' : ∀ q ∈ (swapDiag hAB).range,
      ⁅q, sbar g hgt⁆ ∈ bar t (pPrimeCoreOf 2 (centralizer ({v} : Set G))) := by
    intro q hq
    obtain ⟨⟨l, hlY⟩, hl, rfl⟩ := hDΛ q hq
    have hlΛ : l ∈ Λ := Subgroup.mem_subgroupOf.mp hl
    have hcY : ⁅l, g⁆ ∈ Y := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hlY hgt) (inv_mem hlY)) (inv_mem hgt)
    refine ⟨⟨⁅l, g⁆, hcY⟩, Subgroup.mem_subgroupOf.mpr (hcomm l hlΛ), ?_⟩
    change barMk ↥Y ⁅(⟨l, hlY⟩ : ↥Y), (⟨g, hgt⟩ : ↥Y)⁆ = ⁅barMk ↥Y ⟨l, hlY⟩, barMk ↥Y ⟨g, hgt⟩⁆
    exact map_commutatorElement _ _ _
  have hgs : sbar g hgt * sbar v hvt = sbar v hvt * sbar g hgt := by
    unfold sbar
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change g * v = v * g
    exact Subgroup.mem_centralizer_singleton_iff.1 hgv
  have hgA : sbar g hgt ∈ normalizer ((bar t L : Subgroup _) : Set _) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_bar_of_normalizes hgt hgL)
  have hcent := commute_of_odd_commutators_swapDiag hLc.1 hAB hgs hgA hMq hcomm'
  refine mem_centralizerSection_of_map_eq (rr_pcomp hL).1 (isPCompIn_two_iff.mp (rr_pcomp hL)).2 hgt ?_
  intro m hm
  have h1 : barMk ↥Y m * barMk ↥Y ⟨g, hgt⟩ = barMk ↥Y ⟨g, hgt⟩ * barMk ↥Y m :=
    hcent (barMk ↥Y m) ⟨m, hm, rfl⟩
  rw [map_mul, map_mul, map_inv, ← h1, mul_inv_cancel_right]

end CFSG.GH74.GLS.Bg.Pu5
