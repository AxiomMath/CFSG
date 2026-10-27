module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.St1PumpCalc
public import CFSG.GH74.Generic.BProg.Stability

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace S3Sec29A3

variable {G : Type} [Group G] [Finite G]

theorem barMk_eq_one_of_incl {X Y : Subgroup G} (hle : Y ≤ X) (w : ↥Y)
    (hw : barMk ↥X (Subgroup.inclusion hle w) = 1) : barMk ↥Y w = 1 := by
  set N : Subgroup ↥Y := (pPrimeCore 2 ↥X).comap (Subgroup.inclusion hle) with hN
  have hNn : N.Normal := Subgroup.Normal.comap inferInstance _
  have hodd : Odd (Nat.card N) := by
    have h1 : Nat.card (N.map (Subgroup.inclusion hle)) = Nat.card N :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hle)
    rw [← h1]
    exact Odd.of_dvd_nat (odd_card_pPrimeCore ↥X)
      (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
  have hle2 : N ≤ pPrimeCore 2 ↥Y :=
    CFSG.GroupTheory.le_pPrimeCore_of_normal hNn (Nat.coprime_two_left.2 hodd)
  exact (QuotientGroup.eq_one_iff w).mpr
    (hle2 ((QuotientGroup.eq_one_iff (Subgroup.inclusion hle w)).mp hw))

theorem mem_normalizer_Lam {b u g : G} {J Λ : Subgroup G} (hΛ : IsLam b u J Λ)
    (hgb : g ∈ centralizer ({b} : Set G)) (hgu : g ∈ centralizer ({u} : Set G))
    (hπ : ∀ l ∈ Λ, ∀ hlY : l ∈ centralizer ({u} : Set G),
      barMk ↥(centralizer ({u} : Set G)) (⟨g, hgu⟩ * ⟨l, hlY⟩ * ⟨g, hgu⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩) :
    g ∈ normalizer (Λ : Set G) := by
  set Y' : Subgroup G := centralizer ({b} : Set G) ⊓ centralizer ({u} : Set G) with hY'
  have hgY : g ∈ Y' := Subgroup.mem_inf.2 ⟨hgb, hgu⟩
  have hle : Y' ≤ centralizer ({u} : Set G) := inf_le_right
  obtain ⟨hΛY, hΛ2⟩ := isPCompIn_two_iff.mp hΛ.pcW
  have key : ∀ m ∈ Λ.subgroupOf Y',
      barMk ↥Y' (⟨g, hgY⟩ * m * ⟨g, hgY⟩⁻¹) = barMk ↥Y' m := by
    intro m hm
    have hmΛ : (m : G) ∈ Λ := Subgroup.mem_subgroupOf.mp hm
    have h1 := hπ (m : G) hmΛ (hle m.2)
    have hw : barMk ↥Y' (⟨g, hgY⟩ * m * ⟨g, hgY⟩⁻¹ * m⁻¹) = 1 := by
      refine barMk_eq_one_of_incl hle _ ?_
      have e : Subgroup.inclusion hle (⟨g, hgY⟩ * m * ⟨g, hgY⟩⁻¹ * m⁻¹) =
          ⟨g, hgu⟩ * ⟨(m : G), hle m.2⟩ * ⟨g, hgu⟩⁻¹ * (⟨(m : G), hle m.2⟩)⁻¹ := by
        simp only [map_mul, map_inv]
        rfl
      rw [e, map_mul, map_inv, h1]
      group
    rw [map_mul, map_inv] at hw
    exact mul_inv_eq_one.mp hw
  obtain ⟨hgN, -, -⟩ := TwoThin.mem_centralizerSection_of_map_eq hΛY hΛ2 hgY key
  exact hgN

theorem mem_normalizer_of_normalizes_Lam {b u g : G} {J Λ : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hΛ : IsLam b u J Λ)
    (hgb : g ∈ centralizer ({b} : Set G)) (hgΛ : g ∈ normalizer (Λ : Set G)) :
    g ∈ normalizer (J : Set G) := by
  obtain ⟨hJC, hJ2⟩ := isPCompIn_two_iff.mp hJ
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hsub : (J.subgroupOf (centralizer ({b} : Set G))).IsSubnormal :=
    Components.mathlib_subnormal_of_chain hJ2.1 Subgroup.IsSubnormal.top
  have himg : (J.subgroupOf (centralizer ({b} : Set G))).map
        (barMk ↥(centralizer ({b} : Set G))) =
      (Λ.subgroupOf (centralizer ({b} : Set G))).map (barMk ↥(centralizer ({b} : Set G))) := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩
      obtain ⟨l, hl, o, ho, hlo⟩ := hΛ.cover (m : G) (Subgroup.mem_subgroupOf.mp hm)
      have hlC : l ∈ centralizer ({b} : Set G) := hJC (hΛJ hl)
      have hoC : o ∈ centralizer ({b} : Set G) := hJC (TwoThin.pPrimeCoreOf_le J ho)
      have ho1 := barMk_eq_one_of_mem_pPrimeCoreOf hJC hsub ho hoC
      refine ⟨⟨l, hlC⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
      have hm : m = ⟨l, hlC⟩ * ⟨o, hoC⟩ := Subtype.ext hlo
      rw [hm, map_mul, ho1, mul_one]
    · exact Subgroup.map_mono fun a ha =>
        Subgroup.mem_subgroupOf.mpr (hΛJ (Subgroup.mem_subgroupOf.mp ha))
  refine TwoThin.mem_normalizer_of_map_normalizes hJC hJ2 hgb ?_
  rw [himg]
  exact map_conj_bar_of_normalizes hgb hgΛ

theorem cSec_J_of_act_trivial' {z u : G} {J Λ : Subgroup G} (hΛ : IsLam z u J Λ) {c : G}
    (hcJ : c ∈ normalizer (J : Set G)) (hcu : c ∈ centralizer ({u} : Set G))
    (hπ : ∀ l ∈ Λ, ∀ hlY : l ∈ centralizer ({u} : Set G),
      barMk ↥(centralizer ({u} : Set G)) (⟨c, hcu⟩ * ⟨l, hlY⟩ * ⟨c, hcu⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩) :
    c ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
  have hΛJ : Λ ≤ J := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({u} : Set G) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, hφo, hφρ⟩ := exists_phi hΛJ hΛY hΛ.cover
  have hcX : c ∈ normalizer ((J ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hcJ (Subgroup.le_normalizer hcu)
  have hcO : c ∈ normalizer (pPrimeCoreOf 2 J : Set G) := mem_normalizer_pPrimeCoreOf hcJ
  refine ⟨hcJ, hcO, fun k hk => ?_⟩
  obtain ⟨l, hl, o', ho', rfl⟩ := hΛ.cover k hk
  have hlY : l ∈ centralizer ({u} : Set G) := hΛY hl
  have hcl : c * l * c⁻¹ ∈ Λ := conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hcX hl
  have hcom : ⁅l, c⁆ ∈ Λ := by
    have : ⁅l, c⁆ = l * (c * l * c⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem hl (inv_mem hcl)
  have hπl := hπ l hl hlY
  have hcomY : ⁅l, c⁆ ∈ centralizer ({u} : Set G) := hΛY hcom
  have hπcom : barMk ↥(centralizer ({u} : Set G)) ⟨⁅l, c⁆, hcomY⟩ = 1 := by
    have e : (⟨⁅l, c⁆, hcomY⟩ : ↥(centralizer ({u} : Set G))) =
        ⟨l, hlY⟩ * (⟨c, hcu⟩ * ⟨l, hlY⟩ * ⟨c, hcu⟩⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e, map_mul, map_inv, hπl]
    group
  have hphi := hφρ _ hcom
  have hatone : hatMap hΛJ ⟨⁅l, c⁆, hcom⟩ = 1 := by
    rw [← hphi]
    have h1 : (⟨barMk ↥(centralizer ({u} : Set G)) ⟨⁅l, c⁆, hΛY hcom⟩,
        ⟨⟨_, hΛY hcom⟩, Subgroup.mem_subgroupOf.mpr hcom, rfl⟩⟩ : ↥(PumpCalc.bar u Λ)) = 1 :=
      Subtype.ext hπcom
    rw [h1, map_one]
  have hO : ⁅l, c⁆ ∈ pPrimeCoreOf 2 J := (hatMap_eq_one_iff hΛJ _).mp hatone
  have hO' : ⁅o', c⁆ ∈ pPrimeCoreOf 2 J := by
    have : ⁅o', c⁆ = o' * (c * o'⁻¹ * c⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem ho' ((Subgroup.mem_normalizer_iff.mp hcO _).mp (inv_mem ho'))
  have e2 : ⁅l * o', c⁆ = l * ⁅o', c⁆ * l⁻¹ * ⁅l, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact mul_mem (TwoThin.pPrimeCoreOf_normalized J (hΛJ hl) hO') hO

theorem mem_cSec_of_act_trivial {b u g : G} {J Λ : Subgroup G}
    (hJ : IsPCompIn 2 (centralizer ({b} : Set G)) J) (hΛ : IsLam b u J Λ)
    (hgb : g ∈ centralizer ({b} : Set G)) (hgu : g ∈ centralizer ({u} : Set G))
    (hπ : ∀ l ∈ Λ, ∀ hlY : l ∈ centralizer ({u} : Set G),
      barMk ↥(centralizer ({u} : Set G)) (⟨g, hgu⟩ * ⟨l, hlY⟩ * ⟨g, hgu⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩) :
    g ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
  cSec_J_of_act_trivial' hΛ
    (mem_normalizer_of_normalizes_Lam hJ hΛ hgb (mem_normalizer_Lam hΛ hgb hgu hπ)) hgu hπ

theorem act_trivial_of_cSec {u c : G} {Λ M : Subgroup G}
    (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M) (hΛL : PumpCalc.bar u Λ ≤ PumpCalc.bar u M)
    (hcu : c ∈ centralizer ({u} : Set G)) (hcM : c ∈ centralizerSection M (pPrimeCoreOf 2 M)) :
    ∀ l ∈ Λ, ∀ hlY : l ∈ centralizer ({u} : Set G),
      barMk ↥(centralizer ({u} : Set G)) (⟨c, hcu⟩ * ⟨l, hlY⟩ * ⟨c, hcu⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩ := by
  have hπ := map_eq_of_mem_cSec hM hcu hcM
  intro l hl hlY
  have hmem : barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩ ∈ PumpCalc.bar u M :=
    hΛL ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  obtain ⟨m₁, hm₁, hm₁eq⟩ := hmem
  have h1 := hπ m₁ hm₁
  simp only [map_mul, map_inv] at h1 ⊢
  rw [← hm₁eq]
  exact h1

omit [Finite G] in
theorem act_trivial_of_comm {u d : G} {Λ M : Subgroup G}
    (hcomm : ⁅PumpCalc.bar u Λ, PumpCalc.bar u M⁆ = ⊥)
    (hdu : d ∈ centralizer ({u} : Set G)) (hdM : d ∈ M) :
    ∀ l ∈ Λ, ∀ hlY : l ∈ centralizer ({u} : Set G),
      barMk ↥(centralizer ({u} : Set G)) (⟨d, hdu⟩ * ⟨l, hlY⟩ * ⟨d, hdu⟩⁻¹) =
        barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩ := by
  intro l hl hlY
  have hmem1 : barMk ↥(centralizer ({u} : Set G)) ⟨d, hdu⟩ ∈ PumpCalc.bar u M :=
    ⟨⟨d, hdu⟩, Subgroup.mem_subgroupOf.mpr hdM, rfl⟩
  have hmem2 : barMk ↥(centralizer ({u} : Set G)) ⟨l, hlY⟩ ∈ PumpCalc.bar u Λ :=
    ⟨⟨l, hlY⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have hc := Subgroup.commutator_mem_commutator hmem2 hmem1
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  rw [map_mul, map_mul, map_inv, ← hc]
  group

end S3Sec29A3

end CFSG.GH74.Generic.BProg.B3
