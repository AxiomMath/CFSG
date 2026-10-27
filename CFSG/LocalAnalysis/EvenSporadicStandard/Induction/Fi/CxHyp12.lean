module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.CxFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowBC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCfg610Hyp12
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.Cx

open Subgroup Relation Cover CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.EvenSporadicStandard.Induction.Fi.Eng

section Counting

open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem eq_of_known_type (pf : FiPinned) {K₀ M : Subgroup H} {u₀ : H} (hu₀2 : orderOf u₀ = 2)
    (hu₀K : u₀ ∈ K₀) (hK₀M : K₀ ≤ M) (hMq : CFSG.IsQuasisimple ↥M)
    (hMu : ∀ m ∈ M, m * u₀ = u₀ * m) (hZ : Nat.card (center ↥K₀) = 2)
    (hcard : Nat.card ↥K₀ = 129123503308800)
    (hc22 : Nat.card (Carrier TauCeti.SporadicName.Fi22) = 64561751654400)
    (hR : FiKnown3 (↥M ⧸ center ↥M)) : M = K₀ := by
  have hu₀M : u₀ ∈ M := hK₀M hu₀K
  have hz : (⟨u₀, hu₀M⟩ : ↥M) ∈ center ↥M :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hMu g g.2)
  rcases hR with h22 | h23 | h24
  ·
    have hcM : Nat.card (↥M ⧸ center ↥M) = 64561751654400 := card_of_isSporadic hc22 h22
    set K' : Subgroup ↥M := K₀.subgroupOf M with hK'
    set f : ↥K' →* ↥M ⧸ center ↥M := (QuotientGroup.mk' (center ↥M)).comp K'.subtype with hf
    have eK : ↥K' ≃* ↥K₀ := Subgroup.subgroupOfEquivOfLe hK₀M
    have hK'card : Nat.card ↥K' = 129123503308800 := by rw [Nat.card_congr eK.toEquiv, hcard]
    have hker : f.ker ≤ center ↥K' := by
      intro x hx
      have hx1 : QuotientGroup.mk' (center ↥M) (x : ↥M) = 1 := hx
      have hxc : (x : ↥M) ∈ center ↥M := (QuotientGroup.eq_one_iff _).1 hx1
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hxc (y : ↥M)))
    have hkerc : Nat.card f.ker ≤ 2 := by
      have h1 : Nat.card f.ker ≤ Nat.card (center ↥K') := Subgroup.card_le_of_le hker
      have h2 : Nat.card (center ↥K') = 2 := by rw [card_center_congr eK, hZ]
      omega
    have hprod : Nat.card ↥K' = Nat.card (f.range) * Nat.card f.ker := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
      exact h1
    have hrange : f.range = ⊤ := by
      have hpos : 0 < Nat.card f.ker := Nat.card_pos
      have hge : Nat.card (↥M ⧸ center ↥M) ≤ Nat.card f.range := by
        rw [hcM]
        interval_cases h : Nat.card f.ker <;> omega
      exact Subgroup.eq_top_of_le_card _ hge
    have hmem : ∀ m : ↥M, ∃ k z : ↥M, k ∈ K' ∧ z ∈ center ↥M ∧ m = k * z := by
      intro m
      have : QuotientGroup.mk' (center ↥M) m ∈ f.range := hrange ▸ Subgroup.mem_top _
      obtain ⟨k, hk⟩ := this
      refine ⟨k, (k : ↥M)⁻¹ * m, k.2, QuotientGroup.eq.1 hk, by group⟩
    have hcomm : (commutator ↥M) ≤ K' := by
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨k₁, z₁, hk₁, hz₁, rfl⟩ := hmem a
      obtain ⟨k₂, z₂, hk₂, hz₂, rfl⟩ := hmem b
      rw [Fi.V3.commutatorElement_mul_central (Subgroup.mem_center_iff.1 hz₁)
        (Subgroup.mem_center_iff.1 hz₂)]
      simp only [commutatorElement_def]
      exact K'.mul_mem (K'.mul_mem (K'.mul_mem hk₁ hk₂) (K'.inv_mem hk₁)) (K'.inv_mem hk₂)
    have hperf : commutator ↥M = ⊤ := Group.isPerfect_def.1 hMq.1
    have hK'top : (⊤ : Subgroup ↥M) ≤ K' := by
      rw [← hperf]
      exact hcomm
    refine le_antisymm (fun m hm => ?_) hK₀M
    exact Subgroup.mem_subgroupOf.1 (hK'top (Subgroup.mem_top (⟨m, hm⟩ : ↥M)))
  ·
    have hbot : center ↥M = ⊥ := pf.mult23 ↥M hMq h23
    rw [hbot, Subgroup.mem_bot] at hz
    have : u₀ = 1 := congrArg Subtype.val hz
    rw [this, orderOf_one] at hu₀2
    exact absurd hu₀2 (by norm_num)
  ·
    have hodd : Odd (Nat.card ↥(center ↥M)) := pf.mult24 ↥M hMq h24
    have hord : orderOf (⟨⟨u₀, hu₀M⟩, hz⟩ : ↥(center ↥M)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hu₀2
    have h2 : 2 ∣ Nat.card ↥(center ↥M) := hord ▸ orderOf_dvd_natCard _
    exact absurd (even_iff_two_dvd.2 h2) (Nat.not_even_iff_odd.2 hodd)

end Counting

section Certificates


theorem fiCx_leaf {H : Type} [Group H] [Finite H] {N : Subgroup H}
    (ih : BelowSec (Sol78PredS ([.Fi23, .Fi24Prime] ++ [] ++ [.Fi22])) H)
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hEven : ∀ s ∈ [TauCeti.SporadicName.Fi23, .Fi24Prime], EvenCoverOutHered [] s) :
    Link5bLeaf [.Fi23, .Fi24Prime] [] FiKnown3 H := by
  intro P Q T s hPL hne hT hdata ⟨s', hs', hsc⟩
  have hQL : InL Q := ⟨T, hT, hdata.T_two, hdata.L_comp⟩
  have hQq := hdata.L_comp.isQuasisimple
  have hPq := hdata.K_comp.isQuasisimple
  have hQne : Q ≠ N := inL_ne_of_fStarSimple' hN hQL
  have hS : s' ∈ [TauCeti.SporadicName.Fi23, .Fi24Prime] := by simpa using hs'
  have hSa : s' ∈ [TauCeti.SporadicName.Fi23, .Fi24Prime] ++ [] ++ [.Fi22] :=
    List.mem_append_left _ (List.mem_append_left _ hS)
  rcases List.mem_cons.1 hS with rfl | hS24
  · obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩⟩ :=
      fiLink5bSection H N hN hidx hkp P Q hQq hQne hPq hne T s hdata.L_comp hdata.s_sq
        hdata.K_comp hdata.incl.1 hdata.link
    obtain ⟨f⟩ := hsc
    have hcq : IsSporadic (↥P' ⧸ center ↥P') .Fi23 := ⟨e.symm.trans f⟩
    by_cases hodd : Odd (Nat.card ↥(center ↥P'))
    · obtain ⟨-, ⟨h24'⟩⟩ :=
        ih.apply hsecY hcard N' hFS hidx' hkp' P' hsol ⟨.Fi23, hSa, hq', hodd, hcq⟩
      exact Or.inr (Or.inr ⟨g.trans h24'⟩)
    · obtain ⟨s'', hs'', -⟩ :=
        hEven .Fi23 hS Y (ih.uHered.of_section hsecY) N' hFS hidx' hkp' P' hsol hq' hcq hodd
      exact absurd hs'' (by simp)
  · obtain rfl : s' = .Fi24Prime := List.mem_singleton.1 hS24
    exact (fiFalse_of_link5b fiLink5bSection ih noUp_nil hN hidx hkp hQL hQq hQne hPq hne hSa hsc
      (Or.inl pinFi23Excl24) (hEven _ hS) hdata.L_comp hdata.s_sq hdata.K_comp hdata.incl.1
      hdata.link).elim

theorem hyp12_core (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) (lit : Sol78Lit) {H : Type} [Group H] [Finite H]
    (ih : BelowSec (Sol78PredS fiTypes) H) {N L : Subgroup H} {t : H}
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hcov : OddCover .Fi24Prime L)
    (hSol : SolStd L) (ht2 : orderOf t = 2) (htL : t ∈ centralizer (L : Set H)) {K : Subgroup H}
    (hKL : K ≤ L) (hKs : IsSporadic ↥K .Fi23)
    {u₀ : H} (hu₀K : u₀ ∈ K) (hT : Fi23Transposition K u₀) {M : Subgroup H}
    (hM : IsCompIn M (centralizer ({u₀} : Set H))) (hle : K ⊓ centralizer ({u₀} : Set H) ≤ M)
    (hMt : CFSG.conjugate M t = M) : M = K ⊓ centralizer ({u₀} : Set H) := by
  classical
  have hu₀2 : orderOf u₀ = 2 := hT.2.1
  have hloc := fiLoc_of_transposition hKs hKL hT
  obtain ⟨-, -, -, -, hK₀q, -⟩ := id hloc
  have hut₀ : u₀ * t = t * u₀ := mem_centralizer_iff.1 htL u₀ (hKL hu₀K)
  have hK₀X : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({u₀} : Set H) := inf_le_right
  have hK₀t : K ⊓ centralizer ({u₀} : Set H) ≤ centralizer ({t} : Set H) := fun k hk =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL k (hKL hk.1))
  have hnt := normal_of_fiIn24_layer hcov hloc htL ht2 hSol
  have hKcomp : IsCompIn (K ⊓ centralizer ({u₀} : Set H))
      (centralizer ({u₀} : Set H) ⊓ centralizer ({t} : Set H)) :=
    isCompIn_of_normal (le_inf hK₀X hK₀t) hK₀q hnt
  have hu₀1 : u₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hu₀2; omega
  have hT₀p : IsPGroup 2 ↥(zpowers u₀ ⊔ zpowers t) := by
    have hts : t ∈ normalizer ((zpowers u₀ : Subgroup H) : Set H) := by
      refine Subgroup.centralizer_le_normalizer ((zpowers u₀ : Subgroup H) : Set H) ?_
      rw [centralizer_zpowers_eq]
      exact mem_centralizer_singleton_iff.2 hut₀.symm
    have ht₀sq : t ^ 2 ∈ zpowers u₀ := by
      have h1 : t ^ 2 = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht2] at this
      rw [h1]
      exact one_mem _
    exact isPGroup_sup_zpowers (isPGroup_zpowers_of_orderOf_two hu₀2) hts ht₀sq
  have hT₀ne : zpowers u₀ ⊔ zpowers t ≠ ⊥ := fun hb =>
    hu₀1 (Subgroup.mem_bot.1 (hb ▸ mem_sup_left (mem_zpowers u₀)))
  have hinL : InL (K ⊓ centralizer ({u₀} : Set H)) :=
    ⟨zpowers u₀ ⊔ zpowers t, hT₀ne, hT₀p, by rw [centralizer_sup_zpowers_eq]; exact hKcomp⟩
  have hmult : OddMultTrivial .Fi23 := fun L' _ _ hq _ hcq => pf.mult23 L' hq hcq
  have hK₀K : IsOddCentralExt Fi23D ↥(K ⊓ centralizer ({u₀} : Set H)) :=
    (stage3Row_fi2324 hmult (fi23FixesElem_of_atlas hmult atl.fi22Covers)
      (fi24InFixesElem_of_atlas atl.fi22Covers)).rowIsK .Fi24Prime (by simp) H L _ u₀ hcov hloc
  have rf := fiRowFactsCore_cx pf hyp12 lo atl
  have rr := reachRow_fi22K pf hyp12 atl.fi22Covers atl.fi22Even [.Fi23, .Fi24Prime] []
    (fun s hs => by simpa using hs) (by simp) (by simp)
  have rc : Eng.ReachFacts (IsOddCentralExt Fi23D) [.Fi23, .Fi24Prime] [] [.Fi22] FiKnown3 :=
    { rr with evenOut := rf.evenOut }
  have ih' : BelowSec (Sol78PredS ([.Fi23, .Fi24Prime] ++ [] ++ [.Fi22])) H :=
    BelowSec.mono_types (fun s hs => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with (rfl | rfl) | rfl <;> simp [fiTypes]) ih
  have hjunc : JunctionStmtAt H := Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)
  have hleaf : Link5bLeaf [.Fi23, .Fi24Prime] [] FiKnown3 H :=
    fiCx_leaf ih' hN hidx hKP rf.evenOut
  have hKM : K ⊓ centralizer ({u₀} : Set H) ≤ M ⊔ CFSG.conjugate M t := by
    rw [hMt, sup_idem]
    exact hle
  have hLt : Lt (K ⊓ centralizer ({u₀} : Set H)) M :=
    lt_of_le_sup_conj hu₀2 ht2 hut₀ hKcomp hM hKM
  have hreach := reach_reflTransGen_gen hjunc ih' hleaf rc hN hidx hKP hinL
    (KLike.of_isK hK₀K) (ReflTransGen.single hLt) (rr.K_reach _ hK₀K)
  have hZ0 : Nat.card (center ↥(K ⊓ centralizer ({u₀} : Set H))) = 2 :=
    fi23_card_center_inf_centralizer hKs hu₀K hu₀2 hT.2.2
  exact eq_of_known_type pf hu₀2 ⟨hu₀K, mem_centralizer_singleton_iff.2 rfl⟩ hle hM.isQuasisimple
    (fun m hm => mem_centralizer_singleton_iff.1 (hM.1 hm)) hZ0 hT.2.2 pinCard22 hreach.1

theorem hyp12_at (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) (lit : Sol78Lit) {H : Type} [Group H] [Finite H]
    (ih : BelowSec (Sol78PredS fiTypes) H) {N L : Subgroup H} {t u : H}
    (hKP : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hcov : OddCover .Fi24Prime L)
    (hcfg : Cfg610_2 H N L t u) {K Lu Lut : Subgroup H} (hdat : Cfg610_2Data H L t u K Lu Lut)
    {u₀ : H} (hu₀K : u₀ ∈ K) (hT : Fi23Transposition K u₀) {M : Subgroup H}
    (hM : IsCompIn M (centralizer ({u₀} : Set H))) (hle : K ⊓ centralizer ({u₀} : Set H) ≤ M)
    (hMt : CFSG.conjugate M t = M) : M = K ⊓ centralizer ({u₀} : Set H) :=
  hyp12_core pf hyp12 lo atl lit ih hcfg.fstar hcfg.index_le_two hKP hcov hcfg.standardL
    hcfg.t_order hcfg.t_mem hdat.le_L hdat.isSporadic hu₀K hT hM hle hMt

theorem fi24Cfg610Hyp12_of_engine (pf : FiPinned) (hyp12 : Hyp12Fi) (lo : LieModelOrders)
    (atl : FiAtlas) : Fi24Cfg610Hyp12 :=
  fun lit _ _ _ ih _ _ _ _ hKP hcov hcfg _ _ _ hdat _ hu₀K hT _ hM hle hMt _ =>
    hyp12_at pf hyp12 lo atl lit ih hKP hcov hcfg hdat hu₀K hT hM hle hMt

end Certificates

end CFSG.EvenSporadicStandard.Induction.Fi.Cx
