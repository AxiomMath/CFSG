module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.RowFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.EngSingle
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.Eng

open Subgroup Relation CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

structure FiKnown (S : List TauCeti.SporadicName) (U R : GroupClass) : Prop where
  cases : ∀ (X : Type) [Group X], R X → IsSporadic X .Fi22 ∨ IsSporadic X .Fi23 ∨
    IsSporadic X .Fi24Prime ∨ U X
  u_lt : ∀ (X : Type) [Group X] [Finite X], U X → ∀ s ∈ S, Nat.card X < Nat.card (Carrier s)

structure FiRowFactsCore (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) : Prop where
  reach : ∃ U R : GroupClass, ReachRow IsK S Up Lo R ∧ FiKnown S U R
  evenOut : ∀ s ∈ S, EvenCoverOutHered Up s
  thm24 : ∀ s ∈ S, s = .M ∨ (s ≠ .M ∧ Thm24Hex s)
  inRows : ∀ s ∈ S, s ∈ Sol78Rows := by decide
  std_row : ∀ (G : Type) [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G),
    (∃ s' ∈ S, OddCover s' L) → T ≠ ⊥ → Sol78Link5bData K₁ L T s → CFSG.IsQuasisimple ↥K₁ →
      IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) →
        SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2
  four_a : FourAFacts IsK S

structure FiRowFacts (IsK : GroupClass) (S Up Lo : List TauCeti.SporadicName) : Prop
    extends FiRowFactsCore IsK S Up Lo where
  fi23 : ∀ s ∈ S, Fi23Excl s ∨ TauCeti.SporadicName.Fi24Prime ∈ Up

variable {H : Type} [Group H] [Finite H] {N : Subgroup H}

@[expose] def CoexMax (H : Type) [Group H] : Prop :=
  ∀ P : Subgroup H, InL P → IsSporadic (↥P ⧸ center ↥P) .Fi23 → Maximal P

theorem noLink5bOut_of_types {S Up Lo : List TauCeti.SporadicName}
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hUp : NoUp Up H)
    (hfi : ∀ s ∈ S, Fi23Excl s ∨ TauCeti.SporadicName.Fi24Prime ∈ Up ∨
      (s = TauCeti.SporadicName.Fi23 ∧ CoexMax H ∧
        ∀ (X : Type) [Group X], IsSporadic X .Fi23 → ¬ IsSporadic X .Fi24Prime))
    (hEven : ∀ s ∈ S, EvenCoverOutHered Up s) (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) : NoLink5bOut S Up H := by
  intro P Q T s hPL hne hT hdata ⟨s', hs', hsc⟩
  have hQL : InL Q := ⟨T, hT, hdata.T_two, hdata.L_comp⟩
  have hQq := hdata.L_comp.isQuasisimple
  have hPq := hdata.K_comp.isQuasisimple
  have hQne : Q ≠ N := inL_ne_of_fStarSimple' hN hQL
  rcases List.mem_append.1 hs' with hS | hU
  · have hSa : s' ∈ S ++ Up ++ Lo := List.mem_append_left _ (List.mem_append_left _ hS)
    rcases hfi s' hS with hFi | hFi | ⟨rfl, hmax, h24⟩
    · exact fiFalse_of_link5b fiLink5bSection ih hUp hN hidx hkp hQL hQq hQne hPq hne hSa hsc
        (Or.inl hFi) (hEven s' hS) hdata.L_comp hdata.s_sq hdata.K_comp hdata.incl.1 hdata.link
    · exact fiFalse_of_link5b fiLink5bSection ih hUp hN hidx hkp hQL hQq hQne hPq hne hSa hsc
        (Or.inr hFi) (hEven s' hS) hdata.L_comp hdata.s_sq hdata.K_comp hdata.incl.1 hdata.link
    · obtain ⟨Y, _, _, N', P', hcard, hsecY, hFS, hidx', hkp', hsol, hq', ⟨e⟩, ⟨g⟩⟩ :=
        fiLink5bSection H N hN hidx hkp P Q hQq hQne hPq hne T s hdata.L_comp hdata.s_sq
          hdata.K_comp hdata.incl.1 hdata.link
      obtain ⟨f⟩ := hsc
      have hcq : IsSporadic (↥P' ⧸ center ↥P') .Fi23 := ⟨e.symm.trans f⟩
      by_cases hodd : Odd (Nat.card ↥(center ↥P'))
      · obtain ⟨-, ⟨h24'⟩⟩ :=
          ih.apply hsecY hcard N' hFS hidx' hkp' P' hsol ⟨.Fi23, hSa, hq', hodd, hcq⟩
        obtain ⟨hm⟩ := (hmax P hPL ⟨f⟩).2 Q (Relation.TransGen.single (hdata.lt_of_ne hT))
        exact h24 N' ⟨g.symm.trans (hm.symm.trans f)⟩ ⟨h24'⟩
      · obtain ⟨s'', hs'', ⟨g'⟩⟩ :=
          hEven .Fi23 hS Y (ih.uHered.of_section hsecY) N' hFS hidx' hkp' P' hsol hq' hcq hodd
        exact hUp Q hQL s'' hs'' ⟨g.trans g'⟩
  · exact hUp _ hPL s' hU hsc

theorem fiHyp31_core {IsK : GroupClass} {S Up Lo : List TauCeti.SporadicName}
    (rf : FiRowFactsCore IsK S Up Lo) (lx : Hyp31LitX) (lit : Sol78Lit)
    (hrow : Hyp31Row IsK (IsLS S))
    (ih : BelowSec (Sol78PredS (S ++ Up ++ Lo)) H) (hN : FStarSimple N)
    (hidx : N.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hUp : UpCtx S Up H)
    (hmaxS : ∀ L₁ : Subgroup H, InL L₁ → ∀ s' ∈ S, IsSporadic (↥L₁ ⧸ center ↥L₁) s' →
      Maximal L₁)
    (hN22 : ¬ IsSporadic ↥N .Fi22) (hN23 : ¬ IsSporadic ↥N .Fi23)
    (hN24 : ¬ IsSporadic ↥N .Fi24Prime) {L : Subgroup H} (hL : SolStd L)
    (hcov : ∃ s ∈ S, OddCover s L) : Hyp31Glob H N IsK (IsLS S) ∧ Hyp31FourA H N IsK := by
  obtain ⟨U, R, rr, hkn⟩ := rf.reach
  have hjunc : JunctionStmtAt H := Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)
  have rc : ReachFacts IsK S Up Lo R := { rr with evenOut := rf.evenOut }
  have hL₀ : InL L := inL_of_solStd hL
  have hnotN : ¬ R ↥N := by
    intro hR
    obtain ⟨s, hs, hcovL⟩ := hcov
    rcases hkn.cases ↥N hR with h | h | h | h
    · exact hN22 h
    · exact hN23 h
    · exact hN24 h
    · have := hN.normal
      have hLN : L ≤ N := le_of_perfect_of_index_le_two hidx hcovL.1.1
      obtain ⟨e⟩ := hcovL.2.2
      have h1 : Nat.card (Carrier s) ≤ Nat.card ↥L := by
        rw [← Nat.card_congr e.toEquiv]
        exact Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
      have h2 : Nat.card ↥L ≤ Nat.card ↥N := Subgroup.card_le_of_le hLN
      have h3 := hkn.u_lt ↥N h s hs
      omega
  have c : DescCtx H N IsK S Up Lo R :=
    ⟨hjunc, lit.thm22.sec ih.uHered, ih, hUp, rc, hnotN, hrow.isK_inv, hN, hidx, hkp⟩
  obtain ⟨Q, tw, htw, hQinj, hlam, hfix, hsec⟩ := rf.four_a
  have htab : TwoAdicTable IsK S H := fun L P T s hL hT hdata hPq hK =>
    (rf.std_row H L P T s hL hT hdata hPq hK).2
  have hstdL : ∀ L₁ : Subgroup H, InL L₁ → Maximal L₁ → ∀ s' ∈ S, OddCover s' L₁ →
      SolStd L₁ ∧ ∃ P : Sylow 2 (centralizer (L₁ : Set H)), IsCyclic ↥P := by
    intro L₁ hL₁ hmax s' hs' hcov₁
    have hrank : 3 ≤ CFSG.pRank 2 ↥L₁ :=
      (hrow.quasi_L ↥L₁ ⟨s', hs', hcov₁⟩).2.2
    have hstd : StdBare L₁ := stdBare_of_maximal (lit.thm22 H ih.uHered) hkp hN hidx hmax hrank
    have hsol : SolStd L₁ := solStd_of_inL_of_stdBare hL₁ hstd
    exact ⟨hsol, cyclic_sylow_of_lit lit.toSol78LitCore lx.oddLie hN hidx hkp hsol
      (rf.inRows s' hs') hcov₁⟩
  refine ⟨⟨hN, hidx, ?_, ?_, ?_, ?_⟩, ⟨?_⟩⟩
  ·
    intro L₁ hL₁ hLS
    obtain ⟨s', hs', hq, hodd, hsp⟩ := hLS
    have hcov₁ : OddCover s' L₁ := ⟨hq, hodd, hsp⟩
    have hmax : Maximal L₁ := hmaxS L₁ hL₁ s' hs' hsp
    exact ⟨hmax, (hstdL L₁ hL₁ hmax s' hs' hcov₁).2⟩
  ·
    intro K₁ hK₁L hK₁ G₁ hNG
    exact not_max_of_reach c hL₀ hcov hK₁L hK₁ hNG
  ·
    intro K₁ L₁ hK₁L hK₁ hL₁L h
    rcases desc_of_reach c hL₀ hcov hK₁L hK₁ h with h1 | ⟨hty, hK⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hty, hK⟩
  ·
    intro K₁ L₁ T s hT hmax hdata hK
    have hK₁L : InL K₁ := hdata.inL_left hT
    have hKL : K₁ ≤ L₁ := hdata.le_left
    obtain ⟨hty, -⟩ := single_link_of_lt_le c hL₀ hcov htab hK₁L hmax (hdata.lt_of_ne hT) hKL hK
    exact rf.std_row H L₁ K₁ T s hty hT hdata hK₁L.isQuasisimple hK
  ·
    intro K₁ L₁ hK₁L hmax hlt hKL hK N₀ hcan
    obtain ⟨hty, T, s, hT, hdata⟩ := single_link_of_lt_le c hL₀ hcov htab hK₁L hmax hlt hKL hK
    obtain ⟨s', hs', hcov₁⟩ := hty
    obtain ⟨hsol, hcyc⟩ := hstdL L₁ hmax.1 hmax s' hs' hcov₁
    have hcyc' := forall_sylow_isCyclic hcyc
    have hq : CFSG.IsQuasisimple ↥K₁ := hK₁L.isQuasisimple
    have hQΛ : Q ↥(lam L₁ N₀) :=
      hlam H L₁ K₁ N₀ T s ⟨s', hs', hcov₁⟩ hT hdata hq hK hcan hcyc'
        (fun htw' => htw htw' s' hs' H N L₁ hN hidx hkp hcov₁ hsol hcyc)
    refine ⟨?_, ?_⟩
    ·
      rintro ⟨A, f, hf⟩
      exact hsec H K₁ N₀ hq hK hcan ↥(lam L₁ N₀) hQΛ ⟨A, f, hf⟩
    ·
      intro K₂ _ _ hperf hiso α hα1 hα2
      obtain ⟨e₂⟩ := hiso
      have : Group.IsPerfect ↥K₁ := hq.1
      obtain ⟨e₃⟩ := cqEquiv_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
        (QuotientGroup.mk'_surjective _) (by
          rw [QuotientGroup.ker_mk']
          exact oddCore_le_center hq)
      obtain ⟨h1, h2⟩ := hfix K₂ hperf ⟨_, inferInstance, hK, ⟨e₂.trans e₃⟩⟩ α hα1 hα2
      exact ⟨fun ⟨f, hf⟩ => h1 (hQinj _ _ f hf hQΛ),
        fun hin' ⟨f, hf⟩ => h2 hin' (hQinj _ _ f hf hQΛ)⟩

theorem fiHyp31_of_rowFacts {IsK : GroupClass} {S Up Lo : List TauCeti.SporadicName}
    (rf : FiRowFacts IsK S Up Lo) (lx : Hyp31LitX) : FiHyp31 IsK S (S ++ Up ++ Lo) Up := by
  intro lit hrow H _ _ ih N hN hidx hkp hUp hN22 hN23 hN24 L hL hcov
  obtain ⟨U, R, rr, -⟩ := rf.reach
  have hjunc : JunctionStmtAt H := Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec ih.uHered)
  refine fiHyp31_core rf.toFiRowFactsCore lx lit hrow ih hN hidx hkp
    ⟨hUp, noLink5bOut_of_types ih hUp (fun s hs => (rf.fi23 s hs).imp id Or.inl) rf.evenOut hN
      hidx hkp⟩ ?_ hN22 hN23 hN24 hL hcov
  · intro L₁ hL₁ s' hs' hsp
    exact fiMaximal_of_central_type fiLink5bSection hjunc ih hUp hN hidx hkp hL₁
      (List.mem_append_left _ (List.mem_append_left _ hs')) hsp (rf.fi23 s' hs') (rf.evenOut s' hs')
      (rr.sp_not_exc s' (List.mem_append_left Up hs'))

end CFSG.EvenSporadicStandard.Induction.Fi.Eng
