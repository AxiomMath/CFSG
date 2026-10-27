module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenBlockTwoRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenFourSixTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.GH74.Generic.GKFCover
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.Alternating.Multipliers.Main
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

namespace AltTen

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_of_alt_two_blocks {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) {t : G}
    (htX : t ∈ X) (htL : L.map (MulAut.conj t).toMonoidHom ≠ L) {N : ℕ} (hN : 6 ≤ N)
    (e : ↥(barM X L) ≃* alternatingGroup (Fin N)) : 4 ≤ Open.pRank 3 X := by
  have h2 : 2 ≤ Open.pRank 3 (barM X L) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_alternating hN
  obtain ⟨E, hEL, hE, hE9⟩ := exists_elemAbelian_nine h2
  have hZ : Subgroup.center ↥(barM X L) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  refine four_le_pRank_of_two_blocks hL htX htL hEL hE hE9 ?_
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  have hxL := hEL hxE
  have hmem : (⟨x, hxL⟩ : ↥(barM X L)) ∈ Subgroup.center ↥(barM X L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hxC g g.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hmem

theorem center_eq_bot_of_alt {Y : Type} [Group Y] [Finite Y]
    (hq : Open.IsQuasisimple Y) (hO : CFSG.pCore 2 Y = ⊥) {m : ℕ} (hm : 8 ≤ m)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin m)) : Subgroup.center Y = ⊥ := by
  have hq' : CFSG.IsQuasisimple Y :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff Y).2.2.1.mpr hq
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
  rw [(CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m (by omega)).2,
    if_neg (by omega)] at hdvd
  have hodd := odd_card_center_of_pCore_eq_bot hO
  have h1 : Nat.card (Subgroup.center Y) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem pCore_barM_eq_bot {X L : Subgroup G} (hL : IsTwoPrimeComponent X L) :
    CFSG.pCore 2 ↥(barM X L) = ⊥ := by
  have h1 := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2
    hL.component.2.1
  have h2 : pCoreOf 2 (⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) = ⊥ := by
    have h3 := CFSG.pCore_map_iso 2 (Subgroup.topEquiv (G := ↥X ⧸ CFSG.pCore 2 ↥X))
    rw [CFSG.GH74.GLS.Stage2.Signalizer.pCore_quotient_pCore (A := ↥X) 2] at h3
    have h4 : CFSG.pCore 2 ↥(⊤ : Subgroup (↥X ⧸ CFSG.pCore 2 ↥X)) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)).mp h3
    rw [pCoreOf, h4, Subgroup.map_bot]
  have h5 : pCoreOf 2 (barM X L) = ⊥ := eq_bot_iff.mpr (h1.trans h2.le)
  rw [pCoreOf] at h5
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h5

theorem false_of_alt_two_blocks {X L : Subgroup G}
    (hL : IsTwoPrimeComponent X L) {t : G} (htX : t ∈ X)
    (htL : L.map (MulAut.conj t).toMonoidHom ≠ L) (h3 : Open.pRank 3 X ≤ 3)
    (halt : (∃ n : ℕ, 5 ≤ n ∧ Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃*
        alternatingGroup (Fin (2 * n)))) ∨
      ∃ N : ℕ, 6 ≤ N ∧ Nonempty (↥(barM X L) ≃* alternatingGroup (Fin N))) : False := by
  rcases halt with ⟨n, hn, ⟨e⟩⟩ | ⟨N, hN, ⟨e⟩⟩
  · have hZ := center_eq_bot_of_alt hL.component.2.2 (pCore_barM_eq_bot hL) (by omega) e
    have e' : ↥(barM X L) ≃* alternatingGroup (Fin (2 * n)) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
    have := four_le_pRank_of_alt_two_blocks hL htX htL (by omega) e'
    omega
  · have := four_le_pRank_of_alt_two_blocks hL htX htL hN e
    omega

private theorem false_of_alt_surj {n : ℕ} (hn : 6 ≤ n)
    (g : ↥(alternatingGroup (Fin n)) →* alternatingGroup (Fin 5)) (hg : Function.Surjective g) :
    False := by
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have h := card_eq_sixty_of_isSimpleGroup g hg
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  have h6 : (6 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
  have : (720 : ℕ) ≤ n.factorial := by simpa [Nat.factorial] using h6
  omega

theorem nineThree_cases_of_alt5 (h93 : Asc81bNineThree) (h85 : Asc81bEightFive)
    (hPLT : CitedBlockTransvectionPLType) (hSp : KFactSpTwoSimple) (h7 : CitedBlockAltSevenPL)
    {X S L I₀ : Subgroup G} (hK : Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) (hX : ¬ InClassXBlock L)
    (hI₀ : I₀ ∈ cZero (Subgroup.normalizer (S : Set G) ⊓ L)) (hI₀c : IsTwoPrimeComponent I₀ I₀)
    (f : ↥I₀ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) :
    NineThreeTwo X S L ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (↥(barM X L) ⧸ Subgroup.center ↥(barM X L) ≃*
        alternatingGroup (Fin (2 * n)))) ∨
      ∃ N : ℕ, 6 ≤ N ∧ Nonempty (↥(barM X L) ≃* alternatingGroup (Fin N)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := hL.le
  have hNX : normalizer (S : Set G) ⊓ L ≤ X := inf_le_right.trans hLX
  have hI₀X : I₀ ≤ X := hI₀.le.trans hNX
  have hSy2 : ¬ IsSylowTwoOf (S ⊓ L) L := fun h =>
    hX (h85 G X S L hK hA hL.toIsTwoPrimeComponent h)
  have hI1 : I₀ ≠ ⊥ := by
    haveI : Nontrivial ↥I₀ := hf.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot I₀).mp inferInstance
  obtain ⟨hCP, hCne, hCp, hCsn, -⟩ :=
    CZeroThreePerfect.barM_facts hLX hI₀.le hI₀.subnormal hI₀c.perfect hI1
  set Pb := barM X (normalizer (S : Set G) ⊓ L) with hPb
  set C' := (barM X I₀).subgroupOf Pb with hC'
  have hC'ne : C' ≠ ⊥ := by
    intro h
    apply hCne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCP, ← hC', h, Subgroup.map_bot]
  have hC'p : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective Pb.subtype_injective
    rw [Subgroup.map_commutator, hC', Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCp
  have hC'A5 : ∃ g : ↥C' →* alternatingGroup (Fin 5), Function.Surjective g := by
    set β := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hI₀X with hβdef
    have hβ := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective hI₀X
    set γ := (Subgroup.subgroupOfEquivOfLe hCP).symm with hγ
    refine exists_surjective_alt5_of_ker f hf (γ.toMonoidHom.comp β)
      (fun c => by
        obtain ⟨b, rfl⟩ := γ.surjective c
        obtain ⟨a, rfl⟩ := hβ b
        exact ⟨a, rfl⟩) ?_
    rintro ⟨g0, hg0⟩
    have hg1 : β g0 = 1 := γ.injective (by
      rw [map_one]
      exact (MonoidHom.mem_ker).mp hg0)
    have hgk : g0 ∈ β.ker := hg1
    rw [hβdef, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub,
      Subgroup.mem_subgroupOf] at hgk
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgk
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨x, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hthis := congrArg (fun y => ((y : ↥X) : G)) (congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
    rw [← hxg]
    exact hthis
  obtain ⟨hC''ne, hC''p, hC''s, -⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
  have hC''A5 : ∃ g : ↥(C'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb))) →* alternatingGroup (Fin 5),
      Function.Surjective g := by
    obtain ⟨g, hg⟩ := hC'A5
    refine exists_surjective_alt5_of_ker g hg
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)).subgroupMap C')
      (MonoidHom.subgroupMap_surjective _ _) ?_
    intro y
    have hy : (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)) ((y : ↥C') : ↥Pb) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp y.2)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Pb) ⟨_, hy⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hn5 : ∀ {n : ℕ}, Nonempty (↥Pb ⧸ CFSG.pCore 2 ↥Pb ≃* Equiv.Perm (Fin n)) → 5 ≤ n := by
    rintro n ⟨eP⟩
    exact (eq_alternatingGroup_of_perfect (D := (C'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb))).map
      eP.toMonoidHom)
      (fun h0 => hC''ne ((Subgroup.map_eq_bot_iff_of_injective _ (f := eP.toMonoidHom)
        eP.injective).mp h0))
      (by rw [← Subgroup.map_commutator, hC''p]) (hC''s.map (f := eP.toMonoidHom) eP.surjective)).1
  rcases h93 G X S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7' | h8
  · exact absurd h1 hX
  · exact Or.inl h2
  ·
    exfalso
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hPLT G X S L hK hA hL hX hSy2 h3
    have hperm : ∀ {n : ℕ}, n ≠ 5 → Nonempty (↥(blockPL X S L) ≃* Equiv.Perm (Fin n)) → False := by
      intro n hn5 ⟨e⟩
      obtain ⟨g, hg⟩ := hC'A5
      have hD := eq_alternatingGroup_of_perfect (D := C'.map e.toMonoidHom)
        (fun h0 => hC'ne ((Subgroup.map_eq_bot_iff_of_injective C' (f := e.toMonoidHom)
          e.injective).mp h0))
        (by rw [← Subgroup.map_commutator, hC'p]) (hCsn.map (f := e.toMonoidHom) e.surjective)
      have eD : ↥(alternatingGroup (Fin n)) ≃* ↥C' :=
        (MulEquiv.subgroupCongr hD.2).symm.trans
          (C'.equivMapOfInjective e.toMonoidHom e.injective).symm
      exact false_of_alt_surj (by omega) (g.comp eD.toMonoidHom) (fun a => by
        obtain ⟨c, rfl⟩ := hg a
        obtain ⟨b, rfl⟩ := eD.surjective c
        exact ⟨b, rfl⟩)
    have hsp : ∀ (k : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
        Nonempty (↥(blockPL X S L) ⧸ CFSG.pCore 2 ↥(blockPL X S L) ≃*
          (TauCeti.CFSGIndex.lie d).Group) → False := by
      intro k d hd ⟨eP⟩
      have hk3 : 3 ≤ k := by
        obtain ⟨q, hq2, hdB⟩ := hd
        have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).1
        rw [hdB] at hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hv
        omega
      obtain ⟨hsimp, h29⟩ := hSp k d hk3 hd
      set C'' := C'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)) with hC''
      obtain ⟨g, hg⟩ := hC''A5
      have hDs : (C''.map eP.toMonoidHom).IsSubnormal :=
        hC''s.map (f := eP.toMonoidHom) eP.surjective
      rcases hDs.eq_bot_or_top_of_isSimpleGroup hsimp with h0 | h0
      · exact hC''ne ((Subgroup.map_eq_bot_iff_of_injective C'' (f := eP.toMonoidHom)
          eP.injective).mp h0)
      · have eT : (TauCeti.CFSGIndex.lie d).Group ≃* ↥C'' :=
          (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h0).symm).trans
            (C''.equivMapOfInjective eP.toMonoidHom eP.injective).symm
        have h60 := card_eq_sixty_of_isSimpleGroup (g.comp eT.toMonoidHom) (fun a => by
          obtain ⟨c, rfl⟩ := hg a
          obtain ⟨b, rfl⟩ := eT.surjective c
          exact ⟨b, rfl⟩)
        rw [h60] at h29
        norm_num at h29
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd' with hd' | hd' | ⟨rfl, hd'⟩
      · obtain ⟨d'', hd'', heP⟩ := hOrth m d ⟨q, hq, Or.inl hd'⟩ ⟨e⟩
        exact hsp (m - 1) d'' hd'' heP
      · obtain ⟨d'', hd'', heP⟩ := hOrth m d ⟨q, hq, Or.inr hd'⟩ ⟨e⟩
        exact hsp (m - 1) d'' hd'' heP
      · exact hperm (by norm_num) (hU4 d ⟨q, hq, hd'⟩ ⟨e⟩)
    · rcases hn with rfl | rfl | rfl
      · exact hperm (by norm_num) (hA5 ⟨e⟩)
      · exact hperm (by norm_num) (hA6 ⟨e⟩)
      · exact hperm (by norm_num) (hA8 ⟨e⟩)
  ·
    exfalso
    obtain ⟨-, -, -, -, ⟨eS4⟩⟩ := h4
    have hs := CZeroThreePerfect.isSolvable_of_map_center_perm_four eS4
    have hPL' : Pb ≤ barM X L := Subgroup.map_mono fun y hy => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hy.2
    set eP := (Subgroup.subgroupOfEquivOfLe hPL').symm
    haveI : Group.IsSolvable ↥Pb :=
      solvable_of_solvable_injective (f := eP.toMonoidHom) eP.injective
    exact hC'ne (CZeroThreePerfect.eq_bot_of_perfect_of_isSolvable hC'p)
  ·
    exfalso
    have h72 := h7 G X S L hK hA hL hX hSy2 h5
    obtain ⟨g, hg⟩ := hC'A5
    have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card C' :=
      Subgroup.card_dvd_of_surjective (f := g) hg
    rw [nat_card_alternatingGroup, Nat.card_fin] at h60
    have hC'72 : Nat.card C' ∣ 72 := (Subgroup.card_subgroup_dvd_card C').trans h72
    have := h60.trans hC'72
    norm_num at this
  ·
    obtain ⟨-, n, ⟨e⟩, heP⟩ := h6
    exact Or.inr (Or.inl ⟨n, hn5 heP, ⟨e⟩⟩)
  ·
    obtain ⟨-, n, ⟨e⟩, heP⟩ := h7'
    have := hn5 heP
    exact Or.inr (Or.inr ⟨4 * n, by omega, ⟨e⟩⟩)
  ·
    obtain ⟨-, N, r, ⟨a, ha⟩, hrN, h0, h2, h4', ⟨e⟩, -⟩ := h8
    exact Or.inr (Or.inr ⟨N, by omega, ⟨e⟩⟩)

end AltTen

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
