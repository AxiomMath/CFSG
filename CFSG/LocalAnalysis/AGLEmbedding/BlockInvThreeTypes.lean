module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeBasic
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieZZComp
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeRadical
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeMain

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def KFactParabolicThreeInv : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsClassicalTwoOrG2 Y → ∀ T J : Subgroup Y,
    IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set Y) ≤ J →
      J ≠ Subgroup.normalizer (T : Set Y) → InvThree J

@[expose] def CitedBlockAltSevenInv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeFive M L → InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L))

namespace BlockInvThree

theorem isPGroup_perm_of_lt_three {n : ℕ} (hn : n < 3) : IsPGroup 2 (Equiv.Perm (Fin n)) := by
  refine IsPGroup.of_card (n := n / 2) ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  interval_cases n <;> rfl

theorem invThree_sp (hP2 : KFactParabolicThreeInv) (k : ℕ) (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group]
    (hk : 3 ≤ k) (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) :
    InvThree (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) := by
  set Y := (TauCeti.CFSGIndex.lie d).Group
  obtain ⟨hsimp, h29⟩ := kFactSpTwoSimple_holds k d hk hd
  have hperf := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
  obtain ⟨q, hq2, hdq⟩ := hd
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
    (hpe ▸ dvd_pow_self q.p q.exponent_pos.ne')
  have hcl : IsClassicalTwoOrG2 Y := by
    refine Or.inl ⟨d, ?_, ⟨MulEquiv.refl _⟩⟩
    rw [hdq]
    exact hqp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hT : IsSylowTwoOf (T : Subgroup Y) ⊤ := by
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [show ((T : Subgroup Y).subgroupOf ⊤).index = (T : Subgroup Y).index from
      Subgroup.relIndex_top_right _]
    exact T.not_dvd_index
  refine hP2 Y hcl T ⊤ hT le_top ?_
  intro htop
  have hN : (T : Subgroup Y).Normal := Subgroup.normalizer_eq_top_iff.mp htop.symm
  have := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup Y) with hb | ht
  · apply T.not_dvd_index
    rw [hb, Subgroup.index_bot]
    exact dvd_trans (dvd_pow_self 2 (by norm_num)) h29
  · have hY2 : IsPGroup 2 Y := by
      have h2 := T.isPGroup'
      rw [ht] at h2
      exact h2.of_equiv Subgroup.topEquiv
    have : Group.IsPerfect Y := Group.isPerfect_def.mpr hperf
    have : Nontrivial Y := hsimp.toNontrivial
    have : Group.IsNilpotent Y := hY2.isNilpotent
    exact Group.IsPerfect.not_isSolvable Y inferInstance

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem invThree_of_nineThreeTwo (hP2 : KFactParabolicThreeInv) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  obtain ⟨hcl, T, J, hT, hNJ, hne, -, rfl⟩ := BlockCyc.nineThreeTwo_parabolic hA hL hS h2
  have hJ := hP2 _ hcl T _ hT hNJ hne
  have hP := (InvThree.of_map_center hJ).map_injective (barM M L).subtype
    (barM M L).subtype_injective
  rwa [Subgroup.map_subgroupOf_eq_of_le (barM_mono inf_le_right)] at hP

theorem invThree_of_nineThreeThree (hTPLT : CitedBlockTransvectionPLType)
    (hP2 : KFactParabolicThreeInv) (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hX : ¬ InClassXBlock L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L)
    (h3 : NineThreeThree M S L) :
    InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hTPLT G M S L hK hA hL hX hS h3
  have hval : ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
      (d.1 = .D m q ∨ d.1 = .twistedD m q) → 4 ≤ m := by
    intro m d q hd
    have h := d.2
    rcases hd with hd | hd <;> rw [hd] at h <;>
      exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with hd | hd | ⟨rfl, hd⟩
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inl hd⟩ ⟨e⟩
      have hm := hval m d q (Or.inl hd)
      have : Finite (TauCeti.CFSGIndex.lie d').Group := Finite.of_equiv _ φ.toEquiv
      exact InvThree.of_quotient_pCore_mulEquiv φ
        (invThree_sp hP2 (m - 1) d' (by omega) ⟨q', hq', hd'⟩)
    · obtain ⟨d', ⟨q', hq', hd'⟩, ⟨φ⟩⟩ := hOrth m d ⟨q, hq, Or.inr hd⟩ ⟨e⟩
      have hm := hval m d q (Or.inr hd)
      have : Finite (TauCeti.CFSGIndex.lie d').Group := Finite.of_equiv _ φ.toEquiv
      exact InvThree.of_quotient_pCore_mulEquiv φ
        (invThree_sp hP2 (m - 1) d' (by omega) ⟨q', hq', hd'⟩)
    · obtain ⟨e6⟩ := hU4 d ⟨q, hq, hd⟩ ⟨e⟩
      exact InvThree.of_mulEquiv e6 (invThree_perm (by norm_num))
  · rcases hn with rfl | rfl | rfl
    · obtain ⟨e3⟩ := hA5 ⟨e⟩
      exact InvThree.of_mulEquiv e3 (invThree_perm le_rfl)
    · obtain ⟨e4⟩ := hA6 ⟨e⟩
      exact InvThree.of_mulEquiv e4 (invThree_perm (by norm_num))
    · obtain ⟨e6⟩ := hA8 ⟨e⟩
      exact InvThree.of_mulEquiv e6 (invThree_perm (by norm_num))

omit [Finite G] in
theorem invThree_of_nineThreeFour (h4 : NineThreeFour M S L) :
    InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  obtain ⟨-, -, -, -, ⟨e⟩⟩ := h4
  have hP := (InvThree.of_map_center (InvThree.of_mulEquiv e (invThree_perm (by norm_num))))
    |>.map_injective (barM M L).subtype (barM M L).subtype_injective
  rwa [Subgroup.map_subgroupOf_eq_of_le (barM_mono inf_le_right)] at hP

theorem invThree_of_quotient_perm
    (hP : ¬ IsPGroup 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    {n : ℕ} (e : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin n)) :
    InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exact (hP (isPGroup_of_mulEquiv_quotient_pCore e (isPGroup_perm_of_lt_three hn))).elim
  · exact InvThree.of_quotient_pCore_mulEquiv e (invThree_perm hn)

theorem invThree_of_nineThreeEight (h8 : NineThreeEight M S L) :
    InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L)) := by
  obtain ⟨-, N, r, ⟨t, ht⟩, h2r, h0, h2, h4, -, φ, -, -⟩ := h8
  exact InvThree.of_quotient_pCore_mulEquiv φ (invThree_prod_perm (by omega))

end BlockInvThree

open BlockInvThree

theorem kFactBlockInvertedThree_of (h93 : Asc81bNineThree) (h86 : Asc81bEightSix)
    (hTPLT : CitedBlockTransvectionPLType) (hP2 : KFactParabolicThreeInv)
    (hA7 : CitedBlockAltSevenInv) : KFactBlockInvertedThree := by
  intro G _ _ M S L hK hA hL hX hS
  apply exists_inverted_of_invThree
  have hP := not_isPGroup_blockPL h86 hK hA hL hS
  rcases h93 G M S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact invThree_of_nineThreeTwo hP2 hA hL hS h2
  · exact invThree_of_nineThreeThree hTPLT hP2 hK hA hL hX hS h3
  · exact invThree_of_nineThreeFour h4
  · exact hA7 G M S L hK hA hL hX hS h5
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact invThree_of_quotient_perm hP e
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact invThree_of_quotient_perm hP e
  · exact invThree_of_nineThreeEight h8

end CFSG.AGLEmbedding
