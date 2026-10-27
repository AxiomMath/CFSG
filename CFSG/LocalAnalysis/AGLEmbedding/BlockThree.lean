module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeAux
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

section Types

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

theorem blockHasThree_of_nineThreeTwo (hK2 : KFactParabolicThree) (hLM : L ≤ M)
    (h2 : NineThreeTwo M S L) (hns : ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) :
    BlockHasThree M S L := by
  obtain ⟨hcl, ⟨hJL, T, hT, hNT⟩, hO⟩ := h2
  set Lb := barM M L
  set Jb := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  set q := QuotientGroup.mk' (Subgroup.center ↥Lb)
  have hT₁ := isSylowTwoOf_subgroupOf_top_of_isSylowTwoOf hT
  have hN : ∀ z : ↥Lb,
      q z ∈ Subgroup.normalizer (((T.subgroupOf Lb).map q : Subgroup _) : Set _) →
        (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ Subgroup.normalizer (T : Set _) := fun z hz =>
    coe_mem_normalizer_of_subgroupOf hT.1 (mem_normalizer_of_mk_center_mem_normalizer hT₁ hz)
  refine blockHasThree_of_three_dvd_card_map_center hLM (hK2 _ hcl ((T.subgroupOf Lb).map q)
    ((Jb.subgroupOf Lb).map q)
    (isSylowTwoOf_map_top_of_surjective hT₁ (QuotientGroup.mk'_surjective _)) ?_ ?_)
  · intro y hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr (hNT ⟨z.2, hN z hy⟩))
  · intro heq
    have hJN : Jb ≤ Subgroup.normalizer (T : Set _) := fun j hj => by
      refine hN ⟨j, hJL hj⟩ ?_
      rw [← heq]
      exact Subgroup.mem_map_of_mem q (Subgroup.mem_subgroupOf.mpr hj)
    have hTJ : T ≤ Jb := fun t ht => hNT ⟨hT.1 ht, Subgroup.le_normalizer ht⟩
    have hTO : T ≤ barM M (S ⊓ L) := by
      rw [hO]
      exact normal_pGroup_le_pCoreOf 2 T Jb hTJ
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr hJN) hT.2.1
    refine hns ⟨Subgroup.map_mono fun _ hx => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hx).2, by rw [hO]; exact pCoreOf_isPGroup 2 Jb,
      fun hd => hT.2.2 ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_of_le_left Lb hTO)

theorem blockHasThree_of_nineThreeFour (hLM : L ≤ M) (h4 : NineThreeFour M S L) :
    BlockHasThree M S L := by
  obtain ⟨-, -, -, -, ⟨e⟩⟩ := h4
  refine blockHasThree_of_three_dvd_card_map_center hLM ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem blockHasThree_of_nineThreeEight (hLM : L ≤ M) (h8 : NineThreeEight M S L) :
    BlockHasThree M S L := by
  obtain ⟨-, N, r, hN, -, h0, h2, h4, -, φ, -, -⟩ := h8
  have hm : 3 ≤ N - 2 * r := by
    obtain ⟨k, rfl⟩ := hN
    omega
  exact blockHasThree_of_surjective_perm hLM hm
    ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _)))
    (Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _)))

end Types

section PhaseThree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}

open CFSG.AGLEmbeddingD2 (NoXBlockFor)

theorem TwoLocalPhaseThree.not_isPGroup_normalizer_inf
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ IsPGroup 2 (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L : Subgroup G) := by
  intro h2
  set S := pCoreOf 2 H
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 H
  obtain ⟨hSL, -⟩ := h.weakSBlock_asc81bHyp hK h86 hL
  have hrad := h.twoCore_eq_pCoreOf_normalizer_sup hL.toIsTwoPrimeComponent hSL
  have hT2 : IsPGroup 2 ((L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
    refine (h2.to_sup_of_normal_right' hS2 inf_le_left).to_le ?_
    rintro t ⟨htLS, htN⟩
    have htLS' : t ∈ ((L ⊔ S : Subgroup G) : Set G) := htLS
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L S hSL] at htLS'
    obtain ⟨l, hl, s, hs, rfl⟩ := htLS'
    have hlN : l ∈ Subgroup.normalizer (S : Set G) := by
      have := (Subgroup.normalizer (S : Set G)).mul_mem htN
        (Subgroup.le_normalizer (S.inv_mem hs))
      simpa using this
    exact Subgroup.mul_mem_sup ⟨hlN, hl⟩ hs
  have hNS : (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G) ≤ S :=
    le_of_two_radical le_sup_right hrad inf_le_left hT2 Subgroup.le_normalizer
  have hsyl : IsSylowTwoOf S (L ⊔ S) :=
    ⟨le_sup_right, hS2, not_dvd_index_of_normalizer_inf_le_self le_sup_right hS2 hNS⟩
  exact h.not_isSylowTwoOf_inf hK h85 hD2 hL
    (B6.isSylowTwoOf_inf_normal hsyl le_sup_left (sup_le Subgroup.le_normalizer hSL))

theorem TwoLocalPhaseThree.not_isPGroup_barM_normalizer_inf
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    ¬ IsPGroup 2 (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) := fun h2 =>
  h.not_isPGroup_normalizer_inf hK h85 h86 hD2 hL
    (isPGroup_of_isPGroup_barM (inf_le_right.trans hL.le) h2)

theorem TwoLocalPhaseThree.blockHasThree_of_quotient_perm
    (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G) (hL : IsWeakSBlock M (pCoreOf 2 H) L) {n : ℕ}
    (e : ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ⧸
      CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)) ≃*
        Equiv.Perm (Fin n)) :
    BlockHasThree M (pCoreOf 2 H) L := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · refine (h.not_isPGroup_barM_normalizer_inf hK h85 h86 hD2 hL
      (isPGroup_of_mulEquiv_quotient_pCore e (IsPGroup.of_card (n := n / 2) ?_))).elim
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    interval_cases n <;> rfl
  · exact blockHasThree_of_surjective_perm hL.le hn (e.toMonoidHom.comp (QuotientGroup.mk' _))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))

theorem TwoLocalPhaseThree.blockHasThree (h : TwoLocalPhaseThree M H) (hK : Open.IsKGroup ↥M)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    BlockHasThree M (pCoreOf 2 H) L := by
  obtain ⟨hnot1, hnot2⟩ := h.nineThree_not_one hK h85 hD2 hL
  have hsyl := h.not_isSylowTwoOf_inf hK h85 hD2 hL
  rcases h.nineThree hK h93 hL with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot1
  · exact blockHasThree_of_nineThreeTwo hK2 hL.le h2 (hnot2 h2)
  · exact hC3 G M _ L hK h.asc81bHyp hL hnot1 hsyl h3
  · exact blockHasThree_of_nineThreeFour hL.le h4
  · exact hK5 G M _ L hK h.asc81bHyp hL hnot1 hsyl h5
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact h.blockHasThree_of_quotient_perm hK h85 h86 hD2 hL e
  · obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact h.blockHasThree_of_quotient_perm hK h85 h86 hD2 hL e
  · exact blockHasThree_of_nineThreeEight hL.le h8

end PhaseThree

theorem stmtBlockThree_of (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven) : StmtBlockThree := by
  intro G _ _ p P M H R L h hL
  exact h.toTwoLocalPhaseThree.blockHasThree h.isKGroup.1 h85 h86 h93 (hD2 G h.glob) hK2 hC3 hK5 hL

end CFSG.AGLEmbedding
