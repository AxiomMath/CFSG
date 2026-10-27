module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicInner
import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicSylow
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LieType.Simplicity.Classical
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSp

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding.ParabPrime

namespace TransvectionCyclic

theorem isSimpleGroup_of_model {Y : Type} [Group Y] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y t n p f) :
    IsSimpleGroup Y :=
  (CFSG.LieType.Simplicity.fam_classical_converse _
    ((CFSG.Milestones.fam_classical_model_membership_alltags _).2 ⟨_, _, _, _, hm⟩)).2.2

theorem isSimpleGroup_of_isOrthogonalTwo {Y : Type} [Group Y] (h : IsOrthogonalTwo Y) :
    IsSimpleGroup Y := by
  rcases h with ⟨⟨x, hv⟩, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rcases hd with rfl | rfl | ⟨rfl, rfl⟩
    · exact isSimpleGroup_of_model
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD m q hv e)
    · exact isSimpleGroup_of_model
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv e)
    · exact isSimpleGroup_of_model
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e)
  · have h5 : 5 ≤ Nat.card (Fin n) := by
      rw [Nat.card_fin]
      rcases hn with rfl | rfl | rfl <;> norm_num
    have := alternatingGroup.isSimpleGroup h5
    exact e.isSimpleGroup

end TransvectionCyclic

open TransvectionCyclic

theorem blockTransvectionCenter_holds : BlockTransvectionCenter := by
  intro G _ _ M S L hK hA hL h3
  have hsimp := isSimpleGroup_of_isOrthogonalTwo h3.2.1
  have hperf := hL.component.2.2.1
  set Lb := barM M L
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxC⟩
  rw [Subgroup.mem_bot]
  have hcen : (⟨x, hxL⟩ : ↥Lb) ∈ Subgroup.center ↥Lb := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Lb) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · exfalso
    have hcomm : ∀ a b : ↥Lb, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm
    have hbot : commutator ↥Lb = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      exact Subgroup.mem_centralizer_iff.mpr fun b _ => (hcomm a b).symm
    have htop : commutator ↥Lb = ⊤ := by
      rw [commutator_def]
      exact hperf
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Lb
    exact hab (by
      have h1 : (⊤ : Subgroup ↥Lb) = ⊥ := htop.symm.trans hbot
      have ha : a ∈ (⊥ : Subgroup ↥Lb) := h1 ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup ↥Lb) := h1 ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb])

theorem kFactSpTwoNoncycThree_holds :
    ∀ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k →
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
        ∃ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsPGroup 3 E ∧ ¬ IsCyclic E := by
  intro k d hk ⟨q, hq2, hd⟩
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp
    (hpe ▸ dvd_pow_self q.p q.exponent_pos.ne')
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B k q := hd
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hqp hk
    (MulEquiv.refl _)
  rw [hqp] at hm
  obtain ⟨E, hE, hEc⟩ := CFSG.AGLEmbedding.BlockCyc.hasE9_of_model_psp hm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨E, IsPGroup.of_card hEc, fun hcyc => ?_⟩
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
  have hog : orderOf g = 9 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hEc]
    norm_num
  have h3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.2 g g.2)
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hog] at this
  norm_num at this

namespace TransvectionCyclic

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem not_perfectCyclicSylow_three_of_sp
    {J : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {k : ℕ} {d : TauCeti.ValidLieTypeIndex} (hk : 3 ≤ k)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q)
    (φ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ¬ PerfectCyclicSylow 3 J := by
  have hSp3 := kFactSpTwoNoncycThree_holds
  intro hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
  obtain ⟨E, hE3, hEnc⟩ := hSp3 k d hk hd
  set O : Subgroup ↥J := CFSG.pCore 2 ↥J
  have : O.Normal := CFSG.pCore_normal
  set ψ : ↥J →* (TauCeti.CFSGIndex.lie d).Group := φ.toMonoidHom.comp (QuotientGroup.mk' O)
  have hψ : Function.Surjective ψ := φ.surjective.comp (QuotientGroup.mk'_surjective O)
  set B := E.comap ψ
  have hBE : ∀ b : ↥B, ψ b ∈ E := fun b => b.2
  set f : ↥B →* ↥E := (ψ.domRestrict B).codRestrict E hBE
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hψ x
    exact ⟨⟨y, hx⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥B) := inferInstance
  set Q := P.mapSurjective hf
  have hQ' : (Q : Subgroup ↥E) = ⊤ :=
    (Q.is_maximal' (hE3.of_equiv Subgroup.topEquiv.symm) le_top).symm
  set A := ((P : Subgroup ↥B).map B.subtype).map J.subtype
  have hAJ : A ≤ J := by
    rintro _ ⟨_, -, rfl⟩
    exact Subtype.property _
  have hA3 : IsPGroup 3 A := (P.isPGroup'.map _).map _
  have hAc := hperf _ (perfectJoin_le _) (perfectJoin_perfect _) A
    (le_perfectJoin_of_quotient_perfect Nat.prime_three (by norm_num) φ hQ hAJ hA3) hA3
  apply hEnc
  have e1 : ↥(P : Subgroup ↥B) ≃* ↥A :=
    ((P : Subgroup ↥B).equivMapOfInjective _ B.subtype_injective).trans
      (((P : Subgroup ↥B).map B.subtype).equivMapOfInjective _ J.subtype_injective)
  have hPc : IsCyclic ↥(P : Subgroup ↥B) :=
    isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have hQc : IsCyclic ↥(Q : Subgroup ↥E) := by
    rw [Sylow.coe_mapSurjective]
    exact isCyclic_of_surjective (f.subgroupMap (P : Subgroup ↥B))
      (f.subgroupMap_surjective (P : Subgroup ↥B))
  rw [hQ'] at hQc
  exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective

end TransvectionCyclic

theorem blockTransvectionOddInner_of (hTPLT : CitedBlockTransvectionPLType)
    : BlockTransvectionOddInner := by
  intro G _ _ M S L p hK hA hL hX hS h3 hp hp2 hperf x hxN ⟨k, hxk⟩
  refine mem_sup_centralizer_of_not_dvd_card_outer hp ?_ hxN hxk
  rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    by_cases hp5 : 5 ≤ p
    · exact kFactOutOrthTwoPrime_holds d ⟨m, q, hq, hd⟩ p hp hp5
    · have hp3 : p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact absurd rfl hp2
        · rfl
        · exact absurd hp (by norm_num)
      subst hp3
      have hq2 : q.p = 2 ∧ q.exponent = 1 := by
        rw [TauCeti.PrimePower.card_def] at hq
        exact Nat.prime_two.pow_eq_iff.mp hq
      obtain ⟨x', hv⟩ := d
      rcases hd with hd | hd | ⟨rfl, hd⟩
      · exfalso
        obtain ⟨d', hd', ⟨φ⟩⟩ := (hTPLT G M S L hK hA hL hX hS h3).1 m ⟨x', hv⟩
          ⟨q, hq, Or.inl hd⟩ ⟨e⟩
        have hm : 4 ≤ m := by
          have h := hv
          change x' = _ at hd
          rw [hd] at h
          exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
            ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
        exact not_perfectCyclicSylow_three_of_sp (by omega) hd' φ hperf
      · change x' = _ at hd
        subst hd
        have hmod := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD m q hv
          (MulEquiv.refl _)
        rw [hq2.1, hq2.2] at hmod
        have h2 := card_outer_le_two_of_omegaMinus_two hmod
        intro hdvd
        have := Nat.le_of_dvd h2.1 hdvd
        omega
      · change x' = _ at hd
        subst hd
        have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv
          (MulEquiv.refl _)
        rw [hq2.1, hq2.2] at hmod
        exact not_dvd_card_outer_of_psu_four_two hmod Nat.prime_three (by norm_num)
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact not_dvd_card_outer_alternatingGroup n (by rcases hn with rfl | rfl | rfl <;> norm_num)
      p hp hp2

theorem citedBlockTransvectionCyclic_of_sp (h86 : Asc81bEightSix)
    (hTPLT : CitedBlockTransvectionPLType) :
    CitedBlockTransvectionCyclic :=
  citedBlockTransvectionCyclic_of hTPLT (citedBlockTransvectionInner_of h86
    (blockTransvectionOddInner_of hTPLT) blockTransvectionCenter_holds)

theorem citedBlockTransvectionCyclic_of_PLType (h86 : Asc81bEightSix)
    (hTPLT : CitedBlockTransvectionPLType) : CitedBlockTransvectionCyclic :=
  citedBlockTransvectionCyclic_of_sp h86 hTPLT

end CFSG.AGLEmbedding
