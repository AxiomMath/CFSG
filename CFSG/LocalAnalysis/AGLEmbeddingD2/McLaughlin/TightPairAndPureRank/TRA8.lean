module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRKill

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

@[expose] def KFactBlockPLSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R →
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → NineThreeSix M (pCoreOf 2 H) L →
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)) →
      ∃ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf Q (barM M L) ∧
        Q ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)

@[expose] def PairNineThreeThreeA8Kill : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L →
    ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)) →
      ¬ BlockPLThreeSolv M S L

section A8

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_alt_fin {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

omit [Finite G] in
theorem eq_eight_of_alt {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 5 ≤ m)
    (e : X ≃* alternatingGroup (Fin m))
    (e8 : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 8)) : m = 8 := by
  have hc := center_eq_bot_of_alt hm e
  have h1 : Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
    Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hc).trans
      (QuotientGroup.quotientBot (G := X))).toEquiv
  have h2 := (Nat.card_congr e8.toEquiv).trans (card_alt_fin (by norm_num : 2 ≤ 8))
  have h3 := (Nat.card_congr e.toEquiv).trans (card_alt_fin (by omega : 2 ≤ m))
  have h4 : m.factorial / 2 = (8 : ℕ).factorial / 2 := by rw [← h3, ← h1, h2]
  have h5 : 2 ∣ m.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h6 : 2 ∣ (8 : ℕ).factorial := Nat.dvd_factorial (by norm_num) (by norm_num)
  have h7 : m.factorial = (8 : ℕ).factorial := by omega
  have h8 : 1 < m.factorial := Nat.one_lt_factorial.mpr (by omega)
  exact (Nat.factorial_inj' (Or.inl (by omega))).mp h7

theorem false_of_nineThreeSeven_A8 {M S L : Subgroup G} (hw : IsWeakSBlock M S L)
    (h3 : BlockHasThree M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hsolv : BlockPLThreeSolv M S L) (h7 : NineThreeSeven M S L)
    (e8 : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)) : False := by
  obtain ⟨-, n, ⟨e⟩, ⟨φ⟩⟩ := h7
  have hn4 := le_four_of_blockPLThreeSolv_perm hsolv φ
  have hperf : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr (barM_perfect hw.le hw.perfect)
  have hq : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    (hw.component.2.2).2.toNontrivial
  have : Nontrivial ↥(barM M L) :=
    (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
  have h5 : 5 ≤ 4 * n := five_le_of_perfect_alt (Group.isPerfect_def.mp hperf) e
  have h8 := eq_eight_of_alt h5 e e8
  have hn : n = 2 := by omega
  subst hn
  obtain ⟨y, hyP, hy3, hyC⟩ := exists_order_three_noncentral hw.le h3 hZ
  set Q := barM M (Subgroup.normalizer (S : Set G) ⊓ L)
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyC (Subgroup.one_mem _)
  have hord : orderOf (⟨y, hyP⟩ : ↥Q) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext hy3
    · intro h
      exact hy1 (congrArg Subtype.val h)
  have hdvd : 3 ∣ Nat.card ↥Q := hord ▸ orderOf_dvd_natCard _
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Q)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Q)).exists_card_eq
  have hc2 : Nat.card (↥Q ⧸ CFSG.pCore 2 ↥Q) = 2 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_perm]
  rw [hmul, hc2, hk] at hdvd
  have : 3 ∣ 2 ^ (k + 1) := by simpa [pow_succ, mul_comm] using hdvd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

theorem engineBlock_of_A8 {M S L : Subgroup G} (hw : IsWeakSBlock M S L)
    (hconc : NineThreeConclusion M S L) (hnot1 : ¬ NineThreeOne L)
    (h3 : BlockHasThree M S L) (hsolv : BlockPLThreeSolv M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hA8 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)))
    (h33 : NineThreeThree M S L → False)
    (h6 : NineThreeSix M S L → ∃ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      IsSylowTwoOf Q (barM M L) ∧ Q ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L)) :
    PairTwoEngineBlock M S L := by
  obtain ⟨e8⟩ := hA8
  rcases hconc with h1 | h2 | h3' | h4 | h5 | h6' | h7 | h8
  · exact absurd h1 hnot1
  · exact engineBlock_of_nineThreeTwo h2
  · exact absurd h3' h33
  · obtain ⟨-, hZ3, -⟩ := h4
    exact absurd (by rw [card_inf_centralizer_eq_card_center, hZ3]) hZ
  · exfalso
    obtain ⟨-, ⟨e⟩, -⟩ := id h5
    have := eq_eight_of_alt (by norm_num : 5 ≤ 7) e e8
    omega
  · obtain ⟨Q, hQ, hQP⟩ := h6 h6'
    exact ⟨Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), ⟨e8⟩⟩), Q, hQ, hQP⟩
  · exact (false_of_nineThreeSeven_A8 hw h3 hZ hsolv h7 e8).elim
  · exact (not_nineThreeEight h8 hsolv).elim

end A8

end CFSG.AGLEmbeddingD2.McLaughlin
