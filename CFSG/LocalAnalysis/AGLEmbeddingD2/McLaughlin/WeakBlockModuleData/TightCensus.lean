module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LargeField
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModule
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltTypes

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def Agl418 : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, ∀ [Finite (TauCeti.CFSGIndex.lie d).Group],
    IsClassicalOrG2Index d.1 →
    Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 →
      (∃ q, d.1 = .G2 q) ∨ (∃ q, d.1 = .B 2 q) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ q.card % 3 = 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 3 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 3 q ∧ q.card % 3 = 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 4 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 4 q ∧ q.card % 3 = 1)

@[expose] def IsL5Two (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .A 4 q) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

theorem eq_A_four_of_agl418_list (d : TauCeti.ValidLieTypeIndex) (hq : LieField d.1 = 2)
    (h : (∃ q, d.1 = .G2 q) ∨ (∃ q, d.1 = .B 2 q) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 2 q ∧ q.card % 3 = 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 3 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 3 q ∧ q.card % 3 = 1) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .A 4 q ∧ q.card % 3 = 2) ∨
      (∃ q : TauCeti.PrimePower, d.1 = .twistedA 4 q ∧ q.card % 3 = 1)) :
    ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .A 4 q := by
  have hv := d.2
  rcases h with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨q, hd, h3⟩ | ⟨q, hd, h3⟩ | ⟨q, hd, h3⟩ | ⟨q, hd, h3⟩ |
    ⟨q, hd, h3⟩ | ⟨q, hd, h3⟩
  · rw [hd] at hq hv; simp only [LieField] at hq
    have hq' : q.p ^ q.exponent = 2 := by rwa [TauCeti.PrimePower.card_def] at hq
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hq'] at hv
  · rw [hd] at hq hv; simp only [LieField] at hq
    have hq' : q.p ^ q.exponent = 2 := by rwa [TauCeti.PrimePower.card_def] at hq
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hq'] at hv
  · rw [hd] at hq; simp only [LieField] at hq; rw [hq] at h3; omega
  · rw [hd] at hq hv; simp only [LieField] at hq
    have hq' : q.p ^ q.exponent = 2 := by rwa [TauCeti.PrimePower.card_def] at hq
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff, hq'] at hv
  · rw [hd] at hq hv; simp only [LieField] at hq
    have hq' : q.p ^ q.exponent = 2 := by rwa [TauCeti.PrimePower.card_def] at hq
    simp [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, hq'] at hv
  · rw [hd] at hq; simp only [LieField] at hq; rw [hq] at h3; omega
  · rw [hd] at hq; simp only [LieField] at hq; exact ⟨q, hq, hd⟩
  · rw [hd] at hq; simp only [LieField] at hq; rw [hq] at h3; omega

@[expose] def L2SevenRankOne : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, ∀ [Finite (TauCeti.CFSGIndex.lie d).Group],
    (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) →
      Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≠ 2

theorem lieField_eq_two_of_lt_four (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (hq : LieField d.1 < 4) : LieField d.1 = 2 := by
  have key : ∀ q : TauCeti.PrimePower, q.p = 2 → q.card < 4 → q.card = 2 := by
    intro q hp hc
    rw [TauCeti.PrimePower.card_def, hp] at hc ⊢
    have he := q.exponent_pos
    have he2 : q.exponent < 2 := by
      by_contra hge
      have hge' := Nat.not_lt.mp hge
      have : 2 ^ 2 ≤ 2 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hge'
      omega
    have he1 : q.exponent = 1 := by omega
    rw [he1]; norm_num
  generalize d.1 = i at hd hq
  cases i <;> simp only [IsClassicalOrG2Index, LieField] at hd hq ⊢ <;>
    first | exact absurd hd (by simp) | exact key _ hd hq

omit [Finite G] in
theorem center_eq_bot_of_alt {X : Type*} [Group X] {N : ℕ} (hN : 5 ≤ N)
    (e : X ≃* alternatingGroup (Fin N)) : Subgroup.center X = ⊥ := by
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hperf : Group.IsPerfect (alternatingGroup (Fin N)) :=
    ⟨commutator_alternatingGroup_eq_top (by simpa using hN)⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin N)) :=
    alternatingGroup.isSimpleGroup (by simpa using hN)
  have hnt : Nontrivial (alternatingGroup (Fin N)) := hsimple.toNontrivial
  have hcen : Subgroup.center (alternatingGroup (Fin N)) = ⊥ := by
    rcases (Subgroup.center (alternatingGroup (Fin N))).normal_of_characteristic.eq_bot_or_eq_top
      with h | h
    · exact h
    · exfalso
      have hc : IsMulCommutative (alternatingGroup (Fin N)) := Subgroup.center_eq_top_iff.mp h
      exact Group.IsPerfect.not_isMulCommutative (G := alternatingGroup (Fin N)) hc
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin N)) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    have := hz (e.symm g)
    simpa using congrArg e this
  rw [hcen, Subgroup.mem_bot] at h1
  exact e.injective (by rw [h1, map_one])

theorem PrimePower.p_eq_two_of_card_eq_two {q : TauCeti.PrimePower} (h : q.card = 2) : q.p = 2 := by
  have hdvd : q.p ∣ 2 := by
    rw [← h, TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ (Nat.pos_iff_ne_zero.mp q.exponent_pos)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have := q.prime_p.two_le
  omega

omit [Finite G] in
theorem pRank_top_quot_center_eq [Finite G] {M L : Subgroup G} (hLM : L ≤ M)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    Open.pRank 3 (⊤ : Subgroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) =
      Open.pRank 3 L := by
  have hcop : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' (Subgroup.center ↥(barM M L))).ker) := by
    rw [QuotientGroup.ker_mk', ← card_inf_centralizer_eq_card_center] at *
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ
  have h1 := CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
    (QuotientGroup.mk' (Subgroup.center ↥(barM M L))) (QuotientGroup.mk'_surjective _) hcop
  rw [← pRank_barM_eq Nat.prime_three (by norm_num) M L hLM,
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barM M L), h1]

theorem tightKP_quot_of_alt {X : Type} [Group X] {N : ℕ} (hN : N = 6 ∨ N = 7 ∨ N = 8)
    (e : X ≃* alternatingGroup (Fin N)) : CFSG.AGLEmbeddingD2.McLaughlin.TightKP
      (X ⧸ Subgroup.center X) := by
  have hbot := center_eq_bot_of_alt (by omega) e
  refine Or.inl ⟨N, hN, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans
    ((QuotientGroup.quotientBot (G := X)).trans e)

omit [Finite G] in
theorem quotCenterEquivAlt {X : Type} [Group X] {N : ℕ} (hN : 5 ≤ N)
    (e : X ≃* alternatingGroup (Fin N)) : Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin N)) := by
  have hbot := center_eq_bot_of_alt hN e
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans
    ((QuotientGroup.quotientBot (G := X)).trans e)⟩

@[expose] def IsUThreeThree (X : Type) [Group X] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def TightRow (M L : Subgroup G) : Prop :=
  Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) ∨
  (NineThreeFive M L ∧
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 7))) ∨
  Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 8)) ∨
  IsUThreeThree (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))

omit [Finite G] in
theorem TightRow.tightKP {M L : Subgroup G} (h : TightRow M L) :
    CFSG.AGLEmbeddingD2.McLaughlin.TightKP (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  rcases h with h | ⟨-, h⟩ | h | ⟨d, hd, he⟩
  · exact Or.inl ⟨6, by omega, h⟩
  · exact Or.inl ⟨7, by omega, h⟩
  · exact Or.inl ⟨8, by omega, h⟩
  · exact Or.inr ⟨d, hd, he⟩

omit [Finite G] in
theorem TightRow.of_alt {M L : Subgroup G} {N : ℕ} (hN : N = 6 ∨ N = 8)
    (e : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin N)) :
    TightRow M L := by
  rcases hN with rfl | rfl
  · exact Or.inl ⟨e⟩
  · exact Or.inr (Or.inr (Or.inl ⟨e⟩))

theorem tightRow_or_L5Two_of_block (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hconc : NineThreeConclusion M S L) (hnot1 : ¬ NineThreeOne L)
    (hSyl : NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L) (hr : Open.pRank 3 L = 2)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    TightRow M L ∨ IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
  have hrq := pRank_top_quot_center_eq hL.le hZ
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hL.le, hr]
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot1
  ·
    rcases h2.1 with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · have hlt := lieField_lt_four_of_nineThreeTwo hLF hL h2 (hSyl h2) hsolv d hd e
      have hq2 := lieField_eq_two_of_lt_four d hd hlt
      have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      have hrk : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
          (hrq.trans hr)
      obtain ⟨q, hq, hd'⟩ := eq_A_four_of_agl418_list d hq2 (h418 d hd hrk)
      exact Or.inr ⟨d, ⟨q, hq, hd'⟩, ⟨e⟩⟩
    · have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        (hrq.trans hr)
      have hle := pRank_three_alternating_le (N := n)
      rcases hn with h | h | h
      · subst h; omega
      · exact Or.inl (TightRow.of_alt (Or.inl h) e)
      · exact Or.inl (TightRow.of_alt (Or.inr h) e)
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      have hrk : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
          (hrq.trans hr)
      rcases hd with ⟨hq7, hd⟩ | ⟨hq3, hd⟩
      · exact absurd hrk (hL27 d ⟨hq7, hd⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨d, ⟨hq3, hd⟩, ⟨e⟩⟩)))
  ·
    obtain ⟨-, hortho, -⟩ := h3
    rcases hortho with ⟨d, ⟨m, q, hq2, hD⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      have hp2 := PrimePower.p_eq_two_of_card_eq_two hq2
      have hd : IsClassicalOrG2Index d.1 := by
        rcases hD with h | h | ⟨-, h⟩ <;> rw [h] <;> simp [IsClassicalOrG2Index, hp2]
      have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      have hrk : Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 2 :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
      have hlist := h418 d hd hrk
      have hmod : q.card % 3 = 2 := by rw [hq2]
      rcases hD with h | h | ⟨hm, h⟩ <;>
        rcases hlist with ⟨q', hq'⟩ | ⟨q', hq'⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ |
          ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ | ⟨q', hq', h3⟩ <;>
        simp_all
    · have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
        hrb
      have hle := pRank_three_alternating_le (N := n)
      rcases hn with h | h | h
      · subst h; omega
      · obtain ⟨e'⟩ := quotCenterEquivAlt (by omega) e
        exact Or.inl (TightRow.of_alt (Or.inl h) e')
      · obtain ⟨e'⟩ := quotCenterEquivAlt (by omega) e
        exact Or.inl (TightRow.of_alt (Or.inr h) e')
  ·
    obtain ⟨-, hZ3, -⟩ := h4
    exact absurd (by rw [card_inf_centralizer_eq_card_center, hZ3]) hZ
  ·
    obtain ⟨-, ⟨e⟩, -⟩ := id h5
    obtain ⟨e'⟩ := quotCenterEquivAlt (by omega) e
    exact Or.inl (Or.inr (Or.inl ⟨h5, ⟨e'⟩⟩))
  ·
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSix.le_four h6 hsolv
    have h5 := five_le_of_quasisimple_cover_alt hL.le hL.perfect hL.component.2.2 e
    exact Or.inl (TightRow.of_alt (N := 2 * n) (by omega) e)
  ·
    obtain ⟨n, hn4, ⟨e⟩⟩ := NineThreeSeven.le_four h7 hsolv
    have hperf : Group.IsPerfect ↥(barM M L) :=
      Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
    have hq : Nontrivial (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      (hL.component.2.2).2.toNontrivial
    have : Nontrivial ↥(barM M L) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥(barM M L))).nontrivial
    have h5 : 5 ≤ 4 * n := five_le_of_perfect_alt (Group.isPerfect_def.mp hperf) e
    have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans
      hrb
    have hn' : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn' with h | h | h
    · subst h
      obtain ⟨e'⟩ := quotCenterEquivAlt (by omega) e
      exact Or.inl (TightRow.of_alt (N := 4 * 2) (by omega) e')
    · exfalso
      subst h
      have := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup
        (N := 4 * 3) (by omega)
      omega
    · exfalso
      subst h
      have := CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup
        (N := 4 * 4) (by omega)
      omega
  · exact absurd h8 (fun h => not_nineThreeEight h hsolv)

theorem tightKP_or_L5Two_of_block (hLF : LargeFieldParabolic) (h418 : Agl418)
    (hL27 : L2SevenRankOne) {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (hconc : NineThreeConclusion M S L) (hnot1 : ¬ NineThreeOne L)
    (hSyl : NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L))
    (hsolv : BlockPLThreeSolv M S L) (hr : Open.pRank 3 L = 2)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)) :
    CFSG.AGLEmbeddingD2.McLaughlin.TightKP (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∨
      IsL5Two (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
  (tightRow_or_L5Two_of_block hLF h418 hL27 hL hconc hnot1 hSyl hsolv hr hZ).imp
    TightRow.tightKP id

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
