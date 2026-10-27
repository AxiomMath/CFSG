module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreNineLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreRankA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreRankRows
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicOvergroup
public import CFSG.Quasithin.Background.B2FactorizationResidual

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint.Multiplier

theorem card_multiplier_eq (hG : GriessAllModelsStatement) {Y : Type} [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hY : CFSG.Models.LieModel Y t n p f) :
    Nat.card (griessHopfMultiplier Y) =
      ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
        ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨e⟩⟩ := hG Y t n p f hY
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]
  have h1 : Nat.card (generic t n p f) =
      (genericOrders t n p f).1 * (genericOrders t n p f).2 := card_multPair _ _
  have h2 : Nat.card (exceptional t n p f) =
      (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 := card_multPair _ _
  rw [h1, h2]

theorem genericOrders_two_one_dvd_four {t : CFSG.Assembly.LowTwoRank.StatedLieTag} (n : ℕ)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    (genericOrders t n 2 1).1 * (genericOrders t n 2 1).2 ∣ 4 := by
  rcases ht with rfl | rfl | rfl | rfl
  · simp [genericOrders]
  · simp [genericOrders]
  · simp [genericOrders]
  · simp only [genericOrders]
    simp
    exact Nat.gcd_dvd_left _ _

theorem genericOrders_psu_two_one (n : ℕ) :
    (genericOrders .PSU n 2 1).1 * (genericOrders .PSU n 2 1).2 = Nat.gcd n 3 := by
  simp [genericOrders]

theorem card_multiplier_dvd_sixteen (hG : GriessAllModelsStatement) {Y : Type} [Group Y]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hY : CFSG.Models.LieModel Y t n 2 1) : Nat.card (griessHopfMultiplier Y) ∣ 16 := by
  rw [card_multiplier_eq hG hY]
  exact (mul_dvd_mul (genericOrders_two_one_dvd_four n ht)
    (exceptionalOrders_two_one_dvd t n)).trans (by norm_num)

theorem three_dvd_multiplier_classicalIndexTwo (hG : GriessAllModelsStatement) {Y : Type}
    [Group Y] (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2IndexTwo d.1)
    (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) (h3 : 3 ∣ Nat.card (griessHopfMultiplier Y)) :
    ∃ r : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA r q ∧ q.card = 2 ∧ 3 ∣ r + 1 := by
  obtain ⟨d1, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d1 with
  | A r q =>
    exfalso
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_sixteen hG (t := .PSL) (n := r + 1) (Or.inl rfl) ⟨h.1, Or.inl h⟩
    have := h3.trans this
    omega
  | twistedA r q =>
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hp, hqe] at h
    have hM := card_multiplier_eq hG (t := .PSU) (n := r + 1) (p := 2) (f := 1) ⟨h.1, Or.inl h⟩
    rw [genericOrders_psu_two_one] at hM
    have hexc := exceptionalOrders_two_one_dvd .PSU (r + 1)
    rw [hM] at h3
    have h3' : 3 ∣ Nat.gcd (r + 1) 3 := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · exact h
      · have := h.trans hexc
        omega
    exact ⟨r, q, rfl, hd, h3'.trans (Nat.gcd_dvd_left _ _)⟩
  | B r q =>
    exfalso
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have hr3 : 3 ≤ r := by
      have h2 := hrange.1
      have h3' : r ≠ 2 := fun h => hrange.2 ⟨h, hd⟩
      omega
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_sixteen hG (t := .PSp) (n := r) (Or.inr (Or.inl rfl))
      ⟨h.1, Or.inl h⟩
    have := h3.trans this
    omega
  | D r q =>
    exfalso
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_sixteen hG (t := .POmegaPlus) (n := r)
      (Or.inr (Or.inr (Or.inl rfl))) ⟨h.1, Or.inl h⟩
    have := h3.trans this
    omega
  | twistedD r q =>
    exfalso
    simp only [IsClassicalOrG2IndexTwo] at hd
    obtain ⟨hp, hqe⟩ := primePower_card_two' hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
    rw [hp, hqe] at h
    have := card_multiplier_dvd_sixteen hG (t := .POmegaMinus) (n := r)
      (Or.inr (Or.inr (Or.inr rfl))) ⟨h.1, Or.inl h⟩
    have := h3.trans this
    omega
  | G2 q =>
    exfalso
    simp only [IsClassicalOrG2IndexTwo] at hd
    have := hrange
    omega
  | _ => exact hd.elim

theorem primePower_card_prime {q : TauCeti.PrimePower} {ℓ : ℕ} (hℓ : ℓ.Prime) (h : q.card = ℓ) :
    q.p = ℓ ∧ q.exponent = 1 := by
  have hq : q.p ^ q.exponent = ℓ := by rw [← TauCeti.PrimePower.card_def]; exact h
  exact (Nat.Prime.pow_eq_iff hℓ).mp hq

section Rows


theorem eq_six_or_seven_of_three_dvd_alt {S : Type} [Group S] {m : ℕ} (hm : 5 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) (h3 : 3 ∣ Nat.card (griessHopfMultiplier S)) :
    m = 6 ∨ m = 7 := by
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (alternatingGroup (Fin m))).toEquiv,
    (CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput m hm).2] at h3
  by_contra hcon
  rw [if_neg hcon] at h3
  omega

theorem rows_of_three_dvd_center (hG : GriessAllModelsStatement) {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (h3 : 3 ∣ Nat.card (Subgroup.center X))
    (hcensus : (∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2IndexTwo d.1 ∧
        Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
        Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin n))) ∨
      ∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
        Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) ∨
      ∃ d : TauCeti.ValidLieTypeIndex,
        (∃ r : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA r q ∧ q.card = 2 ∧ 3 ∣ r + 1) ∧
        Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  have hdvd := card_center_dvd_card_griessHopfMultiplier hperf
    (MulEquiv.refl (X ⧸ Subgroup.center X))
  have hM3 : 3 ∣ Nat.card (griessHopfMultiplier (X ⧸ Subgroup.center X)) := h3.trans hdvd
  rcases hcensus with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · exact Or.inr ⟨d, three_dvd_multiplier_classicalIndexTwo hG d hd e hM3, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · have := eq_six_or_seven_of_three_dvd_alt (by norm_num) e hM3
      omega
    · exact Or.inl ⟨e⟩
    · have := eq_six_or_seven_of_three_dvd_alt (by norm_num) e hM3
      omega
  · exfalso
    obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    obtain ⟨hp, hqe⟩ := primePower_card_prime (by norm_num) hq
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hp, hqe] at h
    have hM := card_multiplier_eq hG (t := .PSL) (n := 1 + 1) (p := 7) (f := 1) ⟨h.1, Or.inl h⟩
    rw [hM] at hM3
    simp [genericOrders, exceptionalOrders] at hM3
  · exfalso
    obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    obtain ⟨hp, hqe⟩ := primePower_card_prime (by norm_num) hq
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp, hqe] at h
    have hM := card_multiplier_eq hG (t := .PSU) (n := 2 + 1) (p := 3) (f := 1) ⟨h.1, Or.inl h⟩
    rw [hM] at hM3
    simp [genericOrders, exceptionalOrders] at hM3

end Rows

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def KFactBlockCentreRankTwoPSU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeTwo M S L → BlockPLThreeSolv M S L →
    (NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L)) →
    barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    (∃ d : TauCeti.ValidLieTypeIndex,
      (∃ r : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA r q ∧ q.card = 2 ∧ 3 ∣ r + 1) ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    2 ≤ Open.pRank 3 (barM M (Subgroup.normalizer (S : Set G) ⊓ L))


theorem kFactBlockCentreRankTwoTypeTwo_of_psu (hG : GriessAllModelsStatement)
    (hP : KFactBlockCentreRankTwoPSU) : KFactBlockCentreRankTwoTypeTwo := by
  intro G _ _ M S L hL h2 hsolv hSyl hZP hZ h9
  have h3p : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hY, hpar, hS⟩ := h2
  have h2' : NineThreeTwo M S L := ⟨hY, hpar, hS⟩
  have hnot : ¬ IsSylowTwoOf (pCoreOf 2 (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
      (barM M L) := hS ▸ hSyl h2'
  obtain ⟨T, hT, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hnot hsolv
  have hcensus := kFactParabolicThreeCensus _ hY T _ hT hNJ hJne hJperf
  have hperfX : commutator ↥(barM M L) = ⊤ :=
    Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect))
  have hcard := card_inf_centralizer_eq_card_center (barM M L)
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by rw [← hcard]; exact hZ
  rcases rows_of_three_dvd_center hG ⟨hperfX⟩ h3 hcensus with heA | hpsu
  · obtain ⟨eA⟩ := heA
    have hPL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L := barM_mono inf_le_right
    have hZP' : Subgroup.center ↥(barM M L) ≤
        (barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      apply hZP
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      have := Subgroup.mem_center_iff.mp hx ⟨h, hh⟩
      exact congrArg Subtype.val this
    have := two_le_pRank_of_A6_extension _ hZP' h3 eA hT hNJ hJne
    have hmap := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 h3p
      (barM M L).subtype (barM M L).subtype_injective
      ((barM M (Subgroup.normalizer (S : Set G) ⊓ L)).subgroupOf (barM M L))
    rw [Subgroup.map_subgroupOf_eq_of_le hPL] at hmap
    omega
  · exact hP G M S L hL h2' hsolv hSyl hZP hZ h9 hpsu

theorem kFactBlockCentreRankTwo_of_psu (hG : GriessAllModelsStatement)
    (hP : KFactBlockCentreRankTwoPSU) : KFactBlockCentreRankTwo :=
  kFactBlockCentreRankTwo_of_typeTwo (kFactBlockCentreRankTwoTypeTwo_of_psu hG hP)

end CFSG.AGLEmbeddingD2.McLaughlin
