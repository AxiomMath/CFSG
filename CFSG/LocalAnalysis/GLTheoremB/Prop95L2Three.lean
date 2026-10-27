module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open

def GoodOrd (N : ℕ) : Prop := 8 ∣ N ∨ 5 ∣ N

theorem good_of_pow_dvd {f k N : ℕ} (hk : 3 ≤ f * k) (h : (2 ^ f) ^ k ∣ N) : GoodOrd N := by
  left
  refine dvd_trans ?_ h
  rw [← pow_mul]
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8]
  exact pow_dvd_pow 2 hk

theorem tri_ge {n : ℕ} (hn : 3 ≤ n) : 3 ≤ (n - 1) * n / 2 := by
  apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
  exact le_trans (by norm_num) (Nat.mul_le_mul (show 2 ≤ n - 1 by omega) hn)

theorem card_L2Three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) =
      3 ^ p * (((3 ^ p) ^ 2 - 1) / 2) := by
  have hK : Nat.card (GaloisField 3 p) = 3 ^ p := GaloisField.card 3 p hp.ne_zero
  exact CFSG.SectionRank.OddCover.card_psl_two (by norm_num : Nat.Prime 3) (by norm_num) hK

theorem nine_pow_odd (k : ℕ) : 9 ^ (2 * k + 1) % 16 = 9 ∧ 9 ^ (2 * k + 1) % 5 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h : 9 ^ (2 * (k + 1) + 1) = 9 ^ (2 * k + 1) * 81 := by ring
    rw [h]
    generalize 9 ^ (2 * k + 1) = a at ih ⊢
    omega

theorem not_goodOrd_L2Three (k : ℕ) :
    ¬ GoodOrd (3 ^ (2 * k + 1) * (((3 ^ (2 * k + 1)) ^ 2 - 1) / 2)) := by
  obtain ⟨h16, h5⟩ := nine_pow_odd k
  have hsq : (3 ^ (2 * k + 1)) ^ 2 = 9 ^ (2 * k + 1) := by
    rw [← pow_mul, show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  have hodd : 3 ^ (2 * k + 1) % 2 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  generalize hx : 3 ^ (2 * k + 1) = x at hsq hodd ⊢
  rw [← hsq] at h16 h5
  obtain ⟨w, hw⟩ : ∃ w, w = (x ^ 2 - 1) / 2 := ⟨_, rfl⟩
  rw [← hw]
  have hw2 : 2 * w + 1 = x ^ 2 := by
    rw [hw]
    generalize x ^ 2 = s at h16 h5 ⊢
    omega
  have hw8 : w % 8 = 4 := by
    generalize x ^ 2 = s at h16 h5 hw2
    omega
  have hw5 : w % 5 = 4 := by
    generalize x ^ 2 = s at h5 hw2
    omega
  obtain ⟨q, hq⟩ : ∃ q, w = 8 * q + 4 := ⟨w / 8, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, x = 2 * r + 1 := ⟨x / 2, by omega⟩
  have hN : x * w = 8 * (2 * r * q + r + q) + 4 := by
    rw [hq, hr]
    ring
  rintro (h8 | h5')
  · rw [hN] at h8
    generalize 2 * r * q + r + q = t at h8
    omega
  · rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5' with h | h
    · have hs : 5 ∣ x ^ 2 := dvd_pow h (by norm_num)
      generalize x ^ 2 = s at h5 hs
      omega
    · omega

theorem card_alt (m : ℕ) (hm : 2 ≤ m) : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem goodOrd_alt (m : ℕ) (hm : 5 ≤ m) : GoodOrd (m.factorial / 2) := by
  rcases Nat.lt_or_ge m 6 with h | h
  · obtain rfl : m = 5 := by omega
    right
    decide
  · have h16 : (16 : ℕ) ∣ m.factorial :=
      dvd_trans (by decide : (16 : ℕ) ∣ Nat.factorial 6) (Nat.factorial_dvd_factorial h)
    obtain ⟨c, hc⟩ := h16
    left
    rw [hc]
    omega

theorem good_A (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hv' := (TauCeti.LieTypeIndex.valid_iff _).mp hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp hv'.1
  have hdup := hv'.2
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
  have hL := CFSG.Models.lieModel_A r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  apply good_of_pow_dvd (f := q.exponent) _
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordA (n := r + 1) (by omega) (2 ^ q.exponent))
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · have hr1 : r = 1 := by omega
    subst hr1
    have h4 : 4 ≤ q.card := hr.2 rfl
    have hne : q.card ≠ 4 := fun h =>
      hdup (by
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact Or.inl ⟨rfl, Or.inl h⟩)
    have key : ∀ f : ℕ, 4 ≤ 2 ^ f → 2 ^ f ≠ 4 → 3 ≤ f := by
      intro f h1 h2
      rcases Nat.lt_or_ge f 3 with h | h
      · interval_cases f
        · norm_num at h1
        · norm_num at h1
        · norm_num at h2
      · exact h
    have hf3 : 3 ≤ q.exponent := key q.exponent (hcard ▸ h4) (hcard ▸ hne)
    norm_num
    omega
  · have hK : 3 ≤ (r + 1 - 1) * (r + 1) / 2 := tri_ge (by omega)
    exact le_trans hK (Nat.le_mul_of_pos_left _ q.exponent_pos)

theorem good_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA r q).trans hd
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  have hL := CFSG.Models.lieModel_twistedA r q hv e
  rw [hc, hf] at hL
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  apply good_of_pow_dvd (f := q.exponent) _
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedA (n := r + 1) (by omega) (2 ^ q.exponent))
  have hK : 3 ≤ (r + 1 - 1) * (r + 1) / 2 := tri_ge (by omega)
  exact le_trans hK (Nat.le_mul_of_pos_left _ q.exponent_pos)

theorem good_B (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hdiv : (2 ^ q.exponent) ^ (r * r) ∣ CFSG.Open.ordBC r (2 ^ q.exponent) :=
    CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordBC (n := r) (by omega) (2 ^ q.exponent)
  have hr2 : 2 ≤ r := hr.1
  have hr4 : 4 ≤ r * r := le_trans (by norm_num) (Nat.mul_le_mul hr2 hr2)
  have hpos := q.exponent_pos
  rcases CFSG.Models.lieModel_B r q hv e with hL | hL
  · have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    rw [hd] at hB
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
    apply good_of_pow_dvd (f := q.exponent) _ hdiv
    nlinarith
  · have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    rw [hd] at hB
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
    apply good_of_pow_dvd (f := q.exponent) _ hdiv
    nlinarith

theorem good_D (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hL := CFSG.Models.lieModel_D r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  have hr4 : 4 ≤ r := hr
  have h12 : 3 ≤ r * (r - 1) :=
    le_trans (by norm_num) (Nat.mul_le_mul (by omega : 2 ≤ r) (by omega : 3 ≤ r - 1))
  apply good_of_pow_dvd (f := q.exponent) _ (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordD r (2 ^ q.exponent))
  exact le_trans h12 (Nat.le_mul_of_pos_left _ q.exponent_pos)

theorem good_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hL := CFSG.Models.lieModel_twistedD r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  apply good_of_pow_dvd (f := q.exponent) _
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedD r (2 ^ q.exponent))
  have hr4 : 4 ≤ r := hr
  have h12 : 3 ≤ r * (r - 1) :=
    le_trans (by norm_num) (Nat.mul_le_mul (by omega : 2 ≤ r) (by omega : 3 ≤ r - 1))
  exact le_trans h12 (Nat.le_mul_of_pos_left _ q.exponent_pos)

theorem pow24_dvd_ordF4 (q : ℕ) : q ^ 24 ∣ CFSG.Open.ordF4 q :=
  CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .F4) (n := 0) (by decide) q

theorem pow120_dvd_ordE8 (q : ℕ) : q ^ 120 ∣ CFSG.Open.ordE8 q :=
  CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .E8) (n := 0) (by decide) q

theorem pow6_dvd_ordG2 (q : ℕ) : q ^ 6 ∣ CFSG.Open.ordG2 q :=
  CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .G2) (n := 0) (by decide) q

theorem pow12_dvd_ordTrialityD4 (q : ℕ) : q ^ 12 ∣ CFSG.Open.ordTrialityD4 q :=
  CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .trialityD4) (n := 0) (by decide) q

theorem pow12_dvd_ordTwistedF4 (q : ℕ) : q ^ 12 ∣ CFSG.Open.ordTwistedF4 q := by
  unfold CFSG.Open.ordTwistedF4
  exact ((((dvd_refl (q ^ 12)).mul_right (q ^ 6 + 1)).mul_right (q ^ 4 - 1)).mul_right
    (q ^ 3 + 1)).mul_right (q - 1)

theorem good_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hd : q.p = 2)
    {G : Type} [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :
    GoodOrd (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_E6_even (d := ⟨.E6 q, hv⟩) hd rfl]
  exact good_of_pow_dvd (f := q.exponent) (k := 36) (by have := q.exponent_pos; omega)
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordE6 (2 ^ q.exponent))

theorem good_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hd : q.p = 2)
    {G : Type} [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :
    GoodOrd (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_F4_even (d := ⟨.F4 q, hv⟩) hd rfl]
  exact good_of_pow_dvd (f := q.exponent) (k := 24) (by have := q.exponent_pos; omega)
    (pow24_dvd_ordF4 _)

theorem good_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) (hd : q.p = 2)
    {G : Type} [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    GoodOrd (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_G2_even (d := ⟨.G2 q, hv⟩) hd rfl]
  exact good_of_pow_dvd (f := q.exponent) (k := 6) (by have := q.exponent_pos; omega)
    (pow6_dvd_ordG2 _)

theorem good_trialityD4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv,
    CFSG.AGLEmbedding.card_catGroup_trialityD4_even (d := ⟨.trialityD4 q, hv⟩) hd rfl]
  exact good_of_pow_dvd (f := q.exponent) (k := 12) (by have := q.exponent_pos; omega)
    (pow12_dvd_ordTrialityD4 _)

theorem good_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) (hd : q.p = 2)
    {G : Type} [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) :
    GoodOrd (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hd e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordE7 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact good_of_pow_dvd (f := q.exponent) (k := 63) (by have := q.exponent_pos; omega)
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordE7 (2 ^ q.exponent))

theorem good_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) (hd : q.p = 2)
    {G : Type} [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :
    GoodOrd (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hd e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordE8 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact good_of_pow_dvd (f := q.exponent) (k := 120) (by have := q.exponent_pos; omega)
    (pow120_dvd_ordE8 _)

theorem good_twistedE6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hd (by decide) e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordTwistedE6 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact good_of_pow_dvd (f := q.exponent) (k := 36) (by have := q.exponent_pos; omega)
    (CFSG.EvenSmallLie.CatalogOrders.pow_dvd_ordTwistedE6 (2 ^ q.exponent))

theorem good_suzuki (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hS := CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)
  obtain ⟨-, -, hc⟩ := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_suzuki hS
  rw [hc]
  exact good_of_pow_dvd (f := 2 * m + 1) (k := 2) (by omega)
    (CFSG.EvenSmallLie.CatalogOrders.pow_lieExp_dvd (t := .twistedB2) (n := 0) (by decide) _)

theorem good_tits (hv : (TauCeti.LieTypeIndex.tits).Valid) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hR : CFSG.Blueprint.ReeTitsModel G .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e
  rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hR]
  left
  unfold CFSG.Open.ordTits
  norm_num

theorem good_reeF4 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : GoodOrd (Nat.card G) := by
  have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_reeF4 (d := ⟨.reeF4 m, hv⟩) rfl]
  exact good_of_pow_dvd (f := 2 * m + 1) (k := 12) (by omega) (pow12_dvd_ordTwistedF4 _)

theorem good_of_chev2 (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo d.1)
    (G : Type) [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) : GoodOrd (Nat.card G) := by
  obtain ⟨x, hv⟩ := d
  cases x with
  | A r q => exact good_A r q hv hd e
  | twistedA r q => exact good_twistedA r q hv hd e
  | B r q => exact good_B r q hv hd e
  | C r q =>
    exact absurd (show q.p = 2 from hd)
      (((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2)
  | D r q => exact good_D r q hv hd e
  | twistedD r q => exact good_twistedD r q hv hd e
  | E6 q => exact good_E6 q hv hd e
  | E7 q => exact good_E7 q hv hd e
  | E8 q => exact good_E8 q hv hd e
  | F4 q => exact good_F4 q hv hd e
  | G2 q => exact good_G2 q hv hd e
  | twistedE6 q => exact good_twistedE6 q hv hd e
  | trialityD4 q => exact good_trialityD4 q hv hd e
  | suzuki m => exact good_suzuki m hv e
  | reeG2 m => exact (hd : False).elim
  | reeF4 m => exact good_reeF4 m hv e
  | tits => exact good_tits hv e

theorem good_of_small (d : TauCeti.ValidLieTypeIndex) (G : Type) [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie d).Group)
    (h : (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) :
    GoodOrd (Nat.card G) := by
  obtain ⟨x, hv⟩ := d
  rcases h with ⟨q, hq7, hx⟩ | ⟨q, hq3, hx⟩
  · obtain rfl : x = .A 1 q := hx
    have hL := CFSG.Models.lieModel_A 1 q hv e
    have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    have h7 : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq7
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hB, h7]
    have h168 : CFSG.EvenSmallLie.CatalogOrders.lieOrd (.PSL) (1 + 1) 7 = 168 := by decide
    rw [h168]
    left
    norm_num
  · obtain rfl : x = .twistedA 2 q := hx
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    have hL := CFSG.Models.lieModel_twistedA 2 q hv e
    rw [hc, hf] at hL
    have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    have h3 : q.p ^ q.exponent = 3 := (TauCeti.PrimePower.card_def q).symm.trans hq3
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hB, h3]
    have h6048 : CFSG.EvenSmallLie.CatalogOrders.lieOrd (.PSU) (2 + 1) 3 = 6048 := by decide
    rw [h6048]
    left
    norm_num

theorem l2ThreeNotChevTwoOrAlt_holds : L2ThreeNotChevTwoOrAlt := by
  intro p hp hp2 hfc
  have hY : ¬ GoodOrd (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField 3 p))) := by
    rw [card_L2Three hp hp2]
    obtain ⟨k, rfl⟩ := hp.odd_of_ne_two hp2
    exact not_goodOrd_L2Three k
  unfold CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.FFChevConclusion at hfc
  rcases hfc with hC | ⟨m, hm, ⟨e⟩⟩
  · unfold CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo at hC
    rcases hC with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact hY (good_of_chev2 d hd _ e)
    · apply hY
      rw [Nat.card_congr e.toEquiv, card_alt n (by omega)]
      exact goodOrd_alt n (by omega)
    · exact hY (good_of_small d _ e hd)
  · apply hY
    rw [Nat.card_congr e.toEquiv, card_alt m (by omega)]
    exact goodOrd_alt m hm

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
