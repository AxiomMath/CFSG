module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviTransport
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOUCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial

theorem sp6_eq_two_of_prime_dvd_card {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hpF : p ∣ Nat.card F) : p = 2 := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hn
  rw [hn] at hpF
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpF)

theorem sp6_sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem sp6_not_dvd_card_sub_one {F : Type} [Field F] [Finite F] {p : ℕ}
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) : ¬ p ∣ Nat.card F - 1 := by
  intro h
  apply hpq
  have hq : 1 ≤ Nat.card F := (Finite.one_lt_card (α := F)).le
  rw [sp6_sq_sub_one_eq _ hq]
  exact Dvd.dvd.mul_right h _

theorem sp6_subsingleton_sl {F : Type} [Field F] {m : ℕ} (hm : m < 2) :
    Subsingleton (Matrix.SpecialLinearGroup (Fin m) F) := by
  refine ⟨fun A B => Subtype.ext (Matrix.ext fun i j => ?_)⟩
  have hi := i.isLt
  obtain rfl : m = 1 := by omega
  have hA := A.2
  have hB := B.2
  rw [Matrix.det_unique] at hA hB
  rw [Subsingleton.elim i default, Subsingleton.elim j default, hA, hB]

theorem sp6_not_dvd_card_sl_le_two {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {m : ℕ} (hm : m ≤ 2) :
    ¬ p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) F) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · haveI := sp6_subsingleton_sl (F := F) h
    rw [Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin m) F)]
    exact hp.not_dvd_one
  · obtain rfl : m = 2 := by omega
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have := sp6_eq_two_of_prime_dvd_card hp h1
      omega
    · exact hpq h1

theorem sp6_not_dvd_card_statedSp {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {m : ℕ} (hm : m ≤ 1) :
    ¬ p ∣ Nat.card (StatedSp m F) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  interval_cases m
  · simp only [pow_zero, Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.prod_empty,
      mul_one]
    exact hp.not_dvd_one
  · simp only [one_pow, pow_one, Finset.Icc_self, Finset.prod_singleton, mul_one]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have := sp6_eq_two_of_prime_dvd_card hp h1
      omega
    · exact hpq h1

theorem sp6_commutator_sp {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F)
    {m : ℕ} (hm : m ≤ 2) : commutator (StatedSp m F) = ⊤ := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · have hc : Nat.card (StatedSp 0 F) = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
      simp
    haveI := (Nat.card_eq_one_iff_unique.1 hc).1
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  · exact (spFlag_isQuasisimple_Sp (K := F) (m := m) (by omega) (Or.inl h4)).1

theorem sp6_commutator_sl {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) (k : ℕ) :
    commutator (Matrix.SpecialLinearGroup (Fin k) F) = ⊤ := by
  by_cases hk : 2 ≤ k
  · exact (spFlag_isQuasisimple_SL (K := F) hk (Or.inr h4)).1
  · haveI := sp6_subsingleton_sl (F := F) (m := k) (by omega)
    refine (Subgroup.eq_top_iff' _).2 fun x => ?_
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _

theorem sp6_center_sp2 {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (StatedSp 2 F) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq 2 F,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

theorem sp6_card_center_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  rw [← CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv e,
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

theorem sp6_dvd_card_of_mem {G : Type} [Group G] (H : Subgroup G) {u : G} (hu : u ∈ H)
    {p : ℕ} (hord : orderOf u = p) : p ∣ Nat.card H := by
  have h := orderOf_dvd_natCard (⟨u, hu⟩ : H)
  rwa [Subgroup.orderOf_mk, hord] at h

theorem sp6_commutator_self_eq_of_top {G : Type*} [Group G] (H : Subgroup G)
    (h : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = (⊤ : Subgroup H)) : ⁅H, H⁆ = H := by
  have h1 := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1

theorem sp6_commutator_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = (⊤ : Subgroup A)) :
    ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = (⊤ : Subgroup B) := by
  have h1 := congrArg (Subgroup.map e.toMonoidHom) h
  rw [Subgroup.map_commutator, map_top_of_surjective e.toMonoidHom e.surjective] at h1
  exact h1

theorem sp6_commutator_self_eq {G A : Type} [Group G] [Group A] (H : Subgroup G) (e : ↥H ≃* A)
    (hA : commutator A = ⊤) : ⁅H, H⁆ = H :=
  sp6_commutator_self_eq_of_top H (sp6_commutator_top_of_mulEquiv e.symm hA)

noncomputable def sp6_zero_equiv {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3) (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ}
    (htI : t ∈ I) {j : Fin 4} (hj0 : (j : ℕ) = 0) :
    ↥(spFlagLeviBlock (K := F) hI t j) ≃* ↥(StatedSp (3 - t) F) :=
  (spFlagLeviBlockZeroEquiv (K := F) hI t hj0).trans
    ((MulEquiv.subgroupCongr (sp6_commutator_sp h4 (m := 3 - t)
      (by have := hI1 t htI; have := hI t htI; omega))).trans Subgroup.topEquiv)

theorem sp6_zero_block_len {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 3)
    (hI1 : ∀ i ∈ I, 1 ≤ i) {t : ℕ} (htI : t ∈ I) {j : Fin 4} (hj0 : (j : ℕ) = 0)
    {u : ↥(StatedSp 3 F)} (hu : u ∈ spFlagLeviBlock (K := F) hI t j) (hord : orderOf u = p) :
    3 - t = 2 := by
  have ht := hI1 t htI
  have ht3 := hI t htI
  by_contra hne
  apply sp6_not_dvd_card_statedSp hp hp5 hpq (m := 3 - t) (by omega)
  rw [← Nat.card_congr (sp6_zero_equiv h4 hI hI1 htI hj0).toEquiv]
  exact sp6_dvd_card_of_mem _ hu hord

theorem sp6_mem_block_three {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {I : Set ℕ}
    (hI : ∀ i ∈ I, i ≤ 3) {t : ℕ} {j : Fin 4} (hj0 : (j : ℕ) ≠ 0) (hj : (j : ℕ) ∈ I)
    {u : ↥(StatedSp 3 F)} (hu : u ∈ spFlagLeviBlock (K := F) hI t j) (hord : orderOf u = p) :
    (j : ℕ) - spFlagPrev I (j : ℕ) = 3 := by
  by_contra hne
  have hle : (j : ℕ) - spFlagPrev I (j : ℕ) ≤ 2 := by
    have := j.isLt
    omega
  apply sp6_not_dvd_card_sl_le_two hp hp5 hpq hle
  rw [← Nat.card_congr (spFlagLeviBlockMemEquiv (K := F) hI t hj0 hj).toEquiv]
  exact sp6_dvd_card_of_mem _ hu hord

theorem sp6_block_zero_props {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {p : ℕ} (hp : p.Prime) {A : Type} [Group A] {m : ℕ} (hm : m = 2)
    (e : A ≃* ↥(StatedSp m F)) :
    CFSG.Open.IsQuasisimple A ∧ ¬ p ∣ Nat.card (Subgroup.center A) ∧
      Nonempty (A ⧸ Subgroup.center A ≃* ↥(StatedSp 2 F)) := by
  subst hm
  have hq : CFSG.Open.IsQuasisimple A :=
    CFSG.AGLEmbedding.LeviBlock.isQuasisimple_of_mulEquiv e.symm
      (spFlag_isQuasisimple_Sp (K := F) (m := 2) (by norm_num) (Or.inl h4))
  have hc : Subgroup.center A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := Subgroup.mem_map_of_mem e.toMonoidHom hx
    rw [CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv e, sp6_center_sp2, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [map_one]; exact h1)
  refine ⟨hq, ?_, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientBot.trans e)⟩⟩
  rw [hc, Subgroup.card_bot]
  exact hp.not_dvd_one

theorem sp6_block_three_props {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) {p : ℕ} (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {A : Type} [Group A]
    {k : ℕ} (hk : k = 3) (e : A ≃* Matrix.SpecialLinearGroup (Fin k) F) :
    CFSG.Open.IsQuasisimple A ∧ ¬ p ∣ Nat.card (Subgroup.center A) ∧
      Nonempty (A ⧸ Subgroup.center A ≃*
        (Matrix.SpecialLinearGroup (Fin 3) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  subst hk
  have hq : CFSG.Open.IsQuasisimple A :=
    CFSG.AGLEmbedding.LeviBlock.isQuasisimple_of_mulEquiv e.symm
      (spFlag_isQuasisimple_SL (K := F) (k := 3) (by norm_num) (Or.inl le_rfl))
  refine ⟨hq, ?_, ⟨QuotientGroup.congr _ _ e
    (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv e)⟩⟩
  rw [sp6_card_center_congr e]
  intro h
  exact sp6_not_dvd_card_sub_one hpq (dvd_trans h
    (CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.card_center_SL_dvd (K := F) (k := 3)
      (by norm_num)))

theorem sp6_det_of_cut {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F - 1) {I : Set ℕ} {r : ℕ} (hI : ∀ i ∈ I, i ≤ r) {a b : ℕ}
    (ha : a = 0 ∨ a ∈ I) (hbI : b ∈ I) (g : SymplecticHigher.flagStabilizer r F I)
    (hg : spFlagCutEmb (K := F) a b (hI b hbI) (spFlagCutHom hI ha hbI g) ^ p = 1) :
    Matrix.GeneralLinearGroup.det (spFlagCutHom hI ha hbI g) = 1 := by
  have h2 : spFlagCutEmb (K := F) a b (hI b hbI) (spFlagCutHom hI ha hbI g ^ p) =
      spFlagCutEmb (K := F) a b (hI b hbI) 1 := by
    rw [map_pow, map_one]
    exact hg
  have hpow := spFlagCutEmb_injective (K := F) a b (hI b hbI) h2
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.det_eq_one_of_pow_eq_one hp hpF hpow

theorem sp6_leviSurj {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.Open.StatedSp 3 F)) ≤ 1)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i ≤ 3) (hIne : I.Nonempty)
    {z : CFSG.Open.StatedSp 3 F} (hz : orderOf z = p)
    (hzP : z ∈ SymplecticHigher.flagStabilizer 3 F I) :
    LeviSurj p (SymplecticHigher.flagStabilizer 3 F I) z
        (Matrix.SpecialLinearGroup (Fin 3) F ⧸
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) ∨
      LeviSurj p (SymplecticHigher.flagStabilizer 3 F I) z ↥(CFSG.Open.StatedSp 2 F) := by
  have hp2 : p ≠ 2 := by omega
  have hnd : ¬ p ∣ Nat.card F - 1 := sp6_not_dvd_card_sub_one hpq
  have hI' : ∀ i ∈ I, i ≤ 3 := fun i hi => (hI i hi).2
  have hI1 : ∀ i ∈ I, 1 ≤ i := fun i hi => (hI i hi).1
  obtain ⟨t, htI, hmax⟩ : ∃ t ∈ I, ∀ c ∈ I, c ≤ t := by
    by_cases h3 : (3 : ℕ) ∈ I
    · exact ⟨3, h3, fun c hc => hI' c hc⟩
    by_cases h2 : (2 : ℕ) ∈ I
    · refine ⟨2, h2, fun c hc => ?_⟩
      have h1 := hI' c hc
      have h3' : c ≠ 3 := fun h => h3 (h ▸ hc)
      omega
    obtain ⟨c, hc⟩ := hIne
    have h1 := hI c hc
    have hc3 : c ≠ 3 := fun h => h3 (h ▸ hc)
    have hc2 : c ≠ 2 := fun h => h2 (h ▸ hc)
    refine ⟨1, ?_, fun c' hc' => ?_⟩
    · rw [show (1 : ℕ) = c by omega]
      exact hc
    · have h1' := hI' c' hc'
      have hc'3 : c' ≠ 3 := fun h => h3 (h ▸ hc')
      have hc'2 : c' ≠ 2 := fun h => h2 (h ▸ hc')
      omega
  have hβ : IsPGroup 2 (spFlagLeviHom (K := F) hI' htI).ker :=
    isPGroup_ker_spFlagLeviHom hI' htI hI1
  have hS : Subgroup.pi Set.univ (spFlagLeviBlock (K := F) hI' t) ≤
      (spFlagLeviHom (K := F) hI' htI).range :=
    pi_le_range_spFlagLeviHom hI' htI hmax
  have hcomm : ⁅(spFlagLeviHom (K := F) hI' htI).range,
      (spFlagLeviHom (K := F) hI' htI).range⁆ ≤
      Subgroup.pi Set.univ (spFlagLeviBlock (K := F) hI' t) :=
    commutator_range_spFlagLeviHom_le hI' htI
  have ht1 := hI1 t htI
  have ht3 := hI' t htI
  have hperf : ∀ j, ⁅spFlagLeviBlock (K := F) hI' t j, spFlagLeviBlock (K := F) hI' t j⁆ =
      spFlagLeviBlock (K := F) hI' t j := by
    intro j
    by_cases hj0 : (j : ℕ) = 0
    · exact sp6_commutator_self_eq _ (sp6_zero_equiv h4 hI' hI1 htI hj0)
        (sp6_commutator_sp h4 (m := 3 - t) (by omega))
    by_cases hj : (j : ℕ) ∈ I
    · exact sp6_commutator_self_eq _ (spFlagLeviBlockMemEquiv (K := F) hI' t hj0 hj)
        (sp6_commutator_sl h4 _)
    · rw [spFlagLeviBlock_of_not_mem (K := F) hI' hj0 hj, Subgroup.commutator_bot_left]
  have hpR : ∀ x ∈ (spFlagLeviHom (K := F) hI' htI).range, x ^ p = 1 →
      x ∈ Subgroup.pi Set.univ (spFlagLeviBlock (K := F) hI' t) := by
    rintro x ⟨g, rfl⟩ hx
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    have hxj : spFlagLeviCoord (K := F) hI' htI j g ^ p = 1 := by
      have h := congrFun hx j
      rw [Pi.pow_apply, Pi.one_apply] at h
      exact h
    show spFlagLeviCoord (K := F) hI' htI j g ∈ spFlagLeviBlock (K := F) hI' t j
    by_cases hj0 : (j : ℕ) = 0
    · have hc0 : commutator (StatedSp (3 - t) F) = ⊤ :=
        sp6_commutator_sp h4 (m := 3 - t) (by omega)
      rw [spFlagLeviBlock_of_eq_zero (K := F) hI' hj0, hc0, spFlagLeviCoord_of_eq_zero hI' htI hj0,
        MonoidHom.comp_apply]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
    by_cases hj : (j : ℕ) ∈ I
    · rw [spFlagLeviCoord_of_mem hI' htI hj0 hj, MonoidHom.comp_apply] at hxj
      rw [spFlagLeviBlock_of_mem (K := F) hI' hj0 hj, MonoidHom.range_comp,
        spFlagLeviCoord_of_mem hI' htI hj0 hj, MonoidHom.comp_apply]
      refine Subgroup.mem_map_of_mem _ ?_
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
      exact sp6_det_of_cut hp hnd hI' (spFlagPrev_mem I (j : ℕ)) hj g hxj
    · rw [spFlagLeviCoord_of_not_mem hI' htI hj0 hj, spFlagLeviBlock_of_not_mem (K := F) hI' hj0 hj,
        MonoidHom.one_apply, Subgroup.mem_bot]
  have hblk : ∀ j, (∃ u ∈ spFlagLeviBlock (K := F) hI' t j, orderOf u = p) →
      CFSG.Open.IsQuasisimple ↥(spFlagLeviBlock (K := F) hI' t j) ∧
        ¬ p ∣ Nat.card (Subgroup.center ↥(spFlagLeviBlock (K := F) hI' t j)) := by
    rintro j ⟨u, hu, hord⟩
    by_cases hj0 : (j : ℕ) = 0
    · have hm2 := sp6_zero_block_len h4 hp hp5 hpq hI' hI1 htI hj0 hu hord
      obtain ⟨h1, h2, -⟩ := sp6_block_zero_props h4 hp hm2 (sp6_zero_equiv h4 hI' hI1 htI hj0)
      exact ⟨h1, h2⟩
    by_cases hj : (j : ℕ) ∈ I
    · have hk3 := sp6_mem_block_three hp hp5 hpq hI' hj0 hj hu hord
      obtain ⟨h1, h2, -⟩ :=
        sp6_block_three_props h4 hpq hk3 (spFlagLeviBlockMemEquiv (K := F) hI' t hj0 hj)
      exact ⟨h1, h2⟩
    · exfalso
      rw [spFlagLeviBlock_of_not_mem (K := F) hI' hj0 hj, Subgroup.mem_bot] at hu
      rw [hu, orderOf_one] at hord
      omega
  obtain ⟨j₀, ⟨u, hu, hord⟩, hL⟩ :=
    leviSurj_of_blocks (ι := Fin 4) (G := fun _ : Fin 4 => ↥(StatedSp 3 F))
      (β := spFlagLeviHom (K := F) hI' htI) (S := spFlagLeviBlock (K := F) hI' t)
      hp hp2 hzP hz hrk hβ hS hcomm hperf hpR hblk
  by_cases hj0 : (j₀ : ℕ) = 0
  · right
    have hm2 := sp6_zero_block_len h4 hp hp5 hpq hI' hI1 htI hj0 hu hord
    obtain ⟨e'⟩ := (sp6_block_zero_props h4 hp hm2 (sp6_zero_equiv h4 hI' hI1 htI hj0)).2.2
    exact LeviSurj.of_mulEquiv hL e'
  · left
    have hj : (j₀ : ℕ) ∈ I := by
      by_contra hj
      exfalso
      rw [spFlagLeviBlock_of_not_mem (K := F) hI' hj0 hj, Subgroup.mem_bot] at hu
      rw [hu, orderOf_one] at hord
      omega
    have hk3 := sp6_mem_block_three hp hp5 hpq hI' hj0 hj hu hord
    obtain ⟨e'⟩ :=
      (sp6_block_three_props h4 hpq hk3 (spFlagLeviBlockMemEquiv (K := F) hI' t hj0 hj)).2.2
    exact LeviSurj.of_mulEquiv hL e'

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
