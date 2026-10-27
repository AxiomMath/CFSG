module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBlocks
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOUCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial

theorem fong_eq_two_of_prime_dvd_card {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (hp : p.Prime) (hpF : p ∣ Nat.card F) : p = 2 := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hn
  rw [hn] at hpF
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpF)

theorem fong_sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q - 1) * (q + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem fong_not_dvd_card_sub_one {F : Type} [Field F] [Finite F] {p : ℕ}
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) : ¬ p ∣ Nat.card F - 1 := by
  intro h
  apply hpq
  have hq : 1 ≤ Nat.card F := (Finite.one_lt_card (α := F)).le
  rw [fong_sq_sub_one_eq _ hq]
  exact Dvd.dvd.mul_right h _

theorem fong_not_dvd_card_specialLinear_of_le_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) (m : ℕ) (hm : m ≤ 2) :
    ¬ p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m) F) := by
  rcases Nat.lt_or_ge m 2 with h | h
  · haveI := CFSG.AGLEmbedding.LeviBlock.subsingleton_specialLinear_of_lt_two (K := F) h
    rw [Nat.card_of_subsingleton (1 : Matrix.SpecialLinearGroup (Fin m) F)]
    exact hp.not_dvd_one
  · obtain rfl : m = 2 := by omega
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have := fong_eq_two_of_prime_dvd_card hp h1
      omega
    · exact hpq h1

theorem fong_exists_finset_card_four {F : Type} [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ s : Finset F, s.card = 4 := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem fong_three_le_and_ne_four {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}
    (h4 : 4 ≤ Nat.card F) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : ¬ p ∣ Nat.card F ^ 2 - 1)
    {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) (hIne : I.Nonempty) (j : Fin 4)
    {u : Matrix.GeneralLinearGroup (Fin (linBlockLen 4 I j)) F}
    (hu : u ∈ linBlockSL F 4 I j) (hord : orderOf u = p) :
    3 ≤ linBlockLen 4 I j ∧ linBlockLen 4 I j ≠ 4 := by
  have hdvd : p ∣ Nat.card ↥(linBlockSL F 4 I j) := by
    have h1 := orderOf_dvd_natCard (⟨u, hu⟩ : ↥(linBlockSL F 4 I j))
    rwa [Subgroup.orderOf_mk, hord] at h1
  have hdvd' : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin (linBlockLen 4 I j)) F) := by
    rw [Nat.card_congr (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F)
      (linBlockLen 4 I j)).toEquiv]
    exact hdvd
  have hlen := linBlockLen_le (I := I) j
  refine ⟨?_, ?_⟩
  · by_contra hlt
    exact fong_not_dvd_card_specialLinear_of_le_two hp hp5 hpq _ (by omega) hdvd'
  · intro h4'
    have hstart : (j : ℕ) = 0 ∨ (j : ℕ) ∈ I := by
      by_contra hns
      have := linBlockLen_of_not_start (n := 4) (I := I) (a := j) hns
      omega
    obtain ⟨-, -, -, hno⟩ := linBlockLen_spec (I := I) (a := j) hstart
    obtain ⟨i, hi⟩ := hIne
    obtain ⟨hi1, hi2⟩ := hI i hi
    have := hno i hi
    omega

theorem fong_isQuasisimple_linBlockSL {F : Type} [Field F] {n : ℕ} (I : Set ℕ) (a : Fin n)
    (hm : 3 ≤ linBlockLen n I a) : CFSG.Open.IsQuasisimple ↥(linBlockSL F n I a) := by
  have h : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (linBlockLen n I a)) F) :=
    ⟨(CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hm)).commutator_eq_top,
      (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl hm)).2.1⟩
  exact CFSG.AGLEmbedding.LeviBlock.isQuasisimple_of_mulEquiv
    (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) (linBlockLen n I a)) h

theorem fong_commutator_specialLinear {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (m : ℕ) : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m) F)),
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m) F))⁆ =
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin m) F)) := by
  show commutator (Matrix.SpecialLinearGroup (Fin m) F) = ⊤
  by_cases hm : 2 ≤ m
  · exact (CFSG.LinearGroups.special_linear_isPerfect hm
      (Or.inr (fong_exists_finset_card_four h4))).commutator_eq_top
  · haveI := CFSG.AGLEmbedding.LeviBlock.subsingleton_specialLinear_of_lt_two (K := F)
      (by omega : m < 2)
    exact eq_top_iff.2 fun x _ => by
      rw [Subsingleton.elim x 1]
      exact Subgroup.one_mem _

theorem fong_commutator_self_eq_of_top {G : Type*} [Group G] (H : Subgroup G)
    (h : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = (⊤ : Subgroup H)) : ⁅H, H⁆ = H := by
  have h1 := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1

theorem fong_commutator_top_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = (⊤ : Subgroup A)) :
      ⁅(⊤ : Subgroup B), (⊤ : Subgroup B)⁆ = (⊤ : Subgroup B) := by
  have h1 := congrArg (Subgroup.map e.toMonoidHom) h
  rw [Subgroup.map_commutator, map_top_of_surjective e.toMonoidHom e.surjective] at h1
  exact h1

theorem fong_nonempty_quotient_iso_three {F : Type} [Field F] [Finite F] (m : ℕ) (hm : m = 3)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin m) F))
    (hH : H = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) F →* Matrix.GeneralLinearGroup (Fin m) F).range) :
    Nonempty (↥H ⧸ Subgroup.center ↥H ≃*
      (Matrix.SpecialLinearGroup (Fin 3) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  subst hm
  subst hH
  exact ⟨(QuotientGroup.congr _ _ (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) 3)
    (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv
      (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) 3))).symm⟩

theorem sl4_leviSurj {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F)) ≤ 1)
    (hpq : ¬ p ∣ Nat.card F ^ 2 - 1) {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) (hIne : I.Nonempty)
    {z : Matrix.SpecialLinearGroup (Fin 4) F} (hz : orderOf z = p)
    (hzP : z ∈ LinearFlag.flagStabilizer 4 F I) :
    LeviSurj p (LinearFlag.flagStabilizer 4 F I) z
      (Matrix.SpecialLinearGroup (Fin 3) F ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  classical
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 4) F) := Subtype.finite
  have hp2 : p ≠ 2 := by omega
  have hnd : ¬ p ∣ Nat.card F - 1 := fong_not_dvd_card_sub_one hpq
  have hβ : IsPGroup 2 (linLeviHom F 4 I).ker := isPGroup_ker_linLeviHom (by norm_num)
  have hS : Subgroup.pi Set.univ (fun j => linBlockSL F 4 I j) ≤ (linLeviHom F 4 I).range :=
    pi_le_range_linLeviHom
  have hcomm : ⁅(linLeviHom F 4 I).range, (linLeviHom F 4 I).range⁆ ≤
      Subgroup.pi Set.univ (fun j => linBlockSL F 4 I j) :=
    commutator_range_linLeviHom_le
  have hperf : ∀ j, ⁅linBlockSL F 4 I j, linBlockSL F 4 I j⁆ = linBlockSL F 4 I j := fun j =>
    fong_commutator_self_eq_of_top _ (fong_commutator_top_of_mulEquiv
      (CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := F) (linBlockLen 4 I j))
      (fong_commutator_specialLinear h4 _))
  have hpR : ∀ x ∈ (linLeviHom F 4 I).range, x ^ p = 1 →
      x ∈ Subgroup.pi Set.univ (fun j => linBlockSL F 4 I j) := by
    intro x _ hx
    refine (Subgroup.mem_pi _).2 fun a _ => ?_
    have hxa : x a ^ p = 1 := by
      have h := congrFun hx a
      rwa [Pi.pow_apply, Pi.one_apply] at h
    show x a ∈ linBlockSL F 4 I a
    rw [linBlockSL, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.det_eq_one_of_pow_eq_one hp hnd hxa
  have hblk : ∀ j, (∃ u ∈ linBlockSL F 4 I j, orderOf u = p) →
      CFSG.Open.IsQuasisimple ↥(linBlockSL F 4 I j) ∧
        ¬ p ∣ Nat.card (Subgroup.center ↥(linBlockSL F 4 I j)) := by
    rintro j ⟨u, hu, hord⟩
    have h3 := (fong_three_le_and_ne_four h4 hp hp5 hpq hI hIne j hu hord).1
    refine ⟨fong_isQuasisimple_linBlockSL (F := F) I j h3, fun hdvd => hnd (dvd_trans hdvd ?_)⟩
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.card_center_linBlockSL_dvd j
      (by omega)
  obtain ⟨j₀, ⟨u, hu, hord⟩, hL⟩ :=
    leviSurj_of_blocks (ι := Fin 4)
      (G := fun j => Matrix.GeneralLinearGroup (Fin (linBlockLen 4 I j)) F)
      (β := linLeviHom F 4 I) (S := fun j => linBlockSL F 4 I j)
      hp hp2 hzP hz hrk hβ hS hcomm hperf hpR hblk
  have hm3 : linBlockLen 4 I j₀ = 3 := by
    obtain ⟨h3, hne4⟩ := fong_three_le_and_ne_four h4 hp hp5 hpq hI hIne j₀ hu hord
    have hlen := linBlockLen_le (I := I) j₀
    omega
  obtain ⟨e⟩ :=
    fong_nonempty_quotient_iso_three (F := F) (linBlockLen 4 I j₀) hm3 (linBlockSL F 4 I j₀) rfl
  exact LeviSurj.of_mulEquiv hL e

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
