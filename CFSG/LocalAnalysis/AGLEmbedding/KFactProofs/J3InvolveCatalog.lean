module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrders
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.AGLEmbedding

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

@[expose] def J3Allowed (t : StatedLieTag) (n q : ℕ) : Prop :=
  (t = .PSL ∧ n = 2 ∧ (q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 9 ∨ q = 16 ∨ q = 17 ∨ q = 19)) ∨
  (t = .PSU ∧ (n = 3 ∨ n = 4) ∧ q = 2) ∨ (t = .PSp ∧ n = 2 ∧ (q = 2 ∨ q = 3))

instance (t : StatedLieTag) (n q : ℕ) : Decidable (J3Allowed t n q) := by
  unfold J3Allowed
  infer_instance

theorem j3_search_true :
    lieSearch [2, 3, 5, 17, 19] 50232960 (fun t n q _ => decide (J3Allowed t n q)) = true := by
  decide +kernel

theorem primes_dvd_j3 (q : ℕ) (hq : q.Prime) (hd : q ∣ 50232960) : q ∈ [2, 3, 5, 17, 19] := by
  simpa using
    mem_of_prime_dvd [(2, 7), (3, 5), (5, 1), (17, 1), (19, 1)] (by decide) (by decide) hq hd

theorem j3_lie_search {t : StatedLieTag} (ht : t ∈ searchTags) {n p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hn : lieMin t ≤ n) (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true)
    (hd : lieOrd t n (p ^ f) ∣ 50232960) : J3Allowed t n (p ^ f) := by
  have h := lieSearch_sound (by norm_num) primes_dvd_j3 j3_search_true ht hp hf hn hnB hadm hd
  exact of_decide_eq_true h

theorem seven_dvd_factorial_div_two {n : ℕ} (hn : 7 ≤ n) : 7 ∣ n.factorial / 2 := by
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have h7f : 7 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have he : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h2).symm
  rw [he] at h7f
  exact ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).1 h7f).resolve_left (by norm_num)

theorem not_dvd_of_card_eq {X : Type*} {m : ℕ} (h : Nat.card X = m) (hm : ¬ m ∣ 50232960) :
    ¬ Nat.card X ∣ 50232960 := h ▸ hm

theorem sporadic_eq_j3
    {T : Type} [Group T] [Finite T] [Nontrivial T] {s : TauCeti.SporadicName}
    (e : T ≃* NativeSporadic.Carrier s) (hdvd : Nat.card T ∣ 50232960) : s = .J3 := by
  have h' : Nat.card (NativeSporadic.Carrier s) ∣ 50232960 := by
    rwa [← Nat.card_congr e.toEquiv]
  cases s
  case M11 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Mathieu.card_M11 (by decide))
  case M12 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Mathieu.card_M12 (by decide))
  case M22 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Mathieu.card_M22 (by decide))
  case M23 => exact absurd h' (not_dvd_of_card_eq card_M23 (by decide))
  case M24 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Mathieu.card_M24 (by decide))
  case J1 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.J1.card_J1 (by decide))
  case J2 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.J2.card_J2 (by decide))
  case J3 => rfl
  case J4 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.J4.card_J4 (by decide))
  case HS => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.HS.card_HS (by decide))
  case McL => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.McL.card_McL (by decide))
  case He => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.He.fam_he_order.1 (by decide))
  case Ru => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Ru.card_Ru (by decide))
  case Suz => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Suz.card_Suz (by decide))
  case ONan => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.ON.card_ON (by decide))
  case Co1 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Co1.card_Co1 (by decide))
  case Co2 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Co2.card_Co2 (by decide))
  case Co3 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Co3.card_Co3 (by decide))
  case Fi22 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Fi22.card_Fi22 (by decide))
  case Fi23 => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Fi23.card_Fi23 (by decide))
  case Fi24Prime =>
    exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Fi24.card_Fi24prime (by decide))
  case HN => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.HN.card_HN (by decide))
  case Ly => exact absurd h' (not_dvd_of_card_eq CFSG.Sporadic.Ly.card_Ly (by decide))
  case Th =>
    exact absurd h' (not_dvd_of_card_eq CFSG.RankThree.PartOne.CTP.card_Th (by decide))
  case B => exact absurd h' (not_dvd_of_card_eq CFSG.Monster.Existence.card_nativeB (by decide))
  case M => exact absurd ((twentyfive_dvd_card_of_mulEquiv_M e).trans hdvd) (by norm_num)

theorem j3_catalog_cases
    {T : Type} [Group T] [Finite T] (hT : Catalog T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hdvd : Nat.card T ∣ 50232960) :
    Nonempty (T ≃* alternatingGroup (Fin 6)) ∨ Nat.card T = 60 ∨ Nat.card T = 4080 ∨
    (Nat.card T = 2448 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 17 ∧
        Nonempty (T ≃* StatedProj (StatedSL 2 K))) ∨
    (Nat.card T = 3420 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 19 ∧
        Nonempty (T ≃* StatedProj (StatedSL 2 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
        Nonempty (T ≃* StatedProj (StatedSU 4 2 K))) ∨
    Nonempty (T ≃* NativeSporadic.J3) := by
  obtain ⟨a, b, hab⟩ := hnab
  have hnt : Nontrivial T := ⟨⟨a * b, b * a, hab⟩⟩
  rcases hT with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, h⟩ |
      (⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩) | ⟨s, ⟨e⟩⟩
  · exfalso
    apply hab
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  ·
    have hcard : Nat.card T = n.factorial / 2 := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have hn6 : n ≤ 6 := by
      by_contra hlt
      push Not at hlt
      exact absurd ((seven_dvd_factorial_div_two (by omega)).trans (hcard ▸ hdvd)) (by norm_num)
    interval_cases n
    · right
      left
      rw [hcard]
      decide
    · left
      exact ⟨e⟩
  ·
    obtain ⟨hp, hf, hcl⟩ := h.1
    have hc := card_eq_lieOrd_of_classical h
    have key : t ∈ searchTags ∧ lieMin t ≤ n ∧ n ≤ lieExp t n + 1 ∧ lieAdm t p f = true := by
      cases t
      case PSL => exact ⟨by decide, hcl.1, le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl)), rfl⟩
      case PSU =>
        exact ⟨by decide, hcl.1, le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
      case PSp => exact ⟨by decide, hcl.1, le_lieExp_add_one hcl.1 (by simp), rfl⟩
      case POmegaOdd => exact ⟨by decide, hcl.1, le_lieExp_add_one hcl.1 (by simp), rfl⟩
      case POmegaPlus => exact ⟨by decide, hcl, le_lieExp_add_one hcl (by simp), rfl⟩
      case POmegaMinus => exact ⟨by decide, hcl, le_lieExp_add_one hcl (by simp), rfl⟩
      all_goals exact h.2.elim
    rw [hc] at hdvd
    have hall := j3_lie_search key.1 hp hf key.2.1 key.2.2.1 key.2.2.2 hdvd
    rcases hall with ⟨rfl, rfl, hq⟩ | ⟨rfl, hn34, hq⟩ | ⟨rfl, rfl, hq⟩
    ·
      rcases hq with hq | hq | hq | hq | hq | hq | hq | hq
      · exact absurd (by rw [hq]) hcl.2.1
      · exact absurd (by rw [hq]) hcl.2.2
      · right
        left
        rw [hc, hq]
        decide
      · right
        left
        rw [hc, hq]
        decide
      · left
        obtain ⟨-, K, hKfield, hKfin, hKc, ⟨θ⟩⟩ := h
        have : Fintype K := Fintype.ofFinite K
        have hK9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hKc, hq]
        obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism K hK9
        exact ⟨(θ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans e6⟩
      · right
        right
        left
        rw [hc, hq]
        decide
      · right
        right
        right
        left
        obtain ⟨-, K, hKfield, hKfin, hKc, ⟨θ⟩⟩ := h
        exact ⟨by rw [hc, hq]; decide, K, hKfield, hKfin, hKc.trans hq, ⟨θ⟩⟩
      · right
        right
        right
        right
        left
        obtain ⟨-, K, hKfield, hKfin, hKc, ⟨θ⟩⟩ := h
        exact ⟨by rw [hc, hq]; decide, K, hKfield, hKfin, hKc.trans hq, ⟨θ⟩⟩
    ·
      rcases hn34 with rfl | rfl
      · exact absurd (by rw [hq]) hcl.2
      · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq
        obtain ⟨-, K, hKfield, hKfin, hKc, ⟨θ⟩⟩ := h
        right
        right
        right
        right
        right
        left
        exact ⟨K, hKfield, hKfin, by simpa using hKc, ⟨θ⟩⟩
    ·
      rcases hq with hq | hq
      · exact absurd (by rw [hq]) hcl.2
      · obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hq
        obtain ⟨-, K, hKfield, hKfin, hKc, ⟨θ⟩⟩ :=
          CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three h
        right
        right
        right
        right
        right
        left
        exact ⟨K, hKfield, hKfin, by simpa using hKc, ⟨θ⟩⟩
  ·
    obtain ⟨hp, hf, -⟩ := h.1
    have hc := card_eq_lieOrd_of_exceptional h
    have hts : t ∈ searchTags := by
      revert ht
      cases t <;> decide
    have hmin : lieMin t ≤ 0 := by
      revert ht
      cases t <;> simp [lieMin, chevalleyExceptionalTags]
    have hadm : lieAdm t p f = true := by
      revert ht
      cases t <;> simp [lieAdm, chevalleyExceptionalTags]
    rw [hc] at hdvd
    have hall := j3_lie_search hts hp hf hmin (by omega) hadm hdvd
    exfalso
    revert ht hall
    cases t <;> simp [J3Allowed, chevalleyExceptionalTags]
  ·
    have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht
      cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      rw [hc] at hdvd
      have hadm : lieAdm .twistedG2 3 (2 * a + 1) = true := by
        simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq]
        obtain ⟨-, -, -, -, hodd⟩ := h.1
        omega
      have hall := j3_lie_search (t := .twistedG2) (n := 0) (by decide) Nat.prime_three
        (by omega) (by simp [lieMin]) (by simp [lieExp]) hadm hdvd
      exfalso
      simp [J3Allowed] at hall
    · exact absurd ((thirteen_dvd_card_of_reeTitsModel_twistedF4 h).trans hdvd) (by norm_num)
    · exact absurd ((thirteen_dvd_card_of_reeTitsModel_Tits h).trans hdvd) (by norm_num)
  ·
    obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_suzuki h
    rw [hc] at hdvd
    have hadm : lieAdm .twistedB2 2 (2 * a + 1) = true := by
      simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      omega
    have hall := j3_lie_search (t := .twistedB2) (n := 0) (by decide) Nat.prime_two
      (by omega) (by simp [lieMin]) (by simp [lieExp]) hadm hdvd
    exfalso
    simp [J3Allowed] at hall
  ·
    have hs := sporadic_eq_j3 e hdvd
    subst hs
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))))

end CFSG.AGLEmbedding
