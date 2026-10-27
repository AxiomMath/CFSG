module

public import Certificates.Certificate25280
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.Blueprint

theorem factorial_div_two_ne_card_M24 {n : ℕ} (hn : 5 ≤ n) : n.factorial / 2 ≠ 244823040 := by
  intro h
  by_cases h13 : 13 ≤ n
  · have h1 := Nat.factorial_le h13
    have h2 : (13 : ℕ).factorial = 6227020800 := by decide
    omega
  · interval_cases n <;> revert h <;> decide

theorem mem_primes_of_prime_dvd_card_M24 {q : ℕ} (hq : q.Prime) (hd : q ∣ 244823040) :
    q ∈ [2, 3, 5, 7, 11, 23] := by
  have key : ∀ a e : ℕ, a.Prime → q ∣ a ^ e → q = a := fun a e ha h =>
    (Nat.prime_dvd_prime_iff_eq hq ha).1 (hq.dvd_of_dvd_pow h)
  rw [show (244823040 : ℕ) = 2 ^ 10 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1 * 23 ^ 1 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
        · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
          · simp [key 2 10 Nat.prime_two hd]
          · simp [key 3 3 Nat.prime_three hd]
        · simp [key 5 1 Nat.prime_five hd]
      · simp [key 7 1 (by norm_num) hd]
    · simp [key 11 1 (by norm_num) hd]
  · simp [key 23 1 (by norm_num) hd]

theorem card_eq_of_mulEquiv_zmod {X : Type} [Group X] {p : ℕ} [NeZero p]
    (e : X ≃* Multiplicative (ZMod p)) : Nat.card X = p := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem lieOrd_ne_card_M24 {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hmin : lieMin t ≤ n)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true) :
    lieOrd t n (p ^ f) ≠ 244823040 := by
  intro h
  have hN : (244823040 : ℕ) ≠ 0 := by norm_num
  have hS := lieSearch_sound hN (fun _ hq hd => mem_primes_of_prime_dvd_card_M24 hq hd)
    Certificates.certificate25280 ht hp hf hmin hnB hadm (h ▸ dvd_rfl)
  simp [h] at hS

section


theorem false_of_catalog_not_sporadic
    {X : Type} [Group X] (hX : Catalog X) (hns : ¬ NativeSporadic.SporadicRep X)
    (hord : Nat.card X = 244823040) : False := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  rcases hX with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, h⟩ |
      (⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩) | hs
  · have : NeZero p := ⟨hp.ne_zero⟩
    rw [card_eq_of_mulEquiv_zmod e] at hord
    exact absurd (hord ▸ hp) (by norm_num)
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hord
    exact factorial_div_two_ne_card_M24 hn hord
  · obtain ⟨hp, hf, hcl⟩ := h.1
    have hc := (card_eq_lieOrd_of_classical h).symm.trans hord
    cases t
    case PSL =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl.1
        (le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl))) rfl hc
    case PSU =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl.1
        (le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl)))) rfl hc
    case PSp =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc
    case POmegaOdd =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc
    case POmegaPlus =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl (le_lieExp_add_one hcl (by simp)) rfl hc
    case POmegaMinus =>
      exact lieOrd_ne_card_M24 (by decide) hp hf hcl (le_lieExp_add_one hcl (by simp)) rfl hc
    all_goals exact h.2.elim
  · obtain ⟨hp, hf, -⟩ := h.1
    have hc := (card_eq_lieOrd_of_exceptional h).symm.trans hord
    have hts : t ∈ searchTags := by
      revert ht; cases t <;> decide
    have hmin : lieMin t ≤ 0 := by
      revert ht; cases t <;> simp [lieMin, chevalleyExceptionalTags]
    have hadm : lieAdm t p f = true := by
      revert ht; cases t <;> simp [lieAdm, chevalleyExceptionalTags]
    exact lieOrd_ne_card_M24 hts hp hf hmin (by omega) hadm hc
  · have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      refine lieOrd_ne_card_M24 (t := .twistedG2) (n := 0) (by decide) Nat.prime_three
        (by omega) le_rfl (by omega) ?_ (hc.symm.trans hord)
      simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq]
      omega
    · have h13 := thirteen_dvd_card_of_reeTitsModel_twistedF4 h
      rw [hord] at h13
      exact absurd h13 (by norm_num)
    · have h13 := thirteen_dvd_card_of_reeTitsModel_Tits h
      rw [hord] at h13
      exact absurd h13 (by norm_num)
  · obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_suzuki h
    refine lieOrd_ne_card_M24 (t := .twistedB2) (n := 0) (by decide) Nat.prime_two
      (by omega) le_rfl (by omega) ?_ (hc.symm.trans hord)
    simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega
  · exact hns hs

end

end CFSG.EvenSporadicStandard.TwoFi22.DS81
