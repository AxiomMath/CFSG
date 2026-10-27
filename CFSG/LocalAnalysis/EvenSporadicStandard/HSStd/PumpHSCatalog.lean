module

public import Certificates.Certificate27264
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCatSpor
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpHS

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.Blueprint

theorem factorial_div_two_ne_card_HS {n : ℕ} (hn : 5 ≤ n) : n.factorial / 2 ≠ 44352000 := by
  intro h
  by_cases h12 : 12 ≤ n
  · have h1 := Nat.factorial_le h12
    have h2 : (12 : ℕ).factorial = 479001600 := by decide
    omega
  · interval_cases n <;> revert h <;> decide

theorem mem_primes_of_prime_dvd_card_HS {q : ℕ} (hq : q.Prime) (hd : q ∣ 44352000) :
    q ∈ [2, 3, 5, 7, 11] := by
  have key : ∀ a e : ℕ, a.Prime → q ∣ a ^ e → q = a := fun a e ha h =>
    (Nat.prime_dvd_prime_iff_eq hq ha).1 (hq.dvd_of_dvd_pow h)
  rw [show (44352000 : ℕ) = 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 ^ 1 * 11 ^ 1 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
        · simp [key 2 9 Nat.prime_two hd]
        · simp [key 3 2 Nat.prime_three hd]
      · simp [key 5 3 Nat.prime_five hd]
    · simp [key 7 1 (by norm_num) hd]
  · simp [key 11 1 (by norm_num) hd]

theorem card_eq_of_mulEquiv_zmod_HS {X : Type} [Group X] {p : ℕ} [NeZero p]
    (e : X ≃* Multiplicative (ZMod p)) : Nat.card X = p := by
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem lieOrd_ne_card_HS {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ searchTags) (hp : p.Prime) (hf : 1 ≤ f) (hmin : lieMin t ≤ n)
    (hnB : n ≤ lieExp t n + 1) (hadm : lieAdm t p f = true) :
    lieOrd t n (p ^ f) ≠ 44352000 := by
  intro h
  have hN : (44352000 : ℕ) ≠ 0 := by norm_num
  have hS := lieSearch_sound hN (fun _ hq hd => mem_primes_of_prime_dvd_card_HS hq hd)
    Certificates.certificate27264 ht hp hf hmin hnB hadm (h ▸ dvd_rfl)
  simp [h] at hS

section


theorem false_of_catalog_not_sporadic_HS
    {X : Type} [Group X] (hX : Catalog X) (hns : ¬ NativeSporadic.SporadicRep X)
    (hord : Nat.card X = 44352000) : False := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  rcases hX with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, h⟩ |
      (⟨t, p, f, ht, h⟩ | ⟨t, p, f, ht, h⟩ | ⟨p, f, h⟩) | hs
  · have : NeZero p := ⟨hp.ne_zero⟩
    rw [card_eq_of_mulEquiv_zmod_HS e] at hord
    exact absurd (hord ▸ hp) (by norm_num)
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at hord
    exact factorial_div_two_ne_card_HS hn hord
  · obtain ⟨hp, hf, hcl⟩ := h.1
    have hc := (card_eq_lieOrd_of_classical h).symm.trans hord
    cases t
    case PSL =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl.1
        (le_lieExp_add_one hcl.1 (Or.inr (Or.inl rfl))) rfl hc
    case PSU =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl.1
        (le_lieExp_add_one hcl.1 (Or.inr (Or.inr (Or.inl rfl)))) rfl hc
    case PSp =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc
    case POmegaOdd =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl.1 (le_lieExp_add_one hcl.1 (by simp)) rfl hc
    case POmegaPlus =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl (le_lieExp_add_one hcl (by simp)) rfl hc
    case POmegaMinus =>
      exact lieOrd_ne_card_HS (by decide) hp hf hcl (le_lieExp_add_one hcl (by simp)) rfl hc
    all_goals exact h.2.elim
  · obtain ⟨hp, hf, -⟩ := h.1
    have hc := (card_eq_lieOrd_of_exceptional h).symm.trans hord
    have hts : t ∈ searchTags := by
      revert ht; cases t <;> decide
    have hmin : lieMin t ≤ 0 := by
      revert ht; cases t <;> simp [lieMin, chevalleyExceptionalTags]
    have hadm : lieAdm t p f = true := by
      revert ht; cases t <;> simp [lieAdm, chevalleyExceptionalTags]
    exact lieOrd_ne_card_HS hts hp hf hmin (by omega) hadm hc
  · have htt : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> simp [reeTitsTags]
    rcases htt with rfl | rfl | rfl
    · obtain ⟨rfl, ⟨a, ha, rfl⟩, hc⟩ := card_eq_lieOrd_of_ree h
      refine lieOrd_ne_card_HS (t := .twistedG2) (n := 0) (by decide) Nat.prime_three
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
    refine lieOrd_ne_card_HS (t := .twistedB2) (n := 0) (by decide) Nat.prime_two
      (by omega) le_rfl (by omega) ?_ (hc.symm.trans hord)
    simp only [lieAdm, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    omega
  · exact hns hs

end


theorem isSporadic_HS_of_catalog {X : Type} [Group X] (hX : Catalog X)
    (hord : Nat.card X = 44352000) : NativeSporadic.IsSporadic X .HS := by
  by_cases hs : NativeSporadic.SporadicRep X
  · obtain ⟨s, ⟨e⟩⟩ := hs
    have hs24 := eq_HS_of_card_carrier (s := s) ((Nat.card_congr e.toEquiv).symm.trans hord)
    subst hs24
    exact ⟨e⟩
  · exact (false_of_catalog_not_sporadic_HS hX hs hord).elim

end CFSG.EvenSporadicStandard.HSStd.PumpHS
