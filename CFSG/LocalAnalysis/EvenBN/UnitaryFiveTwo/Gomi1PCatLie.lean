module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PIdentGG
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.EvenSmallLie.CatalogOrders CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem not_alternating_of_dvd {n : ℕ} (hdvd : 979200 ∣ n.factorial / 2)
    (hv : ¬ 2 ^ 9 ∣ n.factorial / 2) (hn : 2 ≤ n) : False := by
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) hn
  have he : n.factorial = 2 * (n.factorial / 2) := (Nat.mul_div_cancel' h2).symm
  have h17 : 17 ∣ n.factorial / 2 := (show 17 ∣ 979200 by norm_num).trans hdvd
  have h17' : 17 ∣ n.factorial := h17.trans (Nat.div_dvd_of_dvd h2)
  have hn17 : 17 ≤ n := (Nat.Prime.dvd_factorial (by norm_num)).1 h17'
  have h10 : 2 ^ 10 ∣ n.factorial :=
    (show 2 ^ 10 ∣ (17).factorial by decide).trans (Nat.factorial_dvd_factorial hn17)
  apply hv
  rw [he, show 2 ^ 10 = 2 * 2 ^ 9 by norm_num] at h10
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h10

@[expose] def charTwoGood (t : StatedLieTag) (n f : ℕ) : Bool :=
  !(decide (lieMin t ≤ n) && decide (f * lieExp t n ≤ 8) &&
      (lieOrd t n (2 ^ f) % 979200 == 0)) ||
    (lieOrd t n (2 ^ f) % 2 ^ 9 == 0) || (lieOrd t n (2 ^ f) == 979200)

theorem charTwoGood_all : ∀ t ∈ [StatedLieTag.PSL, .PSU, .PSp, .POmegaPlus, .POmegaMinus],
    ∀ f ∈ List.range 9, ∀ n ∈ List.range 10, charTwoGood t n f = true := by
  decide +kernel

theorem classical_two_aux {t : StatedLieTag} {n f N : ℕ} (hts : t ∈ searchTags)
    (htc : t ∈ [StatedLieTag.PSL, .PSU, .PSp, .POmegaPlus, .POmegaMinus]) (hf1 : 1 ≤ f)
    (hmin : lieMin t ≤ n) (hnB : n ≤ lieExp t n + 1) (hc : N = lieOrd t n (2 ^ f))
    (hdvd : 979200 ∣ N) (hv : ¬ 2 ^ 9 ∣ N) : N = 979200 := by
  have hdiv : (2 ^ f) ^ lieExp t n ∣ N := hc ▸ pow_lieExp_dvd hmin (2 ^ f)
  have hfe : f * lieExp t n ≤ 8 := by
    by_contra hlt
    push Not at hlt
    apply hv
    refine (pow_dvd_pow 2 hlt).trans ?_
    rw [pow_mul]; exact hdiv
  have he := one_le_lieExp hts hmin
  have hle : lieExp t n ≤ f * lieExp t n := Nat.le_mul_of_pos_left _ hf1
  have hfle : f ≤ f * lieExp t n := Nat.le_mul_of_pos_right _ he
  have hg := charTwoGood_all t htc f (List.mem_range.2 (by omega)) n
    (List.mem_range.2 (by omega))
  have hdvd' : lieOrd t n (2 ^ f) % 979200 = 0 := by
    rw [← hc]; exact Nat.mod_eq_zero_of_dvd hdvd
  have hv' : ¬ lieOrd t n (2 ^ f) % 2 ^ 9 = 0 := by
    rw [← hc]; exact fun h0 => hv (Nat.dvd_of_mod_eq_zero h0)
  simp only [charTwoGood, hmin, hfe, hdvd', hv', decide_true, Bool.true_and, beq_self_eq_true,
    Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hg
  rcases hg with hg | hg
  · exact absurd hg (by simp)
  · rw [hc]; exact hg

theorem classical_two_card {T : Type} [Group T] {t : StatedLieTag} {n f : ℕ}
    (h : StatedClassicalModel T t n 2 f) (hdvd : 979200 ∣ Nat.card T)
    (hv : ¬ 2 ^ 9 ∣ Nat.card T) : Nat.card T = 979200 := by
  have hc := card_eq_lieOrd_of_classical h
  obtain ⟨-, hf1, hadm⟩ := h.1
  cases t
  case PSL =>
    have hmin : lieMin .PSL ≤ n := hadm.1
    exact classical_two_aux (by decide) (by simp) hf1 hmin
      (le_lieExp_add_one hmin (by simp)) hc hdvd hv
  case PSU =>
    have hmin : lieMin .PSU ≤ n := hadm.1
    exact classical_two_aux (by decide) (by simp) hf1 hmin
      (le_lieExp_add_one hmin (by simp)) hc hdvd hv
  case PSp =>
    have hmin : lieMin .PSp ≤ n := hadm.1
    exact classical_two_aux (by decide) (by simp) hf1 hmin
      (le_lieExp_add_one hmin (by simp)) hc hdvd hv
  case POmegaOdd => exact absurd rfl hadm.2
  case POmegaPlus =>
    have hmin : lieMin .POmegaPlus ≤ n := hadm
    exact classical_two_aux (by decide) (by simp) hf1 hmin
      (le_lieExp_add_one hmin (by simp)) hc hdvd hv
  case POmegaMinus =>
    have hmin : lieMin .POmegaMinus ≤ n := hadm
    exact classical_two_aux (by decide) (by simp) hf1 hmin
      (le_lieExp_add_one hmin (by simp)) hc hdvd hv
  all_goals exact h.2.elim

theorem not_exceptional_two
    {T : Type} [Group T] {t : StatedLieTag} {f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel T t 2 f) (hv : ¬ 2 ^ 9 ∣ Nat.card T) : False := by
  have hc := card_eq_lieOrd_of_exceptional h
  obtain ⟨-, hf1, hadm⟩ := h.1
  have hmin : lieMin t ≤ 0 := by
    revert ht; cases t <;> simp [lieMin, chevalleyExceptionalTags]
  have hdiv : (2 ^ f) ^ lieExp t 0 ∣ Nat.card T := hc ▸ pow_lieExp_dvd hmin (2 ^ f)
  have h9 : 9 ≤ f * lieExp t 0 := by
    cases t
    case G2 =>
      have h3 : 3 ≤ 2 ^ f := hadm.2
      have hf2 : 2 ≤ f := by
        by_contra hlt
        have : f = 1 := by omega
        subst this
        norm_num at h3
      simp only [lieExp]
      omega
    all_goals first
      | (simp only [lieExp]; omega)
      | (exfalso; revert ht; decide)
  apply hv
  refine (pow_dvd_pow 2 h9).trans ?_
  rw [pow_mul]; exact hdiv

theorem not_suzuki {T : Type} [Group T] [Finite T] {p f : ℕ}
    (h : SuzukiModel T p f) (hdvd : 979200 ∣ Nat.card T) (hv : ¬ 2 ^ 9 ∣ Nat.card T) :
    False := by
  have hp : p = 2 := h.1
  subst hp
  obtain ⟨hfac, hodd⟩ := factorization_two_card_Suzuki h
  have hN0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have h8 : 2 ^ 8 ∣ Nat.card T := (show 2 ^ 8 ∣ 979200 by norm_num).trans hdvd
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 h8
  have h2 : ¬ 9 ≤ (Nat.card T).factorization 2 := fun h9 =>
    hv ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).2 h9)
  obtain ⟨k, hk⟩ := hodd
  omega

theorem not_twistedF4
    {T : Type} [Group T] {p f : ℕ} (h : ReeTitsModel T .twistedF4 p f)
    (hv : ¬ 2 ^ 9 ∣ Nat.card T) : False := by
  have hp : p = 2 := h.1.2.2.2.1
  subst hp
  have hf3 : 3 ≤ f := h.1.2.2.2.2.2
  have hc := CFSG.ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 h
  apply hv
  rw [hc, ordTwistedF4]
  refine Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _) _) _
  rw [← pow_mul]
  exact pow_dvd_pow 2 (by omega)

theorem not_tits
    {T : Type} [Group T] {p f : ℕ} (h : ReeTitsModel T .Tits p f)
    (hdvd : 979200 ∣ Nat.card T) : False := by
  obtain ⟨⟨-, -, -, hp, hf1⟩, a, hf, hmodel⟩ := h
  subst hp hf1
  obtain rfl : a = 0 := by omega
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.EvenSmallLie.CatalogOrders.exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  rw [pow_one] at hK
  rw [Nat.card_congr (e.trans ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK)).trans
      QuotientGroup.quotientBot)).toEquiv] at hdvd
  have hcard := CFSG.SectionRank.TitsOrder.Tits_card hK
  have : Finite (reeFixed ReeTag.F4 K 0) := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have h1 : Nat.card (commutator (reeFixed ReeTag.F4 K 0)) ∣ Nat.card (reeFixed ReeTag.F4 K 0) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard] at h1
  have h17 := (show 17 ∣ 979200 by norm_num).trans (hdvd.trans h1)
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
