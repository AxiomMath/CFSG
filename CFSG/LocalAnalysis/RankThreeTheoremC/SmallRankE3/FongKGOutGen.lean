module

public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofRed
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

theorem isCyclic_of_comparable_finite {G : Type*} [Group G] [Finite G]
    (h : ∀ a b : G, a ∈ Subgroup.zpowers b ∨ b ∈ Subgroup.zpowers a) : IsCyclic G := by
  have : Nonempty G := ⟨1⟩
  obtain ⟨g, hg⟩ := Finite.exists_max (fun x : G => orderOf x)
  refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨g, ?_⟩
  rw [Subgroup.eq_top_iff']
  intro x
  rcases h x g with hx | hx
  · exact hx
  · have hle : orderOf x ≤ orderOf g := hg x
    have hsub : Subgroup.zpowers g ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hx
    have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers, Nat.card_zpowers]
      exact hle
    have heq : Subgroup.zpowers g = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hsub hcard
    rw [heq]
    exact Subgroup.mem_zpowers x

theorem card_dvd_outer_of_inf_eq_bot {X : Type*} [Group X] [Finite X]
    {P : Subgroup (MulAut X)} (hPI : P ⊓ (MulAut.conj : X →* MulAut X).range = ⊥) :
    Nat.card P ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := by
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).comp
        P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hp
    have hmem : (p : MulAut X) ∈ P ⊓ (MulAut.conj : X →* MulAut X).range := ⟨p.2, hp⟩
    rw [hPI, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact Subgroup.card_dvd_of_injective _ hinj

theorem outTwoCyclic_of_outPNice_two {X : Type*} [Group X] [Finite X] (h : OutPNice 2 X) :
    OutTwoCyclic X := by
  obtain ⟨D, E, -, hD2, hpE, -, hcmp⟩ := h
  intro P hP hPI
  have hPI' : P ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X = ⊥ := hPI
  have hpow : ∀ w ∈ P, ∃ k : ℕ, w ^ (2 ^ k) = 1 := by
    intro w hw
    obtain ⟨k, hk⟩ := hP ⟨w, hw⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hDk : ∀ w ∈ P, ∃ k : ℕ, w ^ (2 ^ k) ∈ D := by
    intro w hw
    obtain ⟨k, hk⟩ := hpow w hw
    exact ⟨k, by rw [hk]; exact D.one_mem⟩
  have hPE : ∀ w ∈ P, w ∈ E := fun w hw => hpE w (hDk w hw)
  have hPD : ∀ w ∈ P, w ∈ D → w = 1 := by
    intro w hwP hwD
    obtain ⟨k, hk⟩ := hpow w hwP
    have hwI : w ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      hD2 w hwD k (by rw [hk]; exact Subgroup.one_mem _)
    have hmem : w ∈ P ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
      ⟨hwP, hwI⟩
    rw [hPI', Subgroup.mem_bot] at hmem
    exact hmem
  refine isCyclic_of_comparable_finite ?_
  intro a b
  rcases hcmp a.1 (hPE a.1 a.2) b.1 (hPE b.1 b.2) (hDk a.1 a.2) (hDk b.1 b.2) with
    ⟨m, hm⟩ | ⟨m, hm⟩
  · have h1 : a.1 * b.1 ^ m = 1 := hPD _ (P.mul_mem a.2 (P.zpow_mem b.2 m)) hm
    left
    refine Subgroup.mem_zpowers_iff.mpr ⟨-m, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  · have h1 : b.1 * a.1 ^ m = 1 := hPD _ (P.mul_mem b.2 (P.zpow_mem a.2 m)) hm
    right
    refine Subgroup.mem_zpowers_iff.mpr ⟨-m, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, zpow_neg]
    exact (eq_inv_of_mul_eq_one_left h1).symm

theorem outTwoCyclic_of_not_four_dvd_card_outer {X : Type*} [Group X] [Finite X]
    (h : ¬ 4 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    OutTwoCyclic X := by
  intro P hP hPI
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hdvd := card_dvd_outer_of_inf_eq_bot hPI
  rw [hk] at hdvd
  have hk1 : k ≤ 1 := by
    by_contra hcon
    have h2k : 2 ≤ k := by omega
    have h4 : (4 : ℕ) ∣ 2 ^ k := by
      have h22 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h22]
      exact pow_dvd_pow 2 h2k
    exact h (dvd_trans h4 hdvd)
  interval_cases k
  · exact isCyclic_of_orderOf_eq_card (1 : ↥P) (by simp [hk])
  · exact isCyclic_of_prime_card (p := 2) (by simpa using hk)

theorem outTwoCyclic_of_noKlein_of_card_outer_le_four {X : Type} [Group X] [Finite X]
    (hK : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.NoKlein X)
    (hc : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 4) :
    OutTwoCyclic X := by
  intro P hP hPI
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    Nat.card_pos
  have hle : Nat.card P ≤ 4 :=
    le_trans (Nat.le_of_dvd hpos (card_dvd_outer_of_inf_eq_bot hPI)) hc
  rw [hk] at hle
  have hk2 : k ≤ 2 := by
    by_contra hcon
    have h8 : 8 ≤ 2 ^ k := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k
  · exact isCyclic_of_orderOf_eq_card (1 : ↥P) (by simp [hk])
  · exact isCyclic_of_prime_card (p := 2) (by simpa using hk)
  · by_cases hcyc : IsCyclic ↥P
    · exact hcyc
    exfalso
    have hcard : Nat.card P = 4 := by simpa using hk
    have hsq' : ∀ x : P, x ^ 2 = 1 := by
      intro x
      have h4 : orderOf x ∣ 4 := by
        have h := orderOf_dvd_natCard x
        rwa [hcard] at h
      have hne : orderOf x ≠ 4 := fun h => hcyc (isCyclic_of_orderOf_eq_card x (by rw [h, hcard]))
      have hle4 : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) h4
      have hpos4 : 0 < orderOf x := orderOf_pos x
      have hdiv2 : orderOf x ∣ 2 := by
        have hcases : orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 4 := by
          omega
        rcases hcases with h1 | h1 | h1 | h1
        · simp [h1]
        · simp [h1]
        · norm_num [h1] at h4
        · exact absurd h1 hne
      exact orderOf_dvd_iff_pow_eq_one.mp hdiv2
    have hsq : ∀ a ∈ P, a * a = 1 := by
      intro a ha
      have h := hsq' ⟨a, ha⟩
      rw [pow_two] at h
      exact congrArg Subtype.val h
    have hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
      intro a ha b hb
      have h1 : (a * b)⁻¹ = a * b :=
        inv_eq_of_mul_eq_one_right (hsq (a * b) (P.mul_mem ha hb))
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq a ha),
        inv_eq_of_mul_eq_one_right (hsq b hb)] at h1
      exact h1.symm
    exact (hK P hcomm hsq hcard) hPI

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
