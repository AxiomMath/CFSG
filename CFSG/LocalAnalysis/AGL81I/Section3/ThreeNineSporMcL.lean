module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporOrder
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftMcLLocal

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.ComponentClassification.OuterAutomorphisms

theorem false_of_mcl
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}
    (h : ThreeNineHyp K E D X₁ 5 d)
    (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .McL) : False := by
  obtain ⟨e⟩ := hs
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.McL.isSimpleGroup_McL e
  have hcK : Nat.card ↥K = 898128000 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL
  have hZ : Subgroup.center ↥K = ⊥ :=
    SporCent.center_eq_bot_of_not_prime (by rw [hcK]; norm_num)
  have hO : Nat.card (Outer ↥K) ≤ 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  have hO0 : 0 < Nat.card (Outer ↥K) := Nat.card_pos
  have hdp := h.d_prime
  have houtd : ¬ d ∣ Nat.card (Outer ↥K) := fun hd => by
    have := Nat.le_of_dvd hO0 hd
    have := hdp.two_le
    exact h.d_ne_two (by omega)
  have hmax : ∀ S : Sylow 5 ↥K, ∀ H : Subgroup ↥K,
      Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) ≤ H →
        H = Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) ∨ H = ⊤ := by
    intro S H hH
    have hco := (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift.isCoatom_normalizer_sylow_five_mcl
      (e.trans eC) S).1
    rcases eq_or_lt_of_le hH with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr (hco.2 _ h1)
  obtain ⟨S, hS⟩ := h.exists_sylow_subgroupOf_eq_normalizer hZ
    (fun h5 => by have := Nat.le_of_dvd hO0 h5; omega) hmax
  have hcN := (CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift.isCoatom_normalizer_sylow_five_mcl
    (e.trans eC) S).2
  obtain ⟨hd1, hd2⟩ := h.dvd_card_of_subgroupOf_le (h.D_le_K_of_not_dvd hZ houtd) hS.le
  rw [hcN] at hd1 hd2
  have hd3 : d = 3 := by
    have h' : d ∣ 2 ^ 3 * (3 * 5 ^ 3) := by norm_num; exact hd1
    rcases hdp.dvd_mul.1 h' with h2 | h35
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_two).1 (hdp.dvd_of_dvd_pow h2))
        h.d_ne_two
    · rcases hdp.dvd_mul.1 h35 with h3 | h5
      · exact (Nat.prime_dvd_prime_iff_eq hdp Nat.prime_three).1 h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hdp Nat.prime_five).1 (hdp.dvd_of_dvd_pow h5))
          h.d_ne
  subst hd3
  rw [hcK, SporCent.factorization_eq_of_pow_dvd (e := 6) Nat.prime_three (by norm_num)
    (by norm_num) (by norm_num)] at hd2
  norm_num at hd2

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp
