module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Excl

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Open

theorem sq_sub_one_eq' (q : ℕ) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · have : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      zify [Nat.one_le_pow 2 q hq, hq]
      ring
    omega

theorem pow_three_dvd_pslOrd (q : ℕ) : q ^ 3 ∣ CFSG.Quasithin.H13.L34.pslOrd q := by
  unfold CFSG.Quasithin.H13.L34.pslOrd
  have hg : Nat.gcd 3 (q - 1) ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    refine Dvd.dvd.mul_right ((Nat.gcd_dvd_right 3 (q - 1)).trans ?_) _
    exact ⟨q + 1, by rw [sq_sub_one_eq', mul_comm]⟩
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem pow_three_dvd_psuOrd (q : ℕ) : q ^ 3 ∣ CFSG.Quasithin.H13.L34.psuOrd q := by
  unfold CFSG.Quasithin.H13.L34.psuOrd
  have hg : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    refine Dvd.dvd.mul_right ((Nat.gcd_dvd_right 3 (q + 1)).trans ?_) _
    exact ⟨q - 1, sq_sub_one_eq' q⟩
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem not_card_dvd_20160_of_isPSLEps3 {X : Type} [Group X] {s : Bool} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : IsPSLEps3 s p 1 X) : ¬ Nat.card X ∣ 20160 := by
  intro hd
  have hq : CFSG.Quasithin.IsPSLEps3q s p X := ⟨p, 1, hp, le_rfl, (pow_one p).symm, h⟩
  obtain ⟨-, hcard⟩ := CFSG.Quasithin.H13.L34.card_of_isPSLEps3q hq
  have h3 : p ^ 3 ∣ Nat.card X := by
    rw [hcard]
    cases s
    · exact pow_three_dvd_psuOrd p
    · exact pow_three_dvd_pslOrd p
  have := CFSG.RankThree.PartOne.SectionalRank.le_two_of_prime_pow_dvd_20160 hp hp2
    (h3.trans hd)
  omega

theorem kg614FusionL3_gen4 :
    ∀ (Γ : Type) [Group Γ] [Finite Γ], Gen4 Γ → quasithinEvenCharacteristic Γ →
      ∀ (K T X M₁ : Subgroup Γ), quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M₁ → T ≤ M₁ →
      K ∈ cComp M₁ →
      CFSG.IsQuasisimple (ModO2 K) →
      (∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
        IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K))) →
      T ≤ Subgroup.normalizer (K : Set Γ) → CFSG.QuasithinUnique.IsSylowTwoOf T (K ⊔ T) →
      X ≤ K → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
      T ≤ Subgroup.normalizer (X : Set Γ) →
      ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
      ∀ E : Subgroup Γ, E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → ¬ E ≤ pCoreOf 2 (K ⊔ T) →
        ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
          ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T) := by
  intro Γ _ _ hΓ hEven K T X M₁ hT hM₁ hTM hK hq ⟨δ, p, hp, hp2, hX⟩ _ _ _ _ _ _ _ _ E _ _ _
  exfalso
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hd := modO2_dvd_of_cComp_of_le hΓ hEven P hM₁.1 hTM hK
  exact not_card_dvd_20160_of_isPSLEps3 hp hp2 hX
    ((Subgroup.card_quotient_dvd_card _).trans hd)

end CFSG.GH74.QTGen4
