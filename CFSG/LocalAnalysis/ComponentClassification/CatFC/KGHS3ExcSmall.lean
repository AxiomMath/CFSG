module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Arms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ArithRest
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.EvenSmallLie.CatalogOrders

theorem three_not_dvd_ordSuzuki {f : ℕ} (hf : Odd f) : ¬ 3 ∣ ordSuzuki (2 ^ f) := by
  have hq : 2 ^ f % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hf
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ f) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq] <;> norm_num
  have hpos : 0 < 2 ^ f := pow_pos (by norm_num) f
  unfold ordSuzuki
  intro h
  rcases Nat.prime_three.dvd_mul.mp h with h1 | h1
  · rcases Nat.prime_three.dvd_mul.mp h1 with h2 | h2
    · have h4 := Nat.prime_three.dvd_of_dvd_pow h2
      omega
    · omega
  · omega



theorem no_hsType_chevalley_large {S : Type} [Group S] [Finite S] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .twistedE6 ∨ t = .E7 ∨ t = .E8) (hp3 : p ≠ 3)
    (h3 : (Nat.card S).factorization 3 ≤ 4) (hM : ChevalleyExceptionalModel S t p f)
    (K : Subgroup S) (hK : HSType ↥K) : False := by
  have hcard : Nat.card S = lieOrd t 0 (p ^ f) := card_eq_lieOrd_of_exceptional hM
  obtain ⟨⟨hpp, -, -⟩, -⟩ := hM
  have hq3 : ¬ 3 ∣ p ^ f := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have h35 : 3 ^ 5 ∣ Nat.card S := by
    rw [hcard]
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact three_pow_five_dvd_ordF4 hq3
    · exact three_pow_five_dvd_ordE6 hq3
    · exact three_pow_five_dvd_ordTwistedE6 hq3
    · exact three_pow_five_dvd_ordE7 hq3
    · exact three_pow_five_dvd_ordE8 hq3
  exact false_of_three_pow_five_dvd h3 h35

theorem no_hsType_reeTits {S : Type} [Group S] [Finite S] {t : StatedLieTag} {p f : ℕ}
    (ht : t = .twistedF4 ∨ t = .Tits) (h3 : (Nat.card S).factorization 3 ≤ 4)
    (hM : ReeTitsModel S t p f) (K : Subgroup S) (hK : HSType ↥K) : False := by
  have h44 : 44352000 ∣ Nat.card S := hK.dvd_card
  have h7 : 7 ∣ Nat.card S := (by norm_num : (7 : ℕ) ∣ 44352000).trans h44
  rcases ht with rfl | rfl
  · have hadm := hM.1
    obtain ⟨-, -, -, hp2, hodd, -⟩ := hadm
    subst hp2
    have hc : Nat.card S = ordTwistedF4 (2 ^ f) :=
      CFSG.ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 hM
    rw [hc] at h7
    rcases not_seven_dvd_or_three_pow_five_dvd_ordTwistedF4 hodd with h | h
    · exact h h7
    · exact false_of_three_pow_five_dvd h3 (by rw [hc]; exact h)
  · exact CFSG.EvenSmallLie.Child3.not_seven_dvd_of_reeTitsModel_Tits hM h7

theorem no_hsType_suzuki {S : Type} [Group S] [Finite S] {p f : ℕ} (hM : SuzukiModel S p f)
    (K : Subgroup S) (hK : HSType ↥K) : False := by
  obtain ⟨hp, ⟨a, -, hf⟩, hcard⟩ := card_eq_lieOrd_of_suzuki hM
  subst hp
  have hcard' : Nat.card S = ordSuzuki (2 ^ f) := hcard
  have h3 : 3 ∣ Nat.card S := (by norm_num : (3 : ℕ) ∣ 44352000).trans hK.dvd_card
  rw [hcard'] at h3
  exact three_not_dvd_ordSuzuki ⟨a, hf⟩ h3

end CFSG.ComponentClassification.CatFC.KGHS3
