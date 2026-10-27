module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10SpCard

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

theorem gcd_four_of_mod_three {q : ℕ} (hq : q % 4 = 3) :
    Nat.gcd 4 (q - 1) = 2 ∧ Nat.gcd 4 (q + 1) = 4 := by
  constructor
  · rw [Nat.gcd_rec, show (q - 1) % 4 = 2 by omega]
    rfl
  · rw [Nat.gcd_rec, show (q + 1) % 4 = 0 by omega]
    rfl

theorem gcd_four_of_mod_one {q : ℕ} (hq : q % 4 = 1) :
    Nat.gcd 4 (q - 1) = 4 ∧ Nat.gcd 4 (q + 1) = 2 := by
  constructor
  · rw [Nat.gcd_rec, show (q - 1) % 4 = 0 by omega]
    rfl
  · rw [Nat.gcd_rec, show (q + 1) % 4 = 2 by omega]
    rfl

theorem card_psl4 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2) (h : LieModel X .PSL 4 p f) :
    Nat.card X * Nat.gcd 4 (p ^ f - 1) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) := by
  have h1 := (CatLeafProof.X10Sp.lieOrder_of_lieModel (Or.inl rfl) hp2 (by norm_num) h).1
  simp only [lieOrderDivisor, lieOrderNumerator] at h1
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at h1
  rw [h1]
  norm_num
  ring

theorem card_psu4 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2) (h : LieModel X .PSU 4 p f) :
    Nat.card X * Nat.gcd 4 (p ^ f + 1) =
      (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
  have h1 := (CatLeafProof.X10Sp.lieOrder_of_lieModel (Or.inr (Or.inl rfl)) hp2 (by norm_num)
    h).1
  simp only [lieOrderDivisor, lieOrderNumerator] at h1
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton] at h1
  rw [h1]
  norm_num [Nat.even_iff]
  ring

theorem card_le_of_l4u4 {S X : Type} [Group S] [Group X] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hX : (p ^ f % 4 = 3 ∧ LieModel X .PSL 4 p f) ∨ (p ^ f % 4 = 1 ∧ LieModel X .PSU 4 p f))
    (hS : LieModel S .PSL 4 p f ∨ LieModel S .PSU 4 p f) : Nat.card S ≤ Nat.card X := by
  have hq3 : 3 ≤ p ^ f :=
    le_trans (by have := hp.two_le; omega) (Nat.le_self_pow (by omega) p)
  have h27 : 27 ≤ (p ^ f) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
  rcases hX with ⟨h3, hX⟩ | ⟨h1, hX⟩
  · obtain ⟨g1, g2⟩ := gcd_four_of_mod_three h3
    have eX := card_psl4 hp2 hX
    rw [g1] at eX
    rcases hS with hS | hS
    · have eS := card_psl4 hp2 hS
      rw [g1] at eS
      omega
    · have eS := card_psu4 hp2 hS
      rw [g2] at eS
      have hb : (p ^ f) ^ 3 + 1 ≤ 2 * ((p ^ f) ^ 3 - 1) := by omega
      have : Nat.card S * 4 ≤ Nat.card X * 4 :=
        calc Nat.card S * 4
            = (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := eS
          _ ≤ (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * (2 * ((p ^ f) ^ 3 - 1)) * ((p ^ f) ^ 4 - 1) := by
            gcongr
          _ = 2 * ((p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)) := by
            ring
          _ = Nat.card X * 4 := by rw [← eX]; ring
      omega
  · obtain ⟨g1, g2⟩ := gcd_four_of_mod_one h1
    have eX := card_psu4 hp2 hX
    rw [g2] at eX
    rcases hS with hS | hS
    · have eS := card_psl4 hp2 hS
      rw [g1] at eS
      have hb : (p ^ f) ^ 3 - 1 ≤ 2 * ((p ^ f) ^ 3 + 1) := by omega
      have : Nat.card S * 4 ≤ Nat.card X * 4 :=
        calc Nat.card S * 4
            = (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) := eS
          _ ≤ (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * (2 * ((p ^ f) ^ 3 + 1)) * ((p ^ f) ^ 4 - 1) := by
            gcongr
          _ = 2 * ((p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1)) := by
            ring
          _ = Nat.card X * 4 := by rw [← eX]; ring
      omega
    · have eS := card_psu4 hp2 hS
      rw [g2] at eS
      omega

theorem false_of_card_le_quotient {S : Type} [Group S] [Finite S] {P : Subgroup S} (hP : P ≠ ⊤)
    (h : Nat.card S ≤ Nat.card (P ⧸ pPrimeCore 2 P)) : False := by
  have h1 : Nat.card (P ⧸ pPrimeCore 2 P) ≤ Nat.card P :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have h2 : Nat.card P ≤ Nat.card S := Subgroup.card_le_card_group P
  exact hP ((Subgroup.card_eq_iff_eq_top P).mp (by omega))

end CFSG.ComponentClassification.GSThmB.Pump516
