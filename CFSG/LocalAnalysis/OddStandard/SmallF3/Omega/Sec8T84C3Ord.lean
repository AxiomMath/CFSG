module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C3Per
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

theorem card_sup_mul_card_inf_of_le_normalizer {Γ : Type} [Group Γ] [Finite Γ]
    {A B : Subgroup Γ} (h : A ≤ normalizer (B : Set Γ)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h
  have hquot : Nat.card (↥(A ⊔ B) ⧸ B.subgroupOf (A ⊔ B))
      = Nat.card (↥A ⧸ B.subgroupOf A) := Nat.card_congr e.symm.toEquiv
  have hcardB : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv
  have hcardInf : Nat.card ↥(B.subgroupOf A) = Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.inf_subgroupOf_left B A]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv
  have hB : Nat.card ↥(A ⊔ B) = Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card ↥B := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (A ⊔ B)), hquot, hcardB]
  have hA : Nat.card ↥A = Nat.card (↥A ⧸ B.subgroupOf A) * Nat.card ↥(A ⊓ B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf A), hcardInf]
  rw [hB, hA]
  ring

theorem card_sup_wreath {Γ : Type} [Group Γ] [Finite Γ] {H P M1 M2 : Subgroup Γ} {u : Γ}
    (hW : WreathMod H P M1 M2 u) : Nat.card ↥(M1 ⊔ M2) = 360 ^ 2 * Nat.card P := by
  have hconj : ∀ a ∈ M1, ∀ b ∈ M2, a * b * a⁻¹ ∈ M2 := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ P := hW.comm a ha b hb
    have hsplit : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [hsplit]
    exact M2.mul_mem (hW.p_le2 hc) hb
  have hnorm : M1 ≤ normalizer (M2 : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact hconj a ha b
    · intro hb
      have hb' := hconj a⁻¹ (M1.inv_mem ha) (a * b * a⁻¹) hb
      have : a⁻¹ * (a * b * a⁻¹) * (a⁻¹)⁻¹ = b := by group
      rwa [this] at hb'
  have hinf : M1 ⊓ M2 = P := le_antisymm hW.inf (le_inf hW.p_le1 hW.p_le2)
  have hmain := card_sup_mul_card_inf_of_le_normalizer (A := M1) (B := M2) hnorm
  rw [hinf] at hmain
  have h1 : Nat.card ↥M1 = 360 * Nat.card P :=
    card_eq_of_quotEquivTo hW.quot1 hW.p_le1
  have h2 : Nat.card ↥M2 = 360 * Nat.card P :=
    card_eq_of_quotEquivTo hW.quot2 hW.p_le2
  rw [h1, h2] at hmain
  have : Nat.card ↥(M1 ⊔ M2) * Nat.card P = (360 ^ 2 * Nat.card P) * Nat.card P := by
    rw [hmain]; ring
  exact Nat.mul_right_cancel (Nat.card_pos (α := ↥P)) this

theorem sq_mul_card_dvd_aut {V : Type} [CommGroup V] [Finite V] (hsq : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 8) {H P M1 M2 : Subgroup (MulAut V)} {u : MulAut V}
    (hW : WreathMod H P M1 M2 u) :
    360 ^ 2 * Nat.card P ∣ ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) := by
  have h1 : Nat.card ↥(M1 ⊔ M2) = 360 ^ 2 * Nat.card P := card_sup_wreath hW
  have h2 : Nat.card (MulAut V) = ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)) :=
    CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hsq 8 hcard
  rw [← h1, ← h2]
  exact Subgroup.card_subgroup_dvd_card (M1 ⊔ M2)

theorem dvd_51_of_dvd_prod {n : ℕ} (hodd : Odd n) (hp : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ 255)
    (hd : 360 ^ 2 * n ∣ ∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ))) : n ∣ 51 := by
  have hprod : (∏ i : Fin 8, (2 ^ 8 - 2 ^ (i : ℕ)))
      = 360 ^ 2 * (2 ^ 22 * (3 * 7 ^ 2 * 17 * 31 * 127)) := by
    norm_num [Fin.prod_univ_eight]
  rw [hprod] at hd
  have hn : n ∣ 2 ^ 22 * (3 * 7 ^ 2 * 17 * 31 * 127) :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : (0 : ℕ) < 360 ^ 2) hd
  have hcop2 : Nat.Coprime n (2 ^ 22) :=
    Nat.Coprime.pow_right 22 hodd.coprime_two_right
  have hn' : n ∣ 3 * 7 ^ 2 * 17 * 31 * 127 := hcop2.dvd_of_dvd_mul_left hn
  rw [show 3 * 7 ^ 2 * 17 * 31 * 127 = 51 * (7 ^ 2 * 31 * 127) by norm_num] at hn'
  have h7 : Nat.Coprime n (7 ^ 2) := by
    have hndvd : ¬ 7 ∣ n := fun h => by
      have := hp 7 (by norm_num) h
      norm_num at this
    exact Nat.prime_seven.coprime_pow_of_not_dvd hndvd
  have h31 : Nat.Coprime n 31 := by
    have hndvd : ¬ 31 ∣ n := fun h => by
      have := hp 31 (by norm_num) h
      norm_num at this
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 31)).mpr hndvd |>.symm
  have h127 : Nat.Coprime n 127 := by
    have hndvd : ¬ 127 ∣ n := fun h => by
      have := hp 127 (by norm_num) h
      norm_num at this
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 127)).mpr hndvd |>.symm
  have hcopM : Nat.Coprime n (7 ^ 2 * 31 * 127) := by
    rw [Nat.coprime_mul_iff_right]
    exact ⟨by rw [Nat.coprime_mul_iff_right]; exact ⟨h7, h31⟩, h127⟩
  exact hcopM.dvd_of_dvd_mul_right hn'

end C10

end CFSG.OddStandard.SmallF3.Omega
