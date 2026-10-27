module

public import CFSG.GH74.Generic.S1.KL3Cfg
public import CFSG.GH74.Generic.S1.KL3ClStated
public import CFSG.GH74.Generic.S1.KL3ClRep
public import CFSG.GH74.Generic.S1.KL3ClForm

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

theorem kl3cl_three_ne_zero {K : Type} [Field K] {p : ℕ} (hp : p.Prime) [CharP K p] (hp3 : p ≠ 3) :
    (3 : K) ≠ 0 := by
  intro h
  have h3 : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 (by exact_mod_cast h)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3)

theorem kl3FamPSp4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3FamPSp4 := by
  intro S _ _ _ p f hp _ hf hmodel F _ _ Pb yb hcfg
  obtain ⟨hF, ⟨eSL⟩, hyb, hyb2, hsolv⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨ρ, y, hρinj, hρH, -, -, -, -⟩ := kl3cl_rep_of_stated hGA e hF eSL hyb hyb2 hsolv
  have hcard : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by simp
  by_cases hp3 : p = 3
  · subst hp3
    have hJ : (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)
        (-1 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
      have h1 : Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)
          (-1 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K) *
          (-Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)
          (-1 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K)) = 1 := by
        rw [Matrix.mul_neg, Matrix.fromBlocks_multiply]
        simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add,
          add_zero, neg_zero, Matrix.fromBlocks_neg, neg_neg]
        exact Matrix.fromBlocks_one
      exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero
    have h6 := kl3cl_card_ge_six_sp hF ρ hρinj _ hJ (fun g => kl3cl_statedSp_form _ (hρH g))
    omega
  · have h6 := kl3cl_card_ge_six_of_char_ne_three (kl3cl_three_ne_zero hp hp3) hF ρ hρinj
    omega

theorem kl3FamU4 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3FamU4 := by
  intro S _ _ _ p f hp _ hf _ hmodel F _ _ Pb yb hcfg
  obtain ⟨hF, ⟨eSL⟩, hyb, hyb2, hsolv⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := 2 * f)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  obtain ⟨ρ, y, hρinj, hρH, -, -, -, -⟩ := kl3cl_rep_of_stated hGA e hF eSL hyb hyb2 hsolv
  by_cases hp3 : p = 3
  · subst hp3
    have h6 := kl3cl_card_ge_six_su f hF ρ hρinj (fun g => kl3cl_statedSU_form _ (hρH g))
    simp at h6
  · have h6 := kl3cl_card_ge_six_of_char_ne_three (kl3cl_three_ne_zero hp hp3) hF ρ hρinj
    simp at h6

theorem kl3FamU5 (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    KL3FamU5 := by
  intro S _ _ _ p f hp hf _ hmodel F _ _ Pb yb hcfg
  obtain ⟨hF, ⟨eSL⟩, hyb, hyb2, hsolv⟩ := hcfg
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (p := p) (f := 2 * f)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  obtain ⟨ρ, y, hρinj, hρH, -, -, -, -⟩ := kl3cl_rep_of_stated hGA e hF eSL hyb hyb2 hsolv
  by_cases hp3 : p = 3
  · subst hp3
    have h6 := kl3cl_card_ge_six_su f hF ρ hρinj (fun g => kl3cl_statedSU_form _ (hρH g))
    simp at h6
  · have h6 := kl3cl_card_ge_six_of_char_ne_three (kl3cl_three_ne_zero hp hp3) hF ρ hρinj
    simp at h6

end CFSG.GH74.Generic.S1
