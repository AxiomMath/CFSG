module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Vocab

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Polynomial

theorem gf16_card_fix4_le : Nat.card {c : GaloisField 2 4 // c ^ 4 = c} ≤ 4 := by
  classical
  have : Fintype (GaloisField 2 4) := Fintype.ofFinite _
  have hdeg : (X ^ 4 - X : (GaloisField 2 4)[X]).natDegree = 4 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
  have hp : (X ^ 4 - X : (GaloisField 2 4)[X]) ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter (fun c : GaloisField 2 4 => c ^ 4 = c)).card
      ≤ (X ^ 4 - X : (GaloisField 2 4)[X]).natDegree := by
        apply Polynomial.card_le_degree_of_subset_roots
        intro z hz
        simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        rw [Polynomial.mem_roots hp]
        simp [Polynomial.IsRoot, hz]
    _ = 4 := hdeg

@[expose] noncomputable def tauHom : GaloisField 2 4 →+ GaloisField 2 4 where
  toFun c := c + c ^ 4
  map_zero' := by simp
  map_add' a b := by rw [gf16_add_pow4]; ring

theorem tau_apply (c : GaloisField 2 4) : tauHom c = c + c ^ 4 := rfl

theorem tau_tau (c : GaloisField 2 4) : tauHom (tauHom c) = 0 := by
  rw [tau_apply, tau_apply, gf16_add_pow4]
  have h16 : (c ^ 4) ^ 4 = c := by rw [← pow_mul]; exact gf16_pow16 c
  rw [h16]
  linear_combination (c + c ^ 4) * gf16_char2

theorem range_tau_le_ker : tauHom.range ≤ tauHom.ker := by
  rintro _ ⟨c, rfl⟩
  exact tau_tau c

theorem card_ker_tau : Nat.card tauHom.ker = 4 := by
  have hle : Nat.card tauHom.ker ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun z : tauHom.ker => (⟨z.1, ?_⟩ : {c : GaloisField 2 4 // c ^ 4 = c})) ?_) gf16_card_fix4_le
    · have hz : z.1 + z.1 ^ 4 = 0 := z.2
      have : z.1 ^ 4 = z.1 := by linear_combination hz + (-z.1) * gf16_char2
      exact this
    · intro a b hab
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
  have hmul := AddSubgroup.card_ker_mul_card_range tauHom
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    have := GaloisField.card 2 4 (by norm_num)
    simpa using this
  have hr : Nat.card tauHom.range ≤ Nat.card tauHom.ker :=
    Nat.card_le_card_of_injective (fun z : tauHom.range => (⟨z.1, range_tau_le_ker z.2⟩ : tauHom.ker))
      (fun a b hab => by apply Subtype.ext; simpa using congrArg Subtype.val hab)
  rw [hK] at hmul
  have hpos : 0 < Nat.card tauHom.ker := Nat.card_pos
  nlinarith

theorem range_tau_eq_ker : tauHom.range = tauHom.ker := by
  apply le_antisymm range_tau_le_ker
  have h1 := AddSubgroup.card_ker_mul_card_range tauHom
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    have := GaloisField.card 2 4 (by norm_num)
    simpa using this
  rw [hK, card_ker_tau] at h1
  have hr : Nat.card tauHom.range = 4 := by omega
  exact (AddSubgroup.eq_of_le_of_card_ge range_tau_le_ker (by rw [hr, card_ker_tau])).ge

end CFSG.GH74.GLS.Stage1.Thm6.Sec13

