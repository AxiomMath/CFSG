module

public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.UniqueElemSylowProj
import CFSG.GroupTheory.WeirSylow.Arith
import CFSG.GroupTheory.WeirSylow.SigmaThree
import CFSG.GroupTheory.WeirSylow.Symplectic
import CFSG.Open.StatedAPI

public section

namespace CFSG.GroupTheory.WeirSylow

open CFSG.Open

theorem one_le_padicValInt_three_pow_orderOf_sub_one {c : ℤ} (h3 : ¬ (3 : ℤ) ∣ c)
    (hc : 2 ≤ |c|) : 1 ≤ padicValInt 3 (c ^ orderOf (c : ZMod 3) - 1) := by
  have hdvd : (3 : ℤ) ∣ c ^ ordMod 3 c - 1 := (dvd_pow_sub_one_iff (p := 3) _).2 dvd_rfl
  have hne : c ^ ordMod 3 c - 1 ≠ 0 := pow_sub_one_ne_zero hc (ordMod_pos h3).ne'
  have h := (padicValInt_dvd_iff (p := 3) 1 _).1 (by simpa using hdvd)
  exact h.resolve_left hne

theorem one_le_padicValNat_three_pow_orderOf_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) (hq : 2 ≤ q) :
    1 ≤ padicValNat 3 (q ^ orderOf (q : ZMod 3) - 1) := by
  have h := one_le_padicValInt_three_pow_orderOf_sub_one (c := (q : ℤ))
    (by exact_mod_cast h3) (by rw [Nat.abs_cast]; exact_mod_cast hq)
  rw [Int.cast_natCast] at h
  have h1 : 1 ≤ q ^ orderOf (q : ZMod 3) := Nat.one_le_pow _ _ (by omega)
  rwa [← padicValInt.of_nat, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one]

theorem orderOf_natCast_zmod_three_of_mod_eq_one {q : ℕ} (h : q % 3 = 1) :
    orderOf (q : ZMod 3) = 1 := by
  rw [← ZMod.natCast_mod, h]
  simp

theorem orderOf_natCast_zmod_three_of_mod_eq_two {q : ℕ} (h : q % 3 = 2) :
    orderOf (q : ZMod 3) = 2 := by
  rw [← ZMod.natCast_mod, h]
  exact orderOf_eq_prime (p := 2) (by decide) (by decide)

theorem orderOf_neg_natCast_zmod_three_of_mod_eq_one {q : ℕ} (h : q % 3 = 1) :
    orderOf (-(q : ZMod 3)) = 2 := by
  rw [← ZMod.natCast_mod, h]
  exact orderOf_eq_prime (p := 2) (by decide) (by decide)

theorem sp_three_div_orderOf_eq_three {q : ℕ} (h3 : ¬ 3 ∣ q) :
    (if Even (orderOf (q : ZMod 3)) then 2 * 3 else 3) / orderOf (q : ZMod 3) = 3 := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases hmod with h | h
  · rw [orderOf_natCast_zmod_three_of_mod_eq_one h]
    decide
  · rw [orderOf_natCast_zmod_three_of_mod_eq_two h]
    decide

theorem uniqueElemSylow_of_sylow_mulEquiv_statedSp {G : Type*} [Group G] [Finite G]
    (K : Type) [Field K] [Finite K] (hK : ¬ 3 ∣ Nat.card K)
    (h : ∀ P : Sylow 3 G, ∃ P' : Sylow 3 (StatedSp 3 K), Nonempty (P ≃* P')) :
    UniqueElemSylow 3 3 G := by
  letI := Fintype.ofFinite K
  have hK' : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  refine uniqueElemSylow_of_sigmaModel (one_le_padicValNat_three_pow_orderOf_sub_one hK' hq2)
    (sp_three_div_orderOf_eq_three hK') fun P => ?_
  obtain ⟨P', ⟨φ⟩⟩ := h P
  obtain ⟨ψ⟩ := sylow_Sp (by decide : Odd 3) K hK' 3 P'
  exact ⟨φ.trans ψ⟩

theorem uniqueElemSylow_statedSp_three (K : Type) [Field K] [Finite K]
    (hK : ¬ 3 ∣ Nat.card K) : UniqueElemSylow 3 3 (StatedSp 3 K) :=
  uniqueElemSylow_of_sylow_mulEquiv_statedSp K hK fun P => ⟨P, ⟨MulEquiv.refl _⟩⟩

theorem uniqueElemSylow_statedProj_statedSp_three (K : Type) [Field K] [Finite K]
    (hK : ¬ 3 ∣ Nat.card K) : UniqueElemSylow 3 3 (StatedProj (StatedSp 3 K)) :=
  UniqueElemSylow.statedProj (d := 2) (by decide)
    (fun c hc => (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff (by norm_num) c).1 hc)
    (uniqueElemSylow_statedSp_three K hK)

end CFSG.GroupTheory.WeirSylow
