module

public import CFSG.LargeExtraspecial.S12T36Core
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.S12InspPSLLin
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL
open CFSG.Blueprint CFSG.Open

namespace S12InspSpO

theorem card_of_lieModel_pomega {X : Type} [Group X] {m : ℕ} (hm : 4 ≤ m)
    (h : LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1) :
    (Nat.card X : ℤ) = 2 ^ (m * (m - 1)) * (2 ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) ∨
      (Nat.card X : ℤ) = 2 ^ (m * (m - 1)) * (2 ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((2 : ℤ) ^ (2 * i) - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h | h
  · left
    rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hc
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
        (by rw [← Nat.card_eq_fintype_card, hK])
      have hK' : (Nat.card K : ℤ) = 2 := by rw [hK]; norm_num
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus hm, hK']
    all_goals exact absurd ht (by decide)
  · right
    rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hc
      have : Fintype K := Fintype.ofFinite K
      have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
        (by rw [← Nat.card_eq_fintype_card, hK])
      have hK' : (Nat.card K : ℤ) = 2 := by rw [hK]; norm_num
      rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus hm hirr, hK']
    all_goals exact absurd ht (by decide)

theorem eq_of_omega_arith {c P a W Z N x : ℤ} (ha : 4 ≤ a) (hc : 0 < c) (hP : 0 < P)
    (hX : x = c * (a - 1) * P ∨ x = c * (a + 1) * P)
    (hW : 2 * W * Z = c * a * ((a * a - 1) * P)) (hZ : Z + N = a * a)
    (hN : 2 * N + a = a * a ∨ 2 * N = a * a + a) (hdvd : x ∣ W) : x = W := by
  have ha0 : 0 < a := by linarith
  have hW' : W = c * (a - 1) * P ∨ W = c * (a + 1) * P := by
    rcases hN with hN | hN
    · left
      have h1 : (2 * a * (a + 1)) * W = (2 * a * (a + 1)) * (c * (a - 1) * P) := by
        linear_combination 2 * hW + 2 * W * hN - 4 * W * hZ
      exact mul_left_cancel₀ (by positivity) h1
    · right
      have h1 : (2 * a * (a - 1)) * W = (2 * a * (a - 1)) * (c * (a + 1) * P) := by
        linear_combination 2 * hW + 2 * W * hN - 4 * W * hZ
      have h2 : 2 * a * (a - 1) ≠ 0 := by
        have : 0 < a - 1 := by linarith
        positivity
      exact mul_left_cancel₀ h2 h1
  obtain ⟨k, hk⟩ := hdvd
  have hcP : c * P ≠ 0 := by positivity
  rcases hX with rfl | rfl <;> rcases hW' with hW' | hW'
  · exact hW'.symm
  · exfalso
    have h1 : (c * P) * (a + 1) = (c * P) * ((a - 1) * k) := by
      linear_combination -hW' + hk
    have h2 := mul_left_cancel₀ hcP h1
    rcases lt_trichotomy k 2 with hk2 | rfl | hk2
    · have : k ≤ 1 := by omega
      nlinarith
    · linarith
    · have : 3 ≤ k := by omega
      nlinarith
  · exfalso
    have h1 : (c * P) * (a - 1) = (c * P) * ((a + 1) * k) := by
      linear_combination -hW' + hk
    have h2 := mul_left_cancel₀ hcP h1
    rcases le_or_gt k 0 with hk0 | hk0
    · nlinarith
    · have : 1 ≤ k := by omega
      nlinarith
  · exact hW'.symm

theorem cast_prod_two_pow_sub_one (k : ℕ) :
    ((∏ j ∈ Finset.Icc 1 (k + 1), (2 ^ (2 * j) - 1) : ℕ) : ℤ) =
      (2 ^ (k + 1) * 2 ^ (k + 1) - 1) * ∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1) := by
  rw [Nat.cast_prod, Finset.prod_Icc_succ_top (by omega), mul_comm]
  congr 1
  · rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, ← pow_add]
    norm_num
    ring_nf
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    norm_num

end S12InspSpO

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem spo_Xbar12_map_eq_omegaGroup {g : G} (hn : 4 ≤ S.width)
    (hL : LieModel (S.Xbar12 g) .POmegaPlus S.width 2 1 ∨
      LieModel (S.Xbar12 g) .POmegaMinus S.width 2 1) :
    (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate := by
  have : Finite S.Qt := Module.finite_of_finite (ZMod 2)
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2)
    (by rw [S.finrank_Qt_eq_two_mul_width]; omega)
  have hle := Xbar12_map_le_omegaGroup (S := S) g
  have hcardX : Nat.card ((S.Xbar12 g).map S.O.subtype) = Nat.card (S.Xbar12 g) :=
    Subgroup.card_map_of_injective S.O.subtype_injective
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [hcardX]
  have hdvd : Nat.card (S.Xbar12 g) ∣ Nat.card (omegaGroup S.q S.q_nondegenerate) :=
    hcardX ▸ Subgroup.card_dvd_of_le hle
  have hX := S12InspSpO.card_of_lieModel_pomega hn hL
  have hV := S12DW.natCard_eq_four_pow S.finrank_Qt_eq_two_mul_width
  have hO : Nat.card S.O * {v | S.q v = 0}.ncard =
      2 ^ (S.width ^ 2) * ∏ j ∈ Finset.Icc 1 S.width, (2 ^ (2 * j) - 1) :=
    S12DW.card_orthogonalGroup_mul_ncard_eq S.q_nondegenerate S.finrank_Qt_eq_two_mul_width
  have hOΩ : Nat.card S.O = 2 * Nat.card (omegaGroup S.q S.q_nondegenerate) :=
    S12DW.card_orthogonalGroup_eq S.q_nondegenerate
  have hZ := S12DW.ncard_eq_zero_eq S.q
  have hNle : {v | S.q v = 1}.ncard ≤ Nat.card S.Qt := Set.ncard_le_card _
  have hN := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic S.q
    (S12DW.polar_eq_zero_imp S.q_nondegenerate) hV
  obtain ⟨k, hk⟩ : ∃ k, S.width = k + 1 := ⟨S.width - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel] at hX
  rw [hk] at hO hV hN
  rw [hOΩ] at hO
  set W := Nat.card (omegaGroup S.q S.q_nondegenerate)
  set Z := {v | S.q v = 0}.ncard
  set N := {v | S.q v = 1}.ncard
  have hZN : Z + N = 4 ^ (k + 1) := by omega
  have h4 : (4 : ℤ) ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) := by
    rw [← mul_pow]
    norm_num
  have hW : 2 * (W : ℤ) * Z = 2 ^ ((k + 1) * k) * 2 ^ (k + 1) *
      ((2 ^ (k + 1) * 2 ^ (k + 1) - 1) * ∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1)) := by
    have e := congrArg (fun r : ℕ => (r : ℤ)) hO
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at e
    rw [S12InspSpO.cast_prod_two_pow_sub_one] at e
    rw [e]
    ring
  have hZN' : (Z : ℤ) + N = 2 ^ (k + 1) * 2 ^ (k + 1) := by
    rw [← h4]
    exact_mod_cast hZN
  have hN' : 2 * (N : ℤ) + 2 ^ (k + 1) = 2 ^ (k + 1) * 2 ^ (k + 1) ∨
      2 * (N : ℤ) = 2 ^ (k + 1) * 2 ^ (k + 1) + 2 ^ (k + 1) := by
    rw [← h4]
    rcases hN with h | h
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  have ha : (4 : ℤ) ≤ 2 ^ (k + 1) := by
    calc (4 : ℤ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hP : (0 : ℤ) < ∏ i ∈ Finset.Icc 1 k, ((2 : ℤ) ^ (2 * i) - 1) := by
    refine Finset.prod_pos fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : (2 : ℤ) ^ 2 ≤ 2 ^ (2 * i) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hdvd' : (Nat.card (S.Xbar12 g) : ℤ) ∣ (W : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
  have := S12InspSpO.eq_of_omega_arith ha (by positivity) hP hX hW hZN' hN' hdvd'
  exact_mod_cast this.symm

theorem spo_Mbar_map_eq_timmesfeldOmega [IsSimpleGroup G] {g : G} (hn : 3 ≤ S.width)
    (hX : (S.Xbar12 g).map S.O.subtype = omegaGroup S.q S.q_nondegenerate) :
    S.Mbar.map S.O.subtype = timmesfeldOmega S.q := by
  have : Nontrivial S.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2)
    (by rw [S.finrank_Qt_eq_two_mul_width]; omega)
  have hXM : (S.Xbar12 g).map S.O.subtype ≤ S.Mbar.map S.O.subtype :=
    Subgroup.map_mono Xbar12_le_Mbar
  have hΩM : omegaGroup S.q S.q_nondegenerate ≤ S.Mbar.map S.O.subtype := hX ▸ hXM
  have hMO : S.Mbar.map S.O.subtype ≤ S.O := map_subtype_le _
  have hidx := Subgroup.relIndex_mul_relIndex (omegaGroup S.q S.q_nondegenerate)
    (S.Mbar.map S.O.subtype) S.O hΩM hMO
  rw [relIndex_omegaGroup] at hidx
  have h1 : (omegaGroup S.q S.q_nondegenerate).relIndex (S.Mbar.map S.O.subtype) ∣ 2 :=
    ⟨_, hidx.symm⟩
  rw [s12_timmesfeldOmega_eq S.q S.q_nondegenerate]
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with ha | ha
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp ha) hΩM
  · exfalso
    rw [ha] at hidx
    have h2 : (S.Mbar.map S.O.subtype).relIndex S.O = 1 := by omega
    have hOM := Subgroup.relIndex_eq_one.mp h2
    refine S.Mbar_ne_top hn (eq_top_iff.mpr fun x _ => ?_)
    obtain ⟨y, hy, hyx⟩ := hOM x.2
    rwa [show y = x from Subtype.ext hyx] at hy

end Setting

end CFSG.LargeExtraspecial
