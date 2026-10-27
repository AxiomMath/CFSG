module

public import CFSG.LieType.D4Small.WeightBasic
public import CFSG.LieType.D4Small.WeightClass

public section

namespace CFSG.LieType.D4Small.D4Datum

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {D : D4Datum G K} {X : Type*} [AddCommGroup X] [Module K X] {ρ : Representation K G X}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {σ : ZMod (Nat.card Kˣ)}

theorem rootOp_ne_mem (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    (h1 : a + castW (Nat.card Kˣ) α ∈ C) :
    a + (2 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C := by
  have h1' : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ C := by
    simpa using h1
  have hne : (1 : ZMod (Nat.card Kˣ)) ≠ 0 := by
    haveI := hC.nontrivial
    exact one_ne_zero
  rcases hC.step a ha α hα 1 hne h1' with h | h
  · have hσ : a + σ • castW (Nat.card Kˣ) α ∈ C := by simpa [h] using h1'
    have h2 := hC.two_smul_not_mem ha hα hσ
    rwa [← h, mul_one] at h2
  · have hσ : a + (-σ) • castW (Nat.card Kˣ) α ∈ C := by simpa [h] using h1'
    have h2 := hC.neg.two_smul_not_mem ha hα hσ
    rwa [← h, mul_one] at h2

private theorem odd_choose_two_card_units (hK : 4 ≤ Nat.card K) :
    Odd ((Nat.card Kˣ).choose 2) := by
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf2 : 2 ≤ (f : ℕ) := by
    have h4 : 2 ^ 2 ≤ 2 ^ (f : ℕ) := by
      rw [← hcard']
      exact hK
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  have hN : Nat.card Kˣ = 2 ^ (f : ℕ) - 1 := by
    rw [Nat.card_units, hcard']
  have hpow : 2 ^ (f : ℕ) = 2 * 2 ^ ((f : ℕ) - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one (by omega : (f : ℕ) ≠ 0)]
  have hsub : 2 ^ (f : ℕ) - 1 - 1 = 2 * (2 ^ ((f : ℕ) - 1) - 1) := by
    omega
  have hchoose : (Nat.card Kˣ).choose 2 =
      (Nat.card Kˣ) * (2 ^ ((f : ℕ) - 1) - 1) := by
    rw [Nat.choose_two_right, hN, hsub]
    rw [show (2 ^ (f : ℕ) - 1) * (2 * (2 ^ ((f : ℕ) - 1) - 1)) =
        2 * ((2 ^ (f : ℕ) - 1) * (2 ^ ((f : ℕ) - 1) - 1)) by ring,
      Nat.mul_div_right _ (by norm_num : 0 < 2)]
  rw [hchoose]
  refine Odd.mul ?_ ?_
  · rw [hN]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : (f : ℕ) ≠ 0)) odd_one
  · exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : (f : ℕ) - 1 ≠ 0)) odd_one

private theorem odd_choose_two_pred_card_units (hK : 8 ≤ Nat.card K) :
    Odd ((Nat.card Kˣ - 1).choose 2) := by
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf3 : 3 ≤ (f : ℕ) := by
    have h8 : 2 ^ 3 ≤ 2 ^ (f : ℕ) := by
      rw [← hcard']
      exact hK
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8
  have hN : Nat.card Kˣ = 2 ^ (f : ℕ) - 1 := by
    rw [Nat.card_units, hcard']
  have hpow : 2 ^ (f : ℕ) = 2 * 2 ^ ((f : ℕ) - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one (by omega : (f : ℕ) ≠ 0)]
  have hsub : 2 ^ (f : ℕ) - 1 - 1 = 2 * (2 ^ ((f : ℕ) - 1) - 1) := by
    omega
  have hchoose : (Nat.card Kˣ - 1).choose 2 =
      (2 ^ ((f : ℕ) - 1) - 1) * (2 ^ (f : ℕ) - 3) := by
    rw [Nat.choose_two_right, hN]
    have h2 : (2 ^ (f : ℕ) - 1) - 1 = 2 * (2 ^ ((f : ℕ) - 1) - 1) := hsub
    have h3 : 2 * (2 ^ ((f : ℕ) - 1) - 1) - 1 = 2 ^ (f : ℕ) - 3 := by omega
    rw [h2, h3]
    rw [show (2 * (2 ^ ((f : ℕ) - 1) - 1)) * (2 ^ (f : ℕ) - 3) =
        2 * ((2 ^ ((f : ℕ) - 1) - 1) * (2 ^ (f : ℕ) - 3)) by ring,
      Nat.mul_div_right _ (by norm_num : 0 < 2)]
  rw [hchoose]
  refine Odd.mul ?_ ?_
  · exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : (f : ℕ) - 1 ≠ 0)) odd_one
  · exact Nat.Even.sub_odd (le_trans (by norm_num : 3 ≤ 2 ^ 3)
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hf3))
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : (f : ℕ) ≠ 0))
      (⟨1, by norm_num⟩ : Odd 3)

theorem rootOp_mul_of_odd {α : Fin 4 → ℤ} (hα : IsD4Root α) {i j : ℕ}
    (hij : i + j ≤ Nat.card Kˣ) (hodd : Odd ((i + j).choose i)) :
    rootOp D ρ α i * rootOp D ρ α j = rootOp D ρ α (i + j) := by
  rw [rootOp_mul D ρ α hα i j, if_pos hij,
    natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero, one_smul]

theorem rootOp_card_eq_zero (hK : 4 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α (Nat.card Kˣ) = 0 := by
  have hN3 : 3 ≤ Nat.card Kˣ := hC.three_le
  have hodd := odd_choose_two_card_units (K := K) hK
  have hA1 : rootOp D ρ α (Nat.card Kˣ - 1) * rootOp D ρ α 1 =
      rootOp D ρ α (Nat.card Kˣ) := by
    have hchoose : (Nat.card Kˣ - 1 + 1).choose (Nat.card Kˣ - 1) = Nat.card Kˣ := by
      calc (Nat.card Kˣ - 1 + 1).choose (Nat.card Kˣ - 1)
          = Nat.card Kˣ - 1 + 1 := Nat.choose_succ_self_right (Nat.card Kˣ - 1)
        _ = Nat.card Kˣ := by omega
    have hodd' : Odd ((Nat.card Kˣ - 1 + 1).choose (Nat.card Kˣ - 1)) := by
      rw [hchoose]
      exact hC.odd
    have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
      (i := Nat.card Kˣ - 1) (j := 1) (by omega) hodd'
    rwa [show Nat.card Kˣ - 1 + 1 = Nat.card Kˣ by omega] at h
  have hA2 : rootOp D ρ α (Nat.card Kˣ - 2) * rootOp D ρ α 2 =
      rootOp D ρ α (Nat.card Kˣ) := by
    have hchoose : (Nat.card Kˣ - 2 + 2).choose (Nat.card Kˣ - 2) =
        (Nat.card Kˣ).choose 2 := by
      rw [show Nat.card Kˣ - 2 + 2 = Nat.card Kˣ by omega]
      exact Nat.choose_symm (by omega : 2 ≤ Nat.card Kˣ)
    have hodd' : Odd ((Nat.card Kˣ - 2 + 2).choose (Nat.card Kˣ - 2)) := by
      rw [hchoose]
      exact hodd
    have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
      (i := Nat.card Kˣ - 2) (j := 2) (by omega) hodd'
    rwa [show Nat.card Kˣ - 2 + 2 = Nat.card Kˣ by omega] at h
  refine ext_of_wtSpace hCw ?_
  intro a ha x hx
  by_cases h1 : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∈ C
  · have h2 : a + (2 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C := by
      exact rootOp_ne_mem hC ha hα (by simpa using h1)
    have hx2 : rootOp D ρ α 2 x = 0 := rootOp_apply_eq_zero hCw hα hx h2
    rw [← hA2, Module.End.mul_apply, hx2, map_zero]
    simp
  · have hx1 : rootOp D ρ α 1 x = 0 := rootOp_apply_eq_zero hCw hα hx (by simpa using h1)
    rw [← hA1, Module.End.mul_apply, hx1, map_zero]
    simp

private theorem one_ne_two_pow_zmod {f l : ℕ} (hl : 2 ^ l < 2 ^ f - 1) (hlpos : 0 < l) :
    (1 : ZMod (2 ^ f - 1)) ≠ (2 : ZMod (2 ^ f - 1)) ^ l := by
  intro h
  have hnat : (1 : ZMod (2 ^ f - 1)) = ((2 ^ l : ℕ) : ZMod (2 ^ f - 1)) := by
    rw [h, Nat.cast_pow]
    norm_num
  have hmod : (1 : ℕ) ≡ 2 ^ l [MOD 2 ^ f - 1] :=
    (ZMod.natCast_eq_natCast_iff 1 (2 ^ l) (2 ^ f - 1)).mp (by simpa using hnat)
  have h2l : 1 < 2 ^ l := Nat.one_lt_two_pow (by omega : l ≠ 0)
  have heq : 1 = 2 ^ l := Nat.ModEq.eq_of_lt_of_lt hmod (by omega) hl
  omega

private theorem one_ne_neg_two_pow_zmod {f l : ℕ} (hl : 2 ^ l < 2 ^ f - 1) (hf3 : 3 ≤ f)
    (hlpos : 0 < l) :
    (1 : ZMod (2 ^ f - 1)) ≠ -((2 : ZMod (2 ^ f - 1)) ^ l) := by
  intro h
  have hsum0 : ((2 ^ l + 1 : ℕ) : ZMod (2 ^ f - 1)) = 0 := by
    rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, h]
    simp
  have hdvd1 : 2 ^ f - 1 ∣ 2 ^ l + 1 :=
    (ZMod.natCast_eq_zero_iff (2 ^ l + 1) (2 ^ f - 1)).mp hsum0
  have hfpos : 0 < 2 ^ f := pow_pos (by norm_num) _
  have hpos : 0 < 2 ^ l + 1 := by positivity
  have h2f : 8 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf3
  have heq : 2 ^ l + 1 = 2 ^ f - 1 :=
    Nat.eq_of_dvd_of_lt_two_mul (Nat.pos_iff_ne_zero.mp hpos) hdvd1 (by omega)
  have hpow2 : 2 ^ l + 2 = 2 ^ f := by omega
  have hfl : l < f := by
    have hlt : 2 ^ l < 2 ^ f :=
      lt_of_lt_of_le hl (Nat.sub_le _ _)
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  have hle1 : 2 ^ l + 2 ≤ 2 ^ (l + 1) := by
    have h2 : 2 ≤ 2 ^ l := by
      have := Nat.one_lt_two_pow (by omega : l ≠ 0)
      omega
    rw [pow_succ]
    omega
  have hle2 : 2 ^ (l + 1) ≤ 2 ^ f :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : l + 1 ≤ f)
  have heq2 : 2 ^ l + 2 = 2 ^ (l + 1) := by
    rw [← hpow2] at hle2
    exact le_antisymm hle1 hle2
  have h2l : 2 ^ l = 2 := by
    rw [pow_succ] at heq2
    omega
  have hl1 : l = 1 := by
    have hpow : 2 ^ l = 2 ^ 1 := by simpa using h2l
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hf2 : f = 2 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    calc 2 ^ f = 2 ^ l + 2 := hpow2.symm
      _ = 2 ^ 1 + 2 := by rw [hl1]
      _ = 2 ^ 2 := by norm_num
  omega

private theorem two_ne_one_zmod {N : ℕ} (hN : 3 ≤ N) : (2 : ZMod N) ≠ 1 := by
  intro h
  have hmod : (1 : ℕ) ≡ 2 [MOD N] :=
    ((ZMod.natCast_eq_natCast_iff 2 1 N).mp (by simpa using h)).symm
  have hdvd : N ∣ 1 := by
    simpa using (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod
  have := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
  omega

private theorem two_ne_neg_one_zmod {N : ℕ} (hN : 5 ≤ N) : (2 : ZMod N) ≠ -1 := by
  intro h
  have h3 : (3 : ZMod N) = 0 := by
    have := congrArg (fun z : ZMod N => z + 1) h
    norm_num at this
    exact this
  have hdvd : N ∣ 3 := (ZMod.natCast_eq_zero_iff 3 N).mp (by simpa using h3)
  have := Nat.le_of_dvd (by norm_num : 0 < 3) hdvd
  omega

private theorem eight_le_card_data (hK : 8 ≤ Nat.card K) {l : ℕ} (hl : 2 ^ l < Nat.card Kˣ) :
    ∃ f : ℕ, 3 ≤ f ∧ Nat.card Kˣ = 2 ^ f - 1 ∧ 2 ^ l < 2 ^ f - 1 ∧
      7 ≤ Nat.card Kˣ ∧ 0 < 2 ^ l := by
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hcard' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  have hf3 : 3 ≤ (f : ℕ) := by
    have h8 : 2 ^ 3 ≤ 2 ^ (f : ℕ) := by
      rw [← hcard']
      exact hK
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8
  have hN : Nat.card Kˣ = 2 ^ (f : ℕ) - 1 := by
    rw [Nat.card_units, hcard']
  have hlN : 2 ^ l < 2 ^ (f : ℕ) - 1 := by
    calc 2 ^ l < Nat.card Kˣ := hl
      _ = 2 ^ (f : ℕ) - 1 := hN
  have hN7 : 7 ≤ Nat.card Kˣ := by
    rw [hN]
    have h8 : 8 ≤ 2 ^ (f : ℕ) := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf3
    omega
  exact ⟨(f : ℕ), hf3, hN, hlN, hN7, pow_pos (by norm_num) l⟩

private theorem rootOp_sub_pow_apply_eq_zero {l : ℕ}
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ l) C)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {x : X} (hx : x ∈ D.wtSpace ρ a) (hl : 2 ^ l < Nat.card Kˣ) (hlpos : 0 < l)
    (h1ne : (1 : ZMod (Nat.card Kˣ)) ≠ (2 : ZMod (Nat.card Kˣ)) ^ l)
    (h1ne' : (1 : ZMod (Nat.card Kˣ)) ≠ -((2 : ZMod (Nat.card Kˣ)) ^ l)) :
    rootOp D ρ α (Nat.card Kˣ - 2 ^ l) x = 0 := by
  have hαnot : a + (1 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C := by
    intro hmem
    have h1ne0 : (1 : ZMod (Nat.card Kˣ)) ≠ 0 := by
      haveI := hC.nontrivial
      exact one_ne_zero
    rcases hC.step a ha α hα 1 h1ne0 hmem with h | h
    · exact h1ne h
    · exact h1ne' h
  have h1x : rootOp D ρ α 1 x = 0 :=
    rootOp_apply_eq_zero hCw hα hx (by simpa using hαnot)
  have hoddk : Odd (Nat.card Kˣ - 2 ^ l) :=
    Nat.Odd.sub_even (Nat.le_of_lt hl) hC.odd
      (Even.pow_of_ne_zero (by norm_num : Even 2) (by omega : l ≠ 0))
  have hodd' : Odd (((Nat.card Kˣ - 2 ^ l) - 1 + 1).choose
      ((Nat.card Kˣ - 2 ^ l) - 1)) := by
    have hchoose : ((Nat.card Kˣ - 2 ^ l) - 1 + 1).choose
        ((Nat.card Kˣ - 2 ^ l) - 1) = Nat.card Kˣ - 2 ^ l := by
      calc ((Nat.card Kˣ - 2 ^ l) - 1 + 1).choose ((Nat.card Kˣ - 2 ^ l) - 1)
          = (Nat.card Kˣ - 2 ^ l) - 1 + 1 :=
            Nat.choose_succ_self_right ((Nat.card Kˣ - 2 ^ l) - 1)
        _ = Nat.card Kˣ - 2 ^ l := by omega
    rwa [hchoose]
  have hA : rootOp D ρ α ((Nat.card Kˣ - 2 ^ l) - 1) * rootOp D ρ α 1 =
      rootOp D ρ α (Nat.card Kˣ - 2 ^ l) := by
    have hij : (Nat.card Kˣ - 2 ^ l) - 1 + 1 ≤ Nat.card Kˣ := by
      rw [Nat.sub_one_add_one (by omega : Nat.card Kˣ - 2 ^ l ≠ 0)]
      exact Nat.sub_le _ _
    have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
      (i := (Nat.card Kˣ - 2 ^ l) - 1) (j := 1) hij hodd'
    rwa [show (Nat.card Kˣ - 2 ^ l) - 1 + 1 = Nat.card Kˣ - 2 ^ l by omega] at h
  rw [← hA, Module.End.mul_apply, h1x, map_zero]

private theorem rootOp_pred_card_apply_eq_zero (hN3 : 3 ≤ Nat.card Kˣ)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {x : X} (hx : x ∈ D.wtSpace ρ a)
    (h2not : a + (2 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C)
    (hodd : Odd ((Nat.card Kˣ - 1).choose 2)) :
    rootOp D ρ α (Nat.card Kˣ - 1) x = 0 := by
  have hodd' : Odd ((Nat.card Kˣ - 3 + 2).choose (Nat.card Kˣ - 3)) := by
    have hchoose : (Nat.card Kˣ - 3 + 2).choose (Nat.card Kˣ - 3) =
        (Nat.card Kˣ - 1).choose 2 := by
      rw [show Nat.card Kˣ - 3 + 2 = Nat.card Kˣ - 1 by omega]
      exact Nat.choose_symm (by omega : 2 ≤ Nat.card Kˣ - 1)
    rwa [hchoose]
  have hA : rootOp D ρ α (Nat.card Kˣ - 3) * rootOp D ρ α 2 =
      rootOp D ρ α (Nat.card Kˣ - 1) := by
    have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
      (i := Nat.card Kˣ - 3) (j := 2) (by omega) hodd'
    rwa [show Nat.card Kˣ - 3 + 2 = Nat.card Kˣ - 1 by omega] at h
  have h2x : rootOp D ρ α 2 x = 0 := rootOp_apply_eq_zero hCw hα hx h2not
  rw [← hA, Module.End.mul_apply, h2x, map_zero]

private theorem rootOp_apply_eq_zero_of_ne_pm (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {x : X} (hx : x ∈ D.wtSpace ρ a) {k : ℕ}
    (hk0 : (k : ZMod (Nat.card Kˣ)) ≠ 0)
    (hk : (k : ZMod (Nat.card Kˣ)) ≠ σ)
    (hk' : (k : ZMod (Nat.card Kˣ)) ≠ -σ) :
    rootOp D ρ α k x = 0 := by
  have hnot : a + (k : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C := by
    intro hmem
    rcases hC.step a ha α hα (k : ZMod (Nat.card Kˣ)) hk0 hmem with h | h
    · exact hk h
    · exact hk' h
  rw [rootOp_apply_eq_zero hCw hα hx hnot]

private theorem rootOp_apply_eq_zero_of_eq_neg_pow (hK : 8 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {l : ℕ} (hl : 2 ^ l < Nat.card Kˣ)
    (hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ l) C)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {x : X} (hx : x ∈ D.wtSpace ρ a) {k : ℕ} (hkadd : k + 2 ^ l = Nat.card Kˣ) :
    rootOp D ρ α k x = 0 := by
  obtain ⟨f, hf3, hN, hlN, hN7, h2lpos⟩ := eight_le_card_data (K := K) hK hl
  have hkN : k = Nat.card Kˣ - 2 ^ l := by omega
  rw [hkN]
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · subst l
    have hk1 : Nat.card Kˣ - 2 ^ 0 = Nat.card Kˣ - 1 := by norm_num
    rw [hk1]
    have h2not : a + (2 : ZMod (Nat.card Kˣ)) • castW (Nat.card Kˣ) α ∉ C := by
      intro hmem
      have h2ne0 : (2 : ZMod (Nat.card Kˣ)) ≠ 0 := by
        intro h2z
        have h2z' : ((2 : ℕ) : ZMod (Nat.card Kˣ)) = 0 := by simpa using h2z
        rw [ZMod.natCast_eq_zero_iff] at h2z'
        have := Nat.le_of_dvd (by norm_num : 0 < 2) h2z'
        omega
      rcases hC.step a ha α hα 2 h2ne0 hmem with h | h
      · norm_num at h
        exact two_ne_one_zmod (by omega) h
      · norm_num at h
        exact two_ne_neg_one_zmod (by omega) h
    rw [rootOp_pred_card_apply_eq_zero hC.three_le hCw ha hα hx h2not
      (odd_choose_two_pred_card_units hK)]
  · have h1ne : (1 : ZMod (Nat.card Kˣ)) ≠ (2 : ZMod (Nat.card Kˣ)) ^ l := by
      rw [hN]
      exact one_ne_two_pow_zmod (f := f) hlN hlpos
    have h1ne' : (1 : ZMod (Nat.card Kˣ)) ≠ -((2 : ZMod (Nat.card Kˣ)) ^ l) := by
      rw [hN]
      exact one_ne_neg_two_pow_zmod (f := f) hlN hf3 hlpos
    rw [rootOp_sub_pow_apply_eq_zero hCw hC ha hα hx hl hlpos h1ne h1ne']

private theorem rootOp_sum_eq_of_small_class (hK : 8 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {l : ℕ} (hl : 2 ^ l < Nat.card Kˣ)
    (hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ l) C)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K)
    {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ∈ C) {x : X} (hx : x ∈ D.wtSpace ρ a) :
    (∑ k ∈ Finset.range (Nat.card Kˣ + 1), c ^ k • rootOp D ρ α k x) =
      x + c ^ (2 ^ l) • rootOp D ρ α (2 ^ l) x := by
  have h2lpos : 0 < 2 ^ l := pow_pos (by norm_num) l
  have hmem0 : (0 : ℕ) ∈ Finset.range (Nat.card Kˣ + 1) := by simp
  have hmemk : 2 ^ l ∈ Finset.range (Nat.card Kˣ + 1) := by
    rw [Finset.mem_range]
    omega
  rw [Finset.sum_eq_add_of_mem (0 : ℕ) (2 ^ l) hmem0 hmemk (by omega) ?_]
  · rw [rootOp_zero D ρ α hα]
    simp
  · intro k hk hkne
    obtain ⟨hk0, hkk⟩ := hkne
    have hkle : k ≤ Nat.card Kˣ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    by_cases hkN : k = Nat.card Kˣ
    · rw [hkN, rootOp_card_eq_zero (C := C) (by omega : 4 ≤ Nat.card K) hCw hC hα]
      simp
    · have hkltN : k < Nat.card Kˣ := lt_of_le_of_ne hkle hkN
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkz : (k : ZMod (Nat.card Kˣ)) ≠ 0 := by
        intro hkz0
        rw [ZMod.natCast_eq_zero_iff] at hkz0
        have := Nat.le_of_dvd hkpos hkz0
        omega
      by_cases hσ : (k : ZMod (Nat.card Kˣ)) = (2 : ZMod (Nat.card Kˣ)) ^ l
      · have hσnat : (k : ZMod (Nat.card Kˣ)) = ((2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) := by
          rw [hσ, Nat.cast_pow]
          norm_num
        have hmod : k ≡ 2 ^ l [MOD Nat.card Kˣ] :=
          (ZMod.natCast_eq_natCast_iff k (2 ^ l) (Nat.card Kˣ)).mp hσnat
        exact absurd (Nat.ModEq.eq_of_lt_of_lt hmod hkltN hl) hkk
      · by_cases hσ' : (k : ZMod (Nat.card Kˣ)) = -((2 : ZMod (Nat.card Kˣ)) ^ l)
        · have hsum0 : ((k + 2 ^ l : ℕ) : ZMod (Nat.card Kˣ)) = 0 := by
            rw [Nat.cast_add, hσ', Nat.cast_pow]
            simp
          have hdvd : Nat.card Kˣ ∣ k + 2 ^ l :=
            (ZMod.natCast_eq_zero_iff (k + 2 ^ l) (Nat.card Kˣ)).mp hsum0
          have hkadd : k + 2 ^ l = Nat.card Kˣ :=
            Nat.eq_of_dvd_of_lt_two_mul (by omega) hdvd (by omega)
          rw [rootOp_apply_eq_zero_of_eq_neg_pow hK hCw hl hC ha hα hx hkadd,
            smul_zero]
        · rw [rootOp_apply_eq_zero_of_ne_pm hCw hC ha hα hx hkz hσ hσ', smul_zero]

theorem rho_x_eq_of_eight_le (hK : 8 ≤ Nat.card K)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    {l : ℕ} (hl : 2 ^ l < Nat.card Kˣ)
    (hC : IsSmallClass (Nat.card Kˣ) ((2 : ZMod (Nat.card Kˣ)) ^ l) C)
    {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) :
    ρ (D.x α c) = 1 + c ^ (2 ^ l) • rootOp D ρ α (2 ^ l) := by
  refine ext_of_wtSpace hCw ?_
  intro a ha x hx
  rw [rho_x_eq_sum D ρ α hα c, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
  exact rootOp_sum_eq_of_small_class hK hCw hl hC hα c ha hx

theorem card_units_eq_three (hK : Nat.card K = 4) : Nat.card Kˣ = 3 := by
  rw [Nat.card_units, hK]

theorem rootOp_three_eq_zero (hK : Nat.card K = 4)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α 3 = 0 := by
  have h := rootOp_card_eq_zero (C := C) (by omega : 4 ≤ Nat.card K) hCw hC hα
  rwa [card_units_eq_three (K := K) hK] at h

theorem rootOp_one_mul_two (hK : Nat.card K = 4)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α 1 * rootOp D ρ α 2 = 0 := by
  have hN := card_units_eq_three (K := K) hK
  have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
    (i := 1) (j := 2) (by omega) (by decide : Odd ((1 + 2).choose 1))
  rw [show (1 + 2 : ℕ) = 3 by norm_num, rootOp_three_eq_zero hK hCw hC hα] at h
  exact h

theorem rootOp_two_mul_one (hK : Nat.card K = 4)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α 2 * rootOp D ρ α 1 = 0 := by
  have hN := card_units_eq_three (K := K) hK
  have h := rootOp_mul_of_odd (D := D) (ρ := ρ) hα
    (i := 2) (j := 1) (by omega) (by decide : Odd ((2 + 1).choose 2))
  rw [show (2 + 1 : ℕ) = 3 by norm_num, rootOp_three_eq_zero hK hCw hC hα] at h
  exact h

theorem rootOp_one_mul_one (hK : Nat.card K = 4) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α 1 * rootOp D ρ α 1 = 0 := by
  have hN := card_units_eq_three (K := K) hK
  have hcoef : (((1 + 1).choose 1 : ℕ) : K) = 0 := by
    norm_num
    exact CharTwo.two_eq_zero
  rw [rootOp_mul D ρ α hα 1 1, if_pos (by omega), hcoef, zero_smul]

theorem rootOp_two_mul_two (hK : Nat.card K = 4) {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    rootOp D ρ α 2 * rootOp D ρ α 2 = 0 := by
  have hN := card_units_eq_three (K := K) hK
  rw [rootOp_mul D ρ α hα 2 2, if_neg (by omega), zero_smul]

theorem rho_x_eq_of_card_eq_four (hK : Nat.card K = 4)
    (hCw : ∀ a, a ∈ C ↔ D.wtSpace ρ a ≠ ⊥)
    (hC : IsSmallClass (Nat.card Kˣ) σ C) {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) :
    ρ (D.x α c) = 1 + c • rootOp D ρ α 1 + c ^ 2 • rootOp D ρ α 2 := by
  have hN := card_units_eq_three (K := K) hK
  have hA3 := rootOp_three_eq_zero (C := C) hK hCw hC hα
  refine ext_of_wtSpace hCw ?_
  intro a ha x hx
  rw [rho_x_eq_sum D ρ α hα c, LinearMap.sum_apply, hN]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hf0 : c ^ 0 • rootOp D ρ α 0 x = x := by
    rw [rootOp_zero D ρ α hα]
    simp
  have hf3 : c ^ 3 • rootOp D ρ α 3 x = 0 := by
    rw [hA3]
    simp
  rw [hf0, hf3]
  norm_num
  abel

end CFSG.LieType.D4Small.D4Datum
