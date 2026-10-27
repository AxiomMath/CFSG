module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsOrth
public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

open CFSG.Open CFSG.HardMathSupport.Solomon CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def HasThreeTwoTwo (W : Type) [Group W] : Prop :=
  ∃ x t₁ t₂ : W, orderOf x = 3 ∧ orderOf t₁ = 2 ∧ orderOf t₂ = 2 ∧ t₁ ≠ t₂ ∧
    t₁ * t₂ = t₂ * t₁ ∧ x * t₁ = t₁ * x ∧ x * t₂ = t₂ * x

theorem hasThreeTwoTwo_of_mulEquiv {W W' : Type} [Group W] [Group W'] (e : W ≃* W')
    (h : HasThreeTwoTwo W') : HasThreeTwoTwo W := by
  obtain ⟨x, t₁, t₂, hx, h1, h2, hne, h12, hx1, hx2⟩ := h
  refine ⟨e.symm x, e.symm t₁, e.symm t₂, by rwa [MulEquiv.orderOf_eq],
    by rwa [MulEquiv.orderOf_eq], by rwa [MulEquiv.orderOf_eq],
    fun h => hne (e.symm.injective h), ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, h12]
  · rw [← map_mul, ← map_mul, hx1]
  · rw [← map_mul, ← map_mul, hx2]

section Models

theorem hasThreeTwoTwo_perm : HasThreeTwoTwo (Equiv.Perm (Fin 8)) :=
  ⟨Equiv.swap 4 5 * Equiv.swap 5 6, Equiv.swap 0 1, Equiv.swap 2 3,
    orderOf_eq_prime (by decide) (by decide), orderOf_eq_prime (by decide) (by decide),
    orderOf_eq_prime (by decide) (by decide), by decide, by decide, by decide, by decide⟩

@[expose] def slX : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide⟩

@[expose] def slT₁ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

@[expose] def slT₂ : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![1, 0, 0, 1; 0, 1, 1, 1; 0, 0, 1, 0; 0, 0, 0, 1], by decide⟩

theorem hasThreeTwoTwo_SL : HasThreeTwoTwo (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
  ⟨slX, slT₁, slT₂, orderOf_eq_prime (by decide) (by decide),
    orderOf_eq_prime (by decide) (by decide), orderOf_eq_prime (by decide) (by decide),
    by decide, by decide, by decide, by decide⟩

@[expose] def oxM : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun i j =>
    match i, j with
    | .inl 0, .inl 0 => 1
    | .inr 0, .inr 0 => 1
    | .inl 1, .inr 2 => 1
    | .inl 2, .inr 1 => 1
    | .inr 1, .inl 2 => 1
    | .inr 1, .inr 1 => 1
    | .inr 2, .inl 1 => 1
    | .inr 2, .inr 2 => 1
    | _, _ => 0

@[expose] def ot₁M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun i j =>
    match i, j with
    | .inl 0, .inr 0 => 1
    | .inr 0, .inl 0 => 1
    | .inl 1, .inl 1 => 1
    | .inl 2, .inl 2 => 1
    | .inr 1, .inr 1 => 1
    | .inr 2, .inr 2 => 1
    | _, _ => 0

@[expose] def ot₂M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  Matrix.of fun i j =>
    match i, j with
    | .inl 0, .inl 0 => 1
    | .inr 0, .inr 0 => 1
    | .inl 1, .inl 2 => 1
    | .inl 2, .inl 1 => 1
    | .inr 1, .inr 2 => 1
    | .inr 2, .inr 1 => 1
    | _, _ => 0

@[expose] def oxGL : GL (Fin 3 ⊕ Fin 3) (ZMod 2) := ⟨oxM, oxM * oxM, by decide, by decide⟩

@[expose] def ot₁GL : GL (Fin 3 ⊕ Fin 3) (ZMod 2) := ⟨ot₁M, ot₁M, by decide, by decide⟩

@[expose] def ot₂GL : GL (Fin 3 ⊕ Fin 3) (ZMod 2) := ⟨ot₂M, ot₂M, by decide, by decide⟩

theorem mem_oPlus_of_preserves {g : GL (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (h : ∀ v : Fin 3 ⊕ Fin 3 → ZMod 2,
      GLAQPlus (ZMod 2) 3 ((g : Matrix _ _ (ZMod 2)).mulVec v) = GLAQPlus (ZMod 2) 3 v) :
    g ∈ GLAOrthGroup (GLAQPlus (ZMod 2) 3) := by
  change g ∈ CFSG.Assembly.LargeEvenOrthGroup (GLAQPlus (ZMod 2) 3)
  rw [CFSG.Assembly.largeEvenOrthGroup_def]
  exact Subgroup.subset_closure h

@[expose] def oX : ↥(GLAOrthGroup (GLAQPlus (ZMod 2) 3)) :=
  ⟨oxGL, mem_oPlus_of_preserves (by decide)⟩

@[expose] def oT₁ : ↥(GLAOrthGroup (GLAQPlus (ZMod 2) 3)) :=
  ⟨ot₁GL, mem_oPlus_of_preserves (by decide)⟩

@[expose] def oT₂ : ↥(GLAOrthGroup (GLAQPlus (ZMod 2) 3)) :=
  ⟨ot₂GL, mem_oPlus_of_preserves (by decide)⟩

theorem hasThreeTwoTwo_oPlus : HasThreeTwoTwo ↥(GLAOrthGroup (GLAQPlus (ZMod 2) 3)) :=
  ⟨oX, oT₁, oT₂, orderOf_eq_prime (by decide) (by decide),
    orderOf_eq_prime (by decide) (by decide), orderOf_eq_prime (by decide) (by decide),
    by decide, by decide, by decide, by decide⟩

end Models

section Orders

theorem card_SL_two (n : ℕ) [NeZero n] :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  rw [Matrix.card_SL_field, ZMod.card]
  simp

theorem pow_le_prod_SL (n : ℕ) :
    2 ^ ((n - 1) * n) ≤ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have h := Finset.pow_card_le_prod Finset.univ (fun i : Fin n => 2 ^ n - 2 ^ (i : ℕ))
    (2 ^ (n - 1)) (fun i _ => by
      have hi : (i : ℕ) ≤ n - 1 := by omega
      have h1 : 2 ^ (i : ℕ) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) hi
      have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      generalize 2 ^ (i : ℕ) = a at h1 ⊢
      generalize 2 ^ (n - 1) = b at h1 h2 ⊢
      omega)
  rwa [Finset.card_univ, Fintype.card_fin, ← pow_mul] at h

theorem eq_four_of_card_SL {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 20160 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = 40320) : n = 4 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [card_SL_two] at hc
  rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
  · revert hc
    decide
  · revert hc
    decide
  · rfl
  · have hb := pow_le_prod_SL n
    have h20 : 2 ^ 20 ≤ 2 ^ ((n - 1) * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (show 4 ≤ n - 1 by omega) h5)
    have : 2 ^ 20 = 1048576 := by norm_num
    omega

theorem card_Sp_ne {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card ↥(StatedSp n (ZMod 2)) = 20160 ∨ Nat.card ↥(StatedSp n (ZMod 2)) = 40320) :
    False := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_statedSp_cast (ZMod 2) n
  have hc' : Nat.card ↥(StatedSp n (ZMod 2)) =
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp n (ZMod 2)) := rfl
  rw [← hc', Nat.card_zmod] at h
  push_cast at h
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
  · have h720 : (Nat.card ↥(StatedSp 2 (ZMod 2)) : ℤ) = 720 := by
      rw [h]
      decide
    omega
  · have hdvd : (2 : ℤ) ^ 9 ∣ (Nat.card ↥(StatedSp n (ZMod 2)) : ℤ) := by
      rw [h]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by nlinarith)) _
    rcases hc with hc | hc <;> rw [hc] at hdvd <;> norm_num at hdvd

theorem card_glaPlus (n : ℕ) :
    Nat.card ↥(GLAOrthGroup (GLAQPlus (ZMod 2) n)) =
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadPlus n (ZMod 2))) :=
  Nat.card_congr (mcltf_glaOrthEquiv (mcltf_coe_quadPlus n)).toEquiv

theorem eq_three_of_card_glaPlus {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card ↥(GLAOrthGroup (GLAQPlus (ZMod 2) n)) = 20160 ∨
      Nat.card ↥(GLAOrthGroup (GLAQPlus (ZMod 2) n)) = 40320) : n = 3 := by
  rw [card_glaPlus] at hc
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) m
  rw [Nat.card_zmod] at h
  push_cast at h
  rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | h3
  · have h72 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadPlus (1 + 1) (ZMod 2))) : ℤ) = 72 := by
      rw [h]
      decide
    omega
  · rfl
  · exfalso
    have hdvd : (2 : ℤ) ^ 13 ∣ (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadPlus (m + 1) (ZMod 2))) : ℤ) := by
      rw [h, mul_assoc, mul_assoc, ← mul_assoc 2, ← pow_succ']
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by nlinarith)) _
    rcases hc with hc | hc <;> rw [hc] at hdvd <;> norm_num at hdvd

theorem card_glaMinus (n : ℕ) :
    Nat.card ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)) =
      Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1)) :=
  Nat.card_congr ((mcltf_glaOrthEquiv (mcltf_coe_quadMinusGLA n 1 1)).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr (mcltf_minusIsometry n 1 1))).toEquiv

theorem card_glaMinus_ne {n : ℕ} (hn : 1 ≤ n)
    (hc : Nat.card ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)) = 20160 ∨
      Nat.card ↥(GLAOrthGroup (GLAQMinus n (1 : ZMod 2) 1)) = 40320) : False := by
  rw [card_glaMinus] at hc
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := ZMod 2)
    mcltf_irr n
  rw [Nat.card_zmod] at h
  push_cast at h
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  · have h120 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (1 + 1) (ZMod 2) 1 1)) : ℤ) = 120 := by
      rw [h]
      decide
    omega
  · have h51840 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (2 + 1) (ZMod 2) 1 1)) : ℤ) = 51840 := by
      rw [h]
      decide
    omega
  · have hdvd : (2 : ℤ) ^ 13 ∣ (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus (n + 1) (ZMod 2) 1 1)) : ℤ) := by
      rw [h, mul_assoc, mul_assoc, ← mul_assoc 2, ← pow_succ']
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by nlinarith)) _
    rcases hc with hc | hc <;> rw [hc] at hdvd <;> norm_num at hdvd

theorem eq_eight_of_card_perm {n : ℕ}
    (hc : Nat.card (Equiv.Perm (Fin n)) = 20160 ∨ Nat.card (Equiv.Perm (Fin n)) = 40320) :
    n = 8 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  rcases (show n ≤ 7 ∨ n = 8 ∨ 9 ≤ n by omega) with h | h | h
  · have : n.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le h
    have h7 : (7 : ℕ).factorial = 5040 := by decide
    omega
  · exact h
  · have : (9 : ℕ).factorial ≤ n.factorial := Nat.factorial_le h
    have h9 : (9 : ℕ).factorial = 362880 := by decide
    omega

end Orders

theorem mcl_hasThreeTwoTwo {W : Type} [Group W] (h : UniquenessMaximal.IsMcLaughlinGroup W)
    (hc : Nat.card W = 20160 ∨ Nat.card W = 40320) : HasThreeTwoTwo W := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · let e' : W ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) := e.trans (mcltf_SLEquiv n).symm
    rw [Nat.card_congr e'.toEquiv] at hc
    obtain rfl := eq_four_of_card_SL hn hc
    exact hasThreeTwoTwo_of_mulEquiv e' hasThreeTwoTwo_SL
  · rw [Nat.card_congr e.toEquiv] at hc
    exact (card_Sp_ne hn hc).elim
  · rw [Nat.card_congr e.toEquiv] at hc
    obtain rfl := eq_three_of_card_glaPlus hn hc
    exact hasThreeTwoTwo_of_mulEquiv e hasThreeTwoTwo_oPlus
  · rw [Nat.card_congr e.toEquiv] at hc
    exact (card_glaMinus_ne hn hc).elim
  · rw [Nat.card_congr e.toEquiv] at hc
    obtain rfl := eq_eight_of_card_perm hc
    exact hasThreeTwoTwo_of_mulEquiv e hasThreeTwoTwo_perm

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64
