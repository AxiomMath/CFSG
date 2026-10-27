module

public import CFSG.GH74.KGroups.L3EpsBlockLin
public import CFSG.GH74.KGroups.L3EpsWreath
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.GH74.Generic.S3

open Subgroup CFSG CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

theorem neg_one_mem_center_sl2 {F : Type} [Field F] : (-1 : SL(2, F)) ∈ center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem neg_one_ne_one_sl2 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.SpecialLinearGroup.coe_neg] at h1
  apply h2
  linear_combination -h1

theorem card_center_sl2 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) : Nat.card (center SL(2, F)) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_mem _⟩, ⟨-1, neg_one_mem_center_sl2⟩, ?_, ?_⟩
  · intro h
    exact neg_one_ne_one_sl2 h2 (congrArg Subtype.val h).symm
  · ext ⟨x, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true, Subtype.mk.injEq]
    exact sl2c_center_eq hx

theorem sl2_no_perm_embedding_le_eleven {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) {n : ℕ} (hn : n ≤ 11) (θ : SL(2, F) →* Equiv.Perm (Fin n))
    (hθ : Function.Injective θ) : False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF2 : ringChar F ≠ 2 := by
    intro h
    have h' := (FiniteField.even_card_iff_char_two (F := F)).1 h
    rw [← Nat.card_eq_fintype_card] at h'
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  set Λ := SL(2, F) with hΛ
  set z : Λ := -1 with hz
  have hzne : z ≠ 1 := neg_one_ne_one_sl2 h2
  have hq : IsQuasisimple Λ := isQuasisimple_sl2c (by omega)
  obtain ⟨i, hzi⟩ : ∃ i : Fin n, θ z i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hzne (hθ (Equiv.ext fun j => by simpa using hcon j))
  let _inst : MulAction Λ (Fin n) := MulAction.compHom (Fin n) θ
  have hsmul : ∀ (g : Λ) (j : Fin n), g • j = θ g j := fun g j => rfl
  set S : Subgroup Λ := MulAction.stabilizer Λ i with hS
  have hSmem : ∀ g : Λ, g ∈ S ↔ θ g i = i := fun g => by
    rw [hS, MulAction.mem_stabilizer_iff, hsmul]
  have hzS : z ∉ S := fun h => hzi ((hSmem z).1 h)
  have hSodd : Odd (Nat.card S) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (even_iff_two_dvd.1 hev)
    have hx2 : (x : Λ) * x = 1 := by
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      exact congrArg Subtype.val this
    have hx1 : (x : Λ) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      omega
    rcases sl2c_sq_eq_one hF2 hx2 with h | h
    · exact hx1 h
    · exact hzS (by have h' : (x : Λ) = z := h; rw [← h']; exact x.2)
  have hidx : S.index = (MulAction.orbit Λ i).ncard := MulAction.index_stabilizer Λ i
  have horbn : (MulAction.orbit Λ i).ncard ≤ n := by
    calc (MulAction.orbit Λ i).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = n := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hΛcard : Nat.card Λ = Nat.card F * (Nat.card F ^ 2 - 1) :=
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F
  have h8 : 8 ∣ Nat.card Λ := by
    rw [hΛcard]
    obtain ⟨k, hk⟩ := hodd
    have hq2 : Nat.card F ^ 2 - 1 = 4 * (k * (k + 1)) := by
      rw [hk]
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      omega
    rw [hq2]
    have : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    obtain ⟨m, hm⟩ := this
    exact ⟨Nat.card F * m, by rw [hm]; ring⟩
  have hSΛ : Nat.card S * S.index = Nat.card Λ := Subgroup.card_mul_index S
  have hcop : Nat.Coprime 8 (Nat.card S) := by
    have : Nat.Coprime (2 ^ 3) (Nat.card S) := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 hSodd)
    simpa using this
  have h8idx : 8 ∣ S.index := by
    have : 8 ∣ S.index * Nat.card S := by rw [mul_comm, hSΛ]; exact h8
    exact hcop.dvd_of_dvd_mul_right this
  have hidx0 : 0 < S.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hidx8 : S.index = 8 := by omega
  set C : Subgroup Λ := center Λ with hC
  have hC2 : Nat.card C = 2 := card_center_sl2 h2
  set π : Λ →* Λ ⧸ C := QuotientGroup.mk' C with hπ
  have hπS : Function.Injective (π.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsC : (s : Λ) ∈ C := (QuotientGroup.eq_one_iff _).1 hs
    rcases sl2c_center_eq hsC with h | h
    · exact Subtype.ext h
    · exact absurd (by have h' : (s : Λ) = z := h; rw [← h']; exact s.2) hzS
  set S' : Subgroup (Λ ⧸ C) := S.map π with hS'
  have hS'card : Nat.card S' = Nat.card S := by
    have hrange : (π.comp S.subtype).range = S' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hπS).toEquiv).symm
  have hbar : Nat.card (Λ ⧸ C) * 2 = Nat.card Λ := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hC2]
  have hbarcard : Nat.card (Λ ⧸ C) = 4 * Nat.card S := by
    have h1 : Nat.card Λ = 8 * Nat.card S := by rw [← hSΛ, hidx8, mul_comm]
    omega
  have hS'idx : S'.index = 4 := by
    have h1 : Nat.card S' * S'.index = Nat.card (Λ ⧸ C) := Subgroup.card_mul_index S'
    rw [hS'card, hbarcard] at h1
    have hS0 : 0 < Nat.card S := Nat.card_pos
    nlinarith
  have hsimple : IsSimpleGroup (Λ ⧸ C) := hq.2.1
  have hbig : 60 ≤ Nat.card (Λ ⧸ C) := by
    have h1 : 120 ≤ Nat.card Λ := by
      rw [hΛcard]
      have h24 : 24 ≤ Nat.card F ^ 2 - 1 := by
        have : 25 ≤ Nat.card F ^ 2 := by nlinarith
        omega
      calc 120 = 5 * 24 := by norm_num
        _ ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h5 h24
    omega
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S'.normalCore with hb | ht
  · have hdvd : S'.normalCore.index ∣ S'.index.factorial :=
      Subgroup.index_normalCore_dvd_factorial_index S'
    rw [hb, Subgroup.index_bot, hS'idx] at hdvd
    have : Nat.card (Λ ⧸ C) ≤ 24 := Nat.le_of_dvd (by norm_num) (by simpa [Nat.factorial] using hdvd)
    omega
  · have hle : (⊤ : Subgroup (Λ ⧸ C)) ≤ S' := ht ▸ S'.normalCore_le
    have : S' = ⊤ := top_le_iff.1 hle
    rw [this, Subgroup.index_top] at hS'idx
    omega

end CFSG.GH74.Generic.S3
