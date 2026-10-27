module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48TI
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin
open scoped MatrixGroups

abbrev Sl28 : Type := SL(2, GF8)

@[expose] def mk28 (a b c d : ℕ) : Matrix (Fin 2) (Fin 2) GF8 :=
  !![GF8.ofNat' a, GF8.ofNat' b; GF8.ofNat' c, GF8.ofNat' d]

@[expose] def slA : Sl28 := ⟨mk28 2 4 4 6, by decide⟩
@[expose] def slW : Sl28 := ⟨mk28 0 1 1 0, by decide⟩
@[expose] def slZ : Sl28 := slA ^ 3

@[expose] def slT : Subgroup Sl28 := Subgroup.zpowers slA
@[expose] def slD : Subgroup Sl28 := Subgroup.normalizer (slT : Set Sl28)

theorem card_sl28 : Nat.card Sl28 = 504 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem slA_pow9 : slA ^ 9 = 1 := by decide +kernel
theorem slA_pow3 : slA ^ 3 ≠ 1 := by decide +kernel
theorem slW_sq : slW * slW = 1 := by decide +kernel
theorem slW_conj : slW * slA * slW⁻¹ = slA⁻¹ := by decide +kernel
theorem slZ_val : (slZ : Matrix (Fin 2) (Fin 2) GF8) = mk28 1 1 1 0 := by decide +kernel

theorem orderOf_slA : orderOf slA = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := slA) (by simpa using slA_pow3)
    (by simpa using slA_pow9)
  simpa using this

theorem card_slT : Nat.card slT = 9 := by
  rw [slT, Nat.card_zpowers, orderOf_slA]

theorem mem_slT_iff (g : Sl28) : g ∈ slT ↔ ∃ k : Fin 9, g = slA ^ (k : ℕ) := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    refine ⟨⟨(n % 9).toNat, by omega⟩, ?_⟩
    conv_lhs => rw [← Int.emod_add_mul_ediv n 9]
    rw [zpow_add, zpow_mul]
    have h9 : slA ^ (9 : ℤ) = 1 := by exact_mod_cast slA_pow9
    rw [h9, one_zpow, mul_one, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]
  · rintro ⟨k, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers slA) _

@[expose] def slAPow : Fin 9 → Matrix (Fin 2) (Fin 2) GF8 :=
  ![mk28 1 0 0 1, mk28 2 4 4 6, mk28 2 6 6 4, mk28 1 1 1 0, mk28 6 2 2 4, mk28 4 2 2 6,
    mk28 0 1 1 1, mk28 4 6 6 2, mk28 6 4 4 2]

theorem slA_pow_val : ∀ k : Fin 9, (slA ^ (k : ℕ) : Matrix (Fin 2) (Fin 2) GF8) = slAPow k := by
  decide +kernel

theorem entries_cent : ∀ p q r s : GF8,
    p * GF8.ofNat' 1 + q * GF8.ofNat' 1 = GF8.ofNat' 1 * p + GF8.ofNat' 1 * r →
    p * GF8.ofNat' 1 + q * GF8.ofNat' 0 = GF8.ofNat' 1 * q + GF8.ofNat' 1 * s →
    r * GF8.ofNat' 1 + s * GF8.ofNat' 1 = GF8.ofNat' 1 * p + GF8.ofNat' 0 * r →
    r * GF8.ofNat' 1 + s * GF8.ofNat' 0 = GF8.ofNat' 1 * q + GF8.ofNat' 0 * s →
    p * s - q * r = 1 → ∃ k : Fin 9, !![p, q; r, s] = slAPow k := by
  decide +kernel

theorem cent_z {g : Sl28} (h : g * slZ = slZ * g) : g ∈ slT := by
  have hM : (g : Matrix (Fin 2) (Fin 2) GF8) * mk28 1 1 1 0 = mk28 1 1 1 0 * g := by
    have := congrArg Subtype.val h
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slZ_val] at this
  have hdet : (g : Matrix (Fin 2) (Fin 2) GF8).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, mk28] at e00 e01 e10 e11
  obtain ⟨k, hk⟩ := entries_cent _ _ _ _ e00 e01 e10 e11 hdet
  refine (mem_slT_iff g).2 ⟨k, Subtype.ext ?_⟩
  exact (Matrix.eta_fin_two _).trans (hk.trans (slA_pow_val k).symm)

theorem order3_slT : ∀ k : Fin 9, (slA ^ (k : ℕ)) ^ 3 = 1 → slA ^ (k : ℕ) ≠ 1 →
    slA ^ (k : ℕ) = slZ ∨ slA ^ (k : ℕ) = slZ⁻¹ := by decide +kernel

theorem slZ_pow3 : slZ ^ 3 = 1 := by
  rw [slZ, ← pow_mul]
  exact slA_pow9

theorem slZ_ne_one : slZ ≠ 1 := slA_pow3

theorem slW_conj_z : slW * slZ * slW⁻¹ = slZ⁻¹ := by
  have := conj_pow (a := slW) (b := slA) (i := 3)
  rw [slZ, ← this, slW_conj, inv_pow]

theorem slW_ne_pow : ∀ k : Fin 9, slW ≠ slA ^ (k : ℕ) := by decide +kernel

theorem aw_sq : ∀ k : Fin 9, (slA ^ (k : ℕ) * slW) * (slA ^ (k : ℕ) * slW) = 1 := by decide +kernel

theorem aw_ne_one : ∀ k : Fin 9, slA ^ (k : ℕ) * slW ≠ 1 := by decide +kernel

theorem w_normalizes : ∀ k : Fin 9, ∃ j : Fin 9, slW * slA ^ (k : ℕ) * slW⁻¹ = slA ^ (j : ℕ) := by
  decide +kernel

theorem isPGroup_slT : IsPGroup 3 slT := IsPGroup.of_card (n := 2) (by rw [card_slT]; norm_num)

@[expose] def SlInD (x : Sl28) : Prop := x ∈ slT ∨ ∃ t ∈ slT, x = t * slW

theorem slT_le_slD : slT ≤ slD := Subgroup.le_normalizer

theorem slW_mem_slD : slW ∈ slD := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  obtain ⟨k, rfl⟩ := (mem_slT_iff _).1 hx
  obtain ⟨j, hj⟩ := w_normalizes k
  rw [SetLike.mem_coe, hj]
  exact (mem_slT_iff _).2 ⟨j, rfl⟩

theorem slInD_of_conj_z {x : Sl28} (hx : x⁻¹ * slZ * x ∈ slT) : SlInD x := by
  obtain ⟨k, hk⟩ := (mem_slT_iff _).1 hx
  have h3 : (slA ^ (k : ℕ)) ^ 3 = 1 := by
    rw [← hk]
    have := conj_pow (a := x⁻¹) (b := slZ) (i := 3)
    simp only [inv_inv] at this
    rw [this, slZ_pow3]
    group
  have h1 : slA ^ (k : ℕ) ≠ 1 := by
    rw [← hk]
    intro h
    apply slZ_ne_one
    calc slZ = x * (x⁻¹ * slZ * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  rcases order3_slT k h3 h1 with h | h
  · left
    rw [h] at hk
    apply cent_z
    calc x * slZ = x * (x⁻¹ * slZ * x) := by rw [hk]
      _ = slZ * x := by group
  · right
    rw [h] at hk
    refine ⟨x * slW, ?_, by rw [mul_assoc, slW_sq, mul_one]⟩
    apply cent_z
    calc (x * slW) * slZ = x * (slW * slZ * slW⁻¹) * slW := by group
      _ = x * (x⁻¹ * slZ * x) * slW := by rw [slW_conj_z, hk]
      _ = slZ * (x * slW) := by group

theorem mem_slD_iff (x : Sl28) : x ∈ slD ↔ SlInD x := by
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ slD := slD.inv_mem hx
    have h1 : x⁻¹ * slA * x ∈ slT := by
      have := ((Subgroup.mem_normalizer_iff.1 hx') slA).1 (Subgroup.mem_zpowers slA)
      simpa using this
    have h2 : x⁻¹ * slZ * x ∈ slT := by
      have := conj_pow (a := x⁻¹) (b := slA) (i := 3)
      simp only [inv_inv] at this
      rw [slZ, ← this]
      exact slT.pow_mem h1 3
    exact slInD_of_conj_z h2
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact slT_le_slD h
    · exact slD.mul_mem (slT_le_slD ht) slW_mem_slD

theorem slW_not_mem_slT : slW ∉ slT := fun h => by
  obtain ⟨k, hk⟩ := (mem_slT_iff _).1 h
  exact slW_ne_pow k hk

theorem card_slD : Nat.card slD = 18 := by
  let f : slT ⊕ slT → slD := Sum.elim (fun t => ⟨t, slT_le_slD t.2⟩)
    (fun t => ⟨(t : Sl28) * slW, slD.mul_mem (slT_le_slD t.2) slW_mem_slD⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (t | t) (t' | t') h
      · have h' := congrArg (fun y : slD => (y : Sl28)) h
        simp only [f, Sum.elim_inl] at h'
        exact congrArg Sum.inl (Subtype.ext h')
      · exfalso
        have h' := congrArg (fun y : slD => (y : Sl28)) h
        simp only [f, Sum.elim_inl, Sum.elim_inr] at h'
        apply slW_not_mem_slT
        have : slW = (t' : Sl28)⁻¹ * t := by rw [h']; group
        rw [this]
        exact slT.mul_mem (slT.inv_mem t'.2) t.2
      · exfalso
        have h' := congrArg (fun y : slD => (y : Sl28)) h
        simp only [f, Sum.elim_inl, Sum.elim_inr] at h'
        apply slW_not_mem_slT
        have : slW = (t : Sl28)⁻¹ * t' := by rw [← h']; group
        rw [this]
        exact slT.mul_mem (slT.inv_mem t.2) t'.2
      · have h' := congrArg (fun y : slD => (y : Sl28)) h
        simp only [f, Sum.elim_inr] at h'
        exact congrArg Sum.inr (Subtype.ext (mul_right_cancel h'))
    · rintro ⟨x, hx⟩
      rcases (mem_slD_iff x).1 hx with h | ⟨t, ht, rfl⟩
      · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨t, ht⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sum, card_slT]

theorem T_cases : ∀ i : Fin 9, slA ^ (i : ℕ) = 1 ∨
    ((slA ^ (i : ℕ)) ^ 3 = 1 ∧ (slA ^ (i : ℕ) = slZ ∨ slA ^ (i : ℕ) = slZ⁻¹)) ∨
    ((slA ^ (i : ℕ)) ^ 3 = slZ ∨ (slA ^ (i : ℕ)) ^ 3 = slZ⁻¹) := by decide +kernel

theorem pelem_slD {y : Sl28} (hy : y ∈ slD) (h3 : ∃ m : ℕ, y ^ (3 ^ m) = 1) : y ∈ slT := by
  rcases (mem_slD_iff y).1 hy with h | ⟨t, ht, rfl⟩
  · exact h
  · exfalso
    obtain ⟨m, hm⟩ := h3
    obtain ⟨k, rfl⟩ := (mem_slT_iff _).1 ht
    obtain ⟨q, hq⟩ := (Odd.pow (Nat.odd_iff.2 rfl : Odd 3) : Odd (3 ^ m))
    have hsq : (slA ^ (k : ℕ) * slW) ^ 2 = 1 := by rw [sq]; exact aw_sq k
    rw [hq, pow_succ, pow_mul, hsq, one_pow, one_mul] at hm
    exact aw_ne_one k hm

theorem ti_slD {a : Sl28} (haD : a ∉ slD) {g : Sl28} (hg : g ∈ slT) (hag : a⁻¹ * g * a ∈ slT) :
    g = 1 := by
  by_contra hg1
  have key : ∃ e : Sl28, (e = slZ ∨ e = slZ⁻¹) ∧ a⁻¹ * e * a ∈ slT := by
    obtain ⟨i, rfl⟩ := (mem_slT_iff _).1 hg
    rcases T_cases i with h | ⟨-, h⟩ | h
    · exact absurd h hg1
    · exact ⟨_, h, hag⟩
    · refine ⟨(slA ^ (i : ℕ)) ^ 3, h, ?_⟩
      have := conj_pow (a := a⁻¹) (b := slA ^ (i : ℕ)) (i := 3)
      simp only [inv_inv] at this
      rw [← this]
      exact slT.pow_mem hag 3
  obtain ⟨e, he, hea⟩ := key
  have hz : a⁻¹ * slZ * a ∈ slT := by
    rcases he with rfl | rfl
    · exact hea
    · have := slT.inv_mem hea
      simpa [mul_assoc] using this
  exact haD ((mem_slD_iff a).2 (slInD_of_conj_z hz))

theorem maximal_slD (X : Subgroup Sl28) (hX : slD ≤ X) : X = slD ∨ X = ⊤ := by
  have hmod := relIndex_modEq_of_ti (p := 3) X slT slD slD slT_le_slD le_rfl hX isPGroup_slT
    (fun y hy h3 => pelem_slD hy h3) (fun a _ haD g hg hag => ti_slD haD hg hag)
  rw [Subgroup.relIndex_self, card_slT] at hmod
  have hidx : slD.index = 28 := by
    have := slD.card_mul_index
    rw [card_slD, card_sl28] at this
    omega
  have hdvd : slD.relIndex X ∣ 28 := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_index_of_le hX
  have key : ∀ r : ℕ, r ≤ 28 → r ∣ 28 → r ≡ 1 [MOD 9] → r = 1 ∨ r = 28 := by decide +kernel
  rcases key _ (Nat.le_of_dvd (by norm_num) hdvd) hdvd hmod with h | h
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h) hX
  · right
    have hmul := Subgroup.relIndex_mul_index hX
    rw [h, hidx] at hmul
    exact Subgroup.index_eq_one.1 (by omega)

end CFSG.AGLEmbedding.KFactProofs.Sp48
