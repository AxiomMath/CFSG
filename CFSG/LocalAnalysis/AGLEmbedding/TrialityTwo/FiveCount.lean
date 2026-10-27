module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Five

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixedSpace (φ : V ≃ₗ[K] V) : Submodule K V :=
  LinearMap.ker (φ.toLinearMap - LinearMap.id)

theorem mem_fixedSpace {φ : V ≃ₗ[K] V} {v : V} : v ∈ fixedSpace φ ↔ φ v = v := by
  simp [fixedSpace, sub_eq_zero]

theorem pow_apply_of_mem_fixedSpace {φ : V ≃ₗ[K] V} {v : V} (hv : v ∈ fixedSpace φ) (n : ℕ) :
    (φ ^ n) v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, mem_fixedSpace.mp hv]

theorem pow_apply_mem {φ : V ≃ₗ[K] V} {W : Submodule K V} (hW : ∀ w ∈ W, φ w ∈ W) (n : ℕ)
    {w : V} (hw : w ∈ W) : (φ ^ n) w ∈ W := by
  induction n with
  | zero => simpa using hw
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply]; exact hW _ ih

theorem exists_pow_eq {φ : V ≃ₗ[K] V} (hφ : φ ^ 5 = 1) {h : V ≃ₗ[K] V}
    (hh : h ∈ Subgroup.zpowers φ) : ∃ n : ℕ, φ ^ n = h :=
  (Submonoid.mem_powers_iff _ _).mp
    ((isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hφ⟩).mem_powers_iff_mem_zpowers.mpr hh)

theorem isPGroup_zpowers {φ : V ≃ₗ[K] V} (hφ : φ ^ 5 = 1) : IsPGroup 5 (Subgroup.zpowers φ) := by
  rintro ⟨h, hh⟩
  obtain ⟨n, rfl⟩ := exists_pow_eq hφ hh
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
  rw [← pow_mul, mul_comm, pow_mul, hφ, one_pow]

def invariantSubMulAction {φ : V ≃ₗ[K] V} (hφ : φ ^ 5 = 1) {W : Submodule K V}
    (hW : ∀ w ∈ W, φ w ∈ W) : SubMulAction (Subgroup.zpowers φ) V where
  carrier := W
  smul_mem' := by
    intro h w hw
    obtain ⟨n, hn⟩ := exists_pow_eq hφ h.2
    change (h : V ≃ₗ[K] V) w ∈ W
    rw [← hn]
    exact pow_apply_mem hW n hw

theorem natCard_modEq_natCard_inf [Finite V] {φ : V ≃ₗ[K] V} (hφ : φ ^ 5 = 1)
    {W : Submodule K V} (hW : ∀ w ∈ W, φ w ∈ W) :
    Nat.card W ≡ Nat.card ↥(W ⊓ fixedSpace φ) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let S := invariantSubMulAction hφ hW
  have h := (isPGroup_zpowers hφ).card_modEq_card_fixedPoints S
  have e1 : Nat.card S = Nat.card W := Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have e2 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers φ) S) =
      Nat.card ↥(W ⊓ fixedSpace φ) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, mem_fixedSpace.mpr
          (congrArg Subtype.val (x.2 ⟨φ, Subgroup.mem_zpowers φ⟩))⟩
        invFun := fun y => ⟨⟨y.1, (Submodule.mem_inf.mp y.2).1⟩, fun h => Subtype.ext (by
          obtain ⟨n, hn⟩ := exists_pow_eq hφ h.2
          change (h : V ≃ₗ[K] V) y.1 = y.1
          rw [← hn]
          exact pow_apply_of_mem_fixedSpace (Submodule.mem_inf.mp y.2).2 n)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2] at h
  exact h

theorem two_pow_finrank_modEq [Finite K] (hK : Nat.card K = 2) [FiniteDimensional K V]
    {φ : V ≃ₗ[K] V} (hφ : φ ^ 5 = 1) {W : Submodule K V} (hW : ∀ w ∈ W, φ w ∈ W) :
    2 ^ finrank K W ≡ 2 ^ finrank K ↥(W ⊓ fixedSpace φ) [MOD 5] := by
  have : Finite V := Module.finite_of_finite K
  have h := natCard_modEq_natCard_inf hφ hW
  rwa [Module.natCard_eq_pow_finrank (K := K) (V := W),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(W ⊓ fixedSpace φ)), hK] at h

theorem two_pow_mod_five (a : ℕ) : 2 ^ a % 5 = 2 ^ (a % 4) % 5 := by
  conv_lhs => rw [← Nat.div_add_mod a 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem four_dvd_of_two_pow_modEq {a b : ℕ} (h : 2 ^ a ≡ 2 ^ b [MOD 5]) (ha : 4 ∣ a) :
    4 ∣ b := by
  have key : ∀ r < 4, 2 ^ 0 % 5 = 2 ^ r % 5 → r = 0 := by decide
  rw [Nat.ModEq, two_pow_mod_five a, two_pow_mod_five b, Nat.mod_eq_zero_of_dvd ha] at h
  exact Nat.dvd_of_mod_eq_zero (key _ (Nat.mod_lt _ (by norm_num)) h)

variable [Finite K] [FiniteDimensional K V] {φ : V ≃ₗ[K] V}

theorem four_dvd_finrank_inf (hK : Nat.card K = 2) (hφ : φ ^ 5 = 1) {W : Submodule K V}
    (hW : ∀ w ∈ W, φ w ∈ W) (h4 : 4 ∣ finrank K W) : 4 ∣ finrank K ↥(W ⊓ fixedSpace φ) :=
  four_dvd_of_two_pow_modEq (two_pow_finrank_modEq hK hφ hW) h4

theorem four_dvd_finrank_of_inf_eq_bot (hK : Nat.card K = 2) (hφ : φ ^ 5 = 1)
    {W : Submodule K V} (hW : ∀ w ∈ W, φ w ∈ W) (hWC : W ⊓ fixedSpace φ = ⊥) :
    4 ∣ finrank K W := by
  have h := two_pow_finrank_modEq hK hφ hW
  rw [hWC, finrank_bot] at h
  exact four_dvd_of_two_pow_modEq h.symm (dvd_zero 4)

theorem four_dvd_finrank_fixedSpace (hK : Nat.card K = 2) (hφ : φ ^ 5 = 1)
    (hV : 4 ∣ finrank K V) : 4 ∣ finrank K (fixedSpace φ) := by
  have h := four_dvd_finrank_inf hK hφ (W := ⊤) (fun _ _ => Submodule.mem_top)
    (by rwa [finrank_top])
  rwa [top_inf_eq] at h

@[expose] def normSum (φ : V ≃ₗ[K] V) (x : V) : V :=
  ∑ i ∈ Finset.range 5, (φ ^ i) x

omit [Finite K] [FiniteDimensional K V] in
theorem normSum_mem_fixedSpace (hφ : φ ^ 5 = 1) (x : V) : normSum φ x ∈ fixedSpace φ := by
  rw [mem_fixedSpace, normSum, map_sum]
  have h := (Finset.sum_range_succ' (fun i => (φ ^ i) x) 5).symm.trans
    (Finset.sum_range_succ (fun i => (φ ^ i) x) 5)
  simp only [hφ, pow_zero] at h
  have h' := add_right_cancel h
  rw [← h']
  exact Finset.sum_congr rfl fun i _ => by rw [pow_succ', LinearEquiv.mul_apply]

omit [Finite K] [FiniteDimensional K V] in
theorem normSum_mem {W : Submodule K V} (hW : ∀ w ∈ W, φ w ∈ W) {x : V} (hx : x ∈ W) :
    normSum φ x ∈ W :=
  W.sum_mem fun i _ => pow_apply_mem hW i hx

end CFSG.AGLEmbedding.TrialityTwo.Five
