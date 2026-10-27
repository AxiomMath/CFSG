module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open scoped Pointwise

variable {Γ : Type*} [Group Γ]

private lemma ffRA_pow_mem_range {n : ℕ} {e : Fin n → Γ} {one : Fin n}
    (hone : e one = 1) {mul : Fin n → Fin n → Fin n}
    (hmul : ∀ i j, e (mul i j) = e i * e j) (i : Fin n) (j : ℕ) :
    e i ^ j ∈ Set.range e := by
  induction j with
  | zero => exact ⟨one, by rw [pow_zero, hone]⟩
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih
    exact ⟨mul a i, by rw [hmul a i, ha, pow_succ]⟩

private lemma ffRA_inv_mem_range [Finite Γ] {n : ℕ} {e : Fin n → Γ} {one : Fin n}
    (hone : e one = 1) {mul : Fin n → Fin n → Fin n}
    (hmul : ∀ i j, e (mul i j) = e i * e j) (i : Fin n) :
    (e i)⁻¹ ∈ Set.range e := by
  have hpos : 0 < orderOf (e i) := orderOf_pos _
  obtain ⟨a, ha⟩ := ffRA_pow_mem_range hone hmul i (orderOf (e i) - 1)
  refine ⟨a, ha.trans ?_⟩
  have h1 : e i ^ (orderOf (e i) - 1) * e i = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  exact eq_inv_of_mul_eq_one_left h1

theorem ffRA_exists_conj_le [Finite Γ] {S : Subgroup Γ} (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.index) {E : Subgroup Γ} (hE : IsPGroup 2 E) :
    ∃ g : Γ, ∀ y ∈ E, g * y * g⁻¹ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ss : Sylow 2 Γ := hS.toSylow hidx
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P Ss
  refine ⟨g, fun y hy => ?_⟩
  have hyP : y ∈ (P : Subgroup Γ) := hEP hy
  have hmem : MulAut.conj g • y ∈ MulAut.conj g • (P : Subgroup Γ) :=
    Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (P : Subgroup Γ) hyP
  have hcoe : MulAut.conj g • (P : Subgroup Γ) = S := by
    rw [← Sylow.coe_subgroup_smul, hg]
    exact IsPGroup.toSylow_coe hS hidx
  rw [hcoe, MulAut.smul_def, MulAut.conj_apply] at hmem
  exact hmem

theorem ffRA_exists_conj_range [Finite Γ] {n k m : ℕ} (e : Fin n → Γ) (he : Function.Injective e)
    (one : Fin n) (hone : e one = 1) (mul : Fin n → Fin n → Fin n)
    (hmul : ∀ i j, e (mul i j) = e i * e j) (hn : n = 2 ^ k) (hm : Odd m)
    (hcard : Nat.card Γ = n * m) {E : Subgroup Γ} (hE : IsPGroup 2 E) :
    ∃ g : Γ, ∀ y ∈ E, ∃ i, e i = g * y * g⁻¹ := by
  classical
  let Sg : Subgroup Γ :=
    { carrier := Set.range e
      one_mem' := ⟨one, hone⟩
      mul_mem' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨mul i j, hmul i j⟩
      inv_mem' := by
        rintro _ ⟨i, rfl⟩
        exact ffRA_inv_mem_range hone hmul i }
  have hcardSg : Nat.card Sg = n := by
    change Nat.card (Set.range e) = n
    rw [Nat.card_range_of_injective he, Nat.card_fin]
  have hSgp : IsPGroup 2 Sg := IsPGroup.of_card (hcardSg.trans hn)
  have hpos : 0 < n := by
    rw [hn]
    exact pow_pos (by norm_num) k
  have hidxeq : Sg.index = m := by
    refine Nat.mul_left_cancel hpos ?_
    calc n * Sg.index = Nat.card Sg * Sg.index := by rw [hcardSg]
      _ = Nat.card Γ := Subgroup.card_mul_index Sg
      _ = n * m := hcard
  have hidx : ¬ 2 ∣ Sg.index := by
    rw [hidxeq]
    exact hm.not_two_dvd_nat
  obtain ⟨g, hg⟩ := ffRA_exists_conj_le hSgp hidx hE
  exact ⟨g, fun y hy => hg y hy⟩

end CFSG.OddStandard.SmallF3.Omega
