module

public import CFSG.ClassicalInvolution.Q3.TL4D1ML32C
public import CFSG.ClassicalInvolution.Q3.TL4D1MBaseC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Generic Matrix
open scoped commutatorElement

noncomputable def sl3A : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by rw [det_eq_det3]; exact sl3Two_facts.1⟩

noncomputable def sl3B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by rw [det_eq_det3]; exact sl3Two_facts.2.1⟩

theorem sl3A_pow_three : sl3A ^ 3 = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact sl3Two_facts.2.2.1)

theorem sl3A_ne_one : sl3A ≠ 1 := fun h => sl3Two_facts.2.2.2.1 (congrArg Subtype.val h)

theorem sl3A_mul_ne : sl3A * sl3B ≠ sl3B * sl3A := fun h =>
  sl3Two_facts.2.2.2.2 (congrArg Subtype.val h)

theorem l32_not_two : ¬ IsPGroup 2 ↥l32 := by
  intro h2
  obtain ⟨k, hk⟩ := h2 ⟨lpermHom sl3A, lpermHom_mem_l32 sl3A⟩
  have h1 : lpermHom sl3A ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h3 : lpermHom sl3A ^ 3 = 1 := by rw [← map_pow, sl3A_pow_three, map_one]
  have hord : orderOf (lpermHom sl3A) = 1 := Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right k (by norm_num)) (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one h1)
  exact sl3A_ne_one (lpermHom_injective (by rw [orderOf_eq_one_iff.mp hord, map_one]))

theorem conj_mem_commutator_l32 {g x : Equiv.Perm (Fin 7)} (hg : g ∈ l32)
    (hx : x ∈ ⁅l32, l32⁆) : g * x * g⁻¹ ∈ ⁅l32, l32⁆ := by
  have h1 : conjSub g ⁅l32, l32⁆ = ⁅l32, l32⁆ := by
    unfold conjSub
    rw [Subgroup.map_commutator]
    have : l32.map (MulAut.conj g).toMonoidHom = l32 := conjSub_eq_self_of_mem hg
    rw [this]
  have := conj_mem_conjSub (n := g) hx
  rwa [h1] at this

theorem l32_perfect : ⁅l32, l32⁆ = l32 := by
  have hle : ⁅l32, l32⁆ ≤ l32 := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact l32.mul_mem (l32.mul_mem (l32.mul_mem ha hb) (l32.inv_mem ha)) (l32.inv_mem hb)
  rcases l32_normal hle fun g hg x hx => conj_mem_commutator_l32 hg hx with h | h
  · exfalso
    apply sl3A_mul_ne
    apply lpermHom_injective
    have hc := Subgroup.commutator_mem_commutator (lpermHom_mem_l32 sl3A)
      (lpermHom_mem_l32 sl3B)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    rw [map_mul, map_mul, hc]
  · exact h

theorem l32_sign : ∀ σ ∈ l32, Equiv.Perm.sign σ = 1 := by
  intro σ hσ
  rw [← l32_perfect] at hσ
  have h1 : Equiv.Perm.sign σ ∈ (⁅l32, l32⁆).map Equiv.Perm.sign := ⟨σ, hσ, rfl⟩
  rw [Subgroup.map_commutator] at h1
  have h2 : ⁅l32.map Equiv.Perm.sign, l32.map Equiv.Perm.sign⁆ ≤ ⊥ :=
    Subgroup.commutator_le.mpr fun a _ b _ => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  exact Subgroup.mem_bot.mp (h2 h1)

theorem l32_normal_not_two : ∀ Q : Subgroup (Equiv.Perm (Fin 7)), Q ≤ l32 →
    (∀ g ∈ l32, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) → ¬ IsPGroup 2 Q → Q = l32 := by
  intro Q hQ hQn h2
  rcases l32_normal hQ hQn with h | h
  · exact absurd (h ▸ IsPGroup.of_bot) h2
  · exact h

theorem l32_normal_two : ∀ Q : Subgroup (Equiv.Perm (Fin 7)), Q ≤ l32 →
    (∀ g ∈ l32, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) → IsPGroup 2 Q → Q = ⊥ := by
  intro Q hQ hQn h2
  rcases l32_normal hQ hQn with h | h
  · exact h
  · exact absurd (h ▸ h2) l32_not_two

theorem e64_normal : ModelNormal e64Sub :=
  aeBarOver_normal l32_sign l32_normal_not_two l32_pairTrans

theorem e64_perfect : ModelPerfect e64Sub :=
  aeBarOver_perfect l32_sign l32_perfect l32_pairTrans

end CFSG.ClassicalInvolution.Q3.TL4
