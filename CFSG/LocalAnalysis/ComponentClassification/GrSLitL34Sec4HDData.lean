module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HDSwap

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

structure SwapData (M K T : Subgroup X) (a : X) : Prop where
  orderOf_eq : orderOf a = 2
  mem_M : a ∈ M
  le_M : K ≤ M
  isPComponent : IsPComponent 2 (K.subgroupOf M)
  conjugate_ne : conjugate K a ≠ K
  only : ∀ K₂ : Subgroup X, K₂ ≤ M → IsPComponent 2 (K₂.subgroupOf M) →
    K₂ = K ∨ K₂ = conjugate K a
  kernel_eq_bot : T ⊓ coreActionKernel K ⊓ coreActionKernel (conjugate K a) = ⊥
  isPGroup : IsPGroup 2 T
  T_le : T ≤ M
  mem_T : a ∈ T
  card_left : Nat.card ↥(T ⊓ K) = 1024
  card_right : Nat.card ↥(T ⊓ conjugate K a) = 1024

omit [Finite X] in
theorem conjugate_injective {H H' : Subgroup X} {g : X} (h : conjugate H g = conjugate H' g) :
    H = H' := by
  rw [← conjugate_conjugate_inv H g, h, conjugate_conjugate_inv]

theorem eq_one_of_mem_oddIn {S J : Subgroup X} (hS2 : IsPGroup 2 S) {x : X} (hxS : x ∈ S)
    (hxO : x ∈ oddIn J) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (orderOf x) :=
    (UnbalancedCorr.odd_card_map_pPrimeCore J).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxO)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨x, hxS⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · rw [hk, pow_succ] at hodd
    exact absurd (even_iff_two_dvd.mpr (dvd_mul_left 2 _)) (Nat.not_even_iff_odd.mpr hodd)

namespace SwapData

variable {M K T : Subgroup X} {a : X} (h : SwapData M K T a)
include h

omit [Finite X] in
theorem mul_self : a * a = 1 := by
  rw [← pow_two, ← h.orderOf_eq, pow_orderOf_eq_one]

omit [Finite X] in
theorem isPComponent_right : IsPComponent 2 ((conjugate K a).subgroupOf M) :=
  isPComponent_conjugate_subgroupOf h.mem_M h.isPComponent

omit [Finite X] in
theorem le_M_right : conjugate K a ≤ M := conjugate_le_of_mem h.le_M h.mem_M

omit [Finite X] in
theorem conj_cases {t : X} (ht : t ∈ T) :
    (conjugate K t = K ∨ conjugate K t = conjugate K a) ∧
      (conjugate (conjugate K a) t = K ∨ conjugate (conjugate K a) t = conjugate K a) :=
  ⟨h.only _ (conjugate_le_of_mem h.le_M (h.T_le ht))
      (isPComponent_conjugate_subgroupOf (h.T_le ht) h.isPComponent),
    h.only _ (conjugate_le_of_mem h.le_M_right (h.T_le ht))
      (isPComponent_conjugate_subgroupOf (h.T_le ht) h.isPComponent_right)⟩

omit [Finite X] in
theorem mem_normalizer_right {t : X} (ht : t ∈ T) (htK : t ∈ normalizer (K : Set X)) :
    t ∈ normalizer (conjugate K a : Set X) := by
  rw [mem_normalizer_iff_conjugate_eq] at htK ⊢
  rcases (h.conj_cases ht).2 with h1 | h1
  · exact absurd (conjugate_injective (h1.trans htK.symm)) h.conjugate_ne
  · exact h1

omit [Finite X] in
theorem swap {t : X} (ht : t ∈ T) (htK : t ∉ normalizer (K : Set X)) :
    conjugate K t = conjugate K a ∧ conjugate (conjugate K a) t = K := by
  rw [mem_normalizer_iff_conjugate_eq] at htK
  have h1 := (h.conj_cases ht).1.resolve_left htK
  refine ⟨h1, (h.conj_cases ht).2.resolve_right fun h2 => h.conjugate_ne ?_⟩
  exact (conjugate_injective (h1.trans h2.symm)).symm

omit [Finite X] in
theorem conj_mem_sup {t x : X} (ht : t ∈ T)
    (hx : x ∈ T ⊓ K ∨ x ∈ T ⊓ conjugate K a) :
    t * x * t⁻¹ ∈ T ⊓ K ⊔ T ⊓ conjugate K a := by
  have hxT : x ∈ T := by rcases hx with hx | hx <;> exact (mem_inf.mp hx).1
  have hT : t * x * t⁻¹ ∈ T := mul_mem (mul_mem ht hxT) (inv_mem ht)
  have hmem : ∀ {H : Subgroup X}, x ∈ H → t * x * t⁻¹ ∈ conjugate H t⁻¹ := fun {H} hxH => by
    rw [mem_conjugate_iff, show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group]
    exact hxH
  have hcases := h.conj_cases (inv_mem ht)
  have fin : ∀ {H : Subgroup X}, (H = K ∨ H = conjugate K a) → t * x * t⁻¹ ∈ H →
      t * x * t⁻¹ ∈ T ⊓ K ⊔ T ⊓ conjugate K a := by
    rintro H (rfl | rfl) h1
    · exact mem_sup_left (mem_inf.mpr ⟨hT, h1⟩)
    · exact mem_sup_right (mem_inf.mpr ⟨hT, h1⟩)
  rcases hx with hx | hx
  · exact fin hcases.1 (hmem (mem_inf.mp hx).2)
  · exact fin hcases.2 (hmem (mem_inf.mp hx).2)

omit [Finite X] in
theorem le_normalizer_sup :
    T ≤ normalizer ((T ⊓ K ⊔ T ⊓ conjugate K a : Subgroup X) : Set X) := by
  have hmap : ∀ t ∈ T, ∀ x ∈ T ⊓ K ⊔ T ⊓ conjugate K a,
      t * x * t⁻¹ ∈ T ⊓ K ⊔ T ⊓ conjugate K a := by
    intro t ht x hx
    have hle : T ⊓ K ⊔ T ⊓ conjugate K a ≤
        (T ⊓ K ⊔ T ⊓ conjugate K a).comap (MulAut.conj t).toMonoidHom :=
      sup_le (fun y hy => h.conj_mem_sup ht (Or.inl hy))
        (fun y hy => h.conj_mem_sup ht (Or.inr hy))
    exact hle hx
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  refine ⟨hmap t ht x, fun hx => ?_⟩
  have h1 := hmap t⁻¹ (inv_mem ht) _ hx
  rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1

theorem commute_left_right {x y : X} (hx : x ∈ T ⊓ K) (hy : y ∈ T ⊓ conjugate K a) :
    x * y = y * x := by
  have hne : K ≠ conjugate K a := fun e => h.conjugate_ne e.symm
  have hKK' := GrS5.commutator_le_inf_oddIn h.le_M h.le_M_right h.isPComponent
    h.isPComponent_right hne
  have h1 : ⁅x, y⁆ ∈ oddIn K :=
    (mem_inf.mp (hKK' (commutator_mem_commutator (mem_inf.mp hx).2 (mem_inf.mp hy).2))).1
  have h2 : ⁅x, y⁆ ∈ T := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).1 (mem_inf.mp hy).1)
      (inv_mem (mem_inf.mp hx).1)) (inv_mem (mem_inf.mp hy).1)
  exact commutatorElement_eq_one_iff_mul_comm.mp (eq_one_of_mem_oddIn h.isPGroup h2 h1)

theorem exists_central : ∃ ζ ∈ T ⊓ K ⊔ T ⊓ conjugate K a, orderOf ζ = 2 ∧
    ∀ s ∈ T, s * ζ = ζ * s := by
  refine exists_central_involution h.isPGroup (sup_le inf_le_left inf_le_left)
    h.le_normalizer_sup fun hbot => ?_
  have h1 : T ⊓ K ≤ ⊥ := hbot ▸ le_sup_left
  have h2 := card_le_of_le h1
  rw [h.card_left, card_bot] at h2
  omega

theorem le_coreActionKernel :
    K ≤ coreActionKernel (conjugate K a) ∧ conjugate K a ≤ coreActionKernel K := by
  have hne : K ≠ conjugate K a := fun e => h.conjugate_ne e.symm
  have hKK' := GrS5.commutator_le_inf_oddIn h.le_M h.le_M_right h.isPComponent
    h.isPComponent_right hne
  refine ⟨fun y hy => mem_coreActionKernel.mpr ⟨(GrS5.commutator_le_of_ne h.le_M_right h.le_M
    h.isPComponent_right h.isPComponent hne.symm).2 hy, fun j hj => ?_⟩,
    fun y hy => mem_coreActionKernel.mpr ⟨(GrS5.commutator_le_of_ne h.le_M h.le_M_right
    h.isPComponent h.isPComponent_right hne).2 hy, fun j hj => ?_⟩⟩
  · have h1 := (mem_inf.mp (hKK' (commutator_mem_commutator (inv_mem hy) (inv_mem hj)))).2
    rw [commutatorElement_def, inv_inv, inv_inv] at h1
    have h2 := inv_mem h1
    rwa [show (y⁻¹ * j⁻¹ * y * j)⁻¹ = j⁻¹ * y⁻¹ * j * y by group] at h2
  · have h1 := (mem_inf.mp (hKK' (commutator_mem_commutator (inv_mem hj) (inv_mem hy)))).1
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1

end SwapData

end CFSG.ComponentClassification.GrSLit.HeDiag
