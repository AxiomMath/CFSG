module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNMove

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_kernel_conjugate {K : Subgroup X} {t y z : X} (hKy : conjugate K y = conjugate K t)
    (hzK : z ∈ coreActionKernel K) (hyz : y * z = z * y) :
    z ∈ coreActionKernel (conjugate K t) := by
  rw [← hKy]
  apply FooteLit.mem_coreActionKernel_conjugate_iff.mpr
  rwa [hyz, mul_inv_cancel_right]

omit [Finite X] in
theorem relIndex_eq_two {W K : Subgroup X} {t : X} (htM : t ∈ normalizer (W : Set X))
    (htK : t ∉ normalizer (K : Set X)) (httK : t * t ∈ normalizer (K : Set X))
    (hr2 : ∀ m ∈ normalizer (W : Set X), conjugate K m = K ∨ conjugate K m = conjugate K t) :
    (normalizer (W : Set X) ⊓ normalizer (K : Set X)).relIndex (normalizer (W : Set X)) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, htM, fun b hb => ?_⟩
  by_cases hbK : b ∈ normalizer (K : Set X)
  · refine Or.inr ⟨mem_inf.mpr ⟨hb, hbK⟩, fun hbt => htK ?_⟩
    rw [show t = b⁻¹ * (b * t) by group]
    exact mul_mem (inv_mem hbK) (mem_inf.mp hbt).2
  · refine Or.inl ⟨mem_inf.mpr ⟨mul_mem hb htM, ?_⟩, fun h' => hbK (mem_inf.mp h').2⟩
    have hKb : conjugate K b = conjugate K t :=
      (hr2 b hb).resolve_left fun e => hbK (mem_normalizer_of_conjugate_eq e)
    apply mem_normalizer_of_conjugate_eq
    rw [← conjugate_conjugate, hKb, conjugate_conjugate, conjugate_eq_of_mem_normalizer httK]

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

section Four

variable (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
  (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup X}
  (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X)) (h1024 : Nat.card ↥(T ⊓ K) = 1024)
include e₁ hT2 hTM h1024

omit h hTM in
theorem exists_mul_of_mem_sup {x : X} (hxT : x ∈ T) (hxN : x ∈ normalizer (K : Set X))
    (hx : x ∈ K ⊔ coreActionKernel K) :
    ∃ k ∈ T ⊓ K, ∃ p ∈ T ⊓ coreActionKernel K, x = k * p := by
  have hS2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  have hdec := HeDiag.inf_sup_coreActionKernel_le' e₁ inf_le_right hS2 h1024'
    (mem_inf.mpr ⟨mem_inf.mpr ⟨hxT, hxN⟩, hx⟩)
  have hPR : T ⊓ normalizer (K : Set X) ⊓ coreActionKernel K ≤
      normalizer ((T ⊓ normalizer (K : Set X) ⊓ K : Subgroup X) : Set X) :=
    fun p hp => mem_normalizer_inf (le_normalizer (mem_inf.mp hp).1)
      (mem_coreActionKernel.mp (mem_inf.mp hp).2).1
  have hset : x ∈ ((T ⊓ normalizer (K : Set X) ⊓ K : Subgroup X) : Set X) *
      ((T ⊓ normalizer (K : Set X) ⊓ coreActionKernel K : Subgroup X) : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hPR]
    exact hdec
  obtain ⟨k, hk, p, hp, rfl⟩ := hset
  exact ⟨k, mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hk).1).1, (mem_inf.mp hk).2⟩, p,
    mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hp).1).1, (mem_inf.mp hp).2⟩, rfl⟩

theorem exists_order_four {t : X} (htT : t ∈ T) (htK : t ∉ normalizer (K : Set X))
    (httK : t * t ∈ normalizer (K : Set X))
    (hQ : ∀ x ∈ T, x ∈ coreActionKernel K → x ∈ coreActionKernel (conjugate K t) → x = 1)
    (hinv : ∀ y ∈ normalizer (W : Set X), orderOf y = 2 → y ∈ normalizer (K : Set X)) :
    ∃ u ∈ T, u ∉ normalizer (K : Set X) ∧ u ^ 4 = 1 ∧ u * u ≠ 1 ∧
      u * u ∈ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  have htM := hTM htT
  have hKt : conjugate K t ≠ K := fun e => htK (mem_normalizer_of_conjugate_eq e)
  have hKtK : K ≤ normalizer (conjugate K t : Set X) :=
    (GrS5.commutator_le_of_ne (conjugate_le_of_mem h.le_normalizer htM) h.le_normalizer
      (isPComponent_conjugate_subgroupOf htM h.isPComponent_K) h.isPComponent_K hKt).2
  have hck : ∀ k ∈ K, t⁻¹ * k * t ∈ coreActionKernel K := fun k hk =>
    h.conj_mem_coreActionKernel hTM hk htT hKt
  have hcK : ∀ {g x : X}, g ∈ normalizer (K : Set X) → x ∈ coreActionKernel K →
      g * x * g⁻¹ ∈ coreActionKernel K :=
    fun hg hx => HeDiag.conj_mem_coreActionKernel_of_mem hg hx
  have hKk : ∀ k ∈ K, conjugate K (t * k) = conjugate K t := fun k hk => by
    rw [← conjugate_conjugate, conjugate_eq_of_mem_normalizer (hKtK hk)]
  by_cases hin : t * t ∈ K ⊔ coreActionKernel K
  ·
    exfalso
    obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup e₁ hT2 h1024 (mul_mem htT htT) httK hin
    have hkT := (mem_inf.mp hk).1
    have hkK := (mem_inf.mp hk).2
    have hyT : t * k⁻¹ ∈ T := mul_mem htT (inv_mem hkT)
    have hyK : t * k⁻¹ ∉ normalizer (K : Set X) := fun hy => htK (by
      rw [show t = t * k⁻¹ * k by group]
      exact mul_mem hy (le_normalizer hkK))
    have hyy : t * k⁻¹ * (t * k⁻¹) = k * (p * (t⁻¹ * k⁻¹ * t)) * k⁻¹ := by
      calc t * k⁻¹ * (t * k⁻¹) = t * t * (t⁻¹ * k⁻¹ * t) * k⁻¹ := by group
        _ = k * p * (t⁻¹ * k⁻¹ * t) * k⁻¹ := by rw [hkp]
        _ = k * (p * (t⁻¹ * k⁻¹ * t)) * k⁻¹ := by group
    have hyyK : t * k⁻¹ * (t * k⁻¹) ∈ coreActionKernel K := by
      rw [hyy]
      exact hcK (le_normalizer hkK) (mul_mem (mem_inf.mp hp).2 (hck _ (inv_mem hkK)))
    have hyyKt := mem_kernel_conjugate (hKk _ (inv_mem hkK)) hyyK (by group)
    have hy1 := hQ _ (mul_mem hyT hyT) hyyK hyyKt
    have hy2 : orderOf (t * k⁻¹) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hy1) fun h1 => hyK (h1 ▸ one_mem _)
    exact hyK (hinv _ (hTM hyT) hy2)
  ·
    obtain ⟨y₀, hy₀S, hy₀K, hy₀y₀⟩ := exists_outer_sq e₁ (S := T ⊓ normalizer (K : Set X))
      inf_le_right hS2 h1024' (mem_inf.mpr ⟨mul_mem htT htT, httK⟩) hin
    have hy₀N := (mem_inf.mp hy₀S).2
    have hd := inv_mul_mem_sup_of_not_mem e₁ httK hy₀N hin hy₀K
    obtain ⟨k, hk, p, hp, hkp⟩ := exists_mul_of_mem_sup e₁ hT2 h1024
      (mul_mem (inv_mem (mul_mem htT htT)) (mem_inf.mp hy₀S).1)
      (mul_mem (inv_mem httK) hy₀N) hd
    have hkT := (mem_inf.mp hk).1
    have hkK := (mem_inf.mp hk).2
    have hpK := (mem_inf.mp hp).2
    have hy₀ : y₀ = t * t * (k * p) := (inv_mul_eq_iff_eq_mul.mp hkp)
    set c : X := p⁻¹ * (k⁻¹ * (t⁻¹ * k * t) * k) with hc
    have hcK' : c ∈ coreActionKernel K := by
      refine mul_mem (inv_mem hpK) ?_
      have h1 := hcK (inv_mem (le_normalizer hkK)) (hck k hkK)
      rwa [inv_inv] at h1
    have hu2 : t * k * (t * k) = y₀ * c := by
      rw [hy₀, hc]
      group
    have huT : t * k ∈ T := mul_mem htT hkT
    have huK : t * k ∉ normalizer (K : Set X) := fun hu => htK (by
      rw [show t = t * k * k⁻¹ by group]
      exact mul_mem hu (inv_mem (le_normalizer hkK)))
    have hu4K : t * k * (t * k) * (t * k * (t * k)) ∈ coreActionKernel K := by
      rw [hu2, show y₀ * c * (y₀ * c) = y₀ * y₀ * (y₀⁻¹ * c * y₀⁻¹⁻¹) * c by group]
      exact mul_mem (mul_mem hy₀y₀ (hcK (inv_mem hy₀N) hcK')) hcK'
    have hu4Kt := mem_kernel_conjugate (hKk k hkK) hu4K (by group)
    have hu4 := hQ _ (mul_mem (mul_mem huT huT) (mul_mem huT huT)) hu4K hu4Kt
    refine ⟨t * k, huT, huK, ?_, fun h1 => hy₀K ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      exact hu4
    · rw [hu2] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact mem_sup_right (inv_mem hcK')
    · rw [hu2]
      exact mul_mem hy₀N (mem_coreActionKernel.mp hcK').1

include h64 hOut in
theorem three_le_pRank_of_sq {u : X} (huT : u ∈ T) (huK : u ∉ normalizer (K : Set X))
    (huu : u * u ∈ normalizer (K : Set X)) (hu4 : u * u * (u * u) = 1) :
    3 ≤ pRank 2 ↥(T ⊓ centralizer ({u} : Set X)) := by
  have hS2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  obtain ⟨E, hET, hEf, hEe, hE8⟩ := HeDiag.exists_eight_fixed e₁ h64 hOut
    (inf_le_right : T ⊓ normalizer (K : Set X) ≤ _) hS2 h1024'
    (mem_inf.mpr ⟨mul_mem huT huT, huu⟩) hu4
  rw [HeDiag.inf_normalizer_inf] at hET
  have hKu : conjugate K u ≠ K := fun e => huK (mem_normalizer_of_conjugate_eq e)
  obtain ⟨hY, hinj, hψT⟩ := h.doubleHom_facts e₁ hT2 hTM huT hKu
  let φ : ↥E →* X := (doubleHom hY).comp (inclusion hET)
  have hφinj : Function.Injective φ := hinj.comp (inclusion_injective hET)
  refine three_le_pRank_of_le (isElemTwo_range hEe φ)
    (by rw [card_range_of_injective hφinj, hE8]) ?_
  rintro _ ⟨y, rfl⟩
  have hcy : Commute (u * u) (inclusion hET y : X) :=
    (mem_centralizer_singleton_iff.mp (hEf y.2)).symm
  exact mem_inf.mpr ⟨(mem_inf.mp (hψT _)).1, mem_centralizer_singleton_iff.mpr
    (commute_doubleHom_of_sq hY (inclusion hET y) hcy).symm.eq⟩

end Four

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
