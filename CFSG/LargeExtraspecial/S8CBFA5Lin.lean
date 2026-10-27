module

public import CFSG.LargeExtraspecial.S8CBFSL2N
public import CFSG.LargeExtraspecial.S8CBFCrit

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module
open scoped Pointwise

theorem le_of_perfect_of_semidirect_sl2 {G : Type*} [Group G] {C Q L R N : Subgroup G}
    {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hC : (C : Set G) = (Q : Set G) * (L : Set G)) (hLC : L ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hQL : Q ⊓ L = ⊥)
    (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (hρ : ρ.range = L)
    (hρi : Function.Injective ρ) (hRC : R ≤ C) (hRperf : ⁅R, R⁆ = R) (hNR : N ≤ R)
    (hnorm : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N) (hN2 : IsPGroup 2 N) : N ≤ Q := by
  have := normal_subgroupOf_of_normalizes hQn
  obtain ⟨e, -⟩ := exists_mulEquiv_quotient_of_mul_eq hC hLC hQn hQL
  let ρL : Matrix.SpecialLinearGroup (Fin 2) K ≃* L :=
    (MonoidHom.ofInjective hρi).trans (MulEquiv.subgroupCongr hρ)
  let E : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥C ⧸ Q.subgroupOf C := ρL.trans e
  let qm := QuotientGroup.mk' (Q.subgroupOf C)
  let M₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    ((R.subgroupOf C).map qm).map E.symm.toMonoidHom
  let T₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
    ((N.subgroupOf C).map qm).map E.symm.toMonoidHom
  have hR'perf : ⁅R.subgroupOf C, R.subgroupOf C⁆ = R.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hRC, hRperf]
  have hM₀ : ⁅M₀, M₀⁆ = M₀ := by
    simp only [M₀]
    rw [← map_commutator, ← map_commutator, hR'perf]
  have hT₀ : IsPGroup 2 T₀ := ((hN2.comap_subtype (K := C)).map _).map _
  have hMT : ∀ g ∈ M₀, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀ := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩ _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨qm (r * n * r⁻¹), ⟨r * n * r⁻¹, ?_, rfl⟩, by simp⟩
    change r ∈ R.subgroupOf C at hr
    change n ∈ N.subgroupOf C at hn
    change r * n * r⁻¹ ∈ N.subgroupOf C
    rw [mem_subgroupOf] at hr hn ⊢
    simpa using hnorm r hr n hn
  intro n hn
  by_contra hnQ
  have hT₀ne : T₀ ≠ ⊥ := by
    intro hbot
    have hmem : E.symm (qm ⟨n, hRC (hNR hn)⟩) ∈ T₀ :=
      ⟨qm ⟨n, hRC (hNR hn)⟩, ⟨⟨n, hRC (hNR hn)⟩, mem_subgroupOf.mpr hn, rfl⟩, rfl⟩
    rw [hbot, mem_bot, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
    exact hnQ hmem
  have hM₀bot := sl2_eq_bot_of_perfect_of_normalizes M₀ T₀ hM₀ hT₀ hMT hT₀ne
  apply hT₀ne
  rw [eq_bot_iff, ← hM₀bot]
  exact map_mono (map_mono fun x hx => hNR hx)

theorem card_le_of_bilinear {K : Type*} [Field K] [Finite K] {n : ℕ}
    (W : Subgroup (Multiplicative (Fin n → K))) (β : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K)
    (h01 : ∀ w ∈ W, ∀ w' ∈ W, β w.toAdd w'.toAdd = 0 ∨ β w.toAdd w'.toAdd = 1)
    (hnd : ∀ w ∈ W, (∀ w' ∈ W, β w.toAdd w'.toAdd = 0) → w = 1) : Nat.card W ≤ 2 ^ n := by
  classical
  let t : Set (Fin n → K) := Multiplicative.toAdd '' (W : Set (Multiplicative (Fin n → K)))
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K t
  have : Fintype b := Fintype.ofFinite b
  have hb : Fintype.card b ≤ n := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_fin_fun] at this
  let Φ : W → (b → Bool) := fun w v => decide (β (w : Multiplicative (Fin n → K)).toAdd v = 1)
  have hΦ : Function.Injective Φ := by
    intro w₁ w₂ h
    have hv : ∀ v ∈ b, β (w₁ : Multiplicative (Fin n → K)).toAdd v =
        β (w₂ : Multiplicative (Fin n → K)).toAdd v := by
      intro v hvb
      obtain ⟨w', hw', rfl⟩ := hbt hvb
      have h1 := congrFun h ⟨_, hvb⟩
      simp only [Φ] at h1
      rcases h01 _ w₁.2 _ hw' with h2 | h2 <;> rcases h01 _ w₂.2 _ hw' with h3 | h3
      · rw [h2, h3]
      · rw [h2, h3] at h1
        simp at h1
      · rw [h2, h3] at h1
        simp at h1
      · rw [h2, h3]
    let d : Multiplicative (Fin n → K) :=
      (w₁ : Multiplicative (Fin n → K)) * ((w₂ : Multiplicative (Fin n → K)))⁻¹
    have hdW : d ∈ W := W.mul_mem w₁.2 (W.inv_mem w₂.2)
    have hdv : ∀ v ∈ b, β d.toAdd v = 0 := by
      intro v hvb
      simp only [d, toAdd_mul, toAdd_inv, map_add, map_neg, LinearMap.add_apply,
        LinearMap.neg_apply, hv v hvb, add_neg_cancel]
    have hspan_le : Submodule.span K b ≤ LinearMap.ker (β d.toAdd) :=
      Submodule.span_le.mpr fun v hvb => hdv v hvb
    have hd1 := hnd d hdW fun w' hw' => by
      have hmem : w'.toAdd ∈ Submodule.span K b := by
        rw [hspan]
        exact Submodule.subset_span ⟨w', hw', rfl⟩
      exact hspan_le hmem
    apply Subtype.ext
    simpa [d, mul_inv_eq_one] using hd1
  calc Nat.card W ≤ Nat.card (b → Bool) := Nat.card_le_card_of_injective Φ hΦ
    _ = 2 ^ Fintype.card b := by simp [Nat.card_eq_fintype_card]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hb

end CFSG.LargeExtraspecial.S8
