module

public import CFSG.LieType.Universal.Spin.Chevalley.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Universal.Spin (upperSL2 upperSL2_add upperSL2_zero coe_upperSL2)
open scoped MatrixGroups

@[expose] def FKSwap {G : Type*} [Group G] (φ : MulAut G) (ℓ : Subgroup G) : Prop :=
  ∃ w ∈ ℓ, w ^ 3 = 1 ∧ w ≠ 1 ∧ ∀ h ∈ ℓ, φ w ≠ h * w * h⁻¹

private lemma fk_map_upperSL2 {R S : Type*} [Field R] [Field S] (f : R →+* S) (c : R) :
    Matrix.SpecialLinearGroup.map f (upperSL2 c) = upperSL2 (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

private lemma fk_map_ringEquiv_symm_map {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : SL(2, R)) :
    Matrix.SpecialLinearGroup.map e.symm.toRingHom
      (Matrix.SpecialLinearGroup.map e.toRingHom x) = x := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

private lemma fk_upperSL2_one_ne_one : (upperSL2 (1 : GaloisField 3 1)) ≠ 1 := by
  intro h
  have h01 := congrArg (fun M : SL(2, GaloisField 3 1) =>
    (M : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 0 1) h
  simp [coe_upperSL2] at h01

private lemma fk_upperSL2_one_pow_three :
    (upperSL2 (1 : GaloisField 3 1)) ^ 3 = 1 := by
  have hchar : (3 : GaloisField 3 1) = 0 := CharP.cast_eq_zero (GaloisField 3 1) 3
  have e : (upperSL2 (1 : GaloisField 3 1)) ^ 3 = upperSL2 (1 + 1 + 1) := by
    rw [upperSL2_add, upperSL2_add, pow_succ, pow_two]
  rw [e, show (1 : GaloisField 3 1) + 1 + 1 = 3 by ring, hchar, upperSL2_zero]

private lemma fk_upperSL2_neg_one {K : Type*} [Field K] :
    upperSL2 (-1 : K) = (upperSL2 1)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← upperSL2_add, neg_add_cancel, upperSL2_zero])

private lemma fk_one_ne_neg_one : (1 : GaloisField 3 1) ≠ -1 := by
  intro h
  have h2 : (2 : GaloisField 3 1) = 0 := by
    have hh := congrArg (fun x : GaloisField 3 1 => x + 1) h
    rw [show (2 : GaloisField 3 1) = 1 + 1 by ring]
    simpa using hh
  have hd := (CharP.cast_eq_zero_iff (GaloisField 3 1) 3 2).mp h2
  norm_num at hd

private theorem fk_sl2_order_three_zmod3 :
    ∀ g : SL(2, ZMod 3), g ^ 3 = 1 → g ≠ 1 →
      ∃ (h : SL(2, ZMod 3)) (e : ZMod 3), (e = 1 ∨ e = -1) ∧
        g = h * upperSL2 e * h⁻¹ := by
  decide

theorem fkSwap_congr {G : Type*} [Group G] (ρ φ : MulAut G) {ℓ ℓ' : Subgroup G}
    (hℓ : ℓ.map ρ.toMonoidHom = ℓ') : FKSwap (ρ⁻¹ * φ * ρ) ℓ ↔ FKSwap φ ℓ' := by
  constructor
  · rintro ⟨w, hwℓ, hw3, hw1, hwconj⟩
    refine ⟨ρ w, ?_, ?_, ?_, ?_⟩
    · rw [← hℓ]
      exact Subgroup.mem_map_of_mem ρ.toMonoidHom hwℓ
    · rw [← map_pow, hw3, map_one]
    · intro h1
      exact hw1 (ρ.injective (by rw [h1, map_one]))
    · intro h' hh'ℓ' hconj
      rw [← hℓ] at hh'ℓ'
      obtain ⟨h, hhℓ, rfl⟩ := hh'ℓ'
      refine hwconj h hhℓ ?_
      rw [show (ρ⁻¹ * φ * ρ) w = ρ⁻¹ (φ (ρ w)) by
            simp [MulAut.coe_mul, MulAut.coe_inv, Function.comp_apply], hconj]
      simp
  · rintro ⟨w', hw'ℓ', hw'3, hw'1, hwconj'⟩
    have hwℓ : ρ.symm w' ∈ ℓ := (Subgroup.mem_map_equiv (f := ρ)).mp (hℓ ▸ hw'ℓ')
    refine ⟨ρ.symm w', hwℓ, ?_, ?_, ?_⟩
    · apply ρ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hw'3, map_one]
    · intro h1
      apply hw'1
      rw [← MulEquiv.apply_symm_apply ρ w', h1, map_one]
    · intro h hhℓ hconj
      refine hwconj' (ρ h) (hℓ ▸ Subgroup.mem_map_of_mem ρ.toMonoidHom hhℓ) ?_
      have h3 := congrArg ρ hconj
      simpa [MulAut.coe_mul, MulAut.coe_inv, Function.comp_apply,
        MulEquiv.apply_symm_apply] using h3

theorem fk_sl2_order_three (g : SL(2, GaloisField 3 1)) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ (h : SL(2, GaloisField 3 1)) (e : GaloisField 3 1), (e = 1 ∨ e = -1) ∧
      g = h * upperSL2 e * h⁻¹ := by
  let eR : GaloisField 3 1 ≃+* ZMod 3 := (GaloisField.equivZmodP 3).toRingEquiv
  have hg'3 : (Matrix.SpecialLinearGroup.map eR.toRingHom g) ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  have hg'1 : Matrix.SpecialLinearGroup.map eR.toRingHom g ≠ 1 := by
    intro h
    apply hg1
    have hc := congrArg (Matrix.SpecialLinearGroup.map eR.symm.toRingHom) h
    rw [fk_map_ringEquiv_symm_map eR g] at hc
    simpa using hc
  obtain ⟨h', e', he', hg'eq⟩ := fk_sl2_order_three_zmod3 _ hg'3 hg'1
  refine ⟨Matrix.SpecialLinearGroup.map eR.symm.toRingHom h', eR.symm e', ?_, ?_⟩
  · rcases he' with h | h
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, map_neg, map_one])
  · have hc := congrArg (Matrix.SpecialLinearGroup.map eR.symm.toRingHom) hg'eq
    rw [fk_map_ringEquiv_symm_map eR g] at hc
    simpa [fk_map_upperSL2, map_mul, map_inv] using hc

theorem fk_swap_cases {G : Type*} [Group G] (f : SL(2, GaloisField 3 1) →* G)
    (hf : Function.Injective f) (φ : MulAut G) (hφ : ∀ x ∈ f.range, φ x ∈ f.range) :
    ∃ (h : G) (e : GaloisField 3 1), h ∈ f.range ∧ (e = 1 ∨ e = -1) ∧
      φ (f (upperSL2 1)) = h * f (upperSL2 e) * h⁻¹ ∧ (e = -1 ↔ FKSwap φ f.range) := by
  let u : G := f (upperSL2 1)
  have hu_mem : u ∈ f.range := MonoidHom.mem_range.mpr ⟨upperSL2 1, rfl⟩
  have hu3 : u ^ 3 = 1 := by
    show (f (upperSL2 1)) ^ 3 = 1
    rw [← map_pow, fk_upperSL2_one_pow_three, map_one]
  have hu1 : u ≠ 1 := by
    show f (upperSL2 1) ≠ 1
    intro h
    exact fk_upperSL2_one_ne_one (hf (by rw [h, map_one]))
  have hφu_mem : φ u ∈ f.range := hφ u hu_mem
  have hφu3 : (φ u) ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hφu1 : φ u ≠ 1 := by
    intro h
    exact hu1 (φ.injective (by rw [h, map_one]))
  by_cases hswap : FKSwap φ f.range
  · have hswap0 : FKSwap φ f.range := hswap
    obtain ⟨w, hwℓ, hw3, hw1, hwconj⟩ := hswap
    obtain ⟨g, hg_eq⟩ := MonoidHom.mem_range.mp hwℓ
    have hg3 : g ^ 3 = 1 := hf (by rw [map_pow, hg_eq, hw3, map_one])
    have hg1 : g ≠ 1 := by
      intro h1
      exact hw1 (by rw [← hg_eq, h1, map_one])
    obtain ⟨k, e0, he0, hgeq⟩ := fk_sl2_order_three g hg3 hg1
    obtain ⟨g', hg'_eq⟩ := MonoidHom.mem_range.mp hφu_mem
    have hg'3 : g' ^ 3 = 1 := hf (by rw [map_pow, hg'_eq, hφu3, map_one])
    have hg'1 : g' ≠ 1 := by
      intro h1
      exact hφu1 (by rw [← hg'_eq, h1, map_one])
    obtain ⟨k', e1, he1, hgeq'⟩ := fk_sl2_order_three g' hg'3 hg'1
    have hw_eq : w = f k * f (upperSL2 e0) * (f k)⁻¹ := by
      rw [← hg_eq, hgeq]
      simp only [map_mul, map_inv]
    have he1_ne : e1 ≠ 1 := by
      intro he1_one
      have hJu : φ u = f k' * u * (f k')⁻¹ := by
        rw [← hg'_eq, hgeq', he1_one]
        simp only [map_mul, map_inv]
        rfl
      have hHmem : φ (f k) * f k' * (f k)⁻¹ ∈ f.range :=
        mul_mem (mul_mem (hφ (f k) (MonoidHom.mem_range.mpr ⟨k, rfl⟩))
          (MonoidHom.mem_range.mpr ⟨k', rfl⟩))
          (inv_mem (MonoidHom.mem_range.mpr ⟨k, rfl⟩))
      refine hwconj (φ (f k) * f k' * (f k)⁻¹) hHmem ?_
      rcases he0 with he0_one | he0_neg
      · have hv : f (upperSL2 e0) = u := by rw [he0_one]
        rw [hw_eq, hv]
        simp only [map_mul, map_inv, hJu]
        group
      · have hv : f (upperSL2 e0) = u⁻¹ := by
          rw [he0_neg, fk_upperSL2_neg_one, map_inv]
        rw [hw_eq, hv]
        simp only [map_mul, map_inv, hJu]
        group
    have he1_neg : e1 = -1 := by
      rcases he1 with h | h
      · exact absurd h he1_ne
      · exact h
    refine ⟨f k', e1, MonoidHom.mem_range.mpr ⟨k', rfl⟩, he1, ?_, ?_⟩
    · rw [← hg'_eq, hgeq']
      simp only [map_mul, map_inv]
    · exact ⟨fun _ => hswap0, fun _ => he1_neg⟩
  · have hswap' : ¬ FKSwap φ f.range := hswap
    unfold FKSwap at hswap
    push Not at hswap
    obtain ⟨h, hhℓ, hconj⟩ := hswap u hu_mem hu3 hu1
    refine ⟨h, 1, hhℓ, Or.inl rfl, ?_, ?_⟩
    · change φ u = h * u * h⁻¹
      exact hconj
    · exact ⟨fun h1 => (fk_one_ne_neg_one h1).elim, fun hk => (hswap' hk).elim⟩

end CFSG.OddStandard.SmallF3.Omega
