module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerU7Block

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

open Matrix Finset CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4
  CFSG.LocalAnalysis.ComponentInitial

open scoped Classical

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def piU (p f : ℕ) (K : Type) [Field K] :
    ↥(StatedSU 7 (p ^ f) K) →* StatedProj (StatedSU 7 (p ^ f) K) :=
  QuotientGroup.mk' ((StatedScalars (Fin 7) K).subgroupOf (StatedSU 7 (p ^ f) K))

theorem piU_eq_one_iff (x : ↥(StatedSU 7 (p ^ f) K)) :
    piU p f K x = 1 ↔ (x : GL (Fin 7) K) ∈ StatedScalars (Fin 7) K := by
  unfold piU
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem scalar_val (c : Kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 7) c : GL (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K) = Matrix.scalar (Fin 7) (c : K) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.one_apply]

theorem scalar_three_eq_one {x : GL (Fin 7) K} (hx : x ∈ StatedScalars (Fin 7) K)
    (hdet : (x : Matrix (Fin 7) (Fin 7) K).det = 1) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
  have hc3 : (c : K) ^ 3 = 1 := by
    have h3' := congrArg (fun g : GL (Fin 7) K => (g : Matrix (Fin 7) (Fin 7) K)) h3
    simp only [Units.val_pow_eq_pow_val, Units.val_one, scalar_val] at h3'
    have key : Matrix.scalar (Fin 7) ((c : K) ^ 3) = (1 : Matrix (Fin 7) (Fin 7) K) := by
      rw [map_pow]
      exact h3'
    have := congrFun (congrFun key 0) 0
    simpa using this
  have hc7 : (c : K) ^ 7 = 1 := by
    rw [scalar_val, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa using hdet
  have hc1 : (c : K) = 1 := by
    have h6 : (c : K) ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, hc3, one_pow]
    have h7 : (c : K) ^ 7 = (c : K) := by
      rw [show (7 : ℕ) = 6 + 1 by norm_num, pow_succ, h6, one_mul]
    rw [← h7, hc7]
  apply Units.ext
  rw [scalar_val, hc1, Units.val_one, map_one]

theorem piU_inj_pow3 (h : UnitaryFieldData p f K) {x : ↥(StatedSU 7 (p ^ f) K)}
    (h3 : x ^ 3 = 1) (hx : piU p f K x = 1) : x = 1 := by
  rw [piU_eq_one_iff] at hx
  have hdet := ((mem_statedSU_iff h 7 (x : GL (Fin 7) K)).mp x.2).1
  have h3' : (x : GL (Fin 7) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
  apply Subtype.ext
  exact scalar_three_eq_one hx hdet h3'

theorem scalar_InH0_eq_one {g : GL (Fin 7) K}
    (hg : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0 (g : Matrix (Fin 7) (Fin 7) K))
    (hsc : g ∈ StatedScalars (Fin 7) K) : g = 1 := by
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hsc
  have hb := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_bottom hg
    (sumEq7.symm (Sum.inr 0)) (sumEq7.symm (Sum.inr 0))
    (by simp [sumEq7_symm_inr_val]) (by simp [sumEq7_symm_inr_val])
  rw [scalar_val] at hb
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, if_true] at hb
  apply Units.ext
  rw [scalar_val, hb, Units.val_one, map_one]

theorem commute_of_piU (h : UnitaryFieldData p f K) {x y : ↥(StatedSU 7 (p ^ f) K)}
    (hy : y ^ 3 = 1) (hc : piU p f K x * piU p f K y = piU p f K y * piU p f K x) :
    x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hc1 : piU p f K c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h' : piU p f K x * piU p f K y * (piU p f K x)⁻¹ * (piU p f K y)⁻¹ = 1 := by
      calc piU p f K x * piU p f K y * (piU p f K x)⁻¹ * (piU p f K y)⁻¹
          = piU p f K y * piU p f K x * (piU p f K x)⁻¹ * (piU p f K y)⁻¹ := by rw [hc]
        _ = 1 := by simp [mul_assoc]
    exact h'
  have hcenter : (c : GL (Fin 7) K) ∈ Subgroup.center (GL (Fin 7) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact (piU_eq_one_iff c).mp hc1
  have hcommute : c * y = y * c := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (Subgroup.mem_center_iff.mp hcenter (y : GL (Fin 7) K)).symm)
  have hxyx : x * y * x⁻¹ = c * y := by
    rw [hcdef]
    simp [mul_assoc]
  have hpow : (x * y * x⁻¹) ^ 3 = 1 := by
    have e : (x * y * x⁻¹) ^ 3 = x * y ^ 3 * x⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [e, hy]
    simp
  have h5 : c ^ 3 * y ^ 3 = 1 := by
    rw [← (show Commute c y from hcommute).mul_pow 3, ← hxyx, hpow]
  have hc3 : c ^ 3 = 1 := by
    rw [hy, mul_one] at h5
    exact h5
  have hc : c = 1 := piU_inj_pow3 h hc3 hc1
  calc x * y = c * (y * x) := by
        rw [hcdef]
        simp [mul_assoc]
    _ = y * x := by rw [hc, one_mul]

theorem H0U_conj_mem (h : UnitaryFieldData p f K) (c : ↥(StatedSU 7 (p ^ f) K))
    (hc : ((c : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * D0 K =
      D0 K * ((c : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K))
    (g : ↥(StatedSU 7 (p ^ f) K)) (hg : g ∈ H0U h) : c * g * c⁻¹ ∈ H0U h := by
  have hgI : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
      ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := hg
  have hGL : (c : GL (Fin 7) K) * ((c⁻¹ : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) = 1 := by
    rw [Subgroup.coe_inv, mul_inv_cancel]
  have hGL' : ((c⁻¹ : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) * (c : GL (Fin 7) K) = 1 := by
    rw [Subgroup.coe_inv, inv_mul_cancel]
  have hmat1 : ((c : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      (((c⁻¹ : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 := by
    rw [← Units.val_mul, hGL, Units.val_one]
  have hmat2 : (((c⁻¹ : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      ((c : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = 1 := by
    rw [← Units.val_mul, hGL', Units.val_one]
  have hconj := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_conj hgI hmat1 hmat2 hc
  show CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
    (((c * g * c⁻¹ : ↥(StatedSU 7 (p ^ f) K)) : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact hconj

theorem kerConcl_of_blockU (h : UnitaryFieldData p f K) (hQ : 3 ∣ p ^ f - 1)
    (P' : Subgroup ↥(StatedSU 7 (p ^ f) K)) (hP3 : ∀ x ∈ P', x ^ 3 = 1)
    (F' : Subgroup ↥(StatedSU 7 (p ^ f) K)) (hF'P : F' ≤ P') (hF'card : Nat.card F' = 9)
    (hF'D : ∀ k ∈ F', ((k : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * D0 K = D0 K ∧
      D0 K * ((k : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = D0 K)
    (hcent : ∀ g : ↥(StatedSU 7 (p ^ f) K), (∀ f ∈ F', g * f = f * g) →
      ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) * D0 K =
        D0 K * ((g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) :
    KerConcl (P'.map (piU p f K)) := by
  haveI : Finite K := h.finite
  haveI : Fact p.Prime := ⟨h.prime⟩
  refine ⟨F'.map (piU p f K), Subgroup.map_mono hF'P, ?_, ?_⟩
  · rw [card_map_eq_of_injOn (piU p f K) F' (fun x hx h' => piU_inj_pow3 h (hP3 x (hF'P hx)) h')]
    exact hF'card
  · let H'' : Subgroup (StatedProj (StatedSU 7 (p ^ f) K)) := (H0U h).map (piU p f K)
    let ψhom : (H0U h) →* H'' :=
      ((piU p f K).comp (H0U h).subtype).codRestrict H'' (fun x => ⟨x.1, x.2, rfl⟩)
    have hψinj : Function.Injective ψhom := by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      have h1 : piU p f K x.1 = 1 := congrArg Subtype.val hx
      rw [piU_eq_one_iff] at h1
      have hxI : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0
          ((x.1 : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := x.2
      have := scalar_InH0_eq_one hxI h1
      rw [this]
      simp
    have hψsurj : Function.Surjective ψhom := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    let ψ : (H0U h) ≃* H'' := MulEquiv.ofBijective ψhom ⟨hψinj, hψsurj⟩
    have hle : H'' ≤ Subgroup.centralizer ((F'.map (piU p f K) : Subgroup _) : Set _) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hz
      have hxk' : x * k = k * x := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul]
        exact CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7.InH0_comm hx (hF'D k hk).1 (hF'D k hk).2
      rw [← map_mul, ← map_mul, hxk']
    refine ⟨H'', hle, ?_, ?_, ?_⟩
    · refine CFSG.Open.IsSubnormal.step hle ?_ (CFSG.Open.IsSubnormal.refl _)
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (g : StatedProj (StatedSU 7 (p ^ f) K))
      have hc' : piU p f K c = (g : StatedProj (StatedSU 7 (p ^ f) K)) := hc
      have hcF : ∀ k ∈ F', c * k = k * c := by
        intro k hk
        have hgk := Subgroup.mem_centralizer_iff.mp g.2 (piU p f K k)
          (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
        apply commute_of_piU h (hP3 k (hF'P hk))
        rw [hc']
        exact hgk.symm
      have hcD := hcent c hcF
      obtain ⟨n', hn'H0, hn'eq⟩ := Subgroup.mem_map.mp hn
      have hconj := H0U_conj_mem h c hcD n' hn'H0
      apply Subgroup.mem_map.mpr
      refine ⟨c * n' * c⁻¹, hconj, ?_⟩
      rw [map_mul, map_mul, map_inv, hc', hn'eq]
      rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv ψ
        (H0U_isQuasisimple h hQ)
    · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv ψ]
      exact H0U_three_dvd h hQ

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7

end
