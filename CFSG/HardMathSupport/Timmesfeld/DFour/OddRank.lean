module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.OmegaRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open Matrix CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem blk4_mulVec_single_of_not (f : Fin 4 → ι) (hf : Function.Injective f)
    (N : Matrix (Fin 4) (Fin 4) K) {a : ι} (ha : a ∉ Set.range f) :
    blk4 f hf N *ᵥ Pi.single a 1 = Pi.single a 1 := by
  funext b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨k, rfl⟩ := hb
    rw [blk4_mulVec_f]
    have hne : ∀ l, f l ≠ a := fun l h => ha ⟨l, h⟩
    simp [hne]
  · exact blk4_mulVec_of_not f hf N _ hb

theorem blk4_commute (f g : Fin 4 → ι) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ k l, f k ≠ g l) (N M : Matrix (Fin 4) (Fin 4) K) :
    blk4 f hf N * blk4 g hg M = blk4 g hg M * blk4 f hf N := by
  have hnf : ∀ k, g k ∉ Set.range f := fun k ⟨l, h⟩ => hfg l k h
  have hng : ∀ k, f k ∉ Set.range g := fun k ⟨l, h⟩ => hfg k l h.symm
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  funext a
  by_cases ha : a ∈ Set.range f
  · obtain ⟨k, rfl⟩ := ha
    rw [blk4_mulVec_f, blk4_mulVec_of_not g hg M _ (hng k), blk4_mulVec_f]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [blk4_mulVec_of_not g hg M _ (hng l)]
  · by_cases hb : a ∈ Set.range g
    · obtain ⟨k, rfl⟩ := hb
      rw [blk4_mulVec_of_not f hf N _ (hnf k), blk4_mulVec_f, blk4_mulVec_f]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [blk4_mulVec_of_not f hf N _ (hnf l)]
    · rw [blk4_mulVec_of_not f hf N _ ha, blk4_mulVec_of_not g hg M _ hb,
        blk4_mulVec_of_not g hg M _ hb, blk4_mulVec_of_not f hf N _ ha]

theorem three_le_pRank_plus_of_char {n : ℕ} (hn : 4 ≤ n) [Finite K] {c : K} (hc : c ≠ 0)
    (hcsq : c ^ 2 ≠ 1) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  set i3 : Fin n := ⟨3, by omega⟩
  have hab : ∀ i j : Fin n, (Sum.inl i : Fin n ⊕ Fin n) ≠ Sum.inr j := fun _ _ => Sum.inl_ne_inr
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  set f₁ := frame4 (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr i0 i1 with hf₁def
  set f₂ := frame4 (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr i2 i3 with hf₂def
  have hf₁ : Function.Injective f₁ :=
    frame4_injective _ _ Sum.inl_injective Sum.inr_injective hab i0 i1 h01
  have hf₂ : Function.Injective f₂ :=
    frame4_injective _ _ Sum.inl_injective Sum.inr_injective hab i2 i3 h23
  have hdisj : ∀ k l, f₁ k ≠ f₂ l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [hf₁def, hf₂def, frame4, i0, i1, i2, i3, Fin.ext_iff]
  have hQ : ∀ v, StatedQuadPlus n K v = ∑ i, v (Sum.inl i) * v (Sum.inr i) + (fun _ => 0) v :=
    fun v => by simp [StatedQuadPlus]
  have HQ₁ := hq_of_sum (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective hab i0 i1 h01 (StatedQuadPlus n K) (fun _ => 0) (fun _ _ _ => rfl) hQ
  have HQ₂ := hq_of_sum (Sum.inl : Fin n → Fin n ⊕ Fin n) Sum.inr Sum.inl_injective
    Sum.inr_injective hab i2 i3 h23 (StatedQuadPlus n K) (fun _ => 0) (fun _ _ _ => rfl) hQ
  set x : GL (Fin n ⊕ Fin n) K := gen f₁ hf₁ lmat lmat_one lmat_mul c3 with hxdef
  set y : GL (Fin n ⊕ Fin n) K := gen f₁ hf₁ rmat rmat_one rmat_mul c3 with hydef
  set z : GL (Fin n ⊕ Fin n) K := gen f₂ hf₂ lmat lmat_one lmat_mul c3 with hzdef
  have hxO : x ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hyO : y ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hzO : z ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₂ hf₂ HQ₂ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, c3_pow_three, map_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← map_pow, c3_pow_three, map_one]
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, c3_pow_three, map_one]
  have hxy : Commute x y := by
    ext1
    simp only [Units.val_mul, hxdef, hydef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hxz : Commute x z := by
    ext1
    simp only [Units.val_mul, hxdef, hzdef, coe_gen]
    exact blk4_commute f₁ f₂ hf₁ hf₂ hdisj _ _
  have hyz : Commute y z := by
    ext1
    simp only [Units.val_mul, hydef, hzdef, coe_gen]
    exact blk4_commute f₁ f₂ hf₁ hf₂ hdisj _ _
  have hx1 : x ∉ StatedScalars (Fin n ⊕ Fin n) K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ 0) (f₁ 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf₁.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hy1 : ∀ m : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K, x ^ m * s ≠ y := by
    rintro m _ ⟨u, rfl⟩ hmc
    have key : ∀ k l, lmat (((c3 : SL(2, K)) ^ m : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l *
        (u : K) = rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l := by
      intro k l
      have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ k) (f₁ l)) hmc
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
        Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
      exact h1
    have hm : (c3 : SL(2, K)) ^ m = c3 ^ (m % 3) := by
      conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, c3_pow_three, one_pow, mul_one]
    rw [hm] at key
    have h3 : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : m % 3
    · have e := key 0 1
      simp [lmat, rmat, c3] at e
    · have e := key 0 0
      rw [pow_one] at e
      simp [lmat, rmat, c3] at e
    · have e := key 0 1
      rw [coe_c3_sq] at e
      simp [lmat, rmat, c3] at e
  have hz1 : ∀ m l : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K, x ^ m * y ^ l * s ≠ z := by
    intro m l s hs
    have hn1 : f₂ 1 ∉ Set.range f₁ := fun ⟨k, hk⟩ => hdisj k 1 hk
    have hfix : ((x ^ m * y ^ l : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₂ 1) 1 =
        Pi.single (f₂ 1) 1 := by
      rw [hxdef, hydef, ← map_pow, ← map_pow, Units.val_mul, coe_gen, coe_gen, blk4_mul]
      exact blk4_mulVec_single_of_not f₁ hf₁ _ hn1
    have hzv : ((z : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₂ 1) 1 =
        Pi.single (f₂ 2) 1 := by
      rw [hzdef, coe_gen]
      funext b
      by_cases hb : b ∈ Set.range f₂
      · obtain ⟨k, rfl⟩ := hb
        rw [blk4_mulVec_f]
        fin_cases k <;> simp [Pi.single_apply, hf₂.eq_iff, lmat, c3]
      · rw [blk4_mulVec_of_not f₂ hf₂ _ _ hb]
        have h1 : b ≠ f₂ 1 := fun h => hb ⟨1, h.symm⟩
        have h2 : b ≠ f₂ 2 := fun h => hb ⟨2, h.symm⟩
        simp [h1, h2]
    exact CFSG.SectionRank.ClassicalEven.mul_scalar_ne (hf₂.ne (by decide)) hfix hzv hs
  exact CFSG.SectionRank.ClassicalEven.three_le_pRank_statedProj hxO hyO hzO hx3 hy3 hz3 hxy
    hxz hyz hx1 hy1 hz1

end CFSG.HardMathSupport.Timmesfeld.DFour
