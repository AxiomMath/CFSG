module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Lift
public import CFSG.HardMathSupport.Timmesfeld.DFour.OddRank4
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FamilyRank

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance (isElemAbelian_of_forall)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

theorem exists_statedProj_map {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {H' H : Subgroup (GL ι K)} (h : H' ≤ H) :
    ∃ ι₀ : StatedProj H' →* StatedProj H, Function.Injective ι₀ ∧
      ∀ g : H', ι₀ (QuotientGroup.mk g) = QuotientGroup.mk (Subgroup.inclusion h g) := by
  have hle : (StatedScalars ι K).subgroupOf H' ≤
      ((StatedScalars ι K).subgroupOf H).comap (Subgroup.inclusion h) := fun g hg => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact hg
  refine ⟨QuotientGroup.map _ _ (Subgroup.inclusion h) hle, ?_, fun g => rfl⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker] at hq
  have : (QuotientGroup.map _ _ (Subgroup.inclusion h) hle) (QuotientGroup.mk g) =
      QuotientGroup.mk (Subgroup.inclusion h g) := rfl
  rw [this, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hq

theorem exists_four_centralizing_involution {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    {c : K} (hc : c ≠ 0) (hcsq : c ^ 2 ≠ 1) (h2 : (2 : K) ≠ 0) :
    ∃ (F : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))))
      (ū : StatedProj (StatedOmega (StatedQuadPlus n K))),
      IsElemAbelian 3 F ∧ 3 ^ 4 ≤ Nat.card F ∧ ū ^ 2 = 1 ∧ ū ≠ 1 ∧ ∀ s ∈ F, s * ū = ū * s := by
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
  set w : GL (Fin n ⊕ Fin n) K := gen f₂ hf₂ rmat rmat_one rmat_mul c3 with hwdef
  have hxO : x ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hyO : y ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hzO : z ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₂ hf₂ HQ₂ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq c3
  have hwO : w ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₂ hf₂ HQ₂ rmat rmat_one rmat_mul (fun A hA u => q4_rmat A hA u) hc hcsq c3
  have hx3 : x ^ 3 = 1 := by rw [hxdef, ← map_pow, c3_pow_three, map_one]
  have hy3 : y ^ 3 = 1 := by rw [hydef, ← map_pow, c3_pow_three, map_one]
  have hz3 : z ^ 3 = 1 := by rw [hzdef, ← map_pow, c3_pow_three, map_one]
  have hw3 : w ^ 3 = 1 := by rw [hwdef, ← map_pow, c3_pow_three, map_one]
  have hxy : Commute x y := by
    ext1
    simp only [Units.val_mul, hxdef, hydef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hzw : Commute z w := by
    ext1
    simp only [Units.val_mul, hzdef, hwdef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hdc : ∀ (a b : GL (Fin n ⊕ Fin n) K) (N M : Matrix (Fin 4) (Fin 4) K),
      (a : Matrix _ _ K) = blk4 f₁ hf₁ N → (b : Matrix _ _ K) = blk4 f₂ hf₂ M → Commute a b := by
    intro a b N M ha hb
    ext1
    simp only [Units.val_mul, ha, hb]
    exact blk4_commute f₁ f₂ hf₁ hf₂ hdisj _ _
  have hxz : Commute x z := hdc x z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyz : Commute y z := hdc y z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hxw : Commute x w := hdc x w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hyw : Commute y w := hdc y w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)
  have hx1 : x ∉ StatedScalars (Fin n ⊕ Fin n) K := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ 0) (f₁ 3)) hu
    simp only [GeneralLinearGroup.coe_scalar, hxdef, coe_gen, blk4_apply_f, Matrix.scalar_apply,
      Matrix.diagonal_apply_ne _ (hf₁.ne (by decide : (0 : Fin 4) ≠ 3))] at h1
    simp [lmat, c3] at h1
  have hlr : ∀ (m : ℕ) (u : K), ¬ ∀ k l, lmat (((c3 : SL(2, K)) ^ m : SL(2, K)) :
      Matrix (Fin 2) (Fin 2) K) k l * u =
        rmat ((c3 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) k l := by
    intro m u key
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
  have hy1 : ∀ m : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K, x ^ m * s ≠ y := by
    rintro m _ ⟨u, rfl⟩ hmc
    refine hlr m u fun k l => ?_
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K => (g : Matrix _ _ K) (f₁ k) (f₁ l)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, ← map_pow, coe_gen,
      Matrix.scalar_apply, Matrix.mul_diagonal, blk4_apply_f] at h1
    exact h1
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
  have hw1 : ∀ m l r : ℕ, ∀ s ∈ StatedScalars (Fin n ⊕ Fin n) K,
      x ^ m * y ^ l * z ^ r * s ≠ w := by
    rintro m l r _ ⟨u, rfl⟩ hmc
    refine hlr r u fun k j => ?_
    have h1 := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      ((g : Matrix _ _ K) *ᵥ Pi.single (f₂ j) 1) (f₂ k)) hmc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, hxdef, hydef, hzdef, hwdef,
      ← map_pow, coe_gen, ← Matrix.mulVec_mulVec, Matrix.scalar_apply,
      Matrix.diagonal_mulVec_single] at h1
    have hvan : ∀ k', (blk4 f₂ hf₂ (lmat (((c3 : SL(2, K)) ^ r : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K)) *ᵥ Pi.single (f₂ j) ((u : K) * 1)) (f₁ k') = 0 := by
      intro k'
      have hn : f₁ k' ∉ Set.range f₂ := fun ⟨k'', hk''⟩ => hdisj k' k'' hk''.symm
      rw [blk4_mulVec_of_not f₂ hf₂ _ _ hn]
      simp [hdisj k' j]
    rw [blk4_mulVec_of_vanish f₁ hf₁ _ hvan, blk4_mulVec_of_vanish f₁ hf₁ _ hvan,
      blk4_mulVec_f, blk4_mulVec_f] at h1
    simpa [Pi.single_apply, hf₂.eq_iff] using h1
  set A₀ : SL(2, K) := ⟨(-1 : Matrix (Fin 2) (Fin 2) K), by simp [Matrix.det_fin_two]⟩ with hA₀
  set u : GL (Fin n ⊕ Fin n) K := gen f₁ hf₁ lmat lmat_one lmat_mul A₀ with hudef
  have huO : u ∈ StatedOmega (StatedQuadPlus n K) :=
    gen_mem_omega _ f₁ hf₁ HQ₁ lmat lmat_one lmat_mul (fun A hA u => q4_lmat A hA u) hc hcsq A₀
  have hA₀c : ∀ A : SL(2, K), A * A₀ = A₀ * A := fun A => by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    change (A : Matrix (Fin 2) (Fin 2) K) * (-1) = (-1) * (A : Matrix (Fin 2) (Fin 2) K)
    simp
  have hu2 : u ^ 2 = 1 := by
    rw [hudef, ← map_pow]
    have : A₀ ^ 2 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      change (-1 : Matrix (Fin 2) (Fin 2) K) ^ 2 = 1
      simp [sq]
    rw [this, map_one]
  have hxu : Commute x u := by
    rw [hxdef, hudef, Commute, SemiconjBy, ← map_mul, ← map_mul, hA₀c]
  have hyu : Commute y u := by
    ext1
    simp only [Units.val_mul, hydef, hudef, coe_gen, blk4_mul, lmat_rmat_comm]
  have hzu : Commute z u := (hdc u z _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)).symm
  have hwu : Commute w u := (hdc u w _ _ (coe_gen _ _ _ _ _ _) (coe_gen _ _ _ _ _ _)).symm
  have hu1 : u ∉ StatedScalars (Fin n ⊕ Fin n) K := by
    rintro ⟨s, hs⟩
    have hn1 : f₂ 0 ∉ Set.range f₁ := fun ⟨k, hk⟩ => hdisj k 0 hk
    have e1 : ((u : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₁ 0) 1 =
        (s : K) • Pi.single (f₁ 0) 1 := by
      rw [← hs]
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mulVec_single]
      funext b
      by_cases hb : b = f₁ 0 <;> simp [Pi.single_apply, hb]
    have e2 : ((u : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ Pi.single (f₂ 0) 1 =
        (s : K) • Pi.single (f₂ 0) 1 := by
      rw [← hs]
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mulVec_single]
      funext b
      by_cases hb : b = f₂ 0 <;> simp [Pi.single_apply, hb]
    have e1' := congrFun e1 (f₁ 0)
    have e2' := congrFun e2 (f₂ 0)
    rw [hudef, coe_gen, blk4_mulVec_f] at e1'
    rw [hudef, coe_gen, blk4_mulVec_single_of_not f₁ hf₁ _ hn1] at e2'
    simp [lmat, hA₀, Pi.single_apply, hf₁.eq_iff] at e1' e2'
    exact h2 (by linear_combination e2' - e1')
  set Hc : Subgroup (GL (Fin n ⊕ Fin n) K) :=
    StatedOmega (StatedQuadPlus n K) ⊓ Subgroup.centralizer {u} with hHc
  have hmemC : ∀ g : GL (Fin n ⊕ Fin n) K, Commute g u → g ∈ Subgroup.centralizer ({u} : Set _) :=
    fun g hg => Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hg.symm.eq
  have hrank := four_le_pRank_statedProj (H := Hc) ⟨hxO, hmemC _ hxu⟩ ⟨hyO, hmemC _ hyu⟩
    ⟨hzO, hmemC _ hzu⟩ ⟨hwO, hmemC _ hwu⟩ hx3 hy3 hz3 hw3 hxy hxz hyz hxw hyw hzw hx1 hy1 hz1 hw1
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (⊤ : Subgroup (StatedProj Hc))
  obtain ⟨ι₀, hι₀, hι₀mk⟩ := exists_statedProj_map (inf_le_left : Hc ≤ StatedOmega (StatedQuadPlus n K))
  let ū : StatedProj (StatedOmega (StatedQuadPlus n K)) := QuotientGroup.mk ⟨u, huO⟩
  refine ⟨E.map ι₀, ū, ?_, ?_, ?_, ?_, ?_⟩
  · refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, isElemAbelian_commute hE ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hι₀, hEcard]
    exact Nat.pow_le_pow_right (by norm_num) hrank
  · change (QuotientGroup.mk ⟨u, huO⟩ : StatedProj (StatedOmega (StatedQuadPlus n K))) ^ 2 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨u, huO⟩ : StatedOmega (StatedQuadPlus n K)) ^ 2 = 1 := Subtype.ext hu2
    rw [this]
    rfl
  · intro h
    apply hu1
    have h' := (QuotientGroup.eq_one_iff _).1 h
    exact Subgroup.mem_subgroupOf.1 h'
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective e
    rw [hι₀mk]
    show (QuotientGroup.mk (Subgroup.inclusion inf_le_left g) :
      StatedProj (StatedOmega (StatedQuadPlus n K))) * QuotientGroup.mk ⟨u, huO⟩ = _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 g.2.2 u (Set.mem_singleton u)).symm

theorem d4FourRank_holds : D4FourRank := by
  intro K _ _ r f hr hr2 hr3 hK
  have hf : 1 ≤ f := one_le_of_card_field hK
  let e0 : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hm : StatedClassicalModel (D4Model K) .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hm K hK e0
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hr2)
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K (ringChar K) 3).1 h'
    rw [hchar] at this
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)
  have hcsq : (2 : K) ^ 2 ≠ 1 := fun h => h3 (by linear_combination h)
  obtain ⟨F, ū, hF, hFc, hū2, hū1, hFū⟩ := exists_four_centralizing_involution (n := 4) le_rfl h2
    hcsq h2
  let e : StatedProj (StatedOmega (StatedQuadPlus 4 K)) ≃* D4Model K := e0.symm
  refine ⟨F.map e.toMonoidHom, e ū, isElemAbelian_map_equiv e hF, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hFc
  · rw [← map_pow, hū2, map_one]
  · intro h
    exact hū1 (e.injective (h.trans (map_one e).symm))
  · rintro _ ⟨s, hs, rfl⟩
    show e s * e ū = e ū * e s
    rw [← map_mul, ← map_mul, hFū s hs]

end CFSG.LocalAnalysis.GLTheoremA
