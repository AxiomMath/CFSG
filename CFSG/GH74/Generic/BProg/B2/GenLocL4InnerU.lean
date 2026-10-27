module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QNsqU
public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank3
public import CFSG.GH74.Generic.BProg.B2.GenLocL4Inner

public section

namespace CFSG.GH74.Generic.BProg.B2

namespace GenLocL4InnerU

section Rank3

open Matrix CFSG CFSG.ComponentClassification Module GenLocL4Q

variable {F : Type} [Field F]

theorem top_of_rank3_nsqU [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    {c m ν : F} (hc : ¬ IsSquare c) (hν : ¬ IsSquare ν) (hm : m ≠ 0)
    {x y z : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1)
    (hz : z * z = ν • 1)
    (hxy : x * y = -(y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (y * z) = (y * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (x * y) = (x * y) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * z = z * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  classical
  have := Fintype.ofFinite F
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hν0 : ν ≠ 0 := ne_zero_of_not_isSquare hν
  obtain ⟨r, hr⟩ := isSquare_mul_of_not hc hν
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hc0 hν0 (by rw [hr]; ring)
  have hl : r / c ≠ 0 := div_ne_zero hr0 hc0
  have hlν : (r / c) * (r / c) * c = ν := by
    field_simp
    linear_combination (-1 : F) * hr
  obtain ⟨R, hRu, hxR, hyR, hzR⟩ := nsq_basis hF hc hm hl hlν hx hy hz hxy hxz hyz
  have hRu' : (hRu.unit : Matrix (Fin 4) (Fin 4) F) = R := hRu.unit_spec
  have hyzR : (y * z) * R = R * ((r / c) • (Yr m * Z0 c)) := by
    rw [inter_mul_gen hyR hzR, Matrix.mul_smul]
  have hxzR : (x * z) * R = R * ((r / c) • (Xr c * Z0 c)) := by
    rw [inter_mul_gen hxR hzR, Matrix.mul_smul]
  have hxyR : (x * y) * R = R * (Xr c * Yr m) := inter_mul_gen hxR hyR
  apply top_of_conj hRu
  refine top_of_nsq_model_uniform hF hF4 hc hm _ ?_ ?_ ?_ ?_ ?_
  · intro g hg1 hg2
    exact H1 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyR) g hg2)
  · intro g hg1 hg2
    exact H2 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hyzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H3 _ (slConj_commute (by rw [hRu']; exact hyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H4 _ (slConj_commute (by rw [hRu']; exact hxyR) g hg1)
      (slConj_commute (by rw [hRu']; exact hxzR) g (comm_smul_gen _ _ _ hg2))
  · intro g hg1 hg2
    exact H5 _ (slConj_commute (by rw [hRu']; exact hxR) g hg1)
      (slConj_commute (by rw [hRu']; exact hzR) g (comm_smul_gen _ _ _ hg2))

end Rank3

section Rank3Core

open Matrix CFSG CFSG.ComponentClassification Subgroup GenLocL4Q

variable {F : Type} [Field F] {A : Type} [Group A]

theorem rank3_coreU [Finite F] [Finite A] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A) (hr : pRank 2 A = 3)
    {a b c : A} {x y z : GL (Fin 4) F} (hax : IsLift α a x) (hby : IsLift α b y)
    (hcz : IsLift α c z)
    (hxy : (x : Matrix (Fin 4) (Fin 4) F) * y = -((y : Matrix (Fin 4) (Fin 4) F) * x))
    (hxz : (x : Matrix (Fin 4) (Fin 4) F) * z = (z : Matrix (Fin 4) (Fin 4) F) * x)
    (hyz : (y : Matrix (Fin 4) (Fin 4) F) * z = (z : Matrix (Fin 4) (Fin 4) F) * y)
    (hzn : ¬ ∃ l : F, (z : Matrix (Fin 4) (Fin 4) F) = l • 1) {c0 : F}
    (hc0 : (x : Matrix (Fin 4) (Fin 4) F) * x = c0 • 1) (hc : ¬ IsSquare c0) : gammaAct α = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 b
  have hcc : c * c = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 c
  obtain ⟨m, hm⟩ := lift_sq_scalar α hbb hby
  obtain ⟨ν, hν⟩ := lift_sq_scalar α hcc hcz
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : (((y * y : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hm, zero_smul]
    exact Units.ne_zero _ this
  have hν0 : ν ≠ 0 := by
    rintro rfl
    have : (((z * z : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hν, zero_smul]
    exact Units.ne_zero _ this
  have hyx : (y : Matrix (Fin 4) (Fin 4) F) * x = -((x : Matrix (Fin 4) (Fin 4) F) * y) := by
    rw [hxy]; simp
  have nx := not_scalar_of_anticomm h2 hxy
  have ny := not_scalar_of_anticomm h2 hyx
  have nxy := not_scalar_of_anticomm h2 (u := x * y) (v := x)
    (by rw [Units.val_mul]; exact W_xy_x hc0 hm hν hxy hxz hyz)
  have nyz := not_scalar_of_anticomm h2 (u := y * z) (v := x)
    (by rw [Units.val_mul]; exact W_yz_x hc0 hm hν hxy hxz hyz)
  have nxz := not_scalar_of_anticomm h2 (u := x * z) (v := y)
    (by rw [Units.val_mul]; exact W_xz_y hc0 hm hν hxy hxz hyz)
  have nxyz := not_scalar_of_anticomm h2 (u := x * (y * z)) (v := x)
    (by rw [Units.val_mul, Units.val_mul]; exact W_xyz_x hc0 hm hν hxy hxz hyz)
  have nyxz := not_scalar_of_anticomm h2 (u := y * (x * z)) (v := y)
    (by rw [Units.val_mul, Units.val_mul]; exact W_yxz_y hc0 hm hν hxy hxz hyz)
  have nxyxz := not_scalar_of_anticomm h2 (u := (x * y) * (x * z)) (v := x)
    (by rw [Units.val_mul, Units.val_mul, Units.val_mul]; exact W_xyxz_x hc0 hm hν hxy hxz hyz)
  have hyz' : IsLift α (b * c) (y * z) := hby.mul hcz
  have hxz' : IsLift α (a * c) (x * z) := hax.mul hcz
  have hxy' : IsLift α (a * b) (x * y) := hax.mul hby
  have H1 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ gammaAct α :=
    fun g hgx hgy => mem_gammaAct_of_pair α hA hr hax hby nx ny nxy g hgx hgy
  have H2 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (y * z) = (y * z) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ gammaAct α :=
    fun g hgx hgw => mem_gammaAct_of_pair α hA hr hax hyz' nx nyz nxyz g hgx
      (by rw [Units.val_mul]; exact hgw)
  have H3 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ gammaAct α :=
    fun g hgy hgw => mem_gammaAct_of_pair α hA hr hby hxz' ny nxz nyxz g hgy
      (by rw [Units.val_mul]; exact hgw)
  have H4 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (x * y) = (x * y) * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * (x * z) = (x * z) * (g : Matrix (Fin 4) (Fin 4) F) →
        g ∈ gammaAct α :=
    fun g hgu hgw => mem_gammaAct_of_pair α hA hr hxy' hxz' nxy nxz nxyxz g
      (by rw [Units.val_mul]; exact hgu) (by rw [Units.val_mul]; exact hgw)
  have H5 : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) →
      (g : Matrix (Fin 4) (Fin 4) F) * z = z * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ gammaAct α :=
    fun g hgx hgz => mem_gammaAct_of_pair α hA hr hax hcz nx hzn nxz g hgx hgz
  have hzn' : ∀ l : F, (z : Matrix (Fin 4) (Fin 4) F) ≠ l • 1 := fun l h => hzn ⟨l, h⟩
  by_cases hsq : IsSquare ν
  · obtain ⟨s, hs⟩ := hsq
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply hν0
      rw [hs]; ring
    have hz2 : (z : Matrix (Fin 4) (Fin 4) F) * z = (s * s) • 1 := by rw [hν, hs]
    exact top_of_rank3_split hF hc hm0 hs0 hc0 hm hz2 hxy hxz hyz hzn' (gammaAct α) H1 H2 H3 H4
  · exact top_of_rank3_nsqU hF hF4 hc hsq hm0 hc0 hm hν hxy hxz hyz (gammaAct α) H1 H2 H3 H4 H5

theorem gammaAct_quat_rank3U [Finite F] [Finite A] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hr : pRank 2 A = 3) (hinj : Function.Injective α)
    (hinner : ∀ c : A, ∃ x : GL (Fin 4) F, IsLift α c x) {a b : A} {x y : GL (Fin 4) F}
    (hax : IsLift α a x) (hby : IsLift α b y)
    (hxy : (x : Matrix (Fin 4) (Fin 4) F) * y = -((y : Matrix (Fin 4) (Fin 4) F) * x)) :
    gammaAct α = ⊤ := by
  classical
  have := hA.1
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have haa : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 b
  have hab : (a * b) * (a * b) = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 (a * b)
  have hcard : Nat.card A = 8 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hr]; norm_num
  have := Fintype.ofFinite A
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a, b, a * b} : Finset A)) (t := Finset.univ) (by
      have h1 : ({1, a, b, a * b} : Finset A).card ≤ 4 := Finset.card_le_four
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
  obtain ⟨z₀, hz₀⟩ := hinner c₀
  obtain ⟨c, z, hc, hcz, hxz, hyz⟩ := exists_comm_lift α hA hax hby hz₀ hxy
  have hc1 : c ≠ 1 := by
    rcases hc with rfl | rfl | rfl | rfl
    · intro h; exact hc₀ (by simp [h])
    · intro h
      apply hc₀
      have : c₀ = a := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right haa)
      simp [this]
    · intro h
      apply hc₀
      have : c₀ = b := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right hbb)
      simp [this]
    · intro h
      apply hc₀
      have : c₀ = a * b := by
        have := inv_eq_of_mul_eq_one_left h
        rw [← this]; exact (inv_eq_of_mul_eq_one_right hab)
      simp [this]
  have hzn : ¬ ∃ l : F, (z : Matrix (Fin 4) (Fin 4) F) = l • 1 := by
    rintro ⟨l, hl⟩
    apply hc1
    apply hinj
    rw [map_one]
    ext g : 1
    exact hcz.fix g (by rw [hl]; simp)
  have hcc : c * c = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 c
  obtain ⟨c0, hc0⟩ := lift_sq_scalar α haa hax
  obtain ⟨m, hm⟩ := lift_sq_scalar α hbb hby
  obtain ⟨ν, hν⟩ := lift_sq_scalar α hcc hcz
  have hc00 : c0 ≠ 0 := by
    rintro rfl
    have : (((x * x : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hc0, zero_smul]
    exact Units.ne_zero _ this
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : (((y * y : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hm, zero_smul]
    exact Units.ne_zero _ this
  have hneg : ¬ IsSquare (-1 : F) := by
    have := Fintype.ofFinite F
    intro h
    exact ((FiniteField.isSquare_neg_one_iff (F := F)).1 h)
      (by rw [← Nat.card_eq_fintype_card]; exact hF4)
  have hyx : (y : Matrix (Fin 4) (Fin 4) F) * x = -((x : Matrix (Fin 4) (Fin 4) F) * y) := by
    rw [hxy]; simp
  by_cases h1 : IsSquare c0
  · by_cases h2' : IsSquare m
    ·
      have hsq : (((x * y : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) *
          (((x * y : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = (-(c0 * m)) • 1 := by
        rw [Units.val_mul]; exact W_xy_sq hc0 hm hν hxy hxz hyz
      have hnsq : ¬ IsSquare (-(c0 * m)) := by
        rintro ⟨r, hr'⟩
        obtain ⟨p, hp⟩ := h1
        obtain ⟨q, hq⟩ := h2'
        apply hneg
        refine ⟨r / (p * q), ?_⟩
        have hp0 : p ≠ 0 := by rintro rfl; apply hc00; rw [hp]; ring
        have hq0 : q ≠ 0 := by rintro rfl; apply hm0; rw [hq]; ring
        field_simp
        rw [hp, hq] at hr'
        linear_combination hr'
      refine rank3_coreU hF hF4 α hA hr (hax.mul hby) hax hcz ?_ ?_ ?_ hzn hsq hnsq
      · rw [Units.val_mul]; exact W_xy_x hc0 hm hν hxy hxz hyz
      · rw [Units.val_mul]; exact (W_z_xy hc0 hm hν hxy hxz hyz).symm
      · exact hxz
    · refine rank3_coreU hF hF4 α hA hr hby hax hcz hyx hyz hxz hzn hm h2'
  · exact rank3_coreU hF hF4 α hA hr hax hby hcz hxy hxz hyz hzn hc0 h1

end Rank3Core

section Quat

open Matrix CFSG CFSG.ComponentClassification Subgroup GenLocL4Q

theorem gammaAct_sl4_quatU {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (hF4 : Nat.card F % 4 = 3) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hinner : ∀ c : A, GenLocL4Q.IsInnerDiag4 (α c)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4)
    (x y : GL (Fin 4) F) (a b : A) (hax : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α a g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hby : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α b g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (y : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((y⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hanti : (x * y : Matrix (Fin 4) (Fin 4) F) = -(y * x : Matrix (Fin 4) (Fin 4) F)) :
    gammaAct α = ⊤ := by
  have _ := hsect
  rcases hA.2 with hr | hr
  · exact gammaAct_quat_rank2 hF α hA hr x y a b hax hby hanti
  · by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
    · obtain ⟨E, hE, hEk⟩ := hker
      exact gammaAct_eq_top_of_le_ker α hE hEk
    · have hker' : ∀ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E → ¬ E ≤ α.ker :=
        fun E hE hEk => hker ⟨E, hE, hEk⟩
      obtain ⟨hr23, hgam, -⟩ := range_reduction α hA hker'
      rw [hgam]
      have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
      let a' : ↥α.range := ⟨α a, a, rfl⟩
      let b' : ↥α.range := ⟨α b, b, rfl⟩
      have hax' : IsLift α.range.subtype a' x := hax
      have hby' : IsLift α.range.subtype b' y := hby
      rcases hr23.2 with hr2 | hr3
      · exact gammaAct_quat_rank2 hF α.range.subtype hr23 hr2 x y a' b' hax hby hanti
      · refine gammaAct_quat_rank3U hF hF4 α.range.subtype hr23 hr3 Subtype.val_injective ?_ hax'
          hby' hanti
        intro c'
        obtain ⟨c, hc⟩ := c'.2
        obtain ⟨u, hu⟩ := hinner c
        refine ⟨u, ?_⟩
        intro g
        have : (α.range.subtype c' : MulAut _) = α c := by
          show (c' : MulAut _) = α c
          exact hc.symm
        rw [this]
        exact hu g

end Quat

section Inner

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification Subgroup Matrix
  GenLocL4Inner

variable {F : Type} [Field F]

theorem gammaAct_sl4_inner_of_quatU [Finite F] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hinner : ∀ c : A, ∃ x : GL (Fin 4) F, ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((α c g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (x : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((x⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hsect : SectionalTwoRankLE ↥(innJoin α) 4) : gammaAct α = ⊤ := by
  choose ρ hρ using hinner
  have hneg := not_isSquare_neg_one hF4
  have hEA := hA.1
  have hcomm_aut : ∀ a b : A, α a * α b = α b * α a := fun a b => by
    rw [← map_mul, ← map_mul, mul_comm' a b]
  by_cases hanti : ∃ a b : A, (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ b : Matrix (Fin 4) (Fin 4) F) =
      -((ρ b : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F))
  · obtain ⟨a, b, hab⟩ := hanti
    exact gammaAct_sl4_quatU hF hF4 α hA (fun c => ⟨ρ c, hρ c⟩) hsect (ρ a) (ρ b) a b (hρ a) (hρ b)
      hab
  · push Not at hanti
    have hab : ∀ a b, ρ a * ρ b = ρ b * ρ a := fun a b =>
      (comm_or_anticomm hneg α ρ hρ a b (hcomm_aut a b)).resolve_right (hanti a b)
    by_cases hall : ∀ a, ∃ μ : F, μ ≠ 0 ∧
        (ρ a : Matrix (Fin 4) (Fin 4) F) * (ρ a : Matrix (Fin 4) (Fin 4) F) =
          (μ * μ) • (1 : Matrix (Fin 4) (Fin 4) F)
    · exact gammaAct_of_commuting_squares hF hEA α ρ hρ hab hall
    · push Not at hall
      obtain ⟨a₀, ha₀⟩ := hall
      obtain ⟨l, hl0, hl⟩ := GenLocL4Ext.rho_sq_scalar α ρ hEA hρ a₀
      have hlns : ¬ IsSquare l := by
        rintro ⟨μ, hμ⟩
        have hμ0 : μ ≠ 0 := fun h => hl0 (by rw [hμ, h, mul_zero])
        exact ha₀ μ hμ0 (by rw [hl, hμ])
      exact gammaAct_sl4_ext_odd hF α hA ρ hρ hab a₀ l hlns (by
        rw [Units.val_mul, hl, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal])

theorem ringChar_ne_two' {F : Type} [Field F] [Finite F] (hF4 : Nat.card F % 4 = 3) :
    ringChar F ≠ 2 := fun h => by
  have := Fintype.ofFinite F
  have hr := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at hr
  omega

end Inner

end GenLocL4InnerU

variable {F : Type} [Field F]

theorem gammaAct_sl4_inner_all [Finite F] (hF4 : Nat.card F % 4 = 3) {A : Type} [Group A] [Finite A]
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
    (hinner : ∀ c : A, GenLocL4Q.IsInnerDiag4 (α c)) (hsect : SectionalTwoRankLE ↥(innJoin α) 4) :
    gammaAct α = ⊤ :=
  GenLocL4InnerU.gammaAct_sl4_inner_of_quatU (GenLocL4InnerU.ringChar_ne_two' hF4) hF4 α hA hinner
    hsect

end CFSG.GH74.Generic.BProg.B2
