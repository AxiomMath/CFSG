module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QNsqBasis

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Subgroup

namespace GenLocL4Q

variable {F : Type} [Field F] {A : Type} [Group A]

@[expose] def pairSub (e f : A) (he : e * e = 1) (hf : f * f = 1) (hef : e * f = f * e) : Subgroup A where
  carrier := {1, e, f, e * f}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq ⊢
    have h1 : e * (e * f) = f := by rw [← mul_assoc, he, one_mul]
    have h2 : f * (e * f) = e := by rw [← mul_assoc, ← hef, mul_assoc, hf, mul_one]
    have h3 : (e * f) * e = f := by rw [hef, mul_assoc, he, mul_one]
    have h4 : (e * f) * f = e := by rw [mul_assoc, hf, mul_one]
    have h5 : (e * f) * (e * f) = 1 := by rw [← mul_assoc, h3, hf]
    rcases hp with h | h | h | h <;> rcases hq with h' | h' | h' | h' <;> rw [h, h'] <;>
      simp [he, hf, hef.symm, h1, h2, h3, h4, h5]
  one_mem' := by simp
  inv_mem' := by
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    have he' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
    have hf' : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
    rcases hp with h | h | h | h <;> rw [h]
    · simp
    · simp [he']
    · simp [hf']
    · right; right; right; rw [_root_.mul_inv_rev, he', hf', hef]

theorem pairSub_adm [Finite A] (hA : IsRank23 A) (hr : pRank 2 A = 3) {e f : A} (he : e * e = 1) (hf : f * f = 1)
    (hef : e * f = f * e) (he1 : e ≠ 1) (hf1 : f ≠ 1) (hef1 : e * f ≠ 1) :
    pRank 2 A - 1 ≤ pRank 2 ↥(pairSub e f he hf hef) := by
  classical
  have hcard : Nat.card A = 8 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hr]; norm_num
  have hfe : e ≠ f := fun h => hef1 (by rw [h, hf])
  have hsub : ({1, e, f, e * f} : Set A) ⊆ (pairSub e f he hf hef : Set A) := by
    intro p hp
    simpa [pairSub] using hp
  have hn1 : e * f ≠ e := fun h => hf1 (by simpa using h)
  have hn2 : e * f ≠ f := fun h => he1 (by simpa using h)
  have h4 : ({1, e, f, e * f} : Set A).ncard = 4 := by
    have m1 : (1 : A) ∉ ({e, f, e * f} : Set A) := by simp [he1.symm, hf1.symm, hef1.symm]
    have m2 : e ∉ ({f, e * f} : Set A) := by simp [hfe, hn1.symm]
    have m3 : f ∉ ({e * f} : Set A) := by simp [hn2.symm]
    rw [Set.ncard_insert_of_notMem m1, Set.ncard_insert_of_notMem m2, Set.ncard_insert_of_notMem m3,
      Set.ncard_singleton]
  have hge : 4 ≤ Nat.card ↥(pairSub e f he hf hef) := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h4] at this
    exact this.trans_eq (Nat.card_coe_set_eq (pairSub e f he hf hef : Set A)).symm
  have h1 := Subgroup.card_mul_index (pairSub e f he hf hef)
  rw [hcard] at h1
  have hidx : (pairSub e f he hf hef).index ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have : 4 * 3 ≤ Nat.card ↥(pairSub e f he hf hef) * (pairSub e f he hf hef).index :=
      Nat.mul_le_mul hge hcon
    omega
  exact (GenLocBasic.adm_iff_index hA.1 _).2 hidx

@[expose] def IsLift (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (e : A) (u : GL (Fin 4) F) : Prop :=
  ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
    ((α e g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((u⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

theorem IsLift.mul {α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)} {e f : A} {u w : GL (Fin 4) F}
    (hu : IsLift α e u) (hw : IsLift α f w) : IsLift α (e * f) (u * w) := by
  intro g
  rw [map_mul, MulAut.mul_apply, hu, hw, _root_.mul_inv_rev]
  simp only [Units.val_mul, Matrix.mul_assoc]

theorem IsLift.fix {α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)} {e : A} {u : GL (Fin 4) F}
    (hu : IsLift α e u) (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) : α e g = g := by
  apply Subtype.ext
  rw [hu g, ← hg, Matrix.mul_assoc, u.mul_inv, Matrix.mul_one]

theorem mem_gammaAct_of_pair [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA : IsRank23 A) (hr : pRank 2 A = 3) {e f : A} {u w : GL (Fin 4) F}
    (hu : IsLift α e u) (hw : IsLift α f w)
    (hnu : ¬ ∃ l : F, (u : Matrix (Fin 4) (Fin 4) F) = l • 1)
    (hnw : ¬ ∃ l : F, (w : Matrix (Fin 4) (Fin 4) F) = l • 1)
    (hnuw : ¬ ∃ l : F, ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = l • 1)
    (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hgu : (g : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F))
    (hgw : (g : Matrix (Fin 4) (Fin 4) F) * (w : Matrix (Fin 4) (Fin 4) F) =
      (w : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) : g ∈ gammaAct α := by
  have he : e * e = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 e
  have hf : f * f = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 f
  have hef : e * f = f * e := by have := hA.1; exact mul_comm' e f
  have he1 : e ≠ 1 := ne_one_of_lift α hu hnu
  have hf1 : f ≠ 1 := ne_one_of_lift α hw hnw
  have hef1 : e * f ≠ 1 := ne_one_of_lift α (hu.mul hw) hnuw
  have hadm := pairSub_adm hA hr he hf hef he1 hf1 hef1
  refine le_gammaAct α hadm ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro h hh
  have hh' : h = 1 ∨ h = e ∨ h = f ∨ h = e * f := by
    simpa [pairSub] using hh
  have hge : α e g = g := hu.fix g hgu
  have hgf : α f g = g := hw.fix g hgw
  rcases hh' with rfl | rfl | rfl | rfl
  · simp
  · exact hge
  · exact hgf
  · rw [map_mul, MulAut.mul_apply, hgf, hge]

section Words

variable {c m ν : F} {x y z : Matrix (Fin 4) (Fin 4) F}

theorem yx_tail (hxy : x * y = -(y * x)) (N : Matrix (Fin 4) (Fin 4) F) : y * (x * N) = -(x * (y * N)) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  rw [← Matrix.mul_assoc, hyx, Matrix.neg_mul, Matrix.mul_assoc]

theorem zx_tail (hxz : x * z = z * x) (N : Matrix (Fin 4) (Fin 4) F) : z * (x * N) = x * (z * N) := by
  rw [← Matrix.mul_assoc, ← hxz, Matrix.mul_assoc]

theorem sq_tail {a : Matrix (Fin 4) (Fin 4) F} {s : F} (h : a * a = s • 1) (N : Matrix (Fin 4) (Fin 4) F) :
    a * (a * N) = s • N := by
  rw [← Matrix.mul_assoc, h, smul_mul_assoc, one_mul]

theorem W_xy_x (hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (x * y) * x = -(x * (x * y)) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, hyx, sq_tail hx, 
    Matrix.mul_neg, 
    ]

theorem W_yz_x (_hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (y * z) * x = -(x * (y * z)) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, hzx, 
    
    ]

theorem W_xyz_x (hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (x * (y * z)) * x = -(x * (x * (y * z))) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, hzx, sq_tail hx, 
    Matrix.mul_neg, 
    ]

theorem W_xz_y (_hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (x * z) * y = -(y * (x * z)) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, hzy, 
    
    neg_neg]

theorem W_yxz_y (_hx : x * x = c • 1) (hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (y * (x * z)) * y = -(y * (y * (x * z))) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, hzy, sq_tail hy,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, 
    neg_neg]

theorem W_xyxz_x (hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    ((x * y) * (x * z)) * x = -(x * ((x * y) * (x * z))) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, hzx, sq_tail hx, 
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, smul_mul_assoc, 
    smul_neg, neg_neg]

theorem W_xy_sq (hx : x * x = c • 1) (hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (x * y) * (x * y) = (-(c * m)) • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, yx_tail hxy, 
    hx, hy, Matrix.mul_neg, Matrix.mul_smul, Matrix.mul_one,
    ]
  module

theorem W_z_xy (_hx : x * x = c • 1) (_hy : y * y = m • 1) (_hz : z * z = ν • 1) (hxy : x * y = -(y * x))
    (hxz : x * z = z * x) (hyz : y * z = z * y) :
    z * (x * y) = (x * y) * z := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  have hzx : z * x = x * z := hxz.symm
  have hzy : z * y = y * z := hyz.symm
  simp only [Matrix.mul_assoc, zx_tail hxz, hzy, 
    
    ]

end Words

theorem rank3_core [Finite F] [Finite A] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F)
    (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A) (hr : pRank 2 A = 3)
    {a b c : A} {x y z : GL (Fin 4) F} (hax : IsLift α a x) (hby : IsLift α b y) (hcz : IsLift α c z)
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
  · exact top_of_rank3_nsq hF hF4 h7 hc hsq hm0 hc0 hm hν hxy hxz hyz (gammaAct α) H1 H2 H3 H4 H5

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
