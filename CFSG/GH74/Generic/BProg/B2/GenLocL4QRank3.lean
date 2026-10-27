module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QRank3Core

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification Subgroup

namespace GenLocL4Q

variable {F : Type} [Field F] {A : Type} [Group A]

theorem IsLift.mul_eq {α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)} {e : A} {u : GL (Fin 4) F}
    (hu : IsLift α e u) (g : Matrix.SpecialLinearGroup (Fin 4) F) :
    ((α e g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
      (u : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
  rw [hu g, Matrix.mul_assoc, u.inv_mul, Matrix.mul_one]

theorem lift_comm_scalar {α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)} {e f : A}
    {u w : GL (Fin 4) F} (hu : IsLift α e u) (hw : IsLift α f w) (hef : e * f = f * e) :
    ∃ ε : F, (u : Matrix (Fin 4) (Fin 4) F) * (w : Matrix (Fin 4) (Fin 4) F) =
      ε • ((w : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F)) := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 4) (Fin 4) F, P = (((w * u)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
    ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := ⟨_, rfl⟩
  have hWP : ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P =
      ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [hP, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hcomm : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * P = P * (g : Matrix (Fin 4) (Fin 4) F) := by
    intro g
    have hh : α e (α f g) = α f (α e g) := by
      have : α e * α f = α f * α e := by rw [← map_mul, ← map_mul, hef]
      exact congrArg (fun φ : MulAut _ => φ g) this
    have h1 : ((α e (α f g) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
      rw [Units.val_mul, ← Matrix.mul_assoc, hu.mul_eq, Matrix.mul_assoc, hw.mul_eq, Matrix.mul_assoc]
    have h2 : ((α f (α e g) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by
      rw [Units.val_mul, ← Matrix.mul_assoc, hw.mul_eq, Matrix.mul_assoc, hu.mul_eq, Matrix.mul_assoc]
    rw [hh] at h1
    have h3 : ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P * (g : Matrix (Fin 4) (Fin 4) F)) =
        ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * P) := by
      calc ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P * (g : Matrix (Fin 4) (Fin 4) F))
          = (((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P) * (g : Matrix (Fin 4) (Fin 4) F) := by
            rw [Matrix.mul_assoc]
        _ = ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) := by rw [hWP]
        _ = ((α f (α e g) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := h1.symm
        _ = ((α f (α e g) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P) := by rw [hWP]
        _ = (((α f (α e g) : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * P := by rw [Matrix.mul_assoc]
        _ = (((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) * P := by
            rw [h2]
        _ = ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * P) := by
            rw [Matrix.mul_assoc]
    have h4 := congrArg (fun N => (((w * u)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * N) h3
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h4
    exact h4.symm
  obtain ⟨ε, hε⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (n := 4) (M := P) hcomm
  refine ⟨ε, ?_⟩
  have h5 : ((u * w : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ε • ((w * u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [← hWP, hε, Matrix.mul_smul, Matrix.mul_one]
  simpa [Units.val_mul] using h5

theorem sign_of_comm_scalar {u w : Matrix (Fin 4) (Fin 4) F} {s ε : F} (hs : s ≠ 0) (hw : w ≠ 0)
    (hu : u * u = s • 1) (huw : u * w = ε • (w * u)) : ε = 1 ∨ ε = -1 := by
  have h1 : u * (u * w) = s • w := by rw [← Matrix.mul_assoc, hu, smul_mul_assoc, one_mul]
  have h2 : u * (u * w) = (ε * ε * s) • w := by
    calc u * (u * w) = u * (ε • (w * u)) := by rw [huw]
      _ = ε • (u * (w * u)) := by rw [Matrix.mul_smul]
      _ = ε • ((u * w) * u) := by rw [Matrix.mul_assoc]
      _ = ε • ((ε • (w * u)) * u) := by rw [huw]
      _ = (ε * ε) • (w * (u * u)) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]
      _ = (ε * ε * s) • w := by rw [hu, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have h3 : (s - ε * ε * s) • w = 0 := by rw [sub_smul, ← h1, h2, sub_self]
  have h4 : s - ε * ε * s = 0 := (smul_eq_zero.1 h3).resolve_right hw
  have h5 : ε * ε = 1 := by
    have : s * (1 - ε * ε) = 0 := by linear_combination h4
    have := (mul_eq_zero.1 this).resolve_left hs
    linear_combination (-1 : F) * this
  exact mul_self_eq_one_iff.1 h5

section Adjust

variable {x y z : Matrix (Fin 4) (Fin 4) F} {ε1 ε2 : F}

theorem zx_tail_s (h : z * x = ε1 • (x * z)) (N : Matrix (Fin 4) (Fin 4) F) :
    z * (x * N) = ε1 • (x * (z * N)) := by
  rw [← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.mul_assoc]

theorem adjust_signs (hxy : x * y = -(y * x)) (h1 : ε1 = 1 ∨ ε1 = -1) (h2 : ε2 = 1 ∨ ε2 = -1)
    (hzx : z * x = ε1 • (x * z)) (hzy : z * y = ε2 • (y * z)) :
    (ε1 = 1 ∧ ε2 = 1 ∧ x * z = z * x ∧ y * z = z * y) ∨
    (ε1 = 1 ∧ ε2 = -1 ∧ x * (z * x) = (z * x) * x ∧ y * (z * x) = (z * x) * y) ∨
    (ε1 = -1 ∧ ε2 = 1 ∧ x * (z * y) = (z * y) * x ∧ y * (z * y) = (z * y) * y) ∨
    (ε1 = -1 ∧ ε2 = -1 ∧ x * (z * (x * y)) = (z * (x * y)) * x ∧ y * (z * (x * y)) = (z * (x * y)) * y) := by
  have hyx : y * x = -(x * y) := by rw [hxy]; simp
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · left
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simpa using hzx.symm
    · simpa using hzy.symm
  · right; left
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [Matrix.mul_assoc, hzx, one_smul,
        ]
    · simp only [Matrix.mul_assoc, yx_tail hxy, hzx, hzy, one_smul,
        neg_smul, Matrix.mul_neg]
  · right; right; left
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [Matrix.mul_assoc, yx_tail hxy, hzx, hzy, one_smul,
        neg_smul, neg_neg, Matrix.mul_neg]
    · simp only [Matrix.mul_assoc, hzy, one_smul,
        ]
  · right; right; right
    refine ⟨rfl, rfl, ?_, ?_⟩
    · simp only [Matrix.mul_assoc, yx_tail hxy, zx_tail_s hzx, hzx, hzy, smul_neg, one_smul,
        neg_smul, neg_neg, Matrix.mul_neg]
    · simp only [Matrix.mul_assoc, yx_tail hxy, zx_tail_s hzx, hzy, smul_neg, one_smul,
        neg_smul, neg_neg, Matrix.mul_neg]

end Adjust
theorem exists_comm_lift [Finite A] (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F))
    (hA : IsRank23 A) {a b c₀ : A} {x y z₀ : GL (Fin 4) F} (hax : IsLift α a x) (hby : IsLift α b y)
    (hcz : IsLift α c₀ z₀)
    (hxy : (x : Matrix (Fin 4) (Fin 4) F) * y = -((y : Matrix (Fin 4) (Fin 4) F) * x)) :
    ∃ (c : A) (z : GL (Fin 4) F), (c = c₀ ∨ c = c₀ * a ∨ c = c₀ * b ∨ c = c₀ * (a * b)) ∧ IsLift α c z ∧
      (x : Matrix (Fin 4) (Fin 4) F) * z = (z : Matrix (Fin 4) (Fin 4) F) * x ∧
      (y : Matrix (Fin 4) (Fin 4) F) * z = (z : Matrix (Fin 4) (Fin 4) F) * y := by
  have := hA.1
  have hcc : c₀ * c₀ = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 c₀
  obtain ⟨s, hs⟩ := lift_sq_scalar α hcc hcz
  have hs0 : s ≠ 0 := by
    rintro rfl
    have : (((z₀ * z₀ : GL (Fin 4) F)) : Matrix (Fin 4) (Fin 4) F) = 0 := by
      rw [Units.val_mul, hs, zero_smul]
    exact Units.ne_zero _ this
  obtain ⟨ε1, hε1⟩ := lift_comm_scalar hcz hax (mul_comm' c₀ a)
  obtain ⟨ε2, hε2⟩ := lift_comm_scalar hcz hby (mul_comm' c₀ b)
  have h1 := sign_of_comm_scalar hs0 (Units.ne_zero x) hs hε1
  have h2 := sign_of_comm_scalar hs0 (Units.ne_zero y) hs hε2
  rcases adjust_signs hxy h1 h2 hε1 hε2 with ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩ | ⟨-, -, e1, e2⟩
  · exact ⟨c₀, z₀, Or.inl rfl, hcz, e1, e2⟩
  · refine ⟨c₀ * a, z₀ * x, Or.inr (Or.inl rfl), hcz.mul hax, ?_, ?_⟩
    · rw [Units.val_mul]; exact e1
    · rw [Units.val_mul]; exact e2
  · refine ⟨c₀ * b, z₀ * y, Or.inr (Or.inr (Or.inl rfl)), hcz.mul hby, ?_, ?_⟩
    · rw [Units.val_mul]; exact e1
    · rw [Units.val_mul]; exact e2
  · refine ⟨c₀ * (a * b), z₀ * (x * y), Or.inr (Or.inr (Or.inr rfl)), hcz.mul (hax.mul hby), ?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul]; exact e1
    · rw [Units.val_mul, Units.val_mul]; exact e2

theorem gammaAct_quat_rank3 [Finite F] [Finite A] (hF : ringChar F ≠ 2) (hF4 : Nat.card F % 4 = 3)
    (h7 : 7 ≤ Nat.card F) (α : A →* MulAut (Matrix.SpecialLinearGroup (Fin 4) F)) (hA : IsRank23 A)
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
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({1, a, b, a * b} : Finset A))
    (t := Finset.univ) (by
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
    exact ((FiniteField.isSquare_neg_one_iff (F := F)).1 h) (by rw [← Nat.card_eq_fintype_card]; exact hF4)
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
      refine rank3_core hF hF4 h7 α hA hr (hax.mul hby) hax hcz ?_ ?_ ?_ hzn hsq hnsq
      · rw [Units.val_mul]; exact W_xy_x hc0 hm hν hxy hxz hyz
      · rw [Units.val_mul]; exact (W_z_xy hc0 hm hν hxy hxz hyz).symm
      · exact hxz
    · refine rank3_core hF hF4 h7 α hA hr hby hax hcz hyx hyz hxz hzn hm h2'
  · exact rank3_core hF hF4 h7 α hA hr hax hby hcz hxy hxz hyz hzn hc0 h1

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
