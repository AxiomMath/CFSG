module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG.GorensteinWalter CFSG.ClassicalInvolution.Q3.TL4.Z2W

section Calculus

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def autU (σ : F ≃+* F) (x : Fˣ) : Fˣ :=
  Units.map σ.toRingHom.toMonoidHom x

theorem autU_val (σ : F ≃+* F) (x : Fˣ) : (autU σ x : F) = σ (x : F) := rfl

theorem autU_mul (σ : F ≃+* F) (x y : Fˣ) : autU σ (x * y) = autU σ x * autU σ y :=
  map_mul (Units.map σ.toRingHom.toMonoidHom) x y

theorem autU_one (σ : F ≃+* F) : autU σ (1 : Fˣ) = 1 :=
  map_one (Units.map σ.toRingHom.toMonoidHom)

theorem autU_inv (σ : F ≃+* F) (x : Fˣ) : autU σ x⁻¹ = (autU σ x)⁻¹ :=
  map_inv (Units.map σ.toRingHom.toMonoidHom) x

theorem autU_neg_one (σ : F ≃+* F) : autU σ (-1 : Fˣ) = -1 := by
  apply Units.ext
  simp [autU]

theorem autU_pow (σ : F ≃+* F) (x : Fˣ) (n : ℕ) : autU σ (x ^ n) = (autU σ x) ^ n :=
  map_pow (Units.map σ.toRingHom.toMonoidHom) x n

theorem autU_comp (σ τ : F ≃+* F) (x : Fˣ) : autU (σ * τ) x = autU σ (autU τ x) := by
  apply Units.ext
  simp only [autU_val]
  rw [RingAut.mul_apply]

theorem autU_one_aut (x : Fˣ) : autU (1 : F ≃+* F) x = x := by
  apply Units.ext
  rw [autU_val, RingAut.coe_one]
  rfl

theorem autU_inv_aut (σ : F ≃+* F) (x : Fˣ) : autU σ⁻¹ (autU σ x) = x := by
  rw [← autU_comp, inv_mul_cancel, autU_one_aut]

theorem autU_aut_inv (σ : F ≃+* F) (x : Fˣ) : autU σ (autU σ⁻¹ x) = x := by
  rw [← autU_comp, mul_inv_cancel, autU_one_aut]

@[expose] noncomputable def gD (x : Fˣ) (σ : F ≃+* F) : PGammaL2 F := ⟨pD x, σ⟩

@[expose] noncomputable def gA (x : Fˣ) (σ : F ≃+* F) : PGammaL2 F := ⟨pA x, σ⟩

@[expose] noncomputable def ubar (F : Type) [Field F] [Finite F] : PGammaL2 F := gD (-1) 1

@[simp] theorem gD_left (x : Fˣ) (σ : F ≃+* F) : (gD x σ).left = pD x := rfl
@[simp] theorem gD_right (x : Fˣ) (σ : F ≃+* F) : (gD x σ).right = σ := rfl
@[simp] theorem gA_left (x : Fˣ) (σ : F ≃+* F) : (gA x σ).left = pA x := rfl
@[simp] theorem gA_right (x : Fˣ) (σ : F ≃+* F) : (gA x σ).right = σ := rfl

theorem gD_eq_iff {x y : Fˣ} {σ τ : F ≃+* F} : gD x σ = gD y τ ↔ x = y ∧ σ = τ := by
  constructor
  · intro h
    exact ⟨pD_eq_iff.mp (congrArg SemidirectProduct.left h),
      congrArg SemidirectProduct.right h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem gA_eq_iff {x y : Fˣ} {σ τ : F ≃+* F} : gA x σ = gA y τ ↔ x = y ∧ σ = τ := by
  constructor
  · intro h
    exact ⟨pA_eq_iff.mp (congrArg SemidirectProduct.left h),
      congrArg SemidirectProduct.right h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem inl_pD_eq (x : Fˣ) : (SemidirectProduct.inl (pD x) : PGammaL2 F) = gD x 1 := rfl

theorem gD_one_one : gD (1 : Fˣ) (1 : F ≃+* F) = 1 := by
  apply SemidirectProduct.ext
  · simp [pD_one]
  · simp

theorem gD_mul_gD (x y : Fˣ) (σ τ : F ≃+* F) : gD x σ * gD y τ = gD (x * autU σ y) (σ * τ) := by
  apply SemidirectProduct.ext
  · simp only [gD_left, gD_right, SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    rw [fieldAut_pD, pD_mul]
    rfl
  · simp only [gD_right, SemidirectProduct.mul_right]

theorem gD_mul_gA (x y : Fˣ) (σ τ : F ≃+* F) : gD x σ * gA y τ = gA (x * autU σ y) (σ * τ) := by
  apply SemidirectProduct.ext
  · simp only [gD_left, gD_right, gA_left, gA_right, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right]
    rw [fieldAut_pA, pD_mul_pA]
    rfl
  · simp only [gD_right, gA_right, SemidirectProduct.mul_right]

theorem gA_mul_gD (x y : Fˣ) (σ τ : F ≃+* F) :
    gA x σ * gD y τ = gA (x * (autU σ y)⁻¹) (σ * τ) := by
  apply SemidirectProduct.ext
  · simp only [gD_left, gD_right, gA_left, gA_right, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right]
    rw [fieldAut_pD, pA_mul_pD]
    rfl
  · simp only [gD_right, gA_right, SemidirectProduct.mul_right]

theorem gA_mul_gA (x y : Fˣ) (σ τ : F ≃+* F) :
    gA x σ * gA y τ = gD (x * (autU σ y)⁻¹) (σ * τ) := by
  apply SemidirectProduct.ext
  · simp only [gD_left, gD_right, gA_left, gA_right, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right]
    rw [fieldAut_pA, pA_mul_pA]
    rfl
  · simp only [gD_right, gA_right, SemidirectProduct.mul_right]

theorem gD_inv (x : Fˣ) (σ : F ≃+* F) : (gD x σ)⁻¹ = gD (autU σ⁻¹ x)⁻¹ σ⁻¹ := by
  rw [inv_eq_of_mul_eq_one_left]
  rw [gD_mul_gD, inv_mul_cancel, inv_mul_cancel, gD_one_one]

theorem gA_inv (x : Fˣ) (σ : F ≃+* F) : (gA x σ)⁻¹ = gA (autU σ⁻¹ x) σ⁻¹ := by
  rw [inv_eq_of_mul_eq_one_left]
  rw [gA_mul_gA, mul_inv_cancel, inv_mul_cancel, gD_one_one]

theorem ubar_eq : ubar F = gD (-1) 1 := rfl

theorem ubar_ne_one (h2 : (2 : F) ≠ 0) : ubar F ≠ 1 := by
  intro h
  rw [ubar_eq, ← gD_one_one] at h
  exact neg_one_ne_one_units h2 (gD_eq_iff.mp h).1

theorem gD_comm_ubar (x : Fˣ) (σ : F ≃+* F) : gD x σ * ubar F = ubar F * gD x σ := by
  rw [ubar_eq, gD_mul_gD, gD_mul_gD, autU_neg_one, autU_one_aut, gD_eq_iff]
  exact ⟨mul_comm x (-1), by simp⟩

theorem gA_comm_ubar (x : Fˣ) (σ : F ≃+* F) : gA x σ * ubar F = ubar F * gA x σ := by
  rw [ubar_eq, gA_mul_gD, gD_mul_gA, autU_neg_one, autU_one_aut, inv_neg_one, gA_eq_iff]
  exact ⟨mul_comm x (-1), by simp⟩

theorem eq_gD_or_gA_of_comm_ubar (h2 : (2 : F) ≠ 0) {g : PGammaL2 F}
    (hg : g * ubar F = ubar F * g) :
    (∃ x : Fˣ, g = gD x g.right) ∨ ∃ x : Fˣ, g = gA x g.right := by
  have hleft := congrArg SemidirectProduct.left hg
  simp only [SemidirectProduct.mul_left, ubar_eq, gD_left, gD_right, fieldAut_pD,
    units_map_neg_one, map_one, MulAut.one_apply] at hleft
  rcases comm_pD_neg_one h2 hleft with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact Or.inl ⟨x, SemidirectProduct.ext (by rw [gD_left]; exact hx) rfl⟩
  · exact Or.inr ⟨x, SemidirectProduct.ext (by rw [gA_left]; exact hx) rfl⟩

@[expose] def IsMon (g : PGammaL2 F) : Prop :=
  (∃ x : Fˣ, g = gD x g.right) ∨ ∃ x : Fˣ, g = gA x g.right

theorem isMon_gD (x : Fˣ) (σ : F ≃+* F) : IsMon (gD x σ) := Or.inl ⟨x, rfl⟩
theorem isMon_gA (x : Fˣ) (σ : F ≃+* F) : IsMon (gA x σ) := Or.inr ⟨x, rfl⟩

theorem isMon_mul {g h : PGammaL2 F} (hg : IsMon g) (hh : IsMon h) : IsMon (g * h) := by
  rcases hg with ⟨x, hx⟩ | ⟨x, hx⟩ <;> rcases hh with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨x * autU g.right y, ?_⟩
    have hgh : g * h = gD (x * autU g.right y) (g.right * h.right) := by
      conv_lhs => rw [hx, hy, gD_mul_gD]
    rw [SemidirectProduct.mul_right]
    exact hgh
  · refine Or.inr ⟨x * autU g.right y, ?_⟩
    have hgh : g * h = gA (x * autU g.right y) (g.right * h.right) := by
      conv_lhs => rw [hx, hy, gD_mul_gA]
    rw [SemidirectProduct.mul_right]
    exact hgh
  · refine Or.inr ⟨x * (autU g.right y)⁻¹, ?_⟩
    have hgh : g * h = gA (x * (autU g.right y)⁻¹) (g.right * h.right) := by
      conv_lhs => rw [hx, hy, gA_mul_gD]
    rw [SemidirectProduct.mul_right]
    exact hgh
  · refine Or.inl ⟨x * (autU g.right y)⁻¹, ?_⟩
    have hgh : g * h = gD (x * (autU g.right y)⁻¹) (g.right * h.right) := by
      conv_lhs => rw [hx, hy, gA_mul_gA]
    rw [SemidirectProduct.mul_right]
    exact hgh

theorem isMon_inv {g : PGammaL2 F} (hg : IsMon g) : IsMon g⁻¹ := by
  rcases hg with ⟨x, hx⟩ | ⟨x, hx⟩
  · refine Or.inl ⟨(autU g.right⁻¹ x)⁻¹, ?_⟩
    have hinv : g⁻¹ = gD (autU g.right⁻¹ x)⁻¹ g.right⁻¹ := by
      conv_lhs => rw [hx, gD_inv]
    rw [SemidirectProduct.inv_right]
    exact hinv
  · refine Or.inr ⟨autU g.right⁻¹ x, ?_⟩
    have hinv : g⁻¹ = gA (autU g.right⁻¹ x) g.right⁻¹ := by
      conv_lhs => rw [hx, gA_inv]
    rw [SemidirectProduct.inv_right]
    exact hinv

theorem isMon_iff_comm_ubar (h2 : (2 : F) ≠ 0) {g : PGammaL2 F} :
    IsMon g ↔ g * ubar F = ubar F * g := by
  constructor
  · intro hg
    rcases hg with ⟨x, hx⟩ | ⟨x, hx⟩
    · rw [hx]; exact gD_comm_ubar x g.right
    · rw [hx]; exact gA_comm_ubar x g.right
  · intro hg
    exact eq_gD_or_gA_of_comm_ubar h2 hg

@[expose] noncomputable def monGrp (F : Type) [Field F] [Finite F] : Subgroup (PGammaL2 F) where
  carrier := {g | IsMon g}
  mul_mem' := isMon_mul
  one_mem' := by
    exact Or.inl ⟨1, by rw [SemidirectProduct.one_right, gD_one_one]⟩
  inv_mem' := isMon_inv

@[expose] noncomputable def nrm (σ : F ≃+* F) (x : Fˣ) (n : ℕ) : Fˣ :=
  ∏ i ∈ Finset.range n, autU (σ ^ i) x

theorem nrm_zero (σ : F ≃+* F) (x : Fˣ) : nrm σ x 0 = 1 := by
  simp [nrm]

theorem nrm_succ (σ : F ≃+* F) (x : Fˣ) (n : ℕ) :
    nrm σ x (n + 1) = nrm σ x n * autU (σ ^ n) x := by
  simp [nrm, Finset.prod_range_succ]

theorem gD_pow (x : Fˣ) (σ : F ≃+* F) (n : ℕ) : (gD x σ) ^ n = gD (nrm σ x n) (σ ^ n) := by
  induction n with
  | zero => rw [pow_zero, nrm_zero, pow_zero, gD_one_one]
  | succ n ih => rw [pow_succ, ih, gD_mul_gD, nrm_succ, pow_succ]

theorem gA_sq (x : Fˣ) (σ : F ≃+* F) : (gA x σ) ^ 2 = gD (x * (autU σ x)⁻¹) (σ ^ 2) := by
  rw [sq, gA_mul_gA, sq]

theorem exists_gD_pow_even {g : PGammaL2 F} (hg : IsMon g) (n : ℕ) :
    ∃ x : Fˣ, g ^ (2 * n) = gD x (g.right ^ (2 * n)) := by
  rcases hg with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨nrm g.right x (2 * n), by rw [hx, gD_pow, gD_right]⟩
  · refine ⟨nrm (g.right ^ 2) (x * (autU g.right x)⁻¹) n, ?_⟩
    conv_lhs => rw [pow_mul, hx, gA_sq, gD_pow]
    rw [← pow_mul]

theorem exists_gD_sq {g : PGammaL2 F} (hg : IsMon g) :
    ∃ x : Fˣ, g ^ 2 = gD x (g.right ^ 2) := by
  obtain ⟨x, hx⟩ := exists_gD_pow_even hg 1
  exact ⟨x, by simpa using hx⟩

end Calculus

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
