module

public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices CFSG.GH74.Filter.ClassicalOdd

section Q8

variable {F : Type} [Field F]

theorem ModelData.exists_q8q8_swap (M : ModelData F) {ρ : Q8 →* GL (Fin 2) F}
    (hρ : ∀ g, ρ g ∈ M.H2) (hinj : Function.Injective ρ) (hz : ρ (QuaternionGroup.a 2) = -1) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ M.K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g) := by
  refine ⟨(diagGLHom F).comp (ρ.prodMap ρ), fun g => ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, d1⟩ := (M.mem_H2 _).1 (hρ g.1)
    obtain ⟨h2, d2⟩ := (M.mem_H2 _).1 (hρ g.2)
    change diagGL (ρ g.1) (ρ g.2) ∈ M.K4
    rw [M.diagGL_mem_K4_iff]
    exact ⟨h1, h2, by rw [d1, d2, one_mul]⟩
  · intro g g' h
    have := diagGL_inj h
    exact Prod.ext (hinj this.1) (hinj this.2)
  · change diagGL (ρ (QuaternionGroup.a 2)) (ρ (QuaternionGroup.a 2)) = xGL F
    rw [hz]
    rfl
  · intro g h
    exact swapGL_mul_diagGL_mul_inv (ρ g) (ρ h)

theorem ModelData.exists_q8q8 (M : ModelData F) {ρ : Q8 →* GL (Fin 2) F}
    (hρ : ∀ g, ρ g ∈ M.H2) (hinj : Function.Injective ρ) (hz : ρ (QuaternionGroup.a 2) = -1) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ M.K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F := by
  obtain ⟨φ, h1, h2, h3, -⟩ := M.exists_q8q8_swap hρ hinj hz
  exact ⟨φ, h1, h2, h3⟩

end Q8

section Linear

variable {F : Type} [Field F] [Finite F]

theorem exists_q8q8_swap_lin (hF : ringChar F ≠ 2) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ (ModelData.lin F).K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g) := by
  obtain ⟨a, b, h⟩ := (odd_field_two_dimensional_quaternion_matrices hF).1
  refine (ModelData.lin F).exists_q8q8_swap
    (ρ := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp
      (quatHom h)) (fun g => ?_) ?_ ?_
  · change _ ∈ StatedSL 2 F
    rw [statedSL_eq_detOne, mem_detOne]
    exact (quatHom h g).2
  · exact SpecialLinearGroup.toGL_injective.comp (quatHom_injective hF h)
  · apply Units.ext
    change ((quatHom h (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) F)) = _
    rw [quatHom_a_two h]
    simp

theorem exists_q8q8_lin (hF : ringChar F ≠ 2) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ (ModelData.lin F).K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F := by
  obtain ⟨φ, h1, h2, h3, -⟩ := exists_q8q8_swap_lin hF
  exact ⟨φ, h1, h2, h3⟩

theorem units_pow_four_eq_one_iff (hF : Nat.card F % 4 = 3) (c : Fˣ) :
    c ^ 4 = 1 ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro h
    have h' : ((c : F)) ^ 4 = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) h
      simpa using this
    have hfact : ((c : F) ^ 2 - 1) * ((c : F) ^ 2 + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 hfact with h1 | h1
    · have h1' : (c : F) * c = 1 := by linear_combination h1
      rcases mul_self_eq_one_iff.1 h1' with h2 | h2
      · exact Or.inl (Units.ext h2)
      · exact Or.inr (Units.ext (by simpa using h2))
    · exfalso
      have hsq : IsSquare (-1 : F) := ⟨c, by linear_combination (-1 : F) * h1⟩
      have : Fintype F := Fintype.ofFinite F
      have h4 := FiniteField.isSquare_neg_one_iff.1 hsq
      rw [← Nat.card_eq_fintype_card] at h4
      omega
  · rintro (rfl | rfl)
    · exact one_pow 4
    · norm_num

omit [Finite F] in
theorem scalar_neg_one_eq (n : ℕ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n) (-1 : Fˣ) : GL (Fin n) F) = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one, Units.val_neg,
    Units.val_one, map_neg, map_one]

omit [Finite F] in
theorem center_statedSL_eq (n : ℕ) :
    Subgroup.center ↥(StatedSL n F) =
      (StatedScalars (Fin n) F).subgroupOf (StatedSL n F) := by
  rw [← map_center_eq_statedScalars n F]
  exact (CFSG.LieType.Universal.Unitary.map_center_mulEquiv
    (specialLinearGroupEquivStatedSL n F)).symm

theorem mem_center_statedSL_four_iff (hF : Nat.card F % 4 = 3) (g : ↥(StatedSL 4 F)) :
    g ∈ Subgroup.center ↥(StatedSL 4 F) ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F := by
  rw [center_statedSL_eq, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hdet : (c : F) ^ 4 = 1 := by
      have h1 : (g : GL (Fin 4) F) ∈ detOne F 4 := by
        rw [← statedSL_eq_detOne]
        exact g.2
      rw [mem_detOne, ← hc] at h1
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using
        h1
    have hc4 : c ^ 4 = 1 := Units.ext (by simpa using hdet)
    rcases (units_pow_four_eq_one_iff hF c).1 hc4 with rfl | rfl
    · exact Or.inl (by rw [← hc, map_one])
    · exact Or.inr (by rw [← hc, xGL_eq_neg_one, scalar_neg_one_eq])
  · rintro (h | h)
    · exact ⟨1, by rw [map_one, h]⟩
    · exact ⟨-1, by rw [h, xGL_eq_neg_one, scalar_neg_one_eq]⟩

theorem mem_center_lin_iff (hF : Nat.card F % 4 = 3) (g : ↥(ModelData.lin F).K4) :
    g ∈ Subgroup.center ↥(ModelData.lin F).K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F :=
  mem_center_statedSL_four_iff hF g

end Linear

section Unitary

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem exists_q8q8_swap_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ (ModelData.uni hF).K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g) := by
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨a, b, ha, hb, hab⟩ := exists_quat_unitary hp2 hF
  have hσ : ∀ x, (unitaryInvolution F p f : F →+* F) x = x ^ (p ^ f) :=
    unitaryInvolution_apply F p f
  refine (ModelData.uni hF).exists_q8q8_swap
    (ρ := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).comp
      (quatHom hab)) (fun g => ?_) ?_ ?_
  · refine ((ModelData.uni hF).mem_H2 _).2 ⟨?_, (quatHom hab g).2⟩
    exact isUni_quatHom hab (σ := (unitaryInvolution F p f : F →+* F)) (by rw [hσ]; exact ha)
      (by rw [hσ]; exact hb) g
  · exact SpecialLinearGroup.toGL_injective.comp (quatHom_injective hK2 hab)
  · apply Units.ext
    change ((quatHom hab (QuaternionGroup.a 2) : Matrix (Fin 2) (Fin 2) F)) = _
    rw [quatHom_a_two hab]
    simp

theorem exists_q8q8_uni (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ (ModelData.uni hF).K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F := by
  obtain ⟨φ, h1, h2, h3, -⟩ := exists_q8q8_swap_uni hF hp2
  exact ⟨φ, h1, h2, h3⟩

omit [Finite F] [Fact (Nat.Prime p)] [CharP F p] in
theorem units_eq_one_or_neg_one_of_unitary (hq : p ^ f % 4 = 1) (c : Fˣ) (h4 : c ^ 4 = 1)
    (hq1 : c ^ (p ^ f + 1) = 1) : c = 1 ∨ c = -1 := by
  have hk : p ^ f + 1 = 4 * ((p ^ f + 1) / 4) + 2 := by omega
  have h2 : c ^ 2 = 1 := by
    have : c ^ (4 * ((p ^ f + 1) / 4) + 2) = 1 := hk ▸ hq1
    rwa [pow_add, pow_mul, h4, one_pow, one_mul] at this
  have h1' : (c : F) * c = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) h2
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 h1' with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by simpa using h))

omit [CharP F p] in
theorem mem_center_statedSU_four_iff (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (g : ↥(StatedSU 4 (p ^ f) F)) :
    g ∈ Subgroup.center ↥(StatedSU 4 (p ^ f) F) ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F := by
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF (n := 4)
    (by norm_num) (fun h => by simp at h)).2
  rw [hZ, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc⟩
    have hmem : (g : GL (Fin 4) F) ∈ StatedSU 4 (p ^ f) F := g.2
    rw [← hc, CFSG.LinearGroups.scalar_mem_statedSU_iff (Fact.out : p.Prime) hF (by norm_num)]
      at hmem
    rcases units_eq_one_or_neg_one_of_unitary hq c hmem.1 hmem.2 with rfl | rfl
    · exact Or.inl (by rw [← hc, map_one])
    · exact Or.inr (by rw [← hc, xGL_eq_neg_one, scalar_neg_one_eq])
  · rintro (h | h)
    · exact ⟨1, by rw [map_one, h]⟩
    · exact ⟨-1, by rw [h, xGL_eq_neg_one, scalar_neg_one_eq]⟩

theorem mem_center_uni_iff (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (g : ↥(ModelData.uni hF).K4) :
    g ∈ Subgroup.center ↥(ModelData.uni hF).K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F :=
  mem_center_statedSU_four_iff hF hq g

end Unitary

section Abstract

variable {F : Type} [Field F]

theorem xGL_ne_one (h2 : (2 : F) ≠ 0) : xGL F ≠ 1 := by
  rw [xGL_eq_neg_one]
  intro h
  have h0 := congrArg (fun u : GL (Fin 4) F => (u : Matrix (Fin 4) (Fin 4) F) 0 0) h
  simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply_eq] at h0
  exact h2 (by linear_combination (-1 : F) * h0)

theorem ringChar_ne_two_of_two_ne_zero (h2 : (2 : F) ≠ 0) : ringChar F ≠ 2 := by
  intro hc
  have h0 := ringChar.Nat.cast_ringChar (R := F)
  rw [hc] at h0
  exact h2 (by exact_mod_cast h0)

theorem mem_center_iff_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    e g ∈ Subgroup.center H ↔ g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h x
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e x)
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h x]

theorem exists_q8_frame_of_model {K : Type*} [Group K] (M : ModelData F)
    (e : K ≃* ↥M.K4) (h2 : (2 : F) ≠ 0)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hq : ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ M.K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g)) :
    ∃ (z : K) (φ : Q8 × Q8 →* K) (w : K), orderOf z = 2 ∧
      (∀ g : K, g ∈ Subgroup.center K ↔ g = 1 ∨ g = z) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = z ∧ w * w = 1 ∧
      ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g) := by
  obtain ⟨φ0, hφ0, hinj, hz, hsw⟩ := hq
  refine ⟨e.symm M.xK, e.symm.toMonoidHom.comp (φ0.codRestrict M.K4 hφ0), e.symm M.wK,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hx : M.xK ≠ 1 := fun h => xGL_ne_one h2 (congrArg Subtype.val h)
    have hxx : M.xK * M.xK = 1 := Subtype.ext xGL_mul_self
    refine orderOf_eq_prime (p := 2) ?_ ?_
    · rw [sq, ← map_mul, hxx, map_one]
    · intro h
      exact hx (e.symm.injective (by rw [h, map_one]))
  · intro g
    rw [← mem_center_iff_of_mulEquiv e, hcenter]
    constructor
    · rintro (h | h)
      · exact Or.inl (e.injective (by rw [map_one]; exact Subtype.ext h))
      · exact Or.inr (e.injective (by rw [MulEquiv.apply_symm_apply]; exact Subtype.ext h))
    · rintro (h | h)
      · exact Or.inl (by rw [h, map_one]; rfl)
      · exact Or.inr (by rw [h, MulEquiv.apply_symm_apply]; rfl)
  · intro a b hab
    have := e.symm.injective hab
    exact hinj (congrArg Subtype.val this)
  · change e.symm (φ0.codRestrict M.K4 hφ0 _) = _
    congr 1
    exact Subtype.ext hz
  · rw [← map_mul]
    have : M.wK * M.wK = 1 := Subtype.ext swapGL_mul_self
    rw [this, map_one]
  · intro g h
    change e.symm M.wK * e.symm (φ0.codRestrict M.K4 hφ0 (g, h)) * (e.symm M.wK)⁻¹ =
      e.symm (φ0.codRestrict M.K4 hφ0 (h, g))
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hsw g h)

theorem exists_center_q8q8_of_model {K : Type*} [Group K] (M : ModelData F)
    (e : K ≃* ↥M.K4) (h2 : (2 : F) ≠ 0)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hq : ∃ φ : Q8 × Q8 →* GL (Fin 4) F, (∀ g, φ g ∈ M.K4) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = xGL F ∧
      ∀ g h : Q8, swapGL F * φ (g, h) * (swapGL F)⁻¹ = φ (h, g)) :
    ∃ (z : K) (φ : Q8 × Q8 →* K), orderOf z = 2 ∧
      (∀ g : K, g ∈ Subgroup.center K ↔ g = 1 ∨ g = z) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = z := by
  obtain ⟨z, φ, -, h1, h2, h3, h4, -⟩ := exists_q8_frame_of_model M e h2 hcenter hq
  exact ⟨z, φ, h1, h2, h3, h4⟩

end Abstract

section IsModel

@[expose] def IsSL4Model (K : Type*) [Group K] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 4 = 3 ∧
      Nonempty (K ≃* StatedSL 4 F)) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      Nonempty (K ≃* StatedSU 4 q F))

variable {K : Type*} [Group K]

theorem IsSL4Model.of_mulEquiv {K' : Type*} [Group K'] (h : IsSL4Model K) (e : K ≃* K') :
    IsSL4Model K' := by
  rcases h with ⟨F, _, _, hF, ⟨e'⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e'⟩⟩
  · exact Or.inl ⟨F, inferInstance, inferInstance, hF, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq, ⟨e.symm.trans e'⟩⟩

theorem IsSL4Model.finite (h : IsSL4Model K) : Finite K := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact Finite.of_equiv _ e.symm.toEquiv
  · exact Finite.of_equiv _ e.symm.toEquiv

theorem IsSL4Model.exists_q8_frame (h : IsSL4Model K) :
    ∃ (z : K) (φ : Q8 × Q8 →* K) (w : K), orderOf z = 2 ∧
      (∀ g : K, g ∈ Subgroup.center K ↔ g = 1 ∨ g = z) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = z ∧ w * w = 1 ∧
      ∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g) := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
    have h2 := two_ne_zero_of_odd_card (F := F) hodd
    exact exists_q8_frame_of_model (ModelData.lin F) e h2 (mem_center_lin_iff hF)
      (exists_q8q8_swap_lin (ringChar_ne_two_of_two_ne_zero h2))
  · obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
    have hodd : Odd (Nat.card F) := by
      rw [hF]
      exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
    have h2 := two_ne_zero_of_odd_card (F := F) hodd
    have hp2 := prime_ne_two_of_odd_card (F := F) (p := p) hodd
    exact exists_q8_frame_of_model (ModelData.uni hF) e h2 (mem_center_uni_iff hF hq)
      (exists_q8q8_swap_uni hF hp2)

theorem IsSL4Model.exists_center_q8q8 (h : IsSL4Model K) :
    ∃ (z : K) (φ : Q8 × Q8 →* K), orderOf z = 2 ∧
      (∀ g : K, g ∈ Subgroup.center K ↔ g = 1 ∨ g = z) ∧ Function.Injective φ ∧
      φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = z := by
  obtain ⟨z, φ, -, h1, h2, h3, h4, -⟩ := h.exists_q8_frame
  exact ⟨z, φ, h1, h2, h3, h4⟩

theorem IsSL4Model.natCard_center (h : IsSL4Model K) : Nat.card (Subgroup.center K) = 2 := by
  obtain ⟨z, φ, hz2, hcenter, -, -⟩ := h.exists_center_q8q8
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Subgroup.one_mem _⟩, ⟨z, (hcenter z).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h1
    have h1' : (1 : K) = z := congrArg Subtype.val h1
    rw [← h1', orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · ext ⟨g, hg⟩
    rcases (hcenter g).1 hg with rfl | rfl <;> simp

end IsModel

section Rank

theorem not_sectionalTwoRankLE_q8q8 : ¬ SectionalTwoRankLE (Q8 × Q8) 3 := by
  intro h
  have h' : SectionalTwoRankLE (V4 × V4) 3 :=
    SectionalTwoRankLE.of_surjective (q8Frattini.prodMap q8Frattini)
      (q8Frattini_surjective.prodMap q8Frattini_surjective) h
  have hV4 : ∀ a : V4, a ^ 2 = 1 := by decide
  have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (V4 × V4)) :=
    ⟨⟨⟨fun a b => Subtype.ext (mul_comm a.1 b.1)⟩⟩,
      fun x _ => Prod.ext (hV4 x.1) (hV4 x.2)⟩
  have := SectionalTwoRankLE.card_le_of_elementary h' ⊤ hE
  rw [Subgroup.card_top, Nat.card_prod, card_V4] at this
  omega

variable {K : Type*} [Group K]

theorem not_sectionalTwoRankLE_three_of_q8q8 (φ : Q8 × Q8 →* K) (hφ : Function.Injective φ) :
    ¬ SectionalTwoRankLE K 3 :=
  fun h => not_sectionalTwoRankLE_q8q8 (SectionalTwoRankLE.of_injective φ hφ h)

theorem IsSL4Model.not_sectionalTwoRankLE_three (h : IsSL4Model K) : ¬ SectionalTwoRankLE K 3 := by
  obtain ⟨z, φ, -, -, hφ, -⟩ := h.exists_center_q8q8
  exact not_sectionalTwoRankLE_three_of_q8q8 φ hφ

theorem IsSL4Model.four_le_sectionalTwoRank (h : IsSL4Model K) : 4 ≤ sectionalTwoRank K := by
  have := h.finite
  by_contra hlt
  exact h.not_sectionalTwoRankLE_three (sectionalTwoRank_le_iff.1 (by omega))

end Rank

end CFSG.GH74.L5U5
