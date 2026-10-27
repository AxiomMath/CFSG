module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups commutatorElement Pointwise

section Sylow

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem quatI_eq_inv_quarterTurn :
    (quatI : SL2 F) = (CFSG.Semidihedral.OddLinearNormals.quarterTurn F)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  refine Subtype.ext ?_
  show (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_conj_quaternion_mem_sylow (hodd : Odd (Nat.card F)) {a b : F}
    (h : a ^ 2 + b ^ 2 = -1) (P : Sylow 2 (SL2 F)) :
    ∃ ρ : SL2 F, ρ * quatI * ρ⁻¹ ∈ (P : Subgroup (SL2 F)) ∧
      ρ * quatJ h * ρ⁻¹ ∈ (P : Subgroup (SL2 F)) := by
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hQ : IsPGroup 2 (CFSG.Semidihedral.OddFieldSL2.quaternionSubgroup F a b h) := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_congr
      (CFSG.Semidihedral.OddFieldSL2.quaternionSubgroupEquiv F h2 a b h).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  obtain ⟨ρ, hρ⟩ := MulAction.exists_smul_eq (SL2 F) S P
  have hI : (quatI : SL2 F) ∈ CFSG.Semidihedral.OddFieldSL2.quaternionSubgroup F a b h := by
    rw [quatI_eq_inv_quarterTurn]
    refine Subgroup.inv_mem _ ⟨QuaternionGroup.a 1, ?_⟩
    exact CFSG.Semidihedral.OddFieldSL2.quaternionHom_rotation F a b h
  have hJ : (quatJ h : SL2 F) ∈ CFSG.Semidihedral.OddFieldSL2.quaternionSubgroup F a b h :=
    ⟨QuaternionGroup.xa 0, CFSG.Semidihedral.OddFieldSL2.quaternionHom_outside F a b h⟩
  have key : ∀ x ∈ S, ρ * x * ρ⁻¹ ∈ (P : Subgroup (SL2 F)) := by
    intro x hx
    have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj ρ) (S : Subgroup (SL2 F)) hx
    rw [← Sylow.coe_subgroup_smul, hρ] at h1
    simpa using h1
  exact ⟨ρ, key _ (hQS hI), key _ (hQS hJ)⟩

theorem neg_one_mem_sylow (hodd : Odd (Nat.card F)) (P : Sylow 2 (SL2 F)) :
    (-1 : SL2 F) ∈ (P : Subgroup (SL2 F)) := by
  obtain ⟨a, b, h⟩ := exists_sq_add_sq_eq_neg_one hodd
  obtain ⟨ρ, hI, -⟩ := exists_conj_quaternion_mem_sylow hodd h P
  have hc : ∀ x : SL2 F, x * (-1) = (-1) * x := fun x =>
    Subgroup.mem_center_iff.mp (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F) x
  have : ρ * quatI * ρ⁻¹ * (ρ * quatI * ρ⁻¹) = -1 := by
    calc ρ * quatI * ρ⁻¹ * (ρ * quatI * ρ⁻¹) = ρ * (quatI * quatI) * ρ⁻¹ := by group
      _ = ρ * (-1) * ρ⁻¹ := by rw [quatI_mul_self]
      _ = -1 := by rw [hc ρ]; group
  rw [← this]
  exact (P : Subgroup (SL2 F)).mul_mem hI hI

theorem glConjSL_eq_of_fix_sylow (hodd : Odd (Nat.card F)) (P : Sylow 2 (SL2 F))
    {D : GL (Fin 2) F} (hD : ∀ x ∈ (P : Subgroup (SL2 F)), glConjSL D x = x) :
    ∀ A, glConjSL D A = A := by
  obtain ⟨a, b, h⟩ := exists_sq_add_sq_eq_neg_one hodd
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨ρ, hρI, hρJ⟩ := exists_conj_quaternion_mem_sylow hodd h P
  exact glConjSL_eq_of_fix_quaternion h h2 ρ (hD _ hρI) (hD _ hρJ)

end Sylow

section Inner

variable {F : Type} [Field F] {G : Type*} [Group G]

@[expose] def ActsByGL (Φ : SL2 F →* G) (x : G) (D : GL (Fin 2) F) : Prop :=
  ∀ A : SL2 F, x * Φ A * x⁻¹ = Φ (glConjSL D A)

theorem ActsByGL.mul {Φ : SL2 F →* G} {x y : G} {D E : GL (Fin 2) F} (hx : ActsByGL Φ x D)
    (hy : ActsByGL Φ y E) : ActsByGL Φ (x * y) (D * E) := by
  intro A
  rw [glConjSL_mul]
  calc x * y * Φ A * (x * y)⁻¹ = x * (y * Φ A * y⁻¹) * x⁻¹ := by group
    _ = x * Φ (glConjSL E A) * x⁻¹ := by rw [hy A]
    _ = Φ (glConjSL D (glConjSL E A)) := hx _

theorem ActsByGL.inv {Φ : SL2 F →* G} {x : G} {D : GL (Fin 2) F} (hx : ActsByGL Φ x D) :
    ActsByGL Φ x⁻¹ D⁻¹ := by
  intro A
  have h := hx (glConjSL D⁻¹ A)
  rw [← glConjSL_mul, mul_inv_cancel, glConjSL_one] at h
  calc x⁻¹ * Φ A * x⁻¹⁻¹ = x⁻¹ * (x * Φ (glConjSL D⁻¹ A) * x⁻¹) * x := by rw [h]; group
    _ = Φ (glConjSL D⁻¹ A) := by group

theorem ActsByGL.one {Φ : SL2 F →* G} : ActsByGL Φ (1 : G) 1 := fun A => by
  simp [glConjSL_one]

theorem actsBy_toGL_iff {Φ : SL2 F →* G} {x : G} {B : SL2 F} :
    ActsByGL Φ x (Matrix.SpecialLinearGroup.toGL B) ↔
      ∀ A, x * Φ A * x⁻¹ = Φ (B * A * B⁻¹) := by
  simp only [ActsByGL, glConjSL_toGL]

@[expose] def InnAct (Φ : SL2 F →* G) (x : G) : Prop :=
  ∃ B : SL2 F, ActsByGL Φ x (Matrix.SpecialLinearGroup.toGL B)

@[expose] def innActSubgroup (Φ : SL2 F →* G) : Subgroup G where
  carrier := {x | InnAct Φ x}
  one_mem' := ⟨1, by rw [map_one]; exact ActsByGL.one⟩
  mul_mem' := by
    rintro x y ⟨B, hB⟩ ⟨C, hC⟩
    exact ⟨B * C, by rw [map_mul]; exact hB.mul hC⟩
  inv_mem' := by
    rintro x ⟨B, hB⟩
    exact ⟨B⁻¹, by rw [map_inv]; exact hB.inv⟩

theorem exists_toGL_eq_of_det_eq_one (D : GL (Fin 2) F)
    (hD : Matrix.GeneralLinearGroup.det D = 1) :
    ∃ B : SL2 F, Matrix.SpecialLinearGroup.toGL B = D := by
  have h : Matrix.det (D : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg Units.val hD
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  exact ⟨⟨(D : Matrix (Fin 2) (Fin 2) F), h⟩, Units.ext rfl⟩

theorem innAct_commutator {Φ : SL2 F →* G} {x y : G} (hx : LinAct Φ x) (hy : LinAct Φ y) :
    InnAct Φ ⁅x, y⁆ := by
  obtain ⟨D, hD⟩ := hx
  obtain ⟨E, hE⟩ := hy
  have hD' : ActsByGL Φ x D := hD
  have hE' : ActsByGL Φ y E := hE
  have h : ActsByGL Φ (x * y * x⁻¹ * y⁻¹) (D * E * D⁻¹ * E⁻¹) :=
    ((hD'.mul hE').mul hD'.inv).mul hE'.inv
  have hdet : Matrix.GeneralLinearGroup.det (D * E * D⁻¹ * E⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [mul_comm (Matrix.GeneralLinearGroup.det D) (Matrix.GeneralLinearGroup.det E)]
    group
  obtain ⟨B, hB⟩ := exists_toGL_eq_of_det_eq_one _ hdet
  refine ⟨B, ?_⟩
  rw [hB, commutatorElement_def]
  exact h

end Inner

section Counting

variable {F : Type} [Field F] [Finite F] {M : Type*} [Group M]

@[expose] def innActPairs (Φ Ψ : SL2 F →* M) : Subgroup (SL2 F × SL2 F) where
  carrier := {p | ActsByGL Φ (Ψ p.1) (Matrix.SpecialLinearGroup.toGL p.2)}
  one_mem' := by
    show ActsByGL Φ (Ψ 1) (Matrix.SpecialLinearGroup.toGL 1)
    rw [map_one, map_one]
    exact ActsByGL.one
  mul_mem' := by
    rintro ⟨y₁, B₁⟩ ⟨y₂, B₂⟩ h₁ h₂
    have h₁' : ActsByGL Φ (Ψ y₁) (Matrix.SpecialLinearGroup.toGL B₁) := h₁
    have h₂' : ActsByGL Φ (Ψ y₂) (Matrix.SpecialLinearGroup.toGL B₂) := h₂
    show ActsByGL Φ (Ψ (y₁ * y₂)) (Matrix.SpecialLinearGroup.toGL (B₁ * B₂))
    rw [map_mul, map_mul]
    exact h₁'.mul h₂'
  inv_mem' := by
    rintro ⟨y, B⟩ h
    have h' : ActsByGL Φ (Ψ y) (Matrix.SpecialLinearGroup.toGL B) := h
    show ActsByGL Φ (Ψ y⁻¹) (Matrix.SpecialLinearGroup.toGL B⁻¹)
    rw [map_inv, map_inv]
    exact h'.inv

theorem false_of_innAct_of_trivial_centralizer (hneg : (-1 : SL2 F) ≠ 1) {Φ Ψ : SL2 F →* M}
    (hinn : ∀ y, InnAct Φ (Ψ y))
    (htriv : ∀ y : SL2 F, (∀ A, Φ A * Ψ y = Ψ y * Φ A) → y = 1) : False := by
  have hc : ∀ x : SL2 F, x * (-1) = (-1) * x := fun x =>
    Subgroup.mem_center_iff.mp (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F) x
  set T := innActPairs Φ Ψ with hT
  let π₁ : T →* SL2 F := (MonoidHom.fst (SL2 F) (SL2 F)).comp T.subtype
  let π₂ : T →* SL2 F := (MonoidHom.snd (SL2 F) (SL2 F)).comp T.subtype
  have hπ₁ : Function.Surjective π₁ := by
    intro y
    obtain ⟨B, hB⟩ := hinn y
    exact ⟨⟨(y, B), hB⟩, rfl⟩
  have hπ₂ : Function.Injective π₂ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨y, B⟩, hyB⟩ h1
    have hB1 : B = 1 := h1
    subst hB1
    have hyB' : ActsByGL Φ (Ψ y) (Matrix.SpecialLinearGroup.toGL 1) := hyB
    rw [map_one] at hyB'
    have hy1 : y = 1 := by
      apply htriv
      intro A
      have h := hyB' A
      rw [glConjSL_one, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    subst hy1
    rfl
  have hmem1 : ((1 : SL2 F), (-1 : SL2 F)) ∈ T := by
    show ActsByGL Φ (Ψ 1) (Matrix.SpecialLinearGroup.toGL (-1))
    rw [actsBy_toGL_iff]
    intro A
    rw [map_one]
    have : (-1 : SL2 F) * A * (-1 : SL2 F)⁻¹ = A := by
      rw [← hc A]
      group
    rw [this]
    group
  have hker : π₁.ker ≠ ⊥ := by
    intro hbot
    have hk : (⟨((1 : SL2 F), (-1 : SL2 F)), hmem1⟩ : T) ∈ π₁.ker := rfl
    rw [hbot, Subgroup.mem_bot] at hk
    have := congrArg (fun z : T => z.1.2) hk
    exact hneg this
  have hcard : Nat.card π₁.ker * Nat.card (SL2 F) = Nat.card T :=
    Subgroup.card_ker_mul_card_of_surjective hπ₁
  have hle : Nat.card T ≤ Nat.card (SL2 F) := Nat.card_le_card_of_injective π₂ hπ₂
  have h2 : 1 < Nat.card π₁.ker := (Subgroup.one_lt_card_iff_ne_bot _).mpr hker
  have hpos : 0 < Nat.card (SL2 F) := Nat.card_pos
  nlinarith

end Counting

section Main

variable {F : Type} [Field F] [Finite F] {M : Type*} [Group M]

omit [Finite F] in
theorem conj_centralizes_of_linAct {Φ : SL2 F →* M} {x c : M} (hx : LinAct Φ x)
    (hc : ∀ A, Φ A * c = c * Φ A) : ∀ A, Φ A * (x * c * x⁻¹) = (x * c * x⁻¹) * Φ A := by
  intro A
  obtain ⟨E, hE⟩ := (linActSubgroup Φ).inv_mem hx
  have h : x⁻¹ * Φ A * x = Φ (glConjSL E A) := by
    have := hE A
    rwa [inv_inv] at this
  have key : Φ A = x * Φ (glConjSL E A) * x⁻¹ := by
    rw [← h]
    group
  calc Φ A * (x * c * x⁻¹) = (x * Φ (glConjSL E A) * x⁻¹) * (x * c * x⁻¹) := by rw [← key]
    _ = x * (Φ (glConjSL E A) * c) * x⁻¹ := by group
    _ = x * (c * Φ (glConjSL E A)) * x⁻¹ := by rw [hc]
    _ = (x * c * x⁻¹) * (x * Φ (glConjSL E A) * x⁻¹) := by group
    _ = (x * c * x⁻¹) * Φ A := by rw [← key]

theorem range_eq_of_sylow_commute (hodd : Odd (Nat.card F)) (h4 : 4 ≤ Nat.card F)
    {Φ Ψ : SL2 F →* M} (hΨ : Function.Injective Ψ)
    (H1 : ∀ x : M, x * Φ (-1) = Φ (-1) * x → LinAct Φ x)
    (H2 : ∀ x : M, x * Ψ (-1) = Ψ (-1) * x → LinAct Ψ x)
    (H4 : (∀ A B, Φ A * Ψ B = Ψ B * Φ A) → Ψ.range = Φ.range)
    (P : Sylow 2 (SL2 F)) (H5 : ∀ x ∈ (P : Subgroup (SL2 F)), Ψ x * Φ (-1) = Φ (-1) * Ψ x) :
    Ψ.range = Φ.range := by
  have hneg : (-1 : SL2 F) ≠ 1 := CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
  have hnegP := neg_one_mem_sylow hodd P
  have hcc : Φ (-1) * Ψ (-1) = Ψ (-1) * Φ (-1) := (H5 _ hnegP).symm
  obtain ⟨D, hD⟩ := H2 (Φ (-1)) hcc
  have hfix : ∀ x ∈ (P : Subgroup (SL2 F)), glConjSL D x = x := by
    intro x hx
    apply hΨ
    rw [← hD x]
    calc Φ (-1) * Ψ x * (Φ (-1))⁻¹ = Ψ x * Φ (-1) * (Φ (-1))⁻¹ := by rw [← H5 x hx]
      _ = Ψ x := by group
  have htriv : ∀ A, glConjSL D A = A := glConjSL_eq_of_fix_sylow hodd P hfix
  have hcomm : ∀ A, Ψ A * Φ (-1) = Φ (-1) * Ψ A := by
    intro A
    have h := hD A
    rw [htriv A] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hlin : ∀ A, LinAct Φ (Ψ A) := fun A => H1 _ (hcomm A)
  have hperf : ⁅Ψ.range, Ψ.range⁆ = Ψ.range := by
    have hp : ⁅(⊤ : Subgroup (SL2 F)), ⊤⁆ = ⊤ :=
      (CFSG.ClassicalInvolution.sl2_isPerfect h4).commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hp]
  have hinn : ∀ y : SL2 F, InnAct Φ (Ψ y) := by
    have hle : Ψ.range ≤ innActSubgroup Φ := by
      rw [← hperf]
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨A, rfl⟩ := hx
      obtain ⟨B, rfl⟩ := hy
      exact innAct_commutator (hlin A) (hlin B)
    exact fun y => hle ⟨y, rfl⟩
  let N : Subgroup (SL2 F) := (Subgroup.centralizer (Φ.range : Set M)).comap Ψ
  have hmemN : ∀ y, y ∈ N ↔ ∀ A, Φ A * Ψ y = Ψ y * Φ A := by
    intro y
    show Ψ y ∈ Subgroup.centralizer (Φ.range : Set M) ↔ _
    rw [Subgroup.mem_centralizer_iff]
    exact ⟨fun h A => h _ ⟨A, rfl⟩, fun h q ⟨A, hA⟩ => hA ▸ h A⟩
  have hNnormal : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hmemN] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_centralizes_of_linAct (hlin g) (hn)
  have hN1 : (-1 : SL2 F) ∈ N ∨ ⊤ = N := by
    rcases CFSG.ClassicalInvolution.sl2_normal_cases h4 N hNnormal with hbot | hcen | htop
    · exfalso
      refine false_of_innAct_of_trivial_centralizer hneg hinn (fun y hy => ?_)
      have : y ∈ N := (hmemN y).mpr hy
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    · left
      rw [hcen]
      exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mpr (Or.inr rfl)
    · right
      exact htop.symm
  rcases hN1 with hN1 | htop
  swap
  · refine H4 fun A B => ?_
    exact (hmemN B).mp (by rw [← htop]; exact Subgroup.mem_top _) A
  have hcommQ : ∀ A, Φ A * Ψ (-1) = Ψ (-1) * Φ A := (hmemN (-1)).mp hN1
  have hlinΨ : ∀ A, LinAct Ψ (Φ A) := fun A => H2 _ (hcommQ A)
  have hJQ : ∀ y A : SL2 F, Ψ y * Φ A * (Ψ y)⁻¹ ∈ Φ.range := by
    intro y A
    obtain ⟨D', hD'⟩ := hlin y
    rw [hD' A]
    exact ⟨_, rfl⟩
  have hQJ : ∀ A y : SL2 F, Φ A * Ψ y * (Φ A)⁻¹ ∈ Ψ.range := by
    intro A y
    obtain ⟨D', hD'⟩ := hlinΨ A
    rw [hD' y]
    exact ⟨_, rfl⟩
  let NJ : Subgroup (SL2 F) := Φ.range.comap Ψ
  have hNJ : NJ.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨A, hA⟩ := (hn : Ψ n ∈ Φ.range)
    show Ψ (g * n * g⁻¹) ∈ Φ.range
    rw [map_mul, map_mul, map_inv, ← hA]
    exact hJQ g A
  rcases sl2_normal_le_center_or_eq_top h4 hNJ with hcen | htopJ
  swap
  ·
    have hle : Ψ.range ≤ Φ.range := by
      rintro _ ⟨y, rfl⟩
      have : y ∈ NJ := by rw [htopJ]; exact Subgroup.mem_top _
      exact this
    have : Finite Φ.range :=
      Finite.of_surjective Φ.rangeRestrict (MonoidHom.rangeRestrict_surjective Φ)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h1 : Nat.card (SL2 F) = Nat.card Ψ.range :=
      Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv
    have h2 : Nat.card Φ.range ≤ Nat.card (SL2 F) :=
      Nat.card_le_card_of_surjective Φ.rangeRestrict (MonoidHom.rangeRestrict_surjective Φ)
    omega
  have hIJ : ∀ y : SL2 F, Ψ y ∈ Φ.range → ∀ w : SL2 F, Ψ y * Ψ w = Ψ w * Ψ y := by
    intro y hy w
    have hy' : y ∈ NJ := hy
    have hyc := Subgroup.mem_center_iff.mp (hcen hy') w
    rw [← map_mul, ← map_mul, hyc]
  have hJQcomm : ⁅Ψ.range, Φ.range⁆ ≤ Subgroup.centralizer (Ψ.range : Set M) := by
    rw [Subgroup.commutator_le]
    intro x hx q hq
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨A, rfl⟩ := hq
    have h1 : ⁅Ψ y, Φ A⁆ ∈ Φ.range := by
      rw [commutatorElement_def]
      exact Φ.range.mul_mem (hJQ y A) (Φ.range.inv_mem ⟨A, rfl⟩)
    have h2 : ⁅Ψ y, Φ A⁆ ∈ Ψ.range := by
      have : ⁅Ψ y, Φ A⁆ = Ψ y * (Φ A * (Ψ y)⁻¹ * (Φ A)⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [this]
      exact Ψ.range.mul_mem ⟨y, rfl⟩ (by
        have := hQJ A y⁻¹
        rwa [map_inv] at this)
    obtain ⟨z, hz⟩ := h2
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, rfl⟩
    rw [← hz]
    exact (hIJ z (hz ▸ h1) w).symm
  have e1 : ⁅⁅Ψ.range, Φ.range⁆, Ψ.range⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hJQcomm
  have e2 : ⁅⁅Φ.range, Ψ.range⁆, Ψ.range⁆ = ⊥ := by
    rw [Subgroup.commutator_comm Φ.range Ψ.range]
    exact e1
  have e3 : ⁅⁅Ψ.range, Ψ.range⁆, Φ.range⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate e1 e2
  rw [hperf] at e3
  have e4 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp e3
  refine H4 fun A B => ?_
  exact Subgroup.mem_centralizer_iff.mp (e4 ⟨B, rfl⟩) (Φ A) ⟨A, rfl⟩

end Main

end CFSG.ClassicalInvolution.G2D4Models
