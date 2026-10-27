module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotFieldNormalizeCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignField
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Timmesfeld.LieEmbed
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

local instance e6PilotCTFieldTwistNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Block

@[expose] def e46 : Fin 4 ⊕ Fin 2 ≃ Fin 6 where
  toFun := Sum.elim ![0, 1, 2, 3] ![4, 5]
  invFun := ![.inl 0, .inl 1, .inl 2, .inl 3, .inr 0, .inr 1]
  left_inv := by decide
  right_inv := by decide

abbrev c4 (i : Fin 4) : Fin 6 := e46 (Sum.inl i)

theorem c4_injective : Function.Injective c4 := fun _ _ h => Sum.inl_injective (e46.injective h)

theorem c4_ne {i j : Fin 4} (hij : i ≠ j) : c4 i ≠ c4 j := fun h => hij (c4_injective h)

variable {K : Type*} [Field K]

@[expose] def blockFourMat (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 6) (Fin 6) K :=
  (fromBlocks A 0 0 (1 : Matrix (Fin 2) (Fin 2) K)).submatrix e46.symm e46.symm

theorem blockFourMat_apply (A : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 ⊕ Fin 2) :
    blockFourMat A (e46 x) (e46 y) = fromBlocks A 0 0 1 x y := by
  simp [blockFourMat]

theorem blockFourMat_one : blockFourMat (1 : Matrix (Fin 4) (Fin 4) K) = 1 := by
  rw [blockFourMat, fromBlocks_one, submatrix_one_equiv]

theorem blockFourMat_mul (A B : Matrix (Fin 4) (Fin 4) K) :
    blockFourMat (A * B) = blockFourMat A * blockFourMat B := by
  rw [blockFourMat, blockFourMat, blockFourMat, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem det_blockFourMat (A : Matrix (Fin 4) (Fin 4) K) : (blockFourMat A).det = A.det := by
  rw [blockFourMat, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]

theorem blockFourMat_map {M : Type*} [Field M] (f : K →+* M) (A : Matrix (Fin 4) (Fin 4) K) :
    blockFourMat (A.map f) = (blockFourMat A).map f := by
  ext k l
  obtain ⟨x, rfl⟩ := e46.surjective k
  obtain ⟨y, rfl⟩ := e46.surjective l
  rw [blockFourMat_apply, Matrix.map_apply, blockFourMat_apply]
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.one_apply, apply_ite f]

theorem blockFourMat_transvection (i j : Fin 4) (c : K) :
    blockFourMat (1 + single i j c) = 1 + single (c4 i) (c4 j) c := by
  ext k l
  obtain ⟨x, rfl⟩ := e46.surjective k
  obtain ⟨y, rfl⟩ := e46.surjective l
  rw [blockFourMat_apply]
  simp only [Matrix.add_apply, Matrix.one_apply, single_apply, e46.injective.eq_iff, c4]
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.one_apply, single_apply, eq_comm]

@[expose] def blockFour : SpecialLinearGroup (Fin 4) K →* SpecialLinearGroup (Fin 6) K where
  toFun A := ⟨blockFourMat (A : Matrix (Fin 4) (Fin 4) K), by rw [det_blockFourMat]; exact A.2⟩
  map_one' := Subtype.ext blockFourMat_one
  map_mul' A B := Subtype.ext
    (blockFourMat_mul (A : Matrix (Fin 4) (Fin 4) K) (B : Matrix (Fin 4) (Fin 4) K))

theorem coe_blockFour (A : SpecialLinearGroup (Fin 4) K) :
    ((blockFour A : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      blockFourMat (A : Matrix (Fin 4) (Fin 4) K) :=
  rfl

theorem blockFour_transvection {i j : Fin 4} (hij : i ≠ j) (c : K) :
    blockFour (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (c4_ne hij) c := by
  apply Subtype.ext
  rw [coe_blockFour, SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    blockFourMat_transvection]

theorem blockFour_map {M : Type*} [Field M] (f : K →+* M) (A : SpecialLinearGroup (Fin 4) K) :
    blockFour (SpecialLinearGroup.map f A) = SpecialLinearGroup.map f (blockFour A) :=
  Subtype.ext (blockFourMat_map f (A : Matrix (Fin 4) (Fin 4) K))

theorem blockFourMat_five_five (A : Matrix (Fin 4) (Fin 4) K) : blockFourMat A 5 5 = 1 := by
  have h := blockFourMat_apply A (Sum.inr 1) (Sum.inr 1)
  simpa [e46] using h

theorem blockFourMat_c4 (A : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    blockFourMat A (c4 i) (c4 j) = A i j := by
  have h := blockFourMat_apply A (Sum.inl i) (Sum.inl j)
  simpa using h

end Block

theorem a5Root_c4_check :
    a5Root (c4 0) (c4 1) = Pi.single 0 1 ∧ a5Root (c4 1) (c4 0) = -Pi.single 0 1 ∧
      a5Root (c4 1) (c4 2) = Pi.single 2 1 ∧ a5Root (c4 2) (c4 1) = -Pi.single 2 1 ∧
      a5Root (c4 2) (c4 3) = Pi.single 3 1 ∧ a5Root (c4 3) (c4 2) = -Pi.single 3 1 := by
  decide +kernel

section Scalars

theorem scalars_four_eq_bot {K : Type*} [Field K] [CharP K 2] : scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  have h4 : ((c : K) ^ 2) * ((c : K) ^ 2) = 1 := by
    rw [← pow_add, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have h1 : (c : K) * (c : K) = 1 := by
    rw [← sq]
    exact charTwo_eq_one_of_mul_self_eq_one h4
  have h0 : (c : K) = 1 := charTwo_eq_one_of_mul_self_eq_one h1
  rw [mem_bot]
  apply Subtype.ext
  rw [hA, h0, map_one, Matrix.SpecialLinearGroup.coe_one]

end Scalars

section Model


variable (K : Type) [Field K]

noncomputable abbrev a3Levi : Subgroup (adjointGroup .E6 K) :=
  CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {0, 2, 3}

variable [Finite K] [CharP K 2]

@[expose] noncomputable def a3Hom : SpecialLinearGroup (Fin 4) K →* adjointGroup .E6 K :=
  (slToAdjointE6 K).comp blockFour

variable {K}

theorem coe_a3Hom_transvection {i j : Fin 4} (hij : i ≠ j) (c : K) :
    ((a3Hom K (SpecialLinearGroup.transvection hij c) : adjointGroup .E6 K) : ModGL .E6 K) =
      pinnedX .E6 K (a5Root (c4 i) (c4 j)) c := by
  rw [a3Hom, MonoidHom.comp_apply, blockFour_transvection, coe_slToAdjointE6_transvection]

theorem coe_a3Hom_map {M : Type} [Field M] [Finite M] [CharP M 2] (ρ : K →+* M)
    (A : SpecialLinearGroup (Fin 4) K) :
    ((a3Hom M (SpecialLinearGroup.map ρ A) : adjointGroup .E6 M) : ModGL .E6 M) =
      baseChangeGL ρ ((a3Hom K A : adjointGroup .E6 K) : ModGL .E6 K) := by
  have h := congrArg (fun x : a5Levi M => ((x : adjointGroup .E6 M) : ModGL .E6 M))
    (a5LeviBaseChange_slToA5Levi ρ (blockFour A))
  simp only [coe_a5LeviBaseChange] at h
  rw [a3Hom, MonoidHom.comp_apply, blockFour_map, a3Hom, MonoidHom.comp_apply]
  exact h.symm

theorem a3Hom_transvection_mem_rootGroup {i j : Fin 4} (hij : i ≠ j) (c : K)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : a5Root (c4 i) (c4 j) = γ) :
    a3Hom K (SpecialLinearGroup.transvection hij c) ∈ (adjDatumE6 K).rootGroup γ := by
  have hr : IsRoot .E6 γ := hγ ▸ isRoot_a5Root (c4_ne hij)
  have h : a3Hom K (SpecialLinearGroup.transvection hij c) =
      CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily .E6) γ c :=
    Subtype.ext (by rw [coe_a3Hom_transvection, coe_xPar_eq_pinnedX hr, hγ])
  rw [h]
  exact CFSG.LieType.Steinberg.Adjoint.xPar_mem hr c

theorem a3Hom_transvection_mem_of_single {i j : Fin 4} (hij : i ≠ j) (c : K)
    {l : Fin (Tag.rank .E6)} (hl : l ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))))
    (hγ : a5Root (c4 i) (c4 j) = Pi.single l 1 ∨ a5Root (c4 i) (c4 j) = -Pi.single l 1) :
    a3Hom K (SpecialLinearGroup.transvection hij c) ∈ a3Levi K := by
  refine CFSG.LieType.CurtisTits.rankOne_le_levi _ hl ?_
  rcases hγ with hγ | hγ
  · exact mem_sup_left (a3Hom_transvection_mem_rootGroup hij c hγ)
  · exact mem_sup_right (a3Hom_transvection_mem_rootGroup hij c hγ)

theorem range_a3Hom : (a3Hom K).range = a3Levi K := by
  apply le_antisymm
  · set S := (a3Levi K).comap (a3Hom K) with hS
    have hcomm : ∀ {a b : SpecialLinearGroup (Fin 4) K}, a ∈ S → b ∈ S → ⁅a, b⁆ ∈ S :=
      fun ha hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have h01 : ∀ c : K, SpecialLinearGroup.transvection (show (0 : Fin 4) ≠ 1 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide) (Or.inl a5Root_c4_check.1)
    have h10 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 0 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide) (Or.inr a5Root_c4_check.2.1)
    have h12 : ∀ c : K, SpecialLinearGroup.transvection (show (1 : Fin 4) ≠ 2 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide) (Or.inl a5Root_c4_check.2.2.1)
    have h21 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 1 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide)
        (Or.inr a5Root_c4_check.2.2.2.1)
    have h23 : ∀ c : K, SpecialLinearGroup.transvection (show (2 : Fin 4) ≠ 3 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide)
        (Or.inl a5Root_c4_check.2.2.2.2.1)
    have h32 : ∀ c : K, SpecialLinearGroup.transvection (show (3 : Fin 4) ≠ 2 by decide) c ∈ S :=
      fun c => a3Hom_transvection_mem_of_single _ c (by decide)
        (Or.inr a5Root_c4_check.2.2.2.2.2)
    have key : ∀ {i j l : Fin 4} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l),
        (∀ c : K, SpecialLinearGroup.transvection hij c ∈ S) →
        (∀ c : K, SpecialLinearGroup.transvection hjl c ∈ S) →
        ∀ c : K, SpecialLinearGroup.transvection hil c ∈ S := by
      intro i j l hij hjl hil h₁ h₂ c
      have h := hcomm (h₁ c) (h₂ 1)
      rwa [SpecialLinearGroup.commutatorElement_transvection hij hjl hil, mul_one] at h
    have h02 := key (by decide) (by decide) (show (0 : Fin 4) ≠ 2 by decide) h01 h12
    have h20 := key (by decide) (by decide) (show (2 : Fin 4) ≠ 0 by decide) h21 h10
    have h13 := key (by decide) (by decide) (show (1 : Fin 4) ≠ 3 by decide) h12 h23
    have h31 := key (by decide) (by decide) (show (3 : Fin 4) ≠ 1 by decide) h32 h21
    have h03 := key (by decide) (by decide) (show (0 : Fin 4) ≠ 3 by decide) h01 h13
    have h30 := key (by decide) (by decide) (show (3 : Fin 4) ≠ 0 by decide) h31 h10
    have hall : ∀ (i j : Fin 4) (hij : i ≠ j) (c : K),
        SpecialLinearGroup.transvection hij c ∈ S := by
      intro i j hij c
      fin_cases i <;> fin_cases j
      all_goals first
        | exact absurd rfl hij
        | exact h01 c | exact h10 c | exact h12 c | exact h21 c | exact h23 c | exact h32 c
        | exact h02 c | exact h20 c | exact h13 c | exact h31 c | exact h03 c | exact h30 c
    rw [MonoidHom.range_eq_map,
      ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field, map_le_iff_le_comap,
      closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    exact hall i j hij c
  · refine iSup₂_le fun l hl => sup_le ?_ ?_ <;> intro g hg
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
        (isRoot_single .E6 l) g).1 hg
      have hc : ∀ {i j : Fin 4} (hij : i ≠ j), a5Root (c4 i) (c4 j) = Pi.single l 1 →
          CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily .E6) (Pi.single l 1) c ∈
            (a3Hom K).range := fun hij hγ =>
        ⟨_, Subtype.ext (by rw [coe_a3Hom_transvection hij c, hγ,
          coe_xPar_eq_pinnedX (isRoot_single .E6 l)])⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact hc (show (0 : Fin 4) ≠ 1 by decide) a5Root_c4_check.1
      · exact hc (show (1 : Fin 4) ≠ 2 by decide) a5Root_c4_check.2.2.1
      · exact hc (show (2 : Fin 4) ≠ 3 by decide) a5Root_c4_check.2.2.2.2.1
    · obtain ⟨c, rfl⟩ := (CFSG.LieType.Steinberg.Adjoint.mem_rootGroup_iff
        (isRoot_neg_single .E6 l) g).1 hg
      have hc : ∀ {i j : Fin 4} (hij : i ≠ j), a5Root (c4 i) (c4 j) = -Pi.single l 1 →
          CFSG.LieType.Steinberg.Adjoint.xPar (rootOperatorFamily .E6) (-Pi.single l 1) c ∈
            (a3Hom K).range := fun hij hγ =>
        ⟨_, Subtype.ext (by rw [coe_a3Hom_transvection hij c, hγ,
          coe_xPar_eq_pinnedX (isRoot_neg_single .E6 l)])⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      · exact hc (show (1 : Fin 4) ≠ 0 by decide) a5Root_c4_check.2.1
      · exact hc (show (2 : Fin 4) ≠ 1 by decide) a5Root_c4_check.2.2.2.1
      · exact hc (show (3 : Fin 4) ≠ 2 by decide) a5Root_c4_check.2.2.2.2.2

theorem a3Hom_injective : Function.Injective (a3Hom K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro A hA
  rw [MonoidHom.mem_ker, a3Hom, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_slToAdjointE6,
    Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, -, hr⟩ := hA
  have h55 := congrFun (congrFun hr 5) 5
  rw [coe_blockFour, blockFourMat_five_five, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h55
  rw [mem_bot]
  ext i j
  have h := congrFun (congrFun hr (c4 i)) (c4 j)
  rw [coe_blockFour, blockFourMat_c4, h55, Matrix.scalar_apply, Matrix.diagonal_apply] at h
  rw [← h, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [c4_ne hij, hij]

variable (K) in
@[expose] noncomputable def a3Model : SpecialLinearGroup (Fin 4) K →* a3Levi K :=
  (a3Hom K).codRestrict (a3Levi K) fun A => by
    rw [← range_a3Hom]
    exact ⟨A, rfl⟩

theorem coe_a3Model (A : SpecialLinearGroup (Fin 4) K) :
    ((a3Model K A : a3Levi K) : adjointGroup .E6 K) = a3Hom K A :=
  rfl

theorem a3Model_surjective : Function.Surjective (a3Model K) := by
  rintro ⟨y, hy⟩
  rw [← range_a3Hom] at hy
  obtain ⟨A, rfl⟩ := hy
  exact ⟨A, rfl⟩

theorem ker_a3Model : (a3Model K).ker = scalars 4 K := by
  rw [scalars_four_eq_bot, MonoidHom.ker_eq_bot_iff]
  exact fun A B h => a3Hom_injective (congrArg Subtype.val h)

variable (K) in
@[expose] noncomputable def a3Equiv : projectiveSL 4 K ≃* a3Levi K :=
  (QuotientGroup.quotientMulEquivOfEq (ker_a3Model (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ a3Model_surjective)

theorem a3Equiv_proj (A : SpecialLinearGroup (Fin 4) K) :
    a3Equiv K (proj 4 K A) = a3Model K A :=
  rfl

theorem exists_ringEquiv_of_forall_a3 {k : Type} [Field k] [Finite k] [CharP k 2] (ι : k →+* K)
    (θ : MulAut (a3Levi K))
    (hθ : ∀ (x : a3Levi k) (y : a3Levi K), ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL ι ((x : adjointGroup .E6 k) : ModGL .E6 k) → θ y = y) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧ ∀ y : a3Levi K,
      (((θ y : a3Levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
        baseChangeGL (ρ : K →+* K) ((y : adjointGroup .E6 K) : ModGL .E6 K) := by
  set Λ := a3Equiv K with hΛ
  set β : MulAut (projectiveSL 4 K) := (Λ.trans θ).trans Λ.symm with hβdef
  have hβapp : ∀ z, β z = Λ.symm (θ (Λ z)) := fun _ => rfl
  have hβ : ∀ (i j : Fin 4) (hij : i ≠ j), ∀ c ∈ Set.range ι,
      β (proj 4 K (SpecialLinearGroup.transvection hij c)) =
        proj 4 K (SpecialLinearGroup.transvection hij c) := by
    rintro i j hij _ ⟨c₀, rfl⟩
    have hmap : SpecialLinearGroup.transvection hij (ι c₀) =
        SpecialLinearGroup.map ι (SpecialLinearGroup.transvection hij c₀) :=
      (SpecialLinearGroup.map_transvection ι hij c₀).symm
    have hfix := hθ (a3Model k (SpecialLinearGroup.transvection hij c₀))
      (a3Model K (SpecialLinearGroup.transvection hij (ι c₀)))
      (by rw [coe_a3Model, coe_a3Model, hmap, coe_a3Hom_map])
    rw [hβapp, hΛ, a3Equiv_proj, hfix, ← a3Equiv_proj, MulEquiv.symm_apply_apply]
  obtain ⟨ρ, hρ, hβρ⟩ := exists_eq_fieldAut_of_forall_apply_transvection (S := Set.range ι)
    (by norm_num : 3 ≤ 4) ⟨1, map_one ι⟩ hβ
  refine ⟨ρ, fun c => hρ _ ⟨c, rfl⟩, fun y => ?_⟩
  obtain ⟨A, rfl⟩ := a3Model_surjective (K := K) y
  have h1 : θ (a3Model K A) = a3Model K (SpecialLinearGroup.map (ρ : K →+* K) A) := by
    have h2 : β (proj 4 K A) = fieldAut 4 K ρ (proj 4 K A) := by rw [hβρ]
    rw [hβapp, fieldAut_proj, hΛ, a3Equiv_proj, MulEquiv.symm_apply_eq, a3Equiv_proj] at h2
    exact h2
  rw [h1, coe_a3Model, coe_a3Model, coe_a3Hom_map]

end Model

section Twist


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

variable (K) in
theorem finite_neighbourLevi (N : E6Neighbour) : Finite (N.levi K) :=
  have : Finite (ModGL .E6 K) := finite_modGL
  inferInstance

@[expose] noncomputable def neighbourLeviEntrywiseEquiv (ρ : K ≃+* K) (N : E6Neighbour) :
    N.levi K ≃* N.levi K :=
  have := finite_neighbourLevi K N
  MulEquiv.ofBijective (leviBaseChange (ρ : K →+* K) N)
    ⟨leviBaseChange_injective _ N, Finite.surjective_of_injective (leviBaseChange_injective _ N)⟩

theorem coe_neighbourLeviEntrywiseEquiv (ρ : K ≃+* K) (N : E6Neighbour) (x : N.levi K) :
    (((neighbourLeviEntrywiseEquiv ρ N x : N.levi K) : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (ρ : K →+* K) ((x : adjointGroup .E6 K) : ModGL .E6 K) :=
  rfl

@[expose] noncomputable def FieldNeighbourIso.twist {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) :
    FieldNeighbourIso σ e N where
  Φ := (neighbourLeviEntrywiseEquiv ρ N).trans h.Φ
  fix x := by
    have hx : neighbourLeviEntrywiseEquiv ρ N (leviInclusion σ N x) = leviInclusion σ N x := by
      refine Subtype.ext (Subtype.ext ?_)
      have hcomp : (ρ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
        RingHom.ext fun c => hρ c
      rw [coe_neighbourLeviEntrywiseEquiv, coe_leviInclusion, F4Pilot.baseChangeGL_baseChangeGL,
        hcomp]
    rw [MulEquiv.trans_apply, hx]
    exact h.fix x

theorem FieldNeighbourIso.twist_apply {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    (ρ : K ≃+* K) (hρ : ∀ c : fixSubfield σ, ρ c = c) (x : N.levi K) :
    (h.twist ρ hρ).Φ x = h.Φ (neighbourLeviEntrywiseEquiv ρ N x) :=
  rfl

end Twist

section Restrict


variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

@[expose] noncomputable def FieldNeighbourIso.restrictTo {N : E6Neighbour}
    (h : FieldNeighbourIso σ e N) {H : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) :
    H →* G :=
  (neighbourCore e N).subtype.comp (h.Φ.toMonoidHom.comp (Subgroup.inclusion hH))

theorem FieldNeighbourIso.restrictTo_apply {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) (x : H) :
    h.restrictTo hH x = (h.Φ ⟨x, hH x.2⟩ : G) :=
  rfl

theorem FieldNeighbourIso.restrictTo_injective {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) : Function.Injective (h.restrictTo hH) :=
  Subtype.val_injective.comp (h.Φ.injective.comp (Subgroup.inclusion_injective _))

theorem FieldNeighbourIso.restrictTo_eq_of_coe_eq {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H H' : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) (hH' : H' ≤ N.levi K) (x : H)
    (y : H') (hxy : (x : adjointGroup .E6 K) = y) : h.restrictTo hH x = h.restrictTo hH' y := by
  rw [h.restrictTo_apply, h.restrictTo_apply]
  exact congrArg (fun z => (h.Φ z : G)) (Subtype.ext hxy)

theorem FieldNeighbourIso.commute_restrictTo {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H H' : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) (hH' : H' ≤ N.levi K) (x : H)
    (y : H') (hxy : Commute (x : adjointGroup .E6 K) y) :
    Commute (h.restrictTo hH x) (h.restrictTo hH' y) := by
  rw [h.restrictTo_apply, h.restrictTo_apply]
  have hc : Commute (⟨x, hH x.2⟩ : N.levi K) ⟨y, hH' y.2⟩ := Subtype.ext hxy.eq
  exact (hc.map h.Φ).map (neighbourCore e N).subtype

theorem FieldNeighbourIso.restrictTo_fix {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) {x : adjointGroup .E6 (fixSubfield σ)}
    (hx : x ∈ N.levi (fixSubfield σ)) (y : H)
    (hxy : ((y : adjointGroup .E6 K) : ModGL .E6 K) =
      baseChangeGL (fixSubfield σ).subtype (x : ModGL .E6 (fixSubfield σ))) :
    h.restrictTo hH y = ((e.symm x : L) : G) := by
  have h1 : (⟨y, hH y.2⟩ : N.levi K) = leviInclusion σ N ⟨x, hx⟩ :=
    Subtype.ext (Subtype.ext (by rw [coe_leviInclusion]; exact hxy))
  rw [h.restrictTo_apply, h1]
  exact h.fix ⟨x, hx⟩

theorem FieldNeighbourIso.range_restrictTo {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    {H : Subgroup (adjointGroup .E6 K)} (hH : H ≤ N.levi K) :
    (h.restrictTo hH).range =
      (H.subgroupOf (N.levi K)).map ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hH x.2⟩, x.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

end Restrict

theorem subgroupOf_iSup₂_of_le {C : Type*} [Group C] {N : Subgroup C} {ι : Type*} {p : ι → Prop}
    {H : ι → Subgroup C} (h : ∀ i, p i → H i ≤ N) :
    (⨆ i, ⨆ (_ : p i), H i).subgroupOf N = ⨆ i, ⨆ (_ : p i), (H i).subgroupOf N := by
  apply Subgroup.map_injective N.subtype_injective
  simp only [Subgroup.map_iSup, Subgroup.subgroupOf_map_subtype]
  rw [inf_of_le_left (iSup₂_le h)]
  exact iSup_congr fun i => iSup_congr fun hi => (inf_of_le_left (h i hi)).symm

theorem a3Nodes_subset_high :
    ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.high.nodes := by
  decide

theorem a3Nodes_subset_six :
    ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) ⊆ E6Neighbour.six.nodes := by
  decide

section Agree


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

omit
  [Finite K] [CharP K 2] in
theorem a3Levi_le_levi_high : a3Levi K ≤ E6Neighbour.high.levi K :=
  levi_le_neighbourLevi a3Nodes_subset_high

omit
  [Finite K] [CharP K 2] in
theorem a3Levi_le_levi_six : a3Levi K ≤ E6Neighbour.six.levi K :=
  levi_le_neighbourLevi a3Nodes_subset_six

theorem FieldNeighbourIso.range_restrictTo_levi {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) :
    (h.restrictTo (levi_le_neighbourLevi (K := K) hJ)).range = pieceCore e J := by
  rw [h.range_restrictTo, ← h.map_leviPiece hq hJ hJ2, Subgroup.map_map]
  congr 1
  rw [levi_adjDatumE6_eq]
  rfl

theorem FieldNeighbourIso.range_restrictTo_a3 {N : E6Neighbour} (h : FieldNeighbourIso σ e N)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) (hN : ({0, 2, 3} : Finset (Fin (Tag.rank .E6))) ⊆ N.nodes) :
    (h.restrictTo (levi_le_neighbourLevi (K := K) hN)).range =
      ⨆ j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))), pieceCore e {j} := by
  have hJN : ∀ j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))), ({j} : Finset _) ⊆ N.nodes :=
    fun j hj => Finset.singleton_subset_iff.2 (hN hj)
  have hA : a3Levi K = ⨆ j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))),
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} := by
    simp only [a3Levi, CFSG.LieType.CurtisTits.levi_singleton]
    rfl
  have hle : ∀ j ∈ ({0, 2, 3} : Finset (Fin (Tag.rank .E6))),
      CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup {j} ≤ N.levi K :=
    fun j hj => levi_le_neighbourLevi (hJN j hj)
  rw [h.range_restrictTo]
  change ((a3Levi K).subgroupOf (N.levi K)).map _ = _
  rw [hA, subgroupOf_iSup₂_of_le hle, Subgroup.map_iSup]
  refine iSup_congr fun j => ?_
  rw [Subgroup.map_iSup]
  refine iSup_congr fun hj => ?_
  exact (h.range_restrictTo (hle j hj)).symm.trans
    (h.range_restrictTo_levi hq (hJN j hj) (by simp))

theorem exists_twist_eq_on_a3 (hX : FieldNeighbourIso σ e .high) (hY : FieldNeighbourIso σ e .six)
    (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    ∃ ρ : K ≃+* K, ∃ hρ : ∀ c : fixSubfield σ, ρ c = c, ∀ x,
      hX.restrictTo (a3Levi_le_levi_high (K := K)) x =
        (hY.twist ρ hρ).restrictTo (a3Levi_le_levi_six (K := K)) x := by
  set f₁ := hX.restrictTo (a3Levi_le_levi_high (K := K)) with hf₁
  set f₂ := hY.restrictTo (a3Levi_le_levi_six (K := K)) with hf₂
  have h₁ : Function.Injective f₁ := hX.restrictTo_injective _
  have h₂ : Function.Injective f₂ := hY.restrictTo_injective _
  have hr : f₁.range = f₂.range := by
    rw [hf₁, hf₂]
    exact (hX.range_restrictTo_a3 hq a3Nodes_subset_high).trans
      (hY.range_restrictTo_a3 hq a3Nodes_subset_six).symm
  have hfix : ∀ (x : a3Levi (fixSubfield σ)) (y : a3Levi K),
      ((y : adjointGroup .E6 K) : ModGL .E6 K) = baseChangeGL (fixSubfield σ).subtype
        ((x : adjointGroup .E6 (fixSubfield σ)) : ModGL .E6 (fixSubfield σ)) → f₁ y = f₂ y := by
    intro x y hxy
    rw [hf₁, hf₂, hX.restrictTo_fix _ (a3Levi_le_levi_high x.2) y hxy,
      hY.restrictTo_fix _ (a3Levi_le_levi_six x.2) y hxy]
  set θ : MulAut (a3Levi K) := ((MonoidHom.ofInjective h₁).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective h₂).symm with hθdef
  have hθ : ∀ y, f₂ (θ y) = f₁ y := by
    intro y
    have h := (MonoidHom.ofInjective h₂).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective h₁ y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨ρ, hρ, hθρ⟩ := exists_ringEquiv_of_forall_a3 (fixSubfield σ).subtype θ
    fun x y hxy => h₂ ((hθ y).trans (hfix x y hxy))
  have hρ' : ∀ c : fixSubfield σ, ρ c = c := hρ
  refine ⟨ρ, hρ', fun x => ?_⟩
  rw [← hθ x, hf₂, hY.restrictTo_apply, (hY.twist ρ hρ').restrictTo_apply,
    FieldNeighbourIso.twist_apply]
  exact congrArg (fun z => (hY.Φ z : G)) (Subtype.ext (Subtype.ext (hθρ x)))

end Agree

end CFSG.SeitzReduction.E6Pilot
