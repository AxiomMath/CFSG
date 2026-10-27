module

public import CFSG.RankThree.FFModules.Transvections
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDescent
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped MatrixGroups
open Matrix

namespace InnerCount

variable {F : Type} [Field F] {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]

@[expose] def hat (E : Y ≃+ (Fin 3 → F)) (a : Y ≃ₗ[ZMod 2] Y) : (Fin 3 → F) ≃+ (Fin 3 → F) :=
  E.symm.trans (a.toAddEquiv.trans E)

theorem hat_apply (E : Y ≃+ (Fin 3 → F)) (a : Y ≃ₗ[ZMod 2] Y) (v : Fin 3 → F) :
    hat E a v = E (a (E.symm v)) :=
  rfl

@[expose] def AllSemilin (E : Y ≃+ (Fin 3 → F)) (A : Subgroup (Y ≃ₗ[ZMod 2] Y)) : Prop :=
  ∀ a ∈ A, ∃ μ : F ≃+* F, ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = μ c • E (a y)

theorem semilin_unique {E : Y ≃+ (Fin 3 → F)} {a : Y ≃ₗ[ZMod 2] Y} {μ ν : F ≃+* F}
    (hμ : ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = μ c • E (a y))
    (hν : ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = ν c • E (a y)) : μ = ν := by
  obtain ⟨y, hy⟩ : ∃ y : Y, E (a y) ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin 3 → F)
    refine ⟨E.symm v, fun h => hv ?_⟩
    have h1 : a (E.symm v) = 0 := (E.map_eq_zero_iff).mp h
    exact (E.symm.map_eq_zero_iff).mp ((a.map_eq_zero_iff).mp h1)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
  have hi0 : E (a y) i ≠ 0 := hi
  ext c
  have hi' := congrFun ((hμ c y).symm.trans (hν c y)) i
  simp only [Pi.smul_apply, smul_eq_mul] at hi'
  exact mul_right_cancel₀ hi0 hi'

variable {E : Y ≃+ (Fin 3 → F)} {A : Subgroup (Y ≃ₗ[ZMod 2] Y)}

noncomputable def mu (hsemi : AllSemilin E A) (a : A) : F ≃+* F :=
  Classical.choose (hsemi a.1 a.2)

theorem mu_spec (hsemi : AllSemilin E A) (a : A) (c : F) (y : Y) :
    E (a.1 (E.symm (c • E y))) = mu hsemi a c • E (a.1 y) :=
  Classical.choose_spec (hsemi a.1 a.2) c y

theorem mu_mul (hsemi : AllSemilin E A) (a b : A) :
    mu hsemi (a * b) = mu hsemi a * mu hsemi b := by
  refine semilin_unique (mu_spec hsemi (a * b)) fun c y => ?_
  have hb : b.1 (E.symm (c • E y)) = E.symm (mu hsemi b c • E (b.1 y)) := by
    rw [← mu_spec hsemi b c y, AddEquiv.symm_apply_apply]
  show E (a.1 (b.1 (E.symm (c • E y)))) = _
  rw [hb, mu_spec hsemi a (mu hsemi b c) (b.1 y)]
  rfl

@[expose] noncomputable def muHom (hsemi : AllSemilin E A) : A →* (F ≃+* F) :=
  MonoidHom.mk' (mu hsemi) (mu_mul hsemi)

theorem muHom_apply (hsemi : AllSemilin E A) (a : A) : muHom hsemi a = mu hsemi a :=
  rfl

theorem mem_ker_muHom_iff (hsemi : AllSemilin E A) (a : A) :
    a ∈ (muHom hsemi).ker ↔ ∀ (c : F) (y : Y), E (a.1 (E.symm (c • E y))) = c • E (a.1 y) := by
  rw [MonoidHom.mem_ker, muHom_apply]
  constructor
  · intro h c y
    have h' := mu_spec hsemi a c y
    rw [h] at h'
    exact h'
  · intro h
    exact semilin_unique (mu_spec hsemi a) (ν := 1) h


theorem card_le_two_of_forall_eq {G : Type*} [Group G] [Finite G]
    (h : ∀ x y : G, x ≠ 1 → y ≠ 1 → x = y) : Nat.card G ≤ 2 := by
  classical
  haveI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card]
  by_cases hall : ∀ x : G, x = 1
  · have : Fintype.card G ≤ 1 :=
      Fintype.card_le_one_iff.mpr fun x y => (hall x).trans (hall y).symm
    omega
  · obtain ⟨x₀, hx₀⟩ := not_forall.mp hall
    have hsub : (Finset.univ : Finset G) ⊆ {1, x₀} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x x₀ hx hx₀]
    calc Fintype.card G = (Finset.univ : Finset G).card := Finset.card_univ.symm
      _ ≤ ({1, x₀} : Finset G).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

theorem mu_involutive (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1) (a : A) (c : F) :
    mu hsemi a (mu hsemi a c) = c := by
  have h1 : a * a = 1 := Subtype.ext (h2 a.1 a.2)
  have h3 : muHom hsemi a * muHom hsemi a = 1 := by rw [← map_mul, h1, map_one]
  exact congrArg (fun θ : F ≃+* F => θ c) h3

theorem exists_ne_of_ne_one (θ : F ≃+* F) (h : θ ≠ 1) : ∃ x, θ x ≠ x := by
  by_contra hcon
  exact h (RingEquiv.ext fun x => by_contra fun hx => hcon ⟨x, hx⟩)

theorem card_range_muHom_le_two [Finite F] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) : Nat.card (muHom hsemi).range ≤ 2 := by
  haveI : Finite (F ≃+* F) :=
    Finite.of_injective (fun θ : F ≃+* F => (θ : F → F)) DFunLike.coe_injective
  refine card_le_two_of_forall_eq ?_
  rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ ha hb
  have ha' : muHom hsemi a ≠ 1 := fun h => ha (Subtype.ext h)
  have hb' : muHom hsemi b ≠ 1 := fun h => hb (Subtype.ext h)
  exact Subtype.ext (ringAut_involution_unique _ _ (mu_involutive hsemi h2 a)
    (mu_involutive hsemi h2 b) (exists_ne_of_ne_one _ ha') (exists_ne_of_ne_one _ hb'))

theorem card_le_two_mul_card_ker [Finite F] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 2 * Nat.card (muHom hsemi).ker := by
  have h := Subgroup.card_ker_mul_card_range (muHom hsemi)
  have h' := card_range_muHom_le_two hsemi h2
  calc Nat.card A = Nat.card (muHom hsemi).ker * Nat.card (muHom hsemi).range := h.symm
    _ ≤ Nat.card (muHom hsemi).ker * 2 := Nat.mul_le_mul_left _ h'
    _ = 2 * Nat.card (muHom hsemi).ker := mul_comm _ _

theorem exists_matrix_aux [CharP F 2] (E : Y ≃+ (Fin 3 → F)) {a : Y ≃ₗ[ZMod 2] Y}
    (haa : a * a = 1) (hlin : ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = c • E (a y)) :
    ∃ g : SL(3, F), ∀ y : Y, E (a y) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ E y := by
  let φ : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := hat E a
      map_add' := map_add _
      map_smul' := fun c v => by
        have h := hlin c (E.symm v)
        simp only [AddEquiv.apply_symm_apply] at h
        exact h }
  have hφ : ∀ v, φ v = E (a (E.symm v)) := fun v => rfl
  have h1 : ∀ z : Y, a (a z) = z := fun z => congrArg (fun m : Y ≃ₗ[ZMod 2] Y => m z) haa
  have hφφ : φ ∘ₗ φ = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    show E (a (E.symm (E (a (E.symm v))))) = v
    rw [AddEquiv.symm_apply_apply, h1, AddEquiv.apply_symm_apply]
  have hMM : LinearMap.toMatrix' φ * LinearMap.toMatrix' φ = 1 := by
    rw [← LinearMap.toMatrix'_comp, hφφ, LinearMap.toMatrix'_id]
  have hd : (LinearMap.toMatrix' φ).det * (LinearMap.toMatrix' φ).det = 1 := by
    rw [← Matrix.det_mul, hMM, Matrix.det_one]
  have h2' : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hdet : (LinearMap.toMatrix' φ).det = 1 := by
    have : ((LinearMap.toMatrix' φ).det - 1) * ((LinearMap.toMatrix' φ).det - 1) = 0 := by
      linear_combination hd + (1 - (LinearMap.toMatrix' φ).det) * h2'
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  refine ⟨⟨LinearMap.toMatrix' φ, hdet⟩, fun y => ?_⟩
  show E (a y) = LinearMap.toMatrix' φ *ᵥ E y
  rw [LinearMap.toMatrix'_mulVec, hφ, AddEquiv.symm_apply_apply]


theorem exists_matrix_ker [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (a : (muHom hsemi).ker) :
    ∃ g : SL(3, F), ∀ y : Y, E (a.1.1 y) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ E y :=
  exists_matrix_aux E (h2 a.1.1 a.1.2) ((mem_ker_muHom_iff hsemi a.1).mp a.2)

noncomputable def toSLFun [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (a : (muHom hsemi).ker) : SL(3, F) :=
  Classical.choose (exists_matrix_ker hsemi h2 a)

theorem toSLFun_spec [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (a : (muHom hsemi).ker) (y : Y) :
    E (a.1.1 y) = (toSLFun hsemi h2 a : Matrix (Fin 3) (Fin 3) F) *ᵥ E y :=
  Classical.choose_spec (exists_matrix_ker hsemi h2 a) y

theorem toSLFun_mul [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (a b : (muHom hsemi).ker) :
    toSLFun hsemi h2 (a * b) = toSLFun hsemi h2 a * toSLFun hsemi h2 b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.ext_iff_mulVec]
  intro v
  obtain ⟨y, rfl⟩ := E.surjective v
  rw [← Matrix.mulVec_mulVec, ← toSLFun_spec hsemi h2 b y,
    ← toSLFun_spec hsemi h2 a (b.1.1 y), ← toSLFun_spec hsemi h2 (a * b) y]
  rfl

@[expose] noncomputable def toSL [CharP F 2] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) : (muHom hsemi).ker →* SL(3, F) :=
  MonoidHom.mk' (toSLFun hsemi h2) (toSLFun_mul hsemi h2)

theorem toSL_apply [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1)
    (a : (muHom hsemi).ker) : toSL hsemi h2 a = toSLFun hsemi h2 a :=
  rfl

theorem toSL_injective [CharP F 2] (hsemi : AllSemilin E A) (h2 : ∀ a ∈ A, a * a = 1) :
    Function.Injective (toSL hsemi h2) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  refine LinearEquiv.ext fun y => E.injective ?_
  rw [toSLFun_spec hsemi h2 a y, toSLFun_spec hsemi h2 b y]
  rw [toSL_apply, toSL_apply] at hab
  rw [hab]

theorem card_ker_muHom_le_sq [Fintype F] [CharP F 2] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card (muHom hsemi).ker ≤ Fintype.card F ^ 2 := by
  have hB2 : ∀ b ∈ (toSL hsemi h2).range, b * b = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (Subtype.ext (h2 a.1.1 a.1.2))
    rw [this, map_one]
  have hBc : ∀ b ∈ (toSL hsemi h2).range, ∀ c ∈ (toSL hsemi h2).range, b * c = c * b := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    have : a * b = b * a := Subtype.ext (Subtype.ext (hc a.1.1 a.1.2 b.1.1 b.1.2))
    rw [this]
  have h1 := CFSG.RankThree.FFModules.card_le_sq_of_elementary hB2 hBc
  have h3 : Nat.card (muHom hsemi).ker ≤ Nat.card (toSL hsemi h2).range :=
    Nat.card_le_card_of_injective (fun x => (⟨toSL hsemi h2 x, x, rfl⟩ : (toSL hsemi h2).range))
      fun x y hxy => toSL_injective hsemi h2 (congrArg Subtype.val hxy)
  omega


theorem apply_apply_of_mul_self {a : Y ≃ₗ[ZMod 2] Y} (haa : a * a = 1) (z : Y) : a (a z) = z :=
  congrArg (fun m : Y ≃ₗ[ZMod 2] Y => m z) haa

theorem hat_smul (hsemi : AllSemilin E A) (a : A) (c : F) (v : Fin 3 → F) :
    hat E a.1 (c • v) = mu hsemi a c • hat E a.1 v := by
  have h := mu_spec hsemi a c (E.symm v)
  simp only [AddEquiv.apply_symm_apply] at h
  exact h

theorem hat_hat {a : Y ≃ₗ[ZMod 2] Y} (haa : a * a = 1) (v : Fin 3 → F) :
    hat E a (hat E a v) = v := by
  show E (a (E.symm (E (a (E.symm v))))) = v
  rw [AddEquiv.symm_apply_apply, apply_apply_of_mul_self haa, AddEquiv.apply_symm_apply]

theorem card_fin3_fun [Fintype F] : Nat.card (Fin 3 → F) = Fintype.card F ^ 3 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]

theorem card_fix_sq_of_nonlinear [Fintype F] [CharP F 2] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (a : A) (hnl : mu hsemi a ≠ 1) :
    Nat.card {y : Y // a.1 y = y} ^ 2 = Fintype.card F ^ 3 := by
  obtain ⟨c, hc⟩ := exists_ne_of_ne_one _ hnl
  have hdesc := card_fix_sq_of_semilinear_involution (K := F) (C := Fin 3 → F)
    (mu hsemi a).toRingHom (mu_involutive hsemi h2 a) ⟨c, hc⟩ (hat E a.1) (hat_smul hsemi a)
    (hat_hat (h2 a.1 a.2))
  rw [card_fin3_fun] at hdesc
  have e : {y : Y // a.1 y = y} ≃ {v : Fin 3 → F // hat E a.1 v = v} :=
    E.toEquiv.subtypeEquiv fun y => by
      rw [hat_apply]
      show a.1 y = y ↔ E (a.1 (E.symm (E y))) = E y
      rw [AddEquiv.symm_apply_apply]
      exact E.injective.eq_iff.symm
  rw [Nat.card_congr e]
  exact hdesc

theorem card_fix_le_sq_of_linear [Fintype F] [CharP F 2] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (a : A) (ha1 : a ≠ 1) (hlin : mu hsemi a = 1) :
    Nat.card {y : Y // a.1 y = y} ≤ Fintype.card F ^ 2 := by
  have hlin' : ∀ (c : F) (y : Y), E (a.1 (E.symm (c • E y))) = c • E (a.1 y) := fun c y => by
    have h := mu_spec hsemi a c y
    rw [hlin] at h
    exact h
  obtain ⟨g, hg⟩ := exists_matrix_aux E (h2 a.1 a.2) hlin'
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply ha1
    refine Subtype.ext (LinearEquiv.ext fun y => E.injective ?_)
    rw [hg y]
    simp
  have hker : LinearMap.ker (CFSG.RankThree.FFModules.subOne g) ≠ ⊤ := fun h =>
    hg1 ((CFSG.RankThree.FFModules.subOne_eq_zero_iff g).mp (LinearMap.ker_eq_top.mp h))
  have hfr : Module.finrank F (LinearMap.ker (CFSG.RankThree.FFModules.subOne g)) ≤ 2 := by
    have := Submodule.finrank_lt hker
    rw [CFSG.RankThree.FFModules.finrank_fin3] at this
    omega
  have e : {y : Y // a.1 y = y} ≃ ↥(LinearMap.ker (CFSG.RankThree.FFModules.subOne g)) :=
    E.toEquiv.subtypeEquiv fun y => by
      rw [LinearMap.mem_ker]
      show a.1 y = y ↔ CFSG.RankThree.FFModules.subOne g (E y) = 0
      rw [CFSG.RankThree.FFModules.subOne_apply, sub_eq_zero, ← hg y]
      exact E.injective.eq_iff.symm
  rw [Nat.card_congr e, CFSG.RankThree.FFModules.card_submodule]
  exact Nat.pow_le_pow_right Fintype.card_pos hfr

theorem card_fix_le_sq_aux [Fintype F] [CharP F 2] (hsemi : AllSemilin E A)
    (h2 : ∀ a ∈ A, a * a = 1) (a : A) (ha1 : a ≠ 1) :
    Nat.card {y : Y // a.1 y = y} ≤ Fintype.card F ^ 2 := by
  by_cases hlin : mu hsemi a = 1
  · exact card_fix_le_sq_of_linear hsemi h2 a ha1 hlin
  · have h := card_fix_sq_of_nonlinear hsemi h2 a hlin
    have hq : 0 < Fintype.card F := Fintype.card_pos
    have h4 : Nat.card {y : Y // a.1 y = y} ^ 2 ≤ (Fintype.card F ^ 2) ^ 2 := by
      rw [h, ← pow_mul]
      exact Nat.pow_le_pow_right hq (by norm_num)
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h4

end InnerCount

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n)
  (hF : Fintype.card F = 2 ^ n) {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
  (E : Y ≃+ (Fin 3 → F)) (A : Subgroup (Y ≃ₗ[ZMod 2] Y))
  (h2 : ∀ a ∈ A, a * a = 1) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
  (hsemi : ∀ a ∈ A, ∃ μ : F ≃+* F, ∀ (c : F) (y : Y),
    E (a (E.symm (c • E y))) = μ c • E (a y))

include hn hF h2 hc hsemi

theorem card_le_two_mul_sq : Nat.card A ≤ 2 * Fintype.card F ^ 2 := by
  have h1 := InnerCount.card_le_two_mul_card_ker hsemi h2
  have h3 := InnerCount.card_ker_muHom_le_sq hsemi h2 hc
  omega

theorem card_fix_le_sq (hA : A ≠ ⊥) :
    Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤ Fintype.card F ^ 2 := by
  haveI : Finite Y := Finite.of_equiv (Fin 3 → F) E.symm.toEquiv
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA
  have hle : Nat.card {y : Y // ∀ a ∈ A, a y = y} ≤ Nat.card {y : Y // a.1 y = y} :=
    Nat.card_le_card_of_injective (fun y => ⟨y.1, y.2 a.1 a.2⟩) fun x y hxy => by
      apply Subtype.ext
      exact congrArg (Subtype.val : {y : Y // a.1 y = y} → Y) hxy
  exact hle.trans (InnerCount.card_fix_le_sq_aux hsemi h2 a ha1)

theorem exists_matrix_of_linear (a : Y ≃ₗ[ZMod 2] Y) (ha : a ∈ A)
    (hlin : ∀ (c : F) (y : Y), E (a (E.symm (c • E y))) = c • E (a y)) :
    ∃ g : SL(3, F), ∀ y : Y, E (a y) = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ E y :=
  InnerCount.exists_matrix_aux E (h2 a ha) hlin

end CFSG.LocalAnalysis.RankThreeUC.S15
