module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesReindex
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFaithful
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

theorem two_eq_zero_k (k : Type*) [Field k] [CharP k 2] : (2 : k) = 0 := by
  exact_mod_cast CharP.cast_eq_zero k 2

section TwoLevel

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem exists_optCons₂ (x : Option (Option ι) → Fin 2) :
    ∃ (a b : Fin 2) (y : ι → Fin 2), x = optCons a (optCons b y) :=
  ⟨x none, x (some none), fun z => x (some (some z)), by
    funext o; rcases o with _ | _ | z <;> rfl⟩

theorem tensorRep_option_option_apply (e : Option (Option ι) → ℕ) (g : SL(2, F))
    (f : (Option (Option ι) → Fin 2) → k) (a' b' : Fin 2) (y' : ι → Fin 2) :
    tensorRep F k e g f (optCons a' (optCons b' y')) =
      ∑ a : Fin 2, ∑ b : Fin 2, twistMat k (e none) g a' a * twistMat k (e (some none)) g b' b *
        tensorRep F k (fun z => e (some (some z))) g (fun y => f (optCons a (optCons b y))) y' := by
  rw [tensorRep_option_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tensorRep_option_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end TwoLevel

section ThreeStep

variable {F : Type*} [Field F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem twistMat_succ_apply (m : ℕ) (g : SL(2, F)) (i j : Fin 2) :
    twistMat k (m + 1) g i j = (twistMat k m g i j) ^ 2 := by
  rw [twistMat_apply, twistMat_apply, pow_succ, pow_mul]

omit [Fintype ι] [DecidableEq ι] in
@[expose] def liftZ : ((ι → Fin 2) → k) →ₗ[k] ((Option (Option ι) → Fin 2) → k) where
  toFun v := fun x => if x none ≠ x (some none) then v (fun z => x (some (some z))) else 0
  map_add' v w := by funext x; by_cases h : x none = x (some none) <;> simp [h]
  map_smul' c v := by funext x; by_cases h : x none = x (some none) <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
@[expose] def liftS : ((Option ι → Fin 2) → k) →ₗ[k] ((Option (Option ι) → Fin 2) → k) where
  toFun w := fun x => if x none = x (some none) then
    w (optCons (x none) (fun z => x (some (some z)))) else 0
  map_add' v w := by funext x; by_cases h : x none = x (some none) <;> simp [h]
  map_smul' c v := by funext x; by_cases h : x none = x (some none) <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
@[expose] def projQ : ((Option (Option ι) → Fin 2) → k) →ₗ[k] ((ι → Fin 2) → k) where
  toFun f := fun y => f (optCons 0 (optCons 1 y)) + f (optCons 1 (optCons 0 y))
  map_add' v w := by funext y; simp; ring
  map_smul' c v := by funext y; simp [mul_add]

omit [Fintype ι] [DecidableEq ι] in
@[expose] def sectT : ((ι → Fin 2) → k) →ₗ[k] ((Option (Option ι) → Fin 2) → k) where
  toFun v := fun x => if x none = 0 ∧ x (some none) = 1 then v (fun z => x (some (some z))) else 0
  map_add' v w := by funext x; by_cases h : x none = 0 ∧ x (some none) = 1 <;> simp [h]
  map_smul' c v := by funext x; by_cases h : x none = 0 ∧ x (some none) = 1 <;> simp [h]

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem liftZ_apply (v : (ι → Fin 2) → k) (a b : Fin 2) (y : ι → Fin 2) :
    liftZ v (optCons a (optCons b y)) = if a ≠ b then v y else 0 := rfl

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem liftS_apply (w : (Option ι → Fin 2) → k) (a b : Fin 2) (y : ι → Fin 2) :
    liftS w (optCons a (optCons b y)) = if a = b then w (optCons a y) else 0 := rfl

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem projQ_apply (f : (Option (Option ι) → Fin 2) → k) (y : ι → Fin 2) :
    projQ f y = f (optCons 0 (optCons 1 y)) + f (optCons 1 (optCons 0 y)) := rfl

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem sectT_apply (v : (ι → Fin 2) → k) (a b : Fin 2) (y : ι → Fin 2) :
    sectT v (optCons a (optCons b y)) = if a = 0 ∧ b = 1 then v y else 0 := rfl

theorem tensorRep_liftZ (e : Option (Option ι) → ℕ)
    (hc : ∀ g : SL(2, F), twistMat k (e none) g = twistMat k (e (some none)) g) (g : SL(2, F))
    (v : (ι → Fin 2) → k) :
    tensorRep F k e g (liftZ v) =
      liftZ (tensorRep F k (fun z => e (some (some z))) g v) := by
  funext x
  obtain ⟨a', b', y', rfl⟩ := exists_optCons₂ x
  rw [tensorRep_option_option_apply, liftZ_apply]
  have hdet := twistMat_det (k := k) (e none) g
  have h2 := two_eq_zero_k k
  simp only [liftZ_apply, ← hc g, Fin.sum_univ_two]
  set G := twistMat k (e none) g with hG
  set R := tensorRep F k (fun z => e (some (some z))) g v y' with hR
  have hslice : ∀ (P : Prop) [Decidable P],
      tensorRep F k (fun z => e (some (some z))) g (fun y => if P then v y else 0) y' =
        if P then R else 0 := by
    intro P _
    by_cases hP : P
    · simp only [hP, ↓reduceIte]; rfl
    · simp only [hP, ↓reduceIte]
      show tensorRep F k (fun z => e (some (some z))) g (0 : (ι → Fin 2) → k) y' = 0
      rw [map_zero]; rfl
  simp only [hslice]
  rcases fin2_cases a' with rfl | rfl <;> rcases fin2_cases b' with rfl | rfl <;>
    simp
  · linear_combination (G 0 0 * G 0 1 * R) * h2
  · linear_combination R * hdet
  · linear_combination R * hdet
  · linear_combination (G 1 0 * G 1 1 * R) * h2

theorem tensorRep_projQ (e : Option (Option ι) → ℕ)
    (hc : ∀ g : SL(2, F), twistMat k (e none) g = twistMat k (e (some none)) g) (g : SL(2, F))
    (f : (Option (Option ι) → Fin 2) → k) :
    projQ (tensorRep F k e g f) =
      tensorRep F k (fun z => e (some (some z))) g (projQ f) := by
  funext y'
  rw [projQ_apply, tensorRep_option_option_apply, tensorRep_option_option_apply]
  have hdet := twistMat_det (k := k) (e none) g
  have h2 := two_eq_zero_k k
  simp only [← hc g, Fin.sum_univ_two]
  have hsplit : tensorRep F k (fun z => e (some (some z))) g (projQ f) y' =
      tensorRep F k (fun z => e (some (some z))) g
        (fun y => f (optCons 0 (optCons 1 y))) y' +
      tensorRep F k (fun z => e (some (some z))) g
        (fun y => f (optCons 1 (optCons 0 y))) y' := by
    have : projQ f = (fun y => f (optCons 0 (optCons 1 y))) + (fun y => f (optCons 1 (optCons 0 y))) :=
      rfl
    rw [this, map_add]; rfl
  rw [hsplit]
  set G := twistMat k (e none) g with hG
  set R00 := tensorRep F k (fun z => e (some (some z))) g (fun y => f (optCons 0 (optCons 0 y))) y'
  set R01 := tensorRep F k (fun z => e (some (some z))) g (fun y => f (optCons 0 (optCons 1 y))) y'
  set R10 := tensorRep F k (fun z => e (some (some z))) g (fun y => f (optCons 1 (optCons 0 y))) y'
  set R11 := tensorRep F k (fun z => e (some (some z))) g (fun y => f (optCons 1 (optCons 1 y))) y'
  linear_combination (R01 + R10) * hdet + (G 0 0 * G 1 0 * R00 + G 0 1 * G 1 1 * R11) * h2

omit [CharP k 2] [Fintype ι] [DecidableEq ι] in
theorem projQ_sectT (v : (ι → Fin 2) → k) : projQ (sectT v) = v := by
  funext y
  rw [projQ_apply, sectT_apply, sectT_apply]
  simp

@[expose] def succHead (e : Option (Option ι) → ℕ) : Option ι → ℕ :=
  fun o => Option.elim o (e none + 1) (fun z => e (some (some z)))

theorem tensorRep_ite {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' → ℕ) (g : SL(2, F))
    (P : Prop) [Decidable P] (v : (ι' → Fin 2) → k) (y : ι' → Fin 2) :
    tensorRep F k e g (fun x => if P then v x else 0) y = if P then tensorRep F k e g v y else 0 := by
  by_cases hP : P
  · simp only [hP, ↓reduceIte]
  · simp only [hP, ↓reduceIte]
    show tensorRep F k e g (0 : (ι' → Fin 2) → k) y = 0
    rw [map_zero]; rfl

theorem tensorRep_liftS (e : Option (Option ι) → ℕ)
    (hc : ∀ g : SL(2, F), twistMat k (e none) g = twistMat k (e (some none)) g) (g : SL(2, F))
    (w : (Option ι → Fin 2) → k) :
    tensorRep F k e g (liftS w) - liftS (tensorRep F k (succHead e) g w) =
      liftZ (fun y => ∑ a : Fin 2, twistMat k (e none) g 0 a * twistMat k (e none) g 1 a *
        tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons a z)) y) := by
  funext x
  obtain ⟨a', b', y', rfl⟩ := exists_optCons₂ x
  rw [Pi.sub_apply, tensorRep_option_option_apply, liftS_apply, liftZ_apply]
  simp only [liftS_apply, ← hc g, Fin.sum_univ_two]
  have hs : tensorRep F k (succHead e) g w (optCons a' y') =
      ∑ a : Fin 2, (twistMat k (e none) g a' a) ^ 2 *
        tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons a z)) y' := by
    rw [tensorRep_option_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [succHead]
    simp only [Option.elim_none, twistMat_succ_apply]
    rfl
  rw [hs]
  simp only [tensorRep_ite, Fin.sum_univ_two]
  set G := twistMat k (e none) g with hG
  set u0 := tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons 0 z)) y'
  set u1 := tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons 1 z)) y'
  rcases fin2_cases a' with rfl | rfl <;> rcases fin2_cases b' with rfl | rfl <;> simp <;> ring

omit [Fintype ι] [DecidableEq ι] in
theorem ker_projQ_le (f : (Option (Option ι) → Fin 2) → k) (hf : projQ f = 0) :
    f ∈ LinearMap.range (liftZ (k := k) (ι := ι)) ⊔ LinearMap.range (liftS (k := k) (ι := ι)) := by
  refine Submodule.mem_sup.mpr ⟨liftZ (fun y => f (optCons 0 (optCons 1 y))), ⟨_, rfl⟩,
    liftS (fun z => f (optCons (z none) (optCons (z none) (fun i => z (some i))))), ⟨_, rfl⟩, ?_⟩
  funext x
  obtain ⟨a, b, y, rfl⟩ := exists_optCons₂ x
  have hy := congrFun hf y
  rw [projQ_apply] at hy
  have hneg : f (optCons 1 (optCons 0 y)) = f (optCons 0 (optCons 1 y)) := by
    have := neg_eq_of_add_eq_zero_right (hy : f (optCons 0 (optCons 1 y)) +
      f (optCons 1 (optCons 0 y)) = 0)
    rw [neg_eq_self_of_charTwo k] at this
    exact this.symm
  simp only [Pi.add_apply, liftZ_apply, liftS_apply, optCons_none]
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;> simp [hneg]

omit [CharP k 2] in
theorem surjective_of_intertwiner {G M E : Type*} [Monoid G] [AddCommGroup M] [Module k M]
    [AddCommGroup E] [Module k E] (R : Representation k G M) (σ : Representation k G E)
    (hσ : σ.IsIrreducible) (f : M →ₗ[k] E) (hf : ∀ g v, f (R g v) = σ g (f v)) (h0 : f ≠ 0) :
    Function.Surjective f := by
  obtain ⟨-, hirr⟩ := (isIrreducible_iff σ).mp hσ
  have hinv : ∀ g, ∀ u ∈ LinearMap.range f, σ g u ∈ LinearMap.range f := by
    rintro g u ⟨v, rfl⟩
    exact ⟨R g v, hf g v⟩
  rcases hirr _ hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) h0
  · exact LinearMap.range_eq_top.mp h

theorem three_step {E : Type*} [AddCommGroup E] [Module k E] (σ : Representation k SL(2, F) E)
    (hσ : σ.IsIrreducible) (e : Option (Option ι) → ℕ)
    (hc : ∀ g : SL(2, F), twistMat k (e none) g = twistMat k (e (some none)) g)
    (π : ((Option (Option ι) → Fin 2) → k) →ₗ[k] E) (hπs : Function.Surjective π)
    (hπ : ∀ g v, π (tensorRep F k e g v) = σ g (π v)) :
    (∃ f : ((ι → Fin 2) → k) →ₗ[k] E, Function.Surjective f ∧
        ∀ g v, f (tensorRep F k (fun z => e (some (some z))) g v) = σ g (f v)) ∨
    (∃ f : ((Option ι → Fin 2) → k) →ₗ[k] E, Function.Surjective f ∧
        ∀ g v, f (tensorRep F k (succHead e) g v) = σ g (f v)) := by
  by_cases hZ : π.comp (liftZ (k := k) (ι := ι)) = 0
  · by_cases hS : π.comp (liftS (k := k) (ι := ι)) = 0
    ·
      left
      have hker : ∀ x, projQ x = 0 → π x = 0 := by
        intro x hx
        obtain ⟨u, ⟨u', rfl⟩, w, ⟨w', rfl⟩, hxw⟩ := Submodule.mem_sup.mp (ker_projQ_le x hx)
        rw [← hxw, map_add]
        have h1 : π (liftZ u') = 0 := congrFun (congrArg DFunLike.coe hZ) u'
        have h2 : π (liftS w') = 0 := congrFun (congrArg DFunLike.coe hS) w'
        rw [h1, h2, add_zero]
      have hfac : ∀ x, π x = π (sectT (projQ x)) := by
        intro x
        have : projQ (x - sectT (projQ x)) = 0 := by
          rw [map_sub, projQ_sectT, sub_self]
        have := hker _ this
        rw [map_sub, sub_eq_zero] at this
        exact this
      have hequi : ∀ g v, π (sectT (tensorRep F k (fun z => e (some (some z))) g v)) =
          σ g (π (sectT v)) := by
        intro g v
        rw [← hπ]
        have : projQ (sectT (tensorRep F k (fun z => e (some (some z))) g v) -
            tensorRep F k e g (sectT v)) = 0 := by
          rw [map_sub, projQ_sectT, tensorRep_projQ e hc, projQ_sectT, sub_self]
        have := hker _ this
        rw [map_sub, sub_eq_zero] at this
        exact this
      refine ⟨π.comp sectT, ?_, hequi⟩
      intro y
      obtain ⟨x, rfl⟩ := hπs y
      exact ⟨projQ x, (hfac x).symm⟩
    · right
      have hequi : ∀ g w, (π.comp liftS) (tensorRep F k (succHead e) g w) =
          σ g ((π.comp liftS) w) := by
        intro g w
        simp only [LinearMap.comp_apply]
        have h3 := tensorRep_liftS e hc g w
        have h4 : liftS (tensorRep F k (succHead e) g w) =
            tensorRep F k e g (liftS w) - liftZ (fun y => ∑ a : Fin 2,
              twistMat k (e none) g 0 a * twistMat k (e none) g 1 a *
              tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons a z)) y) := by
          rw [← h3]; abel
        rw [h4, map_sub, hπ]
        have h5 : π (liftZ (fun y => ∑ a : Fin 2, twistMat k (e none) g 0 a *
            twistMat k (e none) g 1 a *
            tensorRep F k (fun z => e (some (some z))) g (fun z => w (optCons a z)) y)) = 0 :=
          congrFun (congrArg DFunLike.coe hZ) _
        rw [h5, sub_zero]
      exact ⟨π.comp liftS, surjective_of_intertwiner _ σ hσ _ hequi hS, hequi⟩
  · left
    have hequi : ∀ g v, (π.comp liftZ) (tensorRep F k (fun z => e (some (some z))) g v) =
        σ g ((π.comp liftZ) v) := by
      intro g v
      simp only [LinearMap.comp_apply]
      rw [← tensorRep_liftZ e hc, hπ]
    exact ⟨π.comp liftZ, surjective_of_intertwiner _ σ hσ _ hequi hZ, hequi⟩

end ThreeStep


section Induction

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

theorem exists_equiv_option_option {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (hij : i ≠ j) :
    ∃ (ι' : Type) (_ : Fintype ι') (_ : DecidableEq ι') (σ : Option (Option ι') ≃ ι),
      σ none = i ∧ σ (some none) = j ∧ Fintype.card ι' + 2 = Fintype.card ι := by
  let σ₁ : Option {b : ι // b ≠ i} ≃ ι := Equiv.optionSubtypeNe i
  let j' : {b : ι // b ≠ i} := ⟨j, hij.symm⟩
  let σ₂ : Option {b : {b : ι // b ≠ i} // b ≠ j'} ≃ {b : ι // b ≠ i} := Equiv.optionSubtypeNe j'
  refine ⟨{b : {b : ι // b ≠ i} // b ≠ j'}, inferInstance, inferInstance,
    (Equiv.optionCongr σ₂).trans σ₁, rfl, rfl, ?_⟩
  have h1 := Fintype.card_congr σ₁
  have h2 := Fintype.card_congr σ₂
  rw [Fintype.card_option] at h1 h2
  omega

theorem exists_frobTensor_equiv {n : ℕ} (hF : Fintype.card F = 2 ^ n) {E : Type*} [AddCommGroup E]
    [Module k E] (σ : Representation k SL(2, F) E) (hσ : σ.IsIrreducible) :
    ∀ (r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r → ∀ e : ι → ℕ,
      ∀ π : ((ι → Fin 2) → k) →ₗ[k] E, Function.Surjective π →
        (∀ g v, π (tensorRep F k e g v) = σ g (π v)) →
        ∃ J : Finset ℕ, (∀ i ∈ J, i < n) ∧ Nonempty (σ.Equiv (frobTensor F k J)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have := Fintype.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact h
  obtain ⟨hnt, hirr⟩ := (isIrreducible_iff σ).mp hσ
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro ι _ _ hcard e π hπs hπ
    by_cases hinj : Function.Injective (fun i => e i % n)
    ·
      let e' : ι → ℕ := fun i => e i % n
      have htw : ∀ g, tensorRep F k e' g = tensorRep F k e g := by
        intro g
        simp only [tensorRep, MonoidHom.coe_mk, OneHom.coe_mk]
        congr 1
        ext x' x
        simp only [tmatE, e']
        exact Finset.prod_congr rfl fun i _ => by rw [twistMat_mod hF]
      let J : Finset ℕ := Finset.univ.image e'
      have hJn : ∀ i ∈ J, i < n := by
        intro i hi
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
        exact Nat.mod_lt _ hn
      let τ : ι ≃ J := Equiv.ofBijective
        (fun i => ⟨e' i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
        ⟨fun i j h => hinj (congrArg Subtype.val h), fun ⟨j, hj⟩ => by
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
          exact ⟨i, rfl⟩⟩
      let Φ : (tensorRep F k e').Equiv (frobTensor F k J) :=
        reindexEquiv τ e' (fun j : J => (j : ℕ)) (fun i => rfl)
      let π' : ((J → Fin 2) → k) →ₗ[k] E := π.comp (Φ.toLinearEquiv.symm : _ →ₗ[k] _)
      have hπ' : ∀ g v, π' (frobTensor F k J g v) = σ g (π' v) := by
        intro g v
        show π (Φ.symm (frobTensor F k J g v)) = σ g (π (Φ.symm v))
        rw [equiv_apply Φ.symm g v]
        show π (tensorRep F k e' g (Φ.symm v)) = _
        rw [htw, hπ]
      have hπ's : Function.Surjective π' := hπs.comp Φ.toLinearEquiv.symm.surjective
      have hinj' : Function.Injective π' := by
        rw [← LinearMap.ker_eq_bot]
        have hinv : ∀ g, ∀ u ∈ LinearMap.ker π', frobTensor F k J g u ∈ LinearMap.ker π' := by
          intro g u hu
          rw [LinearMap.mem_ker] at hu ⊢
          rw [hπ', hu, map_zero]
        obtain ⟨-, hirrJ⟩ := (isIrreducible_iff (frobTensor F k J)).mp (frobTensor_isIrreducible hF hJn)
        rcases hirrJ _ hinv with h | h
        · exact h
        · exfalso
          obtain ⟨x, y, hxy⟩ := hnt
          obtain ⟨u, rfl⟩ := hπ's x
          obtain ⟨v, rfl⟩ := hπ's y
          have hu : u ∈ LinearMap.ker π' := h ▸ Submodule.mem_top
          have hv : v ∈ LinearMap.ker π' := h ▸ Submodule.mem_top
          rw [LinearMap.mem_ker] at hu hv
          exact hxy (by rw [hu, hv])
      refine ⟨J, hJn, ⟨(Representation.Equiv.mk (LinearEquiv.ofBijective π' ⟨hinj', hπ's⟩)
        (fun g => LinearMap.ext fun v => ?_)).symm⟩⟩
      exact (hπ' g v).symm.symm ▸ rfl
    ·
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, hne, hij⟩ := hinj
      obtain ⟨ι', _, _, σι, hσ1, hσ2, hc⟩ := exists_equiv_option_option hij
      let e'' : Option (Option ι') → ℕ := fun o => e (σι o)
      let Ψ : (tensorRep F k e'').Equiv (tensorRep F k e) :=
        reindexEquiv σι e'' e (fun o => rfl)
      let π'' : ((Option (Option ι') → Fin 2) → k) →ₗ[k] E :=
        π.comp (Ψ.toLinearEquiv : _ →ₗ[k] _)
      have hπ'' : ∀ g v, π'' (tensorRep F k e'' g v) = σ g (π'' v) := by
        intro g v
        show π (Ψ (tensorRep F k e'' g v)) = σ g (π (Ψ v))
        rw [equiv_apply Ψ g v, hπ]
      have hsurj'' : Function.Surjective π'' := hπs.comp Ψ.toLinearEquiv.surjective
      have hcc : ∀ g : SL(2, F), twistMat k (e'' none) g = twistMat k (e'' (some none)) g := by
        intro g
        show twistMat k (e (σι none)) g = twistMat k (e (σι (some none))) g
        rw [hσ1, hσ2, ← twistMat_mod hF (e i) g, ← twistMat_mod hF (e j) g]
        rw [hne]
      rcases three_step σ hσ e'' hcc π'' hsurj'' hπ'' with ⟨f, hfs, hf⟩ | ⟨f, hfs, hf⟩
      · exact ih (Fintype.card ι') (by omega) ι' rfl (fun z => e'' (some (some z))) f hfs hf
      · exact ih (Fintype.card (Option ι')) (by rw [Fintype.card_option]; omega) (Option ι') rfl
          (succHead e'') f hfs hf

@[expose] def natHom (F : Type*) [Field F] (k : Type*) [Field k] [Algebra F k] [CharP k 2] :
    SL(2, F) →* Matrix (Fin 2) (Fin 2) k where
  toFun := twistMat k 0
  map_one' := twistMat_one 0
  map_mul' := twistMat_mul 0

omit [Fintype F] in
theorem natHom_injective : Function.Injective (natHom F k) := by
  intro g h hgh
  ext i j
  have := congrFun (congrFun hgh i) j
  simp only [natHom, MonoidHom.coe_mk, OneHom.coe_mk, twistMat_apply, pow_zero, pow_one] at this
  exact (algebraMap F k).injective this

theorem frobTensor_classification {n : ℕ} (hF : Fintype.card F = 2 ^ n) {E : Type*}
    [AddCommGroup E] [Module k E] (σ : Representation k SL(2, F) E) (hσ : σ.IsIrreducible) :
    ∃! J : Finset ℕ, (∀ i ∈ J, i < n) ∧ Nonempty (σ.Equiv (frobTensor F k J)) := by
  classical
  obtain ⟨m, -, f, hf, hfeq⟩ :=
    faithful_tensor_power (by norm_num : 0 < 2) (natHom F k) natHom_injective σ hσ
  have hex : ∃ J : Finset ℕ, (∀ i ∈ J, i < n) ∧ Nonempty (σ.Equiv (frobTensor F k J)) := by
    refine exists_frobTensor_equiv hF σ hσ m (Fin m) (Fintype.card_fin m) (fun _ => 0) f hf ?_
    intro g v
    rw [← hfeq g v]
    congr 1
  obtain ⟨J, hJ, hJσ⟩ := hex
  refine ⟨J, ⟨hJ, hJσ⟩, ?_⟩
  rintro K ⟨hK, ⟨φ⟩⟩
  obtain ⟨ψ⟩ := hJσ
  exact (frobTensor_nonisomorphic hF hJ hK (ψ.symm.trans φ)).symm

end Induction

end CFSG.QuasithinUnique.Setup.SL2Modules
