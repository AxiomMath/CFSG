module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesReindex
public import Mathlib.Data.Int.Star
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

namespace CFSG.QuasithinUnique.Setup.SL2Modules

open scoped MatrixGroups

section Schur

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [Algebra F k] [CharP k 2]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commutant_scalar {n : ℕ} (hF : Fintype.card F = 2 ^ n) (e : ι → ℕ)
    (he : Function.Injective e) (hlt : ∀ i, e i < n) (c : Module.End k ((ι → Fin 2) → k))
    (hc : ∀ g : SL(2, F), c ∘ₗ tensorRep F k e g = tensorRep F k e g ∘ₗ c) :
    ∃ r : k, c = r • (1 : Module.End k ((ι → Fin 2) → k)) := by
  have hfix : ∀ t : F, tensorRep F k e (uElt t) (c baseVec) = c baseVec := by
    intro t
    have := congrArg (fun T : Module.End k ((ι → Fin 2) → k) => T baseVec) (hc (uElt t))
    simp only [LinearMap.comp_apply, tensorRep_uElt_baseVec] at this
    exact this.symm
  obtain ⟨μ, hμ⟩ := (tensorRep_fixed_iff hF e he hlt (c baseVec)).mp hfix
  refine ⟨μ, ?_⟩
  have hirr := tensorRep_isIrreducible (F := F) (k := k) hF e he hlt
  rw [isIrreducible_iff] at hirr
  obtain ⟨-, hirr⟩ := hirr
  set K := LinearMap.ker (c - μ • (1 : Module.End k ((ι → Fin 2) → k))) with hK
  have hKinv : ∀ g, ∀ u ∈ K, tensorRep F k e g u ∈ K := by
    intro g u hu
    simp only [hK, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero] at hu ⊢
    have := congrArg (fun T : Module.End k ((ι → Fin 2) → k) => T u) (hc g)
    simp only [LinearMap.comp_apply] at this
    rw [this, hu, map_smul]
  have hbase : (baseVec : (ι → Fin 2) → k) ∈ K := by
    simp [hK, hμ]
  rcases hirr K hKinv with h | h
  · exfalso
    have : (baseVec : (ι → Fin 2) → k) = 0 := by
      have := h ▸ hbase
      simpa using this
    have h3 := congrFun this (fun _ => 0)
    simp [baseVec_apply] at h3
  · refine LinearMap.ext fun v => ?_
    have : v ∈ K := h ▸ Submodule.mem_top
    simpa [hK, sub_eq_zero] using this

end Schur

section Involution

variable {X : Type*} (τ : X → X) (hτ : ∀ x, τ (τ x) = x)

@[expose] def invSetoid : Setoid X where
  r x y := y = x ∨ y = τ x
  iseqv := {
    refl := fun x => Or.inl rfl
    symm := by
      rintro x y (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (hτ x).symm
    trans := by
      rintro x y z (rfl | rfl) (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (hτ x) }

abbrev InvQuot := Quotient (invSetoid τ hτ)

theorem invQuot_mk_eq {x y : X} :
    (Quotient.mk (invSetoid τ hτ) x = Quotient.mk (invSetoid τ hτ) y) ↔ (y = x ∨ y = τ x) :=
  Quotient.eq (r := invSetoid τ hτ)

theorem finite_invQuot [Finite X] : Finite (InvQuot τ hτ) :=
  Finite.of_surjective (Quotient.mk (invSetoid τ hτ)) Quotient.mk_surjective

theorem two_mul_card_invQuot [Finite X] :
    2 * Nat.card (InvQuot τ hτ) = Nat.card X + Nat.card {x // τ x = x} := by
  classical
  have := Fintype.ofFinite X
  have : Fintype (InvQuot τ hτ) := Fintype.ofFinite _
  let π : X → InvQuot τ hτ := Quotient.mk _
  have hfib : ∀ q : InvQuot τ hτ, (Finset.univ.filter (fun x => π x = q)).card +
      (Finset.univ.filter (fun x => π x = q ∧ τ x = x)).card = 2 := by
    intro q
    obtain ⟨x₀, rfl⟩ := Quotient.exists_rep q
    have h1 : Finset.univ.filter (fun x => π x = Quotient.mk _ x₀) = {x₀, τ x₀} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, π]
      rw [eq_comm, invQuot_mk_eq]
    by_cases hfix : τ x₀ = x₀
    · have h2 : Finset.univ.filter (fun x => π x = Quotient.mk _ x₀ ∧ τ x = x) = {x₀} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, π]
        rw [eq_comm, invQuot_mk_eq]
        constructor
        · rintro ⟨h | h, _⟩
          · exact h
          · rw [h, hfix]
        · rintro rfl; exact ⟨Or.inl rfl, hfix⟩
      rw [h1, h2, hfix]; simp
    · have h2 : Finset.univ.filter (fun x => π x = Quotient.mk _ x₀ ∧ τ x = x) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, π]
        rw [eq_comm, invQuot_mk_eq]
        rintro ⟨h | h, hx⟩
        · rw [h] at hx; exact hfix hx
        · rw [h, hτ] at hx; exact hfix hx.symm
      rw [h1, h2, Finset.card_pair (Ne.symm hfix)]; simp
  have hsum : Fintype.card X + Fintype.card {x // τ x = x} = ∑ q : InvQuot τ hτ, 2 := by
    have e1 : Fintype.card X =
        ∑ q : InvQuot τ hτ, (Finset.univ.filter (fun x => π x = q)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    have e2 : Fintype.card {x // τ x = x} =
        ∑ q : InvQuot τ hτ, (Finset.univ.filter (fun x => π x = q ∧ τ x = x)).card := by
      rw [Fintype.card_subtype]
      rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      ext x; simp [and_comm]
    rw [e1, e2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => hfib q
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [hsum]; simp [mul_comm]

theorem finrank_ker_funLeft_sub_one (k : Type*) [Field k] [Finite X] :
    Module.finrank k (LinearMap.ker (LinearMap.funLeft k k τ - 1)) =
      Nat.card (InvQuot τ hτ) := by
  classical
  have := Fintype.ofFinite X
  have : Fintype (InvQuot τ hτ) := Fintype.ofFinite _
  let e : LinearMap.ker (LinearMap.funLeft k k τ - 1) ≃ₗ[k] (InvQuot τ hτ → k) :=
    { toFun := fun f => fun q => Quotient.lift (s := invSetoid τ hτ) f.1 (fun a b hab => by
        rcases hab with rfl | rfl
        · rfl
        · have := f.2
          simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
            sub_eq_zero] at this
          exact (congrFun this a).symm) q
      map_add' := fun f g => by
        funext q; obtain ⟨x, rfl⟩ := Quotient.exists_rep q; rfl
      map_smul' := fun c f => by
        funext q; obtain ⟨x, rfl⟩ := Quotient.exists_rep q; rfl
      invFun := fun g => ⟨g ∘ Quotient.mk _, by
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
        funext x
        exact congrArg g ((invQuot_mk_eq τ hτ).mpr (Or.inr rfl)).symm⟩
      left_inv := fun f => by
        apply Subtype.ext; funext x; rfl
      right_inv := fun g => by
        funext q; obtain ⟨x, rfl⟩ := Quotient.exists_rep q; rfl }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

@[expose] def invFunEquiv (β : Type*) :
    {f : X → β // ∀ x, f (τ x) = f x} ≃ (InvQuot τ hτ → β) where
  toFun f := fun q => Quotient.lift (s := invSetoid τ hτ) f.1 (fun a b hab => by
    rcases hab with rfl | rfl
    · rfl
    · exact (f.2 a).symm) q
  invFun g := ⟨g ∘ Quotient.mk _, fun x => congrArg g ((invQuot_mk_eq τ hτ).mpr (Or.inr rfl)).symm⟩
  left_inv f := by apply Subtype.ext; funext x; rfl
  right_inv g := by funext q; obtain ⟨x, rfl⟩ := Quotient.exists_rep q; rfl

theorem card_invariant_functions (β : Type*) [Finite X] :
    Nat.card {f : X → β // ∀ x, f (τ x) = f x} = Nat.card β ^ Nat.card (InvQuot τ hτ) := by
  rw [Nat.card_congr (invFunEquiv τ hτ β), Nat.card_fun]

end Involution

section FieldAut

variable (F : Type*) [Field F] [CharP F 2] {k : Type*} [Field k] [Algebra F k] [CharP k 2]

@[expose] def fieldAut (s : ℕ) : SL(2, F) →* SL(2, F) :=
  Matrix.SpecialLinearGroup.map (iterateFrobenius F 2 s)

variable {F}

theorem fieldAut_apply (s : ℕ) (g : SL(2, F)) (i j : Fin 2) :
    (fieldAut F s g) i j = (g i j) ^ (2 ^ s) := by
  simp [fieldAut, iterateFrobenius_def]

theorem twistMat_fieldAut (s m : ℕ) (g : SL(2, F)) :
    twistMat k m (fieldAut F s g) = twistMat k (m + s) g := by
  ext i j
  rw [twistMat_apply, twistMat_apply, fieldAut_apply, map_pow, ← pow_mul, ← pow_add, add_comm]

variable {ι : Type*} [Fintype ι]

theorem tmatE_fieldAut (s : ℕ) (e : ι → ℕ) (g : SL(2, F)) :
    tmatE k e (fieldAut F s g) = tmatE k (fun i => e i + s) g := by
  ext x' x
  simp only [tmatE, twistMat_fieldAut]

variable [DecidableEq ι]

theorem tensorRep_fieldAut (s : ℕ) (e : ι → ℕ) (g : SL(2, F)) :
    tensorRep F k e (fieldAut F s g) = tensorRep F k (fun i => e i + s) g := by
  simp only [tensorRep, MonoidHom.coe_mk, OneHom.coe_mk, tmatE_fieldAut]

end FieldAut

@[expose] def shiftExp (s i : ℕ) : ℕ := (i + s) % (2 * s)

theorem shiftExp_lt {s : ℕ} (hs : 1 ≤ s) (i : ℕ) : shiftExp s i < 2 * s :=
  Nat.mod_lt _ (Nat.mul_pos (by norm_num) hs)

theorem shiftExp_shiftExp {s : ℕ} (_hs : 1 ≤ s) {i : ℕ} (hi : i < 2 * s) :
    shiftExp s (shiftExp s i) = i := by
  unfold shiftExp
  by_cases h : i < s
  · rw [Nat.mod_eq_of_lt (by omega : i + s < 2 * s)]
    have : i + s + s = i + 2 * s := by ring
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h1 : (i + s) % (2 * s) = i + s - 2 * s := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : i + s - 2 * s + s = i := by omega
    rw [this, Nat.mod_eq_of_lt hi]

theorem shiftExp_ne {s : ℕ} (hs : 1 ≤ s) {i : ℕ} (hi : i < 2 * s) : shiftExp s i ≠ i := by
  intro h
  have := shiftExp_shiftExp hs hi
  rw [h] at this
  unfold shiftExp at h
  by_cases h2 : i < s
  · rw [Nat.mod_eq_of_lt (by omega : i + s < 2 * s)] at h; omega
  · have h1 : (i + s) % (2 * s) = i + s - 2 * s := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1] at h; omega

theorem shiftExp_injOn {s : ℕ} (hs : 1 ≤ s) {i j : ℕ} (hi : i < 2 * s) (hj : j < 2 * s)
    (h : shiftExp s i = shiftExp s j) : i = j := by
  rw [← shiftExp_shiftExp hs hi, h, shiftExp_shiftExp hs hj]

section Main

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {k : Type*} [Field k] [Algebra F k]
  [CharP k 2]

theorem frobTensor_fieldAut {s : ℕ} (hF : Fintype.card F = 2 ^ (2 * s)) (J : Finset ℕ)
    (g : SL(2, F)) :
    frobTensor F k J (fieldAut F s g) =
      tensorRep F k (fun i : J => shiftExp s (i : ℕ)) g := by
  unfold frobTensor
  rw [tensorRep_fieldAut]
  simp only [tensorRep, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  ext x' x
  simp only [tmatE]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [shiftExp, twistMat_mod hF]

theorem frobTensor_shift_eq {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s))
    {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 2 * s)
    (a : Module.End k ((J → Fin 2) → k)) (ha2 : a * a = 1)
    (hconj : ∀ g : SL(2, F), a * frobTensor F k J g = frobTensor F k J (fieldAut F s g) * a) :
    J.image (shiftExp s) = J := by
  classical
  let J' := J.image (shiftExp s)
  have hJ' : ∀ i ∈ J', i < 2 * s := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact shiftExp_lt hs j
  let aEquiv : ((J → Fin 2) → k) ≃ₗ[k] ((J → Fin 2) → k) := LinearEquiv.ofLinearMap a a ha2 ha2
  let e₁ : J → ℕ := fun i => shiftExp s (i : ℕ)
  let φ₁ : (frobTensor F k J).Equiv (tensorRep F k e₁) :=
    Representation.Equiv.mk aEquiv (fun g => by
      have := hconj g
      rw [frobTensor_fieldAut hF] at this
      exact this)
  let τ : J ≃ J' := Equiv.ofBijective (fun i => ⟨shiftExp s (i : ℕ), Finset.mem_image_of_mem _ i.2⟩)
    ⟨fun i j h => by
      apply Subtype.ext
      exact shiftExp_injOn hs (hJ i i.2) (hJ j j.2) (congrArg Subtype.val h),
     fun ⟨j, hj⟩ => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨⟨i, hi⟩, rfl⟩⟩
  let φ₂ : (tensorRep F k e₁).Equiv (frobTensor F k J') :=
    reindexEquiv τ e₁ (fun j : J' => (j : ℕ)) (fun i => rfl)
  exact (frobTensor_nonisomorphic hF hJ hJ' (φ₁.trans φ₂)).symm

end Main

section FlipOp

variable (k : Type*) [Field k] {J : Finset ℕ}

@[expose] def flipOp (σ : J ≃ J) : Module.End k ((J → Fin 2) → k) :=
  LinearMap.funLeft k k (fun y : J → Fin 2 => y ∘ σ)

variable {k}

theorem flipOp_apply (σ : J ≃ J) (f : (J → Fin 2) → k) (y : J → Fin 2) :
    flipOp k σ f y = f (y ∘ σ) := rfl

theorem flipOp_flipOp (σ : J ≃ J) (hσ : ∀ i, σ (σ i) = i) (f : (J → Fin 2) → k) :
    flipOp k σ (flipOp k σ f) = f := by
  funext y
  rw [flipOp_apply, flipOp_apply]
  congr 1
  funext i
  simp [hσ]

theorem flipOp_counts (σ : J ≃ J) (hσ : ∀ i, σ (σ i) = i) (hfree : ∀ i, σ i ≠ i) :
    ∃ m : ℕ, J.card = 2 * m ∧
      2 * Module.finrank k (LinearMap.ker (flipOp k σ - 1)) = 2 ^ (2 * m) + 2 ^ m := by
  classical
  let hσ' : ∀ x : J, σ (σ x) = x := hσ
  have hfixσ : Nat.card {x : J // σ x = x} = 0 := by
    rw [Nat.card_eq_zero]
    left
    exact ⟨fun x => hfree x.1 x.2⟩
  have hJcard : J.card = 2 * Nat.card (InvQuot σ hσ') := by
    have h := two_mul_card_invQuot σ hσ'
    rw [hfixσ, add_zero, Nat.card_eq_finsetCard] at h
    exact h.symm
  refine ⟨Nat.card (InvQuot σ hσ'), hJcard, ?_⟩
  let τ : (J → Fin 2) → (J → Fin 2) := fun y => y ∘ σ
  have hτ : ∀ y, τ (τ y) = y := fun y => by
    funext i; simp [τ, hσ]
  have h1 := finrank_ker_funLeft_sub_one τ hτ k
  have h2 := two_mul_card_invQuot τ hτ
  have hflip : flipOp k σ = LinearMap.funLeft k k τ := rfl
  rw [hflip, h1, h2]
  have hcardX : Nat.card (J → Fin 2) = 2 ^ (2 * Nat.card (InvQuot σ hσ')) := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_finsetCard, hJcard]
  have hfixτ : Nat.card {y : J → Fin 2 // τ y = y} = 2 ^ Nat.card (InvQuot σ hσ') := by
    have h3 := card_invariant_functions σ hσ' (Fin 2)
    rw [Nat.card_fin] at h3
    rw [← h3]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    constructor
    · intro h x
      exact (congrFun h x)
    · intro h
      funext x
      exact h x
  rw [hcardX, hfixτ]

end FlipOp

@[expose] noncomputable def shiftPerm {s : ℕ} (hs : 1 ≤ s) {J : Finset ℕ}
    (hJ : ∀ i ∈ J, i < 2 * s) (hJs : J.image (shiftExp s) = J) : J ≃ J :=
  Equiv.ofBijective
    (fun i => ⟨shiftExp s (i : ℕ), hJs.subset (Finset.mem_image_of_mem _ i.2)⟩)
    ⟨fun i j h => Subtype.ext (shiftExp_injOn hs (hJ i i.2) (hJ j j.2) (congrArg Subtype.val h)),
     fun ⟨j, hj⟩ => by
       obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hJs.symm.subset hj)
       exact ⟨⟨i, hi⟩, rfl⟩⟩

theorem shiftPerm_apply {s : ℕ} (hs : 1 ≤ s) {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 2 * s)
    (hJs : J.image (shiftExp s) = J) (i : J) :
    ((shiftPerm hs hJ hJs i : J) : ℕ) = shiftExp s (i : ℕ) := rfl

section Main2

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {k : Type*} [Field k] [Algebra F k]
  [CharP k 2]

theorem frobTensor_field_involution {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ (2 * s))
    {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 2 * s)
    (a : Module.End k ((J → Fin 2) → k)) (ha2 : a * a = 1)
    (hconj : ∀ g : SL(2, F), a * frobTensor F k J g = frobTensor F k J (fieldAut F s g) * a) :
    ∃ hJs : J.image (shiftExp s) = J, a = flipOp k (shiftPerm hs hJ hJs) ∧
      ∃ m : ℕ, J.card = 2 * m ∧
        Module.finrank k (LinearMap.ker (a - 1)) = 2 ^ m * (2 ^ m + 1) / 2 ∧
        Module.finrank k (LinearMap.range (a - 1)) = 2 ^ m * (2 ^ m - 1) / 2 := by
  classical
  have hJs := frobTensor_shift_eq hs hF hJ a ha2 hconj
  refine ⟨hJs, ?_⟩
  set σ := shiftPerm hs hJ hJs with hσdef
  have hσ : ∀ i, σ (σ i) = i := fun i =>
    Subtype.ext (shiftExp_shiftExp hs (hJ i i.2))
  have hfree : ∀ i, σ i ≠ i := fun i h => shiftExp_ne hs (hJ i i.2) (congrArg Subtype.val h)
  let e : J → ℕ := fun i => (i : ℕ)
  let e₁ : J → ℕ := fun i => shiftExp s (i : ℕ)
  have he : ∀ i, e₁ (σ i) = e i := fun i => shiftExp_shiftExp hs (hJ i i.2)
  let ψ := reindexEquiv (F := F) (k := k) σ e e₁ he
  have hP : ∀ g v, flipOp k σ (frobTensor F k J g v) = tensorRep F k e₁ g (flipOp k σ v) :=
    fun g v => equiv_apply ψ g v
  have hPP : ∀ v, flipOp k σ (flipOp k σ v) = v := flipOp_flipOp σ hσ
  have hP' : ∀ g w, flipOp k σ (tensorRep F k e₁ g w) = frobTensor F k J g (flipOp k σ w) := by
    intro g w
    have := hP g (flipOp k σ w)
    rw [hPP] at this
    rw [← this, hPP]
  have ha' : ∀ g v, a (frobTensor F k J g v) = tensorRep F k e₁ g (a v) := by
    intro g v
    have := congrArg (fun T : Module.End k ((J → Fin 2) → k) => T v) (hconj g)
    simp only [Module.End.mul_apply] at this
    rw [frobTensor_fieldAut hF] at this
    exact this
  have hu : ∀ g : SL(2, F),
      (flipOp k σ ∘ₗ a) ∘ₗ tensorRep F k e g = tensorRep F k e g ∘ₗ (flipOp k σ ∘ₗ a) := by
    intro g
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact (congrArg (flipOp k σ) (ha' g v)).trans (hP' g (a v))
  obtain ⟨r, hr⟩ := commutant_scalar hF e Subtype.val_injective (fun i => hJ i i.2) _ hu
  have har : ∀ v, a v = r • flipOp k σ v := by
    intro v
    have h1 := congrArg (fun T : Module.End k ((J → Fin 2) → k) => T v) hr
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    calc a v = flipOp k σ (flipOp k σ (a v)) := (hPP _).symm
      _ = flipOp k σ (r • v) := by rw [h1]
      _ = r • flipOp k σ v := map_smul _ _ _
  have haa : ∀ v, a (a v) = v := fun v => by
    have := congrArg (fun T : Module.End k ((J → Fin 2) → k) => T v) ha2
    simpa using this
  have hrr : r * r = 1 := by
    have h3 : ∀ v, a (a v) = (r * r) • v := fun v => by
      rw [har v, map_smul, har (flipOp k σ v), hPP, smul_smul]
    have h4 := congrFun (h3 baseVec |>.symm.trans (haa baseVec)) (fun _ => 0)
    simpa [baseVec_apply] using h4
  have hr1 : r = 1 := by
    have h5 : (r - 1) ^ 2 = 0 := by
      rw [sub_pow_char r 1 (p := 2), one_pow, pow_two, hrr, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h5)
  have haP : a = flipOp k σ := LinearMap.ext fun v => by rw [har v, hr1, one_smul]
  refine ⟨haP, ?_⟩
  obtain ⟨m, hm, hk⟩ := flipOp_counts (k := k) σ hσ hfree
  refine ⟨m, hm, ?_⟩
  rw [haP]
  have e2 : (2 : ℕ) ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  have hker : 2 * Module.finrank k (LinearMap.ker (flipOp k σ - 1)) = 2 ^ m * (2 ^ m + 1) := by
    rw [hk, e2]; ring
  have hdim : Module.finrank k ((J → Fin 2) → k) = 2 ^ m * 2 ^ m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hm,
      e2]
  have hrn := LinearMap.finrank_range_add_finrank_ker (flipOp k σ - 1)
  rw [hdim] at hrn
  constructor
  · rw [← hker]; omega
  · have h6 : 2 * Module.finrank k (LinearMap.range (flipOp k σ - 1)) = 2 ^ m * (2 ^ m - 1) := by
      obtain ⟨H, hH'⟩ : ∃ H, 2 ^ m = H + 1 := ⟨2 ^ m - 1, by have := Nat.one_le_two_pow (n := m); omega⟩
      rw [hH'] at hker hrn ⊢
      simp only [Nat.add_sub_cancel]
      nlinarith [hrn, hker]
    rw [← h6]; omega

end Main2

end CFSG.QuasithinUnique.Setup.SL2Modules
