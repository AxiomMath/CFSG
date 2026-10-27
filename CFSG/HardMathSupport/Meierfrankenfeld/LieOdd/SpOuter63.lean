module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpTwoRank
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpDetSquare
import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix hiding gram gram_apply
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank Module

variable {K : Type} [Field K] {r : ℕ}

@[expose] def formLin (u : Fin r ⊕ Fin r → K) : (Fin r ⊕ Fin r → K) →ₗ[K] K where
  toFun v := form v u
  map_add' v w := form_add_left v w u
  map_smul' c v := by simp [form_smul_left]

@[expose] def perpPair (W : Submodule K (Fin r ⊕ Fin r → K)) (e f : Fin r ⊕ Fin r → K) :
    Submodule K (Fin r ⊕ Fin r → K) :=
  W ⊓ LinearMap.ker ((formLin e).prod (formLin f))

theorem mem_perpPair {W : Submodule K (Fin r ⊕ Fin r → K)} {e f x : Fin r ⊕ Fin r → K} :
    x ∈ perpPair W e f ↔ x ∈ W ∧ form x e = 0 ∧ form x f = 0 := by
  simp [perpPair, LinearMap.mem_ker, formLin]

theorem perpPair_nondeg {W : Submodule K (Fin r ⊕ Fin r → K)} (hWn : SympNondeg W)
    {e f : Fin r ⊕ Fin r → K} (he : e ∈ W) (hf : f ∈ W) (hef : form e f = 1) :
    SympNondeg (perpPair W e f) := by
  intro x hx hxo
  rw [mem_perpPair] at hx
  refine hWn x hx.1 fun w hw => ?_
  set w' : Fin r ⊕ Fin r → K := w - form w f • e + form w e • f with hw'
  have hfe : form f e = -1 := by rw [form_antisymm, hef]
  have hee := form_self e
  have hff := form_self f
  have hw'W : w' ∈ perpPair W e f := by
    rw [mem_perpPair]
    refine ⟨?_, ?_, ?_⟩
    · exact W.add_mem (W.sub_mem hw (W.smul_mem _ he)) (W.smul_mem _ hf)
    · rw [hw']
      simp only [form_add_left, form_sub_left, form_smul_left, hee, hfe]
      ring
    · rw [hw']
      simp only [form_add_left, form_sub_left, form_smul_left, hef, hff]
      ring
  have := hxo w' hw'W
  rw [hw'] at this
  simp only [form_add_right, form_sub_right, form_smul_right, hx.2.1, hx.2.2] at this
  linear_combination this

theorem finrank_perpPair (W : Submodule K (Fin r ⊕ Fin r → K)) (e f : Fin r ⊕ Fin r → K) :
    finrank K W ≤ finrank K (perpPair W e f) + 2 := by
  let g : W →ₗ[K] K × K := ((formLin e).prod (formLin f)).domRestrict W
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : finrank K (LinearMap.range g) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range g)
    simpa [Module.finrank_prod] using this
  have h3 : perpPair W e f = (LinearMap.ker g).map W.subtype := by
    ext x
    rw [mem_perpPair, Submodule.mem_map]
    constructor
    · rintro ⟨hxW, h1, h2⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      rw [LinearMap.mem_ker]
      simp [g, formLin, h1, h2]
    · rintro ⟨⟨y, hyW⟩, hy, rfl⟩
      rw [LinearMap.mem_ker] at hy
      have := congrArg Prod.fst hy
      have := congrArg Prod.snd hy
      simp [g, formLin] at *
      exact ⟨hyW, by assumption, by assumption⟩
  rw [h3, Submodule.finrank_map_subtype_eq]
  omega

theorem form_similitude {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} {μ : K}
    (h : aᵀ * gram K r * a = μ • gram K r) (u v : Fin r ⊕ Fin r → K) :
    form (a *ᵥ u) (a *ᵥ v) = μ * form u v := by
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

section Pair

variable (h2 : (2 : K) ≠ 0) {a : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

include h2 in
theorem exists_adapted_pair (haa : ∀ w, a *ᵥ (a *ᵥ w) = w)
    (hform : ∀ u v, form (a *ᵥ u) (a *ᵥ v) = -form u v)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hWa : ∀ w ∈ W, a *ᵥ w ∈ W) (hWn : SympNondeg W)
    (hWne : W ≠ ⊥) :
    ∃ e ∈ W, ∃ f ∈ W, a *ᵥ e = e ∧ a *ᵥ f = -f ∧ form e f = 1 := by
  obtain ⟨x, hxW, hx⟩ : ∃ x ∈ W, a *ᵥ x ≠ -x := by
    by_contra hcon
    push Not at hcon
    apply hWne
    refine eq_bot_iff.2 fun x hx => ?_
    refine (Submodule.mem_bot K).2 (hWn x hx fun y hy => ?_)
    have h := hform x y
    rw [hcon x hx, hcon y hy, form_neg_left, form_neg_right, neg_neg] at h
    have : (2 : K) * form x y = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2
  set e := x + a *ᵥ x with he
  have heW : e ∈ W := W.add_mem hxW (hWa x hxW)
  have hae : a *ᵥ e = e := by
    rw [he, Matrix.mulVec_add, haa, add_comm]
  have he0 : e ≠ 0 := by
    intro h
    exact hx (eq_neg_of_add_eq_zero_right h)
  obtain ⟨y, hyW, hy⟩ : ∃ y ∈ W, form e y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (hWn e heW hcon)
  set y₀ := y - a *ᵥ y with hy₀
  have hy₀W : y₀ ∈ W := W.sub_mem hyW (hWa y hyW)
  have hay₀ : a *ᵥ y₀ = -y₀ := by
    rw [hy₀, Matrix.mulVec_sub, haa]; abel
  have hey : form e (a *ᵥ y) = -form e y := by
    have h := hform e (a *ᵥ y)
    rw [hae, haa] at h
    linear_combination h
  have hey₀ : form e y₀ = 2 * form e y := by
    rw [hy₀, form_sub_right, hey]; ring
  have hne : form e y₀ ≠ 0 := by rw [hey₀]; exact mul_ne_zero h2 hy
  refine ⟨e, heW, (form e y₀)⁻¹ • y₀, W.smul_mem _ hy₀W, hae, ?_, ?_⟩
  · rw [Matrix.mulVec_smul, hay₀, smul_neg]
  · rw [form_smul_right, inv_mul_cancel₀ hne]

theorem perpPair_inv (hform : ∀ u v, form (a *ᵥ u) (a *ᵥ v) = -form u v)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hWa : ∀ w ∈ W, a *ᵥ w ∈ W)
    {e f : Fin r ⊕ Fin r → K} (hae : a *ᵥ e = e) (haf : a *ᵥ f = -f) {x : Fin r ⊕ Fin r → K}
    (hx : x ∈ perpPair W e f) : a *ᵥ x ∈ perpPair W e f := by
  rw [mem_perpPair] at hx ⊢
  refine ⟨hWa x hx.1, ?_, ?_⟩
  · have h := hform x e
    rw [hae, hx.2.1] at h
    simpa using h
  · have h := hform x f
    rw [haf, hx.2.2, form_neg_right] at h
    have h' : form (a *ᵥ x) f = 0 := by
      have : -form (a *ᵥ x) f = 0 := by simpa using h
      exact neg_eq_zero.1 this
    exact h'

end Pair

section Triple

variable (h2 : (2 : K) ≠ 0) {a : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K}

include h2 in
theorem exists_adapted_triple (haa : ∀ w, a *ᵥ (a *ᵥ w) = w)
    (hform : ∀ u v, form (a *ᵥ u) (a *ᵥ v) = -form u v) :
    ∃ e f : Fin 3 → Fin 3 ⊕ Fin 3 → K, (∀ i, a *ᵥ e i = e i) ∧ (∀ i, a *ᵥ f i = -f i) ∧
      (∀ i j, form (e i) (e j) = 0) ∧ (∀ i j, form (f i) (f j) = 0) ∧
      (∀ i j, form (e i) (f j) = if i = j then 1 else 0) := by
  have hsym : ∀ x y : Fin 3 ⊕ Fin 3 → K, form x y = 0 → form y x = 0 := fun x y h => by
    rw [form_antisymm, h, neg_zero]
  have htop : ∀ w ∈ (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)), a *ᵥ w ∈ (⊤ : Submodule K _) :=
    fun _ _ => Submodule.mem_top
  have hfr0 : finrank K (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)) = 6 := finrank_top_three
  have hne0 : (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)) ≠ ⊥ := by
    intro h
    rw [h] at hfr0
    simp at hfr0
  obtain ⟨e₀, -, f₀, -, hae₀, haf₀, hef₀⟩ :=
    exists_adapted_pair h2 haa hform htop sympNondeg_top hne0
  set W₁ := perpPair (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)) e₀ f₀ with hW₁
  have hW₁n : SympNondeg W₁ :=
    perpPair_nondeg sympNondeg_top Submodule.mem_top Submodule.mem_top hef₀
  have hW₁a : ∀ w ∈ W₁, a *ᵥ w ∈ W₁ := fun w hw => perpPair_inv hform htop hae₀ haf₀ hw
  have hW₁d : 4 ≤ finrank K W₁ := by
    have := finrank_perpPair (⊤ : Submodule K (Fin 3 ⊕ Fin 3 → K)) e₀ f₀
    rw [← hW₁] at this
    omega
  have hW₁ne : W₁ ≠ ⊥ := by
    intro h
    rw [h] at hW₁d
    simp at hW₁d
  obtain ⟨e₁, he₁, f₁, hf₁, hae₁, haf₁, hef₁⟩ :=
    exists_adapted_pair h2 haa hform hW₁a hW₁n hW₁ne
  set W₂ := perpPair W₁ e₁ f₁ with hW₂
  have hW₂n : SympNondeg W₂ := perpPair_nondeg hW₁n he₁ hf₁ hef₁
  have hW₂a : ∀ w ∈ W₂, a *ᵥ w ∈ W₂ := fun w hw => perpPair_inv hform hW₁a hae₁ haf₁ hw
  have hW₂d : 2 ≤ finrank K W₂ := by
    have := finrank_perpPair W₁ e₁ f₁
    rw [← hW₂] at this
    omega
  have hW₂ne : W₂ ≠ ⊥ := by
    intro h
    rw [h] at hW₂d
    simp at hW₂d
  obtain ⟨e₂, he₂, f₂, hf₂, hae₂, haf₂, hef₂⟩ :=
    exists_adapted_pair h2 haa hform hW₂a hW₂n hW₂ne
  rw [hW₂, mem_perpPair] at he₂ hf₂
  rw [hW₁, mem_perpPair] at he₁ hf₁
  rw [hW₁, mem_perpPair] at he₂ hf₂
  have e₁e₀ := he₁.2.1
  have e₁f₀ := he₁.2.2
  have f₁e₀ := hf₁.2.1
  have f₁f₀ := hf₁.2.2
  have e₂e₀ := he₂.1.2.1
  have e₂f₀ := he₂.1.2.2
  have f₂e₀ := hf₂.1.2.1
  have f₂f₀ := hf₂.1.2.2
  have e₂e₁ := he₂.2.1
  have e₂f₁ := he₂.2.2
  have f₂e₁ := hf₂.2.1
  have f₂f₁ := hf₂.2.2
  have e₀e₁ := hsym _ _ e₁e₀
  have e₀f₁ := hsym _ _ f₁e₀
  have f₀e₁ := hsym _ _ e₁f₀
  have f₀f₁ := hsym _ _ f₁f₀
  have e₀e₂ := hsym _ _ e₂e₀
  have e₀f₂ := hsym _ _ f₂e₀
  have f₀e₂ := hsym _ _ e₂f₀
  have f₀f₂ := hsym _ _ f₂f₀
  have e₁e₂ := hsym _ _ e₂e₁
  have e₁f₂ := hsym _ _ f₂e₁
  have f₁e₂ := hsym _ _ e₂f₁
  have f₁f₂ := hsym _ _ f₂f₁
  refine ⟨![e₀, e₁, e₂], ![f₀, f₁, f₂], ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hae₀, hae₁, hae₂]
  · intro i; fin_cases i <;> simp [haf₀, haf₁, haf₂]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [form_self, e₁e₀, e₂e₀, e₂e₁, e₀e₁, e₀e₂, e₁e₂]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [form_self, f₁f₀, f₂f₀, f₂f₁, f₀f₁, f₀f₂, f₁f₂]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hef₀, hef₁, hef₂, e₀f₁, e₀f₂, e₁f₀, e₁f₂, e₂f₀, e₂f₁]

end Triple

section Witness

@[expose] def tbl6 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 1, 0; 1, 1, 0, 1, 1, 0; 0, 0, 1, 0, 0, 0; 1, 0, 0, 0, 1, 0; 0, 1, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 1]

@[expose] def X6 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3) :=
  tbl6.submatrix finSumFinEquiv finSumFinEquiv

theorem X6_symp : X6ᵀ * gram (ZMod 3) 3 * X6 = gram (ZMod 3) 3 := by decide +kernel

theorem X6_conj : Matrix.diagonal (sgn (ZMod 3)) * X6 * Matrix.diagonal (sgn (ZMod 3)) * X6 = 1 := by
  decide +kernel

theorem X6_pow : X6 * X6 * X6 * X6 * X6 = 1 := by decide +kernel

theorem X6_zero : X6 (Sum.inl 0) (Sum.inl 0) = 0 := by decide

variable [CharP K 3]

@[expose] noncomputable def φ3 : ZMod 3 →+* K := ZMod.castHom (dvd_refl 3) K

@[expose] noncomputable def X6K : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  X6.map (φ3 (K := K))

theorem gram_map3 : (gram (ZMod 3) 3).map (φ3 (K := K)) = gram K 3 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [gram, Matrix.one_apply, Matrix.fromBlocks]

theorem diag_sgn_map3 :
    (Matrix.diagonal (sgn (ZMod 3)) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 3)).map
      (φ3 (K := K)) = Matrix.diagonal (sgn K) := by
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext a
  cases a <;> simp [sgn]

theorem X6K_symp : X6Kᵀ * gram K 3 * X6K = gram K 3 := by
  have := congrArg (RingHom.mapMatrix (φ3 (K := K))) X6_symp
  simp only [map_mul, RingHom.mapMatrix_apply, Matrix.transpose_map, gram_map3] at this
  exact this

theorem X6K_conj :
    Matrix.diagonal (sgn K) * X6K * Matrix.diagonal (sgn K) * X6K = 1 := by
  have := congrArg (RingHom.mapMatrix (φ3 (K := K))) X6_conj
  simp only [map_mul, map_one, RingHom.mapMatrix_apply, diag_sgn_map3] at this
  exact this

theorem X6K_pow : (X6K (K := K)) * X6K * X6K * X6K * X6K = 1 := by
  have := congrArg (RingHom.mapMatrix (φ3 (K := K))) X6_pow
  simp only [map_mul, map_one, RingHom.mapMatrix_apply] at this
  exact this

theorem X6K_not_scalar {c : K} (hc : c = 1 ∨ c = -1) :
    (X6K (K := K)) ≠ c • (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
  intro h
  have e := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have h0 : (X6K (K := K)) (Sum.inl 0) (Sum.inl 0) = 0 := by
    show φ3 (K := K) (X6 (Sum.inl 0) (Sum.inl 0)) = 0
    rw [X6_zero, map_zero]
  have e' : (0 : K) = c := by
    rw [← h0, e]
    simp
  rcases hc with rfl | rfl
  · exact one_ne_zero e'.symm
  · exact one_ne_zero (by linear_combination e')

end Witness

section Main

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable [CharP K 3]

omit [CharP K 3] in
theorem family_symplectic (vec : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → K)
    (hb : ∀ x y, form (vec x) (vec y) = gram K 3 x y) :
    (Matrix.of fun r c => vec c r : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * gram K 3 *
      (Matrix.of fun r c => vec c r) = gram K 3 := by
  ext x y
  rw [transpose_mul_gram_mul_apply, ← hb x y, form_apply]
  rfl

theorem exists_inverted_of_involutive (h2 : (2 : K) ≠ 0) (A : gsp 3 K)
    (hAA : ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
      ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = 1)
    (hμ : ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * formJ 3 K *
      ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
        (-1 : K) • formJ 3 K) :
    ∃ x : StatedProj (StatedSp 3 K), orderOf x = 5 ∧ conjAut 3 K A x = x⁻¹ := by
  set a : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with ha
  have haa : ∀ w, a *ᵥ (a *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]
  have hform : ∀ u v, form (a *ᵥ u) (a *ᵥ v) = -form u v := by
    intro u v
    have := form_similitude (a := a) (μ := -1) hμ u v
    rw [this]; ring
  obtain ⟨e, f, hae, haf, hee, hff, hef⟩ := exists_adapted_triple h2 haa hform
  set vec : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → K := Sum.elim e f with hvec
  have hb : ∀ x y, form (vec x) (vec y) = gram K 3 x y := by
    rintro (i | i) (j | j)
    · simp [hvec, gram_apply, hee]
    · simp [hvec, gram_apply, hef, eq_comm]
    · rw [hvec]
      simp only [Sum.elim_inr, Sum.elim_inl]
      rw [form_antisymm, hef j i, gram_apply]
      by_cases hij : i = j <;> simp [hij, eq_comm]
    · simp [hvec, gram_apply, hff]
  set M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := Matrix.of fun r c => vec c r with hMdef
  have hM : Mᵀ * gram K 3 * M = gram K 3 := family_symplectic vec hb
  let h : StatedSp 3 K := ofSymplecticMat M hM
  have hmat : mat 3 K h = M := rfl
  have hav : ∀ x, a *ᵥ vec x = sgn K x • vec x := by
    rintro (i | i)
    · simp [hvec, sgn, hae]
    · simp [hvec, sgn, haf]
  have haM : a * M = M * Matrix.diagonal (sgn K) := by
    ext i j
    have e1 : (a * M) i j = (a *ᵥ vec j) i := rfl
    rw [e1, hav j, Matrix.mul_diagonal]
    simp [hMdef, mul_comm]
  have hsgn : ∀ x : Fin 3 ⊕ Fin 3, sgn K x * sgn K x = 1 := by
    rintro (i | i) <;> simp [sgn]
  have hDD : Matrix.diagonal (sgn K) * Matrix.diagonal (sgn K) =
      (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    exact hsgn x
  let Dg : GL (Fin 3 ⊕ Fin 3) K := ⟨Matrix.diagonal (sgn K), Matrix.diagonal (sgn K), hDD, hDD⟩
  let Xs : StatedSp 3 K := ofSymplecticMat X6K X6K_symp
  let Hg : GL (Fin 3 ⊕ Fin 3) K := (h : GL (Fin 3 ⊕ Fin 3) K)
  let Xg : GL (Fin 3 ⊕ Fin 3) K := (Xs : GL (Fin 3 ⊕ Fin 3) K)
  have hAHD : (A : GL (Fin 3 ⊕ Fin 3) K) * Hg = Hg * Dg := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact haM
  have hA : (A : GL (Fin 3 ⊕ Fin 3) K) = Hg * Dg * Hg⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]; exact hAHD
  have key : Dg * Xg * Dg⁻¹ = Xg⁻¹ := by
    refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
    rw [Units.val_mul, Units.val_mul]
    exact X6K_conj
  have hconj : conjSp 3 K A (h * Xs * h⁻¹) = (h * Xs * h⁻¹)⁻¹ := by
    apply Subtype.ext
    rw [coe_conjSp, hA]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    change Hg * Dg * Hg⁻¹ * (Hg * Xg * Hg⁻¹) * (Hg * Dg * Hg⁻¹)⁻¹ = (Hg * Xg * Hg⁻¹)⁻¹
    calc Hg * Dg * Hg⁻¹ * (Hg * Xg * Hg⁻¹) * (Hg * Dg * Hg⁻¹)⁻¹
        = Hg * (Dg * Xg * Dg⁻¹) * Hg⁻¹ := by group
      _ = Hg * Xg⁻¹ * Hg⁻¹ := by rw [key]
      _ = (Hg * Xg * Hg⁻¹)⁻¹ := by group
  have hX5 : Xs * Xs * Xs * Xs * Xs = 1 := by
    apply Subtype.ext
    apply Units.ext
    show X6K * X6K * X6K * X6K * X6K = 1
    exact X6K_pow
  have hx5 : (h * Xs * h⁻¹) ^ 5 = 1 := by
    rw [conj_pow, show Xs ^ 5 = Xs * Xs * Xs * Xs * Xs by simp [pow_succ], hX5]
    group
  have hx1 : (QuotientGroup.mk (h * Xs * h⁻¹) : StatedProj (StatedSp 3 K)) ≠ 1 := by
    intro hmk
    obtain ⟨ε, hε, hεm⟩ := pm_of_mk_eq_one hmk
    refine X6K_not_scalar hε ?_
    have e : Xs = h⁻¹ * (h * Xs * h⁻¹) * h := by group
    have e2 : mat 3 K Xs = mat 3 K h⁻¹ * mat 3 K (h * Xs * h⁻¹) * mat 3 K h := by
      conv_lhs => rw [e]
      rw [map_mul, map_mul]
    show mat 3 K Xs = _
    rw [e2, hεm, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← map_mul, inv_mul_cancel,
      map_one]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨QuotientGroup.mk (h * Xs * h⁻¹), orderOf_eq_prime ?_ hx1, ?_⟩
  · rw [← QuotientGroup.mk_pow, hx5]; rfl
  · show conjAut 3 K A (proj 3 K (h * Xs * h⁻¹)) = (proj 3 K (h * Xs * h⁻¹))⁻¹
    rw [conjAut_proj, hconj, map_inv]

end Main

section Scalar

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

theorem finrank_ker_formLin_three (v : Fin 3 ⊕ Fin 3 → K) :
    5 ≤ finrank K (LinearMap.ker (formLin v)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (formLin v)
  have h2 : finrank K (LinearMap.range (formLin v)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (formLin v))
    simpa using this
  have h3 : finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by
    rw [Module.finrank_pi]; simp
  omega

theorem commute_rank1_of_conjAut_trivial_three (h2 : (2 : K) ≠ 0) (M : gsp 3 K)
    (h : conjAut 3 K M = 1) (v : Fin 3 ⊕ Fin 3 → K) :
    ((M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) * rank1 v v =
      rank1 v v * ((M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) := by
  obtain ⟨x, hx⟩ := exists_sp_one_add (rank1 v v) (rank1_self_sq h2 v) (rank1_self_hB h2 v)
  have h1 : conjAut 3 K M (proj 3 K x) = proj 3 K x := by rw [h]; rfl
  rw [conjAut_proj] at h1
  have h3 := QuotientGroup.eq.1 h1
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h3
  obtain ⟨c, hc⟩ := h3
  set a : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    ((M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with ha
  set ai : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    (((M : GL (Fin 3 ⊕ Fin 3) K)⁻¹ : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with hai
  have hai1 : ai * a = 1 := Units.inv_mul _
  have ha1 : a * ai = 1 := Units.mul_inv _
  set X : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K := 1 + rank1 v v with hX
  have e1 : c • (a * X * ai) = X := by
    have h4 : (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c : GL (Fin 3 ⊕ Fin 3) K) =
        (conjSp 3 K M x)⁻¹ * x := hc
    have h5 : conjSp 3 K M x * Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c =
        (x : GL (Fin 3 ⊕ Fin 3) K) := by
      rw [h4]; simp
    have h6 := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) K =>
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)) h5
    have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin 3) c : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = (c : K) • 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.GeneralLinearGroup.scalar, hij]
    simp only [Units.val_mul, hs, coe_conjSp, hx] at h6
    rw [Matrix.mul_smul, Matrix.mul_one] at h6
    exact h6
  by_cases hv : v = 0
  · subst hv
    simp [rank1]
  have hinj : ∀ y, a *ᵥ y = 0 → y = 0 := by
    intro y hy
    have : ai *ᵥ (a *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hai1, Matrix.one_mulVec]
    rw [← this, hy, Matrix.mulVec_zero]
  have hc1 : c = 1 := by
    by_contra hne
    have hc' : (c : K) - 1 ≠ 0 := fun h' => hne (Units.ext (sub_eq_zero.1 h'))
    have e2 : c • (a * X) = X * a := by
      have := congrArg (fun N => N * a) e1
      rw [Matrix.smul_mul, Matrix.mul_assoc (a * X), hai1, Matrix.mul_one] at this
      exact this
    have hU : ∀ u : Fin 3 ⊕ Fin 3 → K, form u v = 0 → ∃ s : K, a *ᵥ u = s • v := by
      intro u hu
      have := congrArg (fun N => N *ᵥ u) e2
      simp only [Units.smul_def, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at this
      have hXu : X *ᵥ u = u := by
        rw [hX, Matrix.add_mulVec, Matrix.one_mulVec, rank1_mulVec]
        have : symB u v = 0 := hu
        rw [this, zero_smul, add_zero]
      have hXau : X *ᵥ (a *ᵥ u) = a *ᵥ u + symB (a *ᵥ u) v • v := by
        rw [hX, Matrix.add_mulVec, Matrix.one_mulVec, rank1_mulVec]
      rw [hXu, hXau] at this
      refine ⟨((c : K) - 1)⁻¹ * symB (a *ᵥ u) v, ?_⟩
      have h7 : ((c : K) - 1) • (a *ᵥ u) = symB (a *ᵥ u) v • v := by
        have : (c : K) • (a *ᵥ u) = a *ᵥ u + symB (a *ᵥ u) v • v := this
        calc ((c : K) - 1) • (a *ᵥ u) = (c : K) • (a *ᵥ u) - a *ᵥ u := by module
          _ = symB (a *ᵥ u) v • v := by rw [this]; abel
      calc a *ᵥ u = ((c : K) - 1)⁻¹ • (((c : K) - 1) • (a *ᵥ u)) := by
            rw [smul_smul, inv_mul_cancel₀ hc', one_smul]
        _ = _ := by rw [h7, smul_smul]
    obtain ⟨sv, hsv⟩ := hU v (form_self v)
    have hsv0 : sv ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hsv
      exact hv (hinj v hsv)
    have hsub : LinearMap.ker (formLin v) ≤ Submodule.span K {v} := by
      intro u hu
      rw [LinearMap.mem_ker] at hu
      obtain ⟨su, hsu⟩ := hU u hu
      have h0 : a *ᵥ (sv • u - su • v) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hsu, hsv]
        module
      have h8 := hinj _ h0
      rw [Submodule.mem_span_singleton]
      refine ⟨su / sv, ?_⟩
      have : sv • u = su • v := sub_eq_zero.1 h8
      calc (su / sv) • v = sv⁻¹ • (su • v) := by rw [smul_smul, div_eq_inv_mul]
        _ = u := by rw [← this, smul_smul, inv_mul_cancel₀ hsv0, one_smul]
    have hle := Submodule.finrank_mono hsub
    have hsp : finrank K (Submodule.span K ({v} : Set (Fin 3 ⊕ Fin 3 → K))) ≤ 1 := by
      simpa using finrank_span_le_card ({v} : Set (Fin 3 ⊕ Fin 3 → K))
    have := finrank_ker_formLin_three v
    omega
  rw [hc1] at e1
  simp only [one_smul] at e1
  have e2 : a * X = X * a := by
    calc a * X = (a * X * ai) * a := by rw [Matrix.mul_assoc (a * X), hai1, Matrix.mul_one]
      _ = X * a := by rw [e1]
  rw [hX, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at e2
  exact add_left_cancel e2

theorem exists_scalar_of_conjAut_trivial_three (h2 : (2 : K) ≠ 0) (M : gsp 3 K)
    (h : conjAut 3 K M = 1) :
    ∃ lam : K, ((M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) =
      lam • 1 := by
  set a : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    ((M : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with ha
  have hcol : ∀ v : Fin 3 ⊕ Fin 3 → K, v ≠ 0 → ∃ c : K, a *ᵥ v = c • v := by
    intro v hv
    obtain ⟨w, hw⟩ : ∃ w, symB w v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (eq_zero_of_symB_forall hcon)
    have hc := commute_rank1_of_conjAut_trivial_three h2 M h v
    have := congrArg (fun N => N *ᵥ w) hc
    simp only [← Matrix.mulVec_mulVec, rank1_mulVec v v w, Matrix.mulVec_smul] at this
    have h' : a *ᵥ v = (symB (a *ᵥ w) v / symB w v) • v := by
      rw [rank1_mulVec v v (a *ᵥ w)] at this
      calc a *ᵥ v = (symB w v)⁻¹ • (symB w v • a *ᵥ v) := by
            rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
        _ = (symB w v)⁻¹ • (symB (a *ᵥ w) v • v) := by rw [this]
        _ = _ := by rw [smul_smul, div_eq_inv_mul]
    exact ⟨_, h'⟩
  have hnot : ∀ v, ¬ LinearIndependent K ![v, Matrix.mulVecLin a v] := by
    intro v
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · obtain ⟨c, hc⟩ := hcol v hv
      rw [LinearIndependent.pair_iff' hv]
      push Not
      exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨lam, hlam⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hnot
  refine ⟨lam, matrix_ext_of_mulVec fun w => ?_⟩
  have := LinearMap.congr_fun hlam w
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  simpa using this

end Scalar

section Outer

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable [Finite K] [CharP K 3]

omit [Finite K] in
theorem two_ne_zero_char_three : (2 : K) ≠ 0 := by
  intro h
  have h' := (CharP.cast_eq_zero_iff K 3 2).mp (by exact_mod_cast h)
  exact absurd (Nat.le_of_dvd (by norm_num) h') (by norm_num)

theorem eq_zero_or_one_or_neg_one (hK : Nat.card K = 3) (x : K) : x = 0 ∨ x = 1 ∨ x = -1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := two_ne_zero_char_three
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have h0m : (0 : K) ≠ -1 := by
    intro h; exact one_ne_zero (neg_eq_zero.1 h.symm)
  have h1m : (1 : K) ≠ -1 := by
    intro h; exact h2 (by linear_combination h)
  have hcard : ({0, 1, -1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_eq_three.2 ⟨0, 1, -1, h01, h0m, h1m, rfl⟩, ← Nat.card_eq_fintype_card, hK]
  have huniv : ({0, 1, -1} : Finset K) = Finset.univ := Finset.eq_univ_of_card _ hcard
  have hx : x ∈ ({0, 1, -1} : Finset K) := by rw [huniv]; exact Finset.mem_univ x
  simpa using hx

theorem orderOf_two_zmod_five_ge_three : 3 ≤ orderOf (2 : ZMod 5) := by
  have h : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  omega

theorem outer_involution_inverts_order_five (hK : Nat.card K = 3)
    (hsimple : IsSimpleGroup (StatedProj (StatedSp 3 K)))
    (hcent : Subgroup.center (StatedProj (StatedSp 3 K)) = ⊥)
    (ψ : MulAut (StatedProj (StatedSp 3 K)))
    (hψ : ψ ∉ (MulAut.conj : StatedProj (StatedSp 3 K) →*
      MulAut (StatedProj (StatedSp 3 K))).range) (hψ2 : ψ * ψ = 1) :
    ∃ x : StatedProj (StatedSp 3 K), orderOf x = 5 ∧ ψ x = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero_char_three
  have hK1 : Nat.card K = 3 ^ 1 := by rw [pow_one]; exact hK
  obtain ⟨A, σ, hσ⟩ := exists_conjAut_fieldAut (by norm_num : (3 : ℕ) ≠ 2) hK1
    (by norm_num : 2 ≤ 3) ψ
  have hσ1 : σ = 1 := by
    have hAut : Nat.card (K ≃+* K) = 1 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : Nat.Prime 3) K
        hK1).1
    have := (Nat.card_eq_one_iff_unique.1 hAut).1
    exact Subsingleton.elim _ _
  rw [hσ1, map_one, mul_one] at hσ
  subst hσ
  have hμ : ¬ IsSquare ((multiplier 3 K A : Kˣ) : K) := fun hs =>
    hψ (conjAut_mem_range_of_isSquare A hs)
  have hAA : conjAut 3 K (A * A) = 1 := by rw [map_mul]; exact hψ2
  obtain ⟨lam, hlam⟩ := exists_scalar_of_conjAut_trivial_three h2 (A * A) hAA
  set a : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    ((A : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with ha
  have hA2 : a * a = lam • 1 := by
    rw [← hlam]
    rfl
  set μ : K := ((multiplier 3 K A : Kˣ) : K) with hμdef
  have hA : aᵀ * formJ 3 K * a = μ • formJ 3 K := multiplier_spec A
  have haa : ∀ x, a *ᵥ (a *ᵥ x) = lam • x := by
    intro x
    rw [Matrix.mulVec_mulVec, hA2, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hlam : lam * lam = μ * μ := by
    obtain ⟨v, w, hvw⟩ := exists_symB_one (K := K) (r := 3)
    have h := symB_similitude hA (a *ᵥ v) (a *ᵥ w)
    rw [haa, haa, symB_smul_left, symB_smul_right, symB_similitude hA v w, hvw] at h
    linear_combination h
  have hcase : lam = μ ∨ lam = -μ := by
    have : (lam - μ) * (lam + μ) = 0 := by linear_combination hlam
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hcase with hlm | hlm
  · exfalso
    exact no_similitude_sq_eq_mul_of_odd h2 (by decide) hsimple hcent A
      (by show a * a = μ • 1; rw [hA2, hlm]) hμ
  · have hμ0 : μ ≠ 0 := Units.ne_zero _
    have hμ1 : μ ≠ 1 := fun h => hμ ⟨1, by rw [h]; ring⟩
    have hμm : μ = -1 := by
      rcases eq_zero_or_one_or_neg_one hK μ with h | h | h
      · exact absurd h hμ0
      · exact absurd h hμ1
      · exact h
    have hlam1 : lam = 1 := by rw [hlm, hμm]; ring
    refine exists_inverted_of_involutive h2 A ?_ ?_
    · rw [hA2, hlam1, one_smul]
    · rw [hA, hμm]

end Outer

section Centre

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable [NeZero r]

theorem transvections_not_commute :
    let i0 : Fin r := ⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩
    (QuotientGroup.mk (Eel (Pi.single (Sum.inl i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1
        (form_zero_left _)) : StatedProj (StatedSp r K)) *
      QuotientGroup.mk (Eel (Pi.single (Sum.inr i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1
        (form_zero_left _)) ≠
    QuotientGroup.mk (Eel (Pi.single (Sum.inr i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1
        (form_zero_left _)) *
      QuotientGroup.mk (Eel (Pi.single (Sum.inl i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1
        (form_zero_left _)) := by
  intro i0 hc
  set Tv := Eel (Pi.single (Sum.inl i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1 (form_zero_left _) with hTv
  set Tw := Eel (Pi.single (Sum.inr i0) (1 : K) : Fin r ⊕ Fin r → K) 0 1 (form_zero_left _) with hTw
  have h1' : (QuotientGroup.mk (Tv * Tw * (Tw * Tv)⁻¹) : StatedProj (StatedSp r K)) = 1 := by
    have : (QuotientGroup.mk (Tv * Tw) : StatedProj (StatedSp r K)) =
        QuotientGroup.mk (Tw * Tv) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact hc
    rw [QuotientGroup.mk_mul, this, QuotientGroup.mk_inv]
    exact mul_inv_cancel _
  obtain ⟨ε, hε, hm⟩ := pm_of_mk_eq_one h1'
  have e : Tv * Tw = (Tv * Tw * (Tw * Tv)⁻¹) * (Tw * Tv) := by group
  have key : ∀ w, mat r K Tv *ᵥ (mat r K Tw *ᵥ w) = ε • (mat r K Tw *ᵥ (mat r K Tv *ᵥ w)) := by
    intro w
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← map_mul, ← map_mul, e, map_mul, hm,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]
  have h := key (Pi.single (Sum.inl i0) 1)
  have hee := form_e_e (K := K) i0 i0
  have hef : form (Pi.single (Sum.inl i0) (1 : K) : Fin r ⊕ Fin r → K) (Pi.single (Sum.inr i0) 1) = 1 := by
    rw [form_e_f]; simp
  have hfe : form (Pi.single (Sum.inr i0) (1 : K) : Fin r ⊕ Fin r → K) (Pi.single (Sum.inl i0) 1) = -1 := by
    rw [form_f_e]; simp
  have hff := form_f_f (K := K) i0 i0
  rw [hTv, hTw, Eel_mulVec, Eel_mulVec, Eel_mulVec, Eel_mulVec] at h
  simp only [form_add_left, form_smul_left, form_zero_right, form_zero_left, hee, hef, hfe,
    zero_smul, add_zero, one_mul, mul_zero] at h
  have h0 := congrFun h (Sum.inl i0)
  simp at h0
  rcases hε with rfl | rfl
  · exact zero_ne_one h0
  · exact one_ne_zero (neg_eq_zero.1 h0.symm)

end Centre

section Final

variable [Finite K] [CharP K 3]

omit [Finite K] [CharP K 3] in
theorem isSimpleGroup_psp63 (hK : Nat.card K = 3) : IsSimpleGroup (StatedProj (StatedSp 3 K)) :=
  CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 3 (by norm_num)
    (Or.inr (Or.inl ⟨hK, by norm_num⟩))

omit [Finite K] [CharP K 3] in
theorem center_psp63_eq_bot (hK : Nat.card K = 3) :
    Subgroup.center (StatedProj (StatedSp 3 K)) = ⊥ := by
  have hsimple := isSimpleGroup_psp63 hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (StatedProj (StatedSp 3 K))) with h | h
  · exact h
  · exfalso
    have hmem : (QuotientGroup.mk (Eel (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) :
        Fin 3 ⊕ Fin 3 → K) 0 1 (form_zero_left _)) : StatedProj (StatedSp 3 K)) ∈
        Subgroup.center (StatedProj (StatedSp 3 K)) := by
      rw [h]; exact Subgroup.mem_top _
    exact transvections_not_commute (K := K) (r := 3)
      ((Subgroup.mem_center_iff.mp hmem _).symm)

theorem houter_psp63 (hK : Nat.card K = 3) :
    ∀ ψ : MulAut (StatedProj (StatedSp 3 K)), ψ ∉ (MulAut.conj : StatedProj (StatedSp 3 K) →*
        MulAut (StatedProj (StatedSp 3 K))).range → ψ * ψ = 1 →
      ∃ (p' : ℕ) (_ : Fact p'.Prime) (x : StatedProj (StatedSp 3 K)), p' ≠ 2 ∧
        3 ≤ orderOf (2 : ZMod p') ∧ orderOf x = p' ∧ ψ x = x⁻¹ := by
  intro ψ hψ hψ2
  obtain ⟨x, hx, hψx⟩ := outer_involution_inverts_order_five hK (isSimpleGroup_psp63 hK)
    (center_psp63_eq_bot hK) ψ hψ hψ2
  exact ⟨5, ⟨by norm_num⟩, x, by norm_num, orderOf_two_zmod_five_ge_three, hx, hψx⟩

end Final

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
