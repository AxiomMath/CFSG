module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Basic

public section

open Matrix LinearMap
open scoped commutatorElement

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

section Basic
variable {V : Type} [AddCommGroup V] {K : Type} [Field K] [Module K V]

@[expose] noncomputable def qd (B : LinearMap.BilinForm K V) (x : V) : K := (2:K)⁻¹ * B x x

@[expose] noncomputable def eichLin (B : LinearMap.BilinForm K V) (a w : V) : Module.End K V :=
  LinearMap.id + (B a).smulRight w - (B w).smulRight a - (qd B w) • (B a).smulRight a

theorem eichLin_apply (B : LinearMap.BilinForm K V) (a w x : V) :
    eichLin B a w x = x + B a x • w - B w x • a - (qd B w * B a x) • a := by
  simp [eichLin, mul_smul]

theorem qd_add (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) (w w' : V) :
    qd B (w + w') = qd B w + qd B w' + B w w' := by
  simp only [qd, map_add, LinearMap.add_apply]
  rw [hs w' w]
  field_simp
  ring

theorem qd_smul (B : LinearMap.BilinForm K V) (c : K) (w : V) : qd B (c • w) = c ^ 2 * qd B w := by
  simp only [qd, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem eichLin_mul (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0)
    {a w w' : V} (haa : B a a = 0) (haw : B a w = 0) (haw' : B a w' = 0) :
    eichLin B a w * eichLin B a w' = eichLin B a (w + w') := by
  have hwa : B w a = 0 := by rw [hs]; exact haw
  have hwa' : B w' a = 0 := by rw [hs]; exact haw'
  ext1 x
  show eichLin B a w (eichLin B a w' x) = _
  simp only [eichLin_apply, map_add, map_sub, map_smul, LinearMap.add_apply, haa, haw', hwa, qd_add B hs h2]
  module

theorem eichLin_zero (B : LinearMap.BilinForm K V) (a : V) : eichLin B a 0 = 1 := by
  ext1 x
  simp [eichLin_apply, qd]

theorem eichLin_scale (B : LinearMap.BilinForm K V) (c c' : K) (a w : V) :
    eichLin B (c • a) (c' • w) = eichLin B a ((c * c') • w) := by
  ext1 x
  simp only [eichLin_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, qd_smul, smul_smul]
  module

theorem eichLin_swap (B : LinearMap.BilinForm K V) {a w : V}
    (haa : B a a = 0) (hww : B w w = 0) :
    eichLin B a w = eichLin B w (-a) := by
  ext1 x
  simp only [eichLin_apply, map_neg, LinearMap.neg_apply, qd, haa, hww]
  simp
  module

theorem eichLin_isom (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0)
    {a w : V} (haa : B a a = 0) (haw : B a w = 0) (x y : V) :
    B (eichLin B a w x) (eichLin B a w y) = B x y := by
  have hwa : B w a = 0 := by rw [hs]; exact haw
  have hqw : B w w = 2 * qd B w := by simp only [qd]; field_simp
  simp only [eichLin_apply, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, haa, haw, hwa, hqw]
  rw [hs x a, hs x w]
  ring

@[expose] noncomputable def torLin (B : LinearMap.BilinForm K V) (a a' : V) (α : K) : Module.End K V :=
  LinearMap.id + (α - 1) • (B a').smulRight a + (α⁻¹ - 1) • (B a).smulRight a'

theorem torLin_apply (B : LinearMap.BilinForm K V) (a a' : V) (α : K) (x : V) :
    torLin B a a' α x = x + ((α - 1) * B a' x) • a + ((α⁻¹ - 1) * B a x) • a' := by
  simp [torLin, mul_smul]

theorem torLin_mul (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) {a a' : V}
    (haa : B a a = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1) {α β : K} (hα : α ≠ 0)
    (hβ : β ≠ 0) :
    torLin B a a' α * torLin B a a' β = torLin B a a' (α * β) := by
  have ha'a : B a' a = 1 := by rw [hs]; exact haa'
  ext1 x
  show torLin B a a' α (torLin B a a' β x) = _
  simp only [torLin_apply, map_add, map_smul, haa, ha'a', haa', ha'a]
  have : (α * β)⁻¹ = α⁻¹ * β⁻¹ := mul_inv α β
  rw [this]
  match_scalars <;> field_simp <;> ring

theorem torLin_one (B : LinearMap.BilinForm K V) (a a' : V) : torLin B a a' 1 = 1 := by
  ext1 x
  simp [torLin_apply]

theorem torLin_isom (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) {a a' : V}
    (haa : B a a = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1) {α : K} (hα : α ≠ 0) (x y : V) :
    B (torLin B a a' α x) (torLin B a a' α y) = B x y := by
  have ha'a : B a' a = 1 := by rw [hs]; exact haa'
  simp only [torLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa, ha'a', haa', ha'a]
  rw [hs x a, hs x a']
  field_simp
  ring

theorem torLin_a (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) {a a' : V}
    (haa : B a a = 0) (haa' : B a a' = 1) (α : K) : torLin B a a' α a = α • a := by
  have ha'a : B a' a = 1 := by rw [hs]; exact haa'
  rw [torLin_apply, haa, ha'a]
  module

theorem torLin_w (B : LinearMap.BilinForm K V) {a a' w : V}
    (haw : B a w = 0) (ha'w : B a' w = 0) (α : K) : torLin B a a' α w = w := by
  rw [torLin_apply, haw, ha'w]
  simp

theorem exists_dual_one_zero (B : LinearMap.BilinForm K V)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {a w : V}
    (hind : ∀ p r : K, p • a + r • w = 0 → p = 0 ∧ r = 0) :
    ∃ x, B a x = 1 ∧ B w x = 0 := by
  by_contra hcon
  push Not at hcon
  have h1 : ∀ x, B w x = 0 → B a x = 0 := by
    intro x hx
    by_contra hne
    apply hcon ((B a x)⁻¹ • x)
    · simp [hne]
    · simp [hx]
  have hw0 : w ≠ 0 := by
    intro h
    have := hind 0 1 (by simp [h])
    exact one_ne_zero this.2
  obtain ⟨y, hy⟩ : ∃ y, B w y ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hw0 (hnd w hh)
  have h2 : ∀ x, B a x = (B a y / B w y) * B w x := by
    intro x
    have := h1 (x - (B w x / B w y) • y) (by simp [map_sub]; field_simp; ring)
    simp only [map_sub, map_smul, smul_eq_mul] at this
    have h' : B a x = B w x / B w y * B a y := sub_eq_zero.mp this
    rw [h']
    ring
  have h3 : a - (B a y / B w y) • w = 0 := by
    apply hnd
    intro x
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [h2 x]
    ring
  have := hind 1 (-(B a y / B w y)) (by rw [neg_smul, one_smul, ← sub_eq_add_neg]; exact h3)
  exact one_ne_zero this.1

theorem exists_partner (B : LinearMap.BilinForm K V) (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {a w : V} (haa : B a a = 0) (haw : B a w = 0)
    (hind : ∀ p r : K, p • a + r • w = 0 → p = 0 ∧ r = 0) :
    ∃ a', B a a' = 1 ∧ B a' a' = 0 ∧ B a' w = 0 := by
  obtain ⟨x, hx1, hx2⟩ := exists_dual_one_zero B hnd hind
  refine ⟨x - qd B x • a, ?_, ?_, ?_⟩
  · simp [map_sub, haa, hx1]
  · have hxa : B x a = 1 := by rw [hs]; exact hx1
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, haa, hxa, qd]
    field_simp
    rw [hx1]
    ring
  · have hxw : B x w = 0 := by rw [hs]; exact hx2
    simp [map_sub, haw, hxw]

end Basic

section GLsec

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem gl_ext {A A' : Matrix ι ι K} (h : ∀ x, A *ᵥ x = A' *ᵥ x) : A = A' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

@[expose] def isomGroup (B : LinearMap.BilinForm K (ι → K)) : Subgroup (GL ι K) where
  carrier := {A | ∀ x y, B ((A : Matrix ι ι K) *ᵥ x) ((A : Matrix ι ι K) *ᵥ y) = B x y}
  mul_mem' := by
    intro A A' hA hA' x y
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hA, hA']
  one_mem' := by intro x y; simp
  inv_mem' := by
    intro A hA x y
    have h1 : ∀ z, (A : Matrix ι ι K) *ᵥ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec]; simp
    have := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y)
    rw [h1, h1] at this
    exact this.symm

@[expose] def omegaGroup (B : LinearMap.BilinForm K (ι → K)) : Subgroup (GL ι K) :=
  ⁅isomGroup B, isomGroup B⁆

theorem omegaGroup_le (B : LinearMap.BilinForm K (ι → K)) : omegaGroup B ≤ isomGroup B := by
  rw [omegaGroup, Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact (isomGroup B).mul_mem ((isomGroup B).mul_mem ((isomGroup B).mul_mem h₁ h₂)
    ((isomGroup B).inv_mem h₁)) ((isomGroup B).inv_mem h₂)

theorem mem_isomGroup_iff {B : LinearMap.BilinForm K (ι → K)} {A : GL ι K} :
    A ∈ isomGroup B ↔ ∀ x y, B ((A : Matrix ι ι K) *ᵥ x) ((A : Matrix ι ι K) *ᵥ y) = B x y :=
  Iff.rfl

open Classical in
@[expose] noncomputable def endU (f : Module.End K (ι → K)) : GL ι K :=
  if h : IsUnit (LinearMap.toMatrix' f) then h.unit else 1

theorem isUnit_toMatrix' {f : Module.End K (ι → K)} (hf : IsUnit f) :
    IsUnit (LinearMap.toMatrix' f) := by
  obtain ⟨u, rfl⟩ := hf
  refine ⟨⟨LinearMap.toMatrix' (u : Module.End K (ι → K)), LinearMap.toMatrix' (↑u⁻¹ : Module.End K (ι → K)), ?_, ?_⟩, rfl⟩
  · rw [← LinearMap.toMatrix'_mul]; simp
  · rw [← LinearMap.toMatrix'_mul]; simp

theorem endU_val {f : Module.End K (ι → K)} (hf : IsUnit f) :
    ((endU f : GL ι K) : Matrix ι ι K) = LinearMap.toMatrix' f := by
  simp [endU, isUnit_toMatrix' hf]

theorem endU_mulVec {f : Module.End K (ι → K)} (hf : IsUnit f) (x : ι → K) :
    ((endU f : GL ι K) : Matrix ι ι K) *ᵥ x = f x := by
  rw [endU_val hf, LinearMap.toMatrix'_mulVec]

theorem endU_mul {f g : Module.End K (ι → K)} (hf : IsUnit f) (hg : IsUnit g) :
    endU f * endU g = endU (f * g) := by
  apply Units.ext
  rw [endU_val (hf.mul hg), Units.val_mul, endU_val hf, endU_val hg, LinearMap.toMatrix'_mul]

theorem endU_one : endU (1 : Module.End K (ι → K)) = 1 := by
  apply Units.ext
  rw [endU_val isUnit_one, Units.val_one]
  exact LinearMap.toMatrix'_one

section Eich

variable (B : LinearMap.BilinForm K (ι → K))

@[expose] noncomputable def eichU (a w : ι → K) : GL ι K := endU (eichLin B a w)

@[expose] noncomputable def torU (a a' : ι → K) (α : K) : GL ι K := endU (torLin B a a' α)

variable {B}

omit [Fintype ι] [DecidableEq ι] in
theorem eichLin_isUnit (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) : IsUnit (eichLin B a w) := by
  have h3 : B a (-w) = 0 := by simp [haw]
  refine ⟨⟨eichLin B a w, eichLin B a (-w), ?_, ?_⟩, rfl⟩
  · rw [eichLin_mul B hs h2 haa haw h3, add_neg_cancel, eichLin_zero]
  · rw [eichLin_mul B hs h2 haa h3 haw, neg_add_cancel, eichLin_zero]

theorem eichU_mulVec (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) (x : ι → K) :
    ((eichU B a w : GL ι K) : Matrix ι ι K) *ᵥ x = eichLin B a w x :=
  endU_mulVec (eichLin_isUnit hs h2 haa haw) x

theorem eichU_mul (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w w' : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) (haw' : B a w' = 0) :
    eichU B a w * eichU B a w' = eichU B a (w + w') := by
  unfold eichU
  rw [endU_mul (eichLin_isUnit hs h2 haa haw) (eichLin_isUnit hs h2 haa haw'),
    eichLin_mul B hs h2 haa haw haw']

theorem eichU_zero (a : ι → K) : eichU B a 0 = 1 := by
  unfold eichU
  rw [eichLin_zero]
  exact endU_one

theorem eichU_inv (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) : (eichU B a w)⁻¹ = eichU B a (-w) := by
  apply inv_eq_of_mul_eq_one_right
  rw [eichU_mul hs h2 haa haw (by simp [haw]), add_neg_cancel, eichU_zero]

theorem eichU_pow (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) (n : ℕ) : eichU B a w ^ n = eichU B a (n • w) := by
  induction n with
  | zero => simp [eichU_zero]
  | succ n ih =>
    have h3 : B a (n • w) = 0 := by rw [map_nsmul, haw, smul_zero]
    rw [pow_succ, ih, eichU_mul hs h2 haa h3 haw, succ_nsmul]

theorem eichU_mem (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) : eichU B a w ∈ isomGroup B := by
  intro x y
  rw [eichU_mulVec hs h2 haa haw, eichU_mulVec hs h2 haa haw]
  exact eichLin_isom B hs h2 haa haw x y

theorem eichU_scale (c c' : K) (a w : ι → K) :
    eichU B (c • a) (c' • w) = eichU B a ((c * c') • w) := by
  unfold eichU
  rw [eichLin_scale]

theorem eichU_swap {a w : ι → K}
    (haa : B a a = 0) (hww : B w w = 0) : eichU B a w = eichU B w (-a) := by
  unfold eichU
  rw [eichLin_swap B haa hww]

theorem eichU_conj (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {g : GL ι K} (hg : g ∈ isomGroup B)
    {a w : ι → K} (haa : B a a = 0) (haw : B a w = 0) :
    g * eichU B a w * g⁻¹ = eichU B ((g : Matrix ι ι K) *ᵥ a) ((g : Matrix ι ι K) *ᵥ w) := by
  have hg' : g⁻¹ ∈ isomGroup B := (isomGroup B).inv_mem hg
  have hgaa : B ((g : Matrix ι ι K) *ᵥ a) ((g : Matrix ι ι K) *ᵥ a) = 0 := by rw [hg, haa]
  have hgaw : B ((g : Matrix ι ι K) *ᵥ a) ((g : Matrix ι ι K) *ᵥ w) = 0 := by rw [hg, haw]
  apply Units.ext
  apply gl_ext
  intro x
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    eichU_mulVec hs h2 haa haw, eichU_mulVec hs h2 hgaa hgaw]
  have h1 : (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec]; simp
  have hB : ∀ u : ι → K, B ((g : Matrix ι ι K) *ᵥ u) ((g : Matrix ι ι K) *ᵥ u) = B u u := fun u => hg u u
  have h4 : qd B ((g : Matrix ι ι K) *ᵥ w) = qd B w := by simp only [qd, hB]
  have h5 : B a (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = B ((g : Matrix ι ι K) *ᵥ a) x := by
    rw [← hg a (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x), h1]
  have h6 : B w (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) = B ((g : Matrix ι ι K) *ᵥ w) x := by
    rw [← hg w (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x), h1]
  rw [eichLin_apply, eichLin_apply, h4, ← h5, ← h6, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, h1]

omit [Fintype ι] [DecidableEq ι] in
theorem torLin_isUnit (hs : ∀ x y, B x y = B y x) {a a' : ι → K}
    (haa : B a a = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1) {α : K} (hα : α ≠ 0) :
    IsUnit (torLin B a a' α) := by
  refine ⟨⟨torLin B a a' α, torLin B a a' α⁻¹, ?_, ?_⟩, rfl⟩
  · rw [torLin_mul B hs haa ha'a' haa' hα (inv_ne_zero hα), mul_inv_cancel₀ hα, torLin_one]
  · rw [torLin_mul B hs haa ha'a' haa' (inv_ne_zero hα) hα, inv_mul_cancel₀ hα, torLin_one]

theorem torU_mulVec (hs : ∀ x y, B x y = B y x) {a a' : ι → K}
    (haa : B a a = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1) {α : K} (hα : α ≠ 0)
    (x : ι → K) :
    ((torU B a a' α : GL ι K) : Matrix ι ι K) *ᵥ x = torLin B a a' α x :=
  endU_mulVec (torLin_isUnit hs haa ha'a' haa' hα) x

theorem torU_mem (hs : ∀ x y, B x y = B y x) {a a' : ι → K}
    (haa : B a a = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1) {α : K} (hα : α ≠ 0) :
    torU B a a' α ∈ isomGroup B := by
  intro x y
  rw [torU_mulVec hs haa ha'a' haa' hα, torU_mulVec hs haa ha'a' haa' hα]
  exact torLin_isom B hs haa ha'a' haa' hα x y

theorem eichU_mem_commutator (hs : ∀ x y, B x y = B y x) (h2 : (2:K) ≠ 0) {a a' w : ι → K}
    (haa : B a a = 0) (haw : B a w = 0) (ha'a' : B a' a' = 0) (haa' : B a a' = 1)
    (ha'w : B a' w = 0) : eichU B a w ∈ omegaGroup B := by
  have ht := torU_mem hs haa ha'a' haa' h2
  have hU := eichU_mem hs h2 haa haw
  have hc := Subgroup.commutator_mem_commutator ht hU
  have hta : ((torU B a a' 2 : GL ι K) : Matrix ι ι K) *ᵥ a = (2:K) • a := by
    rw [torU_mulVec hs haa ha'a' haa' h2, torLin_a B hs haa haa']
  have htw : ((torU B a a' 2 : GL ι K) : Matrix ι ι K) *ᵥ w = w := by
    rw [torU_mulVec hs haa ha'a' haa' h2, torLin_w B haw ha'w]
  have hconj := eichU_conj hs h2 ht haa haw
  have hsc := eichU_scale (B := B) 2 1 a w
  rw [one_smul, mul_one] at hsc
  rw [hta, htw, hsc] at hconj
  have h3 : B a ((2:K) • w) = 0 := by rw [map_smul, haw, smul_zero]
  have h4 : B a (-w) = 0 := by rw [map_neg, haw, neg_zero]
  have : ⁅torU B a a' 2, eichU B a w⁆ = eichU B a w := by
    rw [commutatorElement_def, hconj, eichU_inv hs h2 haa haw, eichU_mul hs h2 haa h3 h4]
    congr 1
    rw [two_smul]; abel
  rwa [this] at hc

end Eich

end GLsec

end CFSG.HardMathSupport.Foote.ModuleExclusions
