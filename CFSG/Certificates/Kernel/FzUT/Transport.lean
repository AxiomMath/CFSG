module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319SpecA
public import CFSG.Certificates.Kernel.FzUT.Basic

public section

namespace CFSG.KC.FzUT

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.FritzII

@[expose] def cj (β σ : MulAut FzUT) : MulAut FzUT := β.symm.trans (σ.trans β)

theorem cj_apply (β σ : MulAut FzUT) (x : FzUT) : cj β σ x = β (σ (β.symm x)) := rfl

theorem cj_beta (β σ : MulAut FzUT) (x : FzUT) : cj β σ (β x) = β (σ x) := by
  rw [cj_apply, MulEquiv.symm_apply_apply]

theorem inZ_map' (β : MulAut FzUT) {z : FzUT} (h : FzInZ z) : FzInZ (β z) := kcInZ_map β h

variable (β : MulAut FzUT) (hβ : ∀ x, β (fzRho0 x) = fzRho0 (β x))
include hβ

theorem symm_rho (x : FzUT) : β.symm (fzRho0 x) = fzRho0 (β.symm x) := by
  apply β.injective
  rw [MulEquiv.apply_symm_apply, hβ, MulEquiv.apply_symm_apply]

omit hβ in
theorem card_fix_cj (σ : MulAut FzUT) :
    (Finset.univ.filter fun x : FzUT => cj β σ x = x).card =
      (Finset.univ.filter fun x : FzUT => σ x = x).card := by
  have hset : (Finset.univ.filter fun x : FzUT => cj β σ x = x) =
      (Finset.univ.filter fun x : FzUT => σ x = x).map β.toEquiv.toEmbedding := by
    ext x
    obtain ⟨y, rfl⟩ := β.surjective x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
    rw [cj_beta, β.injective.eq_iff]
    change σ y = y ↔ σ (β.symm (β y)) = β.symm (β y)
    rw [MulEquiv.symm_apply_apply]
  rw [hset, Finset.card_map]

theorem validTriple_cj {t s l : MulAut FzUT} (h : FzValidTriple t s l) :
    FzValidTriple (cj β t) (cj β s) (cj β l) where
  t_sq x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.t_sq, MulEquiv.apply_symm_apply]
  t_rho x := by rw [cj_apply, cj_apply, symm_rho β hβ, h.t_rho, hβ]
  t_Z x := by
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [cj_beta, ← map_inv, ← map_mul]
    exact inZ_map' β (h.t_Z y)
  t_fix := by rw [card_fix_cj, h.t_fix]
  s_sq x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.s_sq, MulEquiv.apply_symm_apply]
  s_rho x := by rw [cj_apply, cj_apply, symm_rho β hβ, h.s_rho, hβ]
  s_ne := by
    obtain ⟨x, hx⟩ := h.s_ne
    exact ⟨β x, by rw [cj_beta]; exact fun h' => hx (β.injective h')⟩
  ts x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.ts]
  s_inv x hx := by
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [cj_beta] at hx ⊢
    rw [h.s_inv y (β.injective hx), map_inv]
  s_fix x := by
    obtain ⟨y, rfl⟩ := β.surjective x
    rw [cj_beta, ← map_inv, ← map_mul, cj_beta, h.s_fix]
  l_sq x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.l_sq, MulEquiv.apply_symm_apply]
  l_rho x := by rw [cj_apply, cj_apply, symm_rho β hβ, h.l_rho, hβ, hβ]
  tl x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.tl]
  sl x := by simp only [cj_apply, MulEquiv.symm_apply_apply, h.sl]
  l_Z := by
    obtain ⟨z, hz, hlz⟩ := h.l_Z
    exact ⟨β z, inZ_map' β hz, by rw [cj_beta]; exact fun h' => hlz (β.injective h')⟩
  l_Q := by
    obtain ⟨x, hx⟩ := h.l_Q
    refine ⟨β x, ?_⟩
    rw [cj_beta, ← map_inv, ← map_mul, cj_beta]
    exact fun h' => hx (β.injective h')

omit hβ

theorem validX_cj {t l : MulAut FzUT} {x₁ : FzUT} (h : FzValidX t l x₁) :
    FzValidX (cj β t) (cj β l) (β x₁) where
  fix := by rw [cj_beta, h.fix]
  x1_four := by rw [← map_pow, h.x1_four, map_one]
  x2_four := by rw [cj_beta, ← map_pow, h.x2_four, map_one]
  comm := by rw [cj_beta, ← map_mul, ← map_mul, h.comm]
  gen y := by
    obtain ⟨y, rfl⟩ := β.surjective y
    rw [cj_beta, cj_beta, β.injective.eq_iff, h.gen y]
    constructor
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, by rw [hij, map_mul, map_pow, map_pow]⟩
    · rintro ⟨i, j, hij⟩
      exact ⟨i, j, β.injective (by rw [hij, map_mul, map_pow, map_pow])⟩

theorem fzAp_cj (b : ZMod 2) (σ : MulAut FzUT) (q : FzUT) :
    fzAp b (cj β σ) q = β (fzAp b σ (β.symm q)) := by
  unfold fzAp
  split_ifs
  · rw [MulEquiv.apply_symm_apply]
  · rfl

theorem fzAct_cj (t s l : MulAut FzUT) (v : FzV) (q : FzUT) :
    fzAct (cj β t) (cj β s) (cj β l) v q = β (fzAct t s l v (β.symm q)) := by
  simp only [fzAct, fzAp_cj, MulEquiv.symm_apply_apply]

@[expose] def phiE : FzElt ≃ FzElt where
  toFun x := (β.symm x.1, x.2)
  invFun x := (β x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem phiE_apply (x : FzElt) : phiE β x = (β.symm x.1, x.2) := rfl

theorem phiE_symm_apply (x : FzElt) : (phiE β).symm x = (β x.1, x.2) := rfl

theorem phi_mul (t s l : MulAut FzUT) (x y : FzElt) :
    phiE β (fzMulC (cj β t) (cj β s) (cj β l) x y) =
      fzMulC t s l (phiE β x) (phiE β y) := by
  simp only [phiE_apply, fzMulC, fzAct_cj, map_mul, MulEquiv.symm_apply_apply]

theorem phi_symm_mul (t s l : MulAut FzUT) (x y : FzElt) :
    (phiE β).symm (fzMulC t s l x y) =
      fzMulC (cj β t) (cj β s) (cj β l) ((phiE β).symm x) ((phiE β).symm y) := by
  apply (phiE β).injective
  rw [Equiv.apply_symm_apply, phi_mul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem reach_map {X Y : Type} {m : X → X → X} {one : X} {m' : Y → Y → Y} {one' : Y} (f : X → Y)
    (hf : ∀ a b, f (m a b) = m' (f a) (f b)) (h1 : f one = one') {S : Set X} {S' : Set Y}
    (hS : ∀ g ∈ S, f g ∈ S') {e : X} (h : FzReach m one S e) : FzReach m' one' S' (f e) := by
  induction h with
  | one => rw [h1]; exact FzReach.one
  | gen hg => exact FzReach.gen (hS _ hg)
  | mul _ _ iha ihb => rw [hf]; exact FzReach.mul iha ihb

theorem q8_map {X Y : Type} {m : X → X → X} {one : X} {m' : Y → Y → Y} {one' : Y} (f : X → Y)
    (hf : ∀ a b, f (m a b) = m' (f a) (f b)) (h1 : f one = one') (hinj : Function.Injective f)
    {a b : X} (h : FzQ8 m one a b) : FzQ8 m' one' (f a) (f b) where
  four := by simp only [← hf, h.four, h1]
  sq := by simp only [← hf, h.sq]
  conj := by simp only [← hf, h.conj]
  ne hc := h.ne (hinj (by rw [hf, hc, h1]))

theorem pair_map {X Y : Type} {m : X → X → X} {m' : Y → Y → Y} (f : X → Y)
    (hf : ∀ a b, f (m a b) = m' (f a) (f b)) {a b c d : X}
    (h : ∀ u ∈ ({a, b} : Set X), ∀ w ∈ ({c, d} : Set X), m u w = m w u) :
    ∀ u ∈ ({f a, f b} : Set Y), ∀ w ∈ ({f c, f d} : Set Y), m' u w = m' w u := by
  intro u hu w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hw
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;>
    rw [← hf, ← hf, h _ (by simp) _ (by simp)]

theorem shapeAt_map {X Y : Type} {m : X → X → X} {one : X} {m' : Y → Y → Y} {one' : Y}
    (f : X → Y) (hf : ∀ a b, f (m a b) = m' (f a) (f b)) (h1 : f one = one')
    (hinj : Function.Injective f) (hsurj : Function.Surjective f)
    {a11 a12 a21 a22 a31 a32 y : X} (h : FzShapeAt m one a11 a12 a21 a22 a31 a32 y) :
    FzShapeAt m' one' (f a11) (f a12) (f a21) (f a22) (f a31) (f a32) (f y) where
  quat₁ := q8_map f hf h1 hinj h.quat₁
  quat₂ := q8_map f hf h1 hinj h.quat₂
  quat₃ := q8_map f hf h1 hinj h.quat₃
  sq_eq := by simp only [← hf, h.sq_eq]
  comm₁₂ := pair_map f hf h.comm₁₂
  comm₁₃ := pair_map f hf h.comm₁₃
  comm₂₃ := pair_map f hf h.comm₂₃
  y_sq := by simp only [← hf, h.y_sq, h1]
  y_a11 := by simp only [← hf, h.y_a11]
  y_a12 := by simp only [← hf, h.y_a12]
  y_a31 := by simp only [← hf, h.y_a31]
  y_a32 := by simp only [← hf, h.y_a32]
  gen e := by
    obtain ⟨e, rfl⟩ := hsurj e
    refine reach_map f hf h1 ?_ (h.gen e)
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem shape_cj {t s l : MulAut FzUT} {x₁ : FzUT}
    (h : FzShape (cj β t) (cj β s) (cj β l) (β x₁)) : FzShape t s l x₁ := by
  obtain ⟨r₁, r₃, hS⟩ := h
  refine ⟨β.symm r₁, β.symm r₃, ?_⟩
  have h1 : phiE β fzOneC = fzOneC := by simp [phiE_apply, fzOneC]
  have key := shapeAt_map (phiE β) (phi_mul β t s l) h1 (phiE β).injective (phiE β).surjective hS
  simp only [phi_mul] at key
  simpa only [phiE_apply, cj_beta, MulEquiv.symm_apply_apply, map_inv, map_mul,
    map_one] using key

theorem inW_cj (t : MulAut FzUT) (x : FzElt) : fzInW (cj β t) ((phiE β).symm x) ↔ fzInW t x := by
  simp only [fzInW, phiE_symm_apply, cj_beta, β.injective.eq_iff]

theorem autW_cj {t s l : MulAut FzUT} (h : FzAutW (cj β t) (cj β s) (cj β l)) :
    FzAutW t s l := by
  intro α hα x
  let α' : FzElt ≃ FzElt := (phiE β).trans (α.trans (phiE β).symm)
  have hα' : ∀ x y, α' (fzMulC (cj β t) (cj β s) (cj β l) x y) =
      fzMulC (cj β t) (cj β s) (cj β l) (α' x) (α' y) := by
    intro x y
    change (phiE β).symm (α (phiE β _)) = _
    rw [phi_mul, hα, phi_symm_mul]
    rfl
  have key := h α' hα' ((phiE β).symm x)
  have e : α' ((phiE β).symm x) = (phiE β).symm (α x) := by
    change (phiE β).symm (α (phiE β ((phiE β).symm x))) = _
    rw [Equiv.apply_symm_apply]
  rw [e, inW_cj, inW_cj] at key
  exact key

end CFSG.KC.FzUT
