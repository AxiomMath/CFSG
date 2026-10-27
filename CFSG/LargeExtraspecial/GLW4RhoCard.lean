module

public import CFSG.LargeExtraspecial.GLW4MatB
public import CFSG.LargeExtraspecial.GLW4RhoMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module Matrix QuadraticMap CFSG.LargeExtraspecial.GLR CFSG.GH74.GLS.Bg.Thompson

@[expose] def W8 : List (Fin 4 → ZMod 2) :=
  [![0,0,0,0], ![1,0,0,0], ![0,1,0,0], ![1,1,0,0], ![0,0,0,1], ![1,0,0,1], ![0,1,0,1],
    ![1,1,0,1]]

theorem mem_W8 (v : Fin 4 → ZMod 2) (hv : bN v v = 0) : v ∈ W8 := by revert v; decide

@[expose] def bNf (u v : Fin 4 → ZMod 2) : ZMod 2 :=
  u 0 * v 2 + u 1 * v 3 + u 2 * (v 0 + v 2) + u 3 * v 1

theorem bN_eq_bNf (u v : Fin 4 → ZMod 2) : bN u v = bNf u v := by
  simp [bN, bNf, N, mulVec, dotProduct, Fin.sum_univ_four]

@[expose] def isoTripleB (v₁ v₂ v₃ : Fin 4 → ZMod 2) : Bool :=
  decide (bNf (Pi.single 0 1) v₁ = 0) && decide (bNf (Pi.single 0 1) v₂ = 1) &&
    decide (bNf (Pi.single 0 1) v₃ = 0) && decide (bNf v₁ v₂ = 0) && decide (bNf v₁ v₃ = 1) &&
    decide (bNf v₂ v₃ = 0)

@[expose] def triples : List ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  W8.flatMap fun v₁ => odd8.flatMap fun v₂ => W8.map fun v₃ => (v₁, v₂, v₃)

theorem mem_triples {v₁ v₂ v₃ : Fin 4 → ZMod 2} (h₁ : bN v₁ v₁ = 0) (h₂ : bN v₂ v₂ = 1)
    (h₃ : bN v₃ v₃ = 0) : (v₁, v₂, v₃) ∈ triples := by
  simp only [triples, List.mem_flatMap, List.mem_map]
  exact ⟨v₁, mem_W8 _ h₁, v₂, mem_odd8 _ h₂, v₃, mem_W8 _ h₃, rfl⟩

@[expose] def isoTriples : List ((Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :=
  triples.filter fun t => isoTripleB t.1 t.2.1 t.2.2

theorem isoTriples_length : isoTriples.length = 48 := by decide +kernel

theorem mem_isoTriples_of_isoN {g : Mat} (hg : IsoN g) (hinv : ∃ g', g' * g = 1) :
    (g *ᵥ Pi.single 1 1, g *ᵥ Pi.single 2 1, g *ᵥ Pi.single 3 1) ∈ isoTriples := by
  have h0 := hg.fix_e₀ hinv
  simp only [isoTriples, List.mem_filter, isoTripleB, Bool.and_eq_true, decide_eq_true_eq,
    ← bN_eq_bNf]
  refine ⟨mem_triples ?_ ?_ ?_, ?_⟩
  · rw [hg.bN_apply]; decide
  · rw [hg.bN_apply]; decide
  · rw [hg.bN_apply]; decide
  · rw [← h0]
    simp only [hg.bN_apply]
    decide

theorem mat_eq_of_dot {A B : Mat} (h : ∀ u v, u ⬝ᵥ (A *ᵥ v) = u ⬝ᵥ (B *ᵥ v)) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rwa [single_dotProduct, single_dotProduct, mulVec_single_apply, mulVec_single_apply, one_mul,
    one_mul] at this

theorem isoN_of_forall {g : Mat} (h : ∀ u v, bN (g *ᵥ u) (g *ᵥ v) = bN u v) : IsoN g :=
  mat_eq_of_dot fun u v => by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← dot_mulVec_left]
    exact h u v

theorem card_le_length {α β : Type*} [DecidableEq α] (l : List α) (f : β → α)
    (hf : Function.Injective f) (hmem : ∀ b, f b ∈ l) : Nat.card β ≤ l.length := by
  let g : β → l.toFinset := fun b => ⟨f b, List.mem_toFinset.mpr (hmem b)⟩
  have hg : Function.Injective g := fun a b h => hf (congrArg Subtype.val h)
  calc Nat.card β ≤ Nat.card l.toFinset := Nat.card_le_card_of_injective g hg
    _ = l.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ l.length := List.toFinset_card_le l

theorem le_32_of_pow_le {k : ℕ} (h : 2 ^ k ≤ 48) : 2 ^ k ≤ 32 := by
  have hk : k ≤ 5 := by
    by_contra hk
    have h6 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h6.trans h) (by norm_num)
  calc 2 ^ k ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) hk
    _ = 32 := by norm_num

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

theorem formOf_eq_bN (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hN : gram C e s = N)
    (a a' : C.At) : C.formOf s a a' = bN (e.equivFun a) (e.equivFun a') := by
  rw [formOf_eq_dot_gram e, hN]
  rfl

theorem card_W₀_le (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O} (hN : gram C e s = N) :
    Nat.card {a : C.At // C.formOf s a a = 0} ≤ 8 :=
  (card_le_length W8 (fun a : {a : C.At // C.formOf s a a = 0} => e.equivFun a.1)
    (fun a b hab => Subtype.ext (e.equivFun.injective hab))
    (fun a => mem_W8 _ (by rw [← formOf_eq_bN e hN]; exact a.2))).trans_eq rfl

theorem card_le_of_isPGroup_N (e : Basis (Fin 4) (ZMod 2) C.At) {s : S.O}
    (hN : gram C e s = N) {P : Subgroup (C.At ≃ₗ[ZMod 2] C.At)} (hP : IsPGroup 2 P)
    (hiso : P ≤ TauCeti.BilinForm.isometryGroup (C.formOf s)) : Nat.card P ≤ 32 := by
  classical
  let mat : (C.At ≃ₗ[ZMod 2] C.At) → Mat := fun φ =>
    LinearMap.toMatrix e e (φ : C.At →ₗ[ZMod 2] C.At)
  have hcol : ∀ (φ : C.At ≃ₗ[ZMod 2] C.At) (a : C.At),
      mat φ *ᵥ e.equivFun a = e.equivFun (φ a) := fun φ a => by
    simp only [mat, Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr e e _ a
  have hsingle : ∀ j : Fin 4, e.equivFun (e j) = Pi.single j 1 := fun j => by
    rw [Basis.equivFun_apply, Basis.repr_self, Finsupp.single_eq_pi_single]
  have hinv : ∀ φ : C.At ≃ₗ[ZMod 2] C.At, ∃ g', g' * mat φ = 1 := fun φ =>
    ⟨mat φ.symm, by
      simp only [mat]
      rw [← LinearMap.toMatrix_comp]
      convert LinearMap.toMatrix_id e
      exact LinearMap.ext fun a => φ.symm_apply_apply a⟩
  have hisoN : ∀ φ ∈ P, IsoN (mat φ) := fun φ hφ => isoN_of_forall fun u v => by
    have h1 := (TauCeti.BilinForm.mem_isometryGroup_iff.mp (hiso hφ)) (e.equivFun.symm u)
      (e.equivFun.symm v)
    rw [formOf_eq_bN e hN, formOf_eq_bN e hN, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, ← hcol, ← hcol, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at h1
    exact h1
  let t : P → (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) := fun φ =>
    (mat φ *ᵥ Pi.single 1 1, mat φ *ᵥ Pi.single 2 1, mat φ *ᵥ Pi.single 3 1)
  have ht : Function.Injective t := by
    intro φ ψ h
    simp only [t, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h0 : mat φ *ᵥ Pi.single 0 1 = mat ψ *ᵥ Pi.single 0 1 := by
      rw [(hisoN φ φ.2).fix_e₀ (hinv φ), (hisoN ψ ψ.2).fix_e₀ (hinv ψ)]
    have hall : ∀ j : Fin 4, (φ : C.At ≃ₗ[ZMod 2] C.At) (e j) = (ψ : C.At ≃ₗ[ZMod 2] C.At) (e j) :=
      fun j => by
        apply e.equivFun.injective
        rw [← hcol, ← hcol, hsingle]
        fin_cases j
        exacts [h0, h1, h2, h3]
    exact Subtype.ext (e.ext' hall)
  have hmem : ∀ φ : P, t φ ∈ isoTriples := fun φ =>
    mem_isoTriples_of_isoN (hisoN φ φ.2) (hinv φ)
  have h48 : Nat.card P ≤ 48 := (card_le_length isoTriples t ht hmem).trans_eq isoTriples_length
  have : Finite P := Finite.of_injective t ht
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk] at h48 ⊢
  exact le_32_of_pow_le h48

end CFSG.LargeExtraspecial.GLW4
