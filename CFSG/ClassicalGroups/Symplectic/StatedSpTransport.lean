module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.ClassicalGroups.F2Fixed.Descent
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedInf
public import CFSG.ClassicalGroups.F2Swap
public import CFSG.ClassicalGroups.Alternating.NaturalModuleExtension

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Alternating CFSG.Open CFSG.Open.StatedAPI
open CFSG.ClassicalGroups
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {m : ℕ} {K : Type} [Field K]

section Hom

variable {X : Type*} [Group X]

@[expose] noncomputable def toGsp (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) :
    X →* Gsp (spForm m K) :=
  viaMatrix (StatedSp m K) (spEquiv (m := m) (K := K)) φ hφ

theorem toGsp_app (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (x : X)
    (v : Fin m ⊕ Fin m → K) :
    (toGsp φ hφ x).app v = (φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v :=
  rfl

theorem LspGL_eq_matrixOf (u : Fin m ⊕ Fin m → K) :
    LspGL m K u = matrixOf (StatedSp m K) (spEquiv (m := m) (K := K))
      (Lsp (spForm m K) spForm_isAlt u) :=
  rfl

theorem toGsp_surjective (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) :
    Function.Surjective (toGsp φ hφ) :=
  viaMatrix_surjective φ hφ

theorem ker_toGsp (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) :
    (toGsp φ hφ).ker = φ.ker :=
  ker_viaMatrix φ hφ

end Hom

section Transport

variable [Finite K] [CharP K 2] {X : Type*} [Group X] {M : Type*} [AddCommGroup M] [Finite M]

theorem stroth_2_1_ii_of_hom (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hm : 1 ≤ m) (h2 : ∀ x : M, x + x = 0) [DistribMulAction X M]
    (hker : ∀ x ∈ φ.ker, ∀ a : M, x • a = a) {u u' : Fin m ⊕ Fin m → K}
    (huu' : spForm m K u u' ≠ 0) {L₁ L₂ : Subgroup X} (hL₁ : L₁.map φ = LspGL m K u)
    (hL₂ : L₂.map φ = LspGL m K u')
    (hdec : IsCompl (fixedSub M (L₁ : Set X)) (fixedSub M (L₂ : Set X))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  have hk : ∀ x ∈ (toGsp φ hφ).ker, ∀ a : M, x • a = a := by
    intro x hx a
    rw [ker_toGsp] at hx
    exact hker x hx a
  letI : DistribMulAction (Gsp (spForm m K)) M :=
    descendAction (toGsp φ hφ) (toGsp_surjective φ hφ) hk
  have e1 : fixedSub M ((Lsp (spForm m K) spForm_isAlt u : Subgroup (Gsp (spForm m K))) :
      Set (Gsp (spForm m K))) = fixedSub M (L₁ : Set X) :=
    (fixedSub_descend (toGsp φ hφ) (toGsp_surjective φ hφ) hk _).trans
      (fixedSub_viaMatrix_eq φ hφ hker hL₁)
  have e2 : fixedSub M ((Lsp (spForm m K) spForm_isAlt u' : Subgroup (Gsp (spForm m K))) :
      Set (Gsp (spForm m K))) = fixedSub M (L₂ : Set X) :=
    (fixedSub_descend (toGsp φ hφ) (toGsp_surjective φ hφ) hk _).trans
      (fixedSub_viaMatrix_eq φ hφ hker hL₂)
  refine stroth_2_1_ii_sp spForm_isAlt spForm_nondegenerate hm finrank_spSpace h2 huu' ?_
  rw [e1, e2]
  exact hdec

theorem stroth_2_2_of_hom (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    (hK : 2 < Nat.card K) (hm : 2 ≤ m) (h2 : ∀ x : M, x + x = 0) [DistribMulAction X M]
    (hker : ∀ x ∈ φ.ker, ∀ a : M, x • a = a) (ι : (Fin m ⊕ Fin m → K) →+ M)
    (hι : Function.Injective ι)
    (hιeq : ∀ (x : X) (v : Fin m ⊕ Fin m → K),
      ι ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) = x • ι v)
    (htriv : ∀ (x : X) (a : M), x • a - a ∈ ι.range)
    (hind : ∀ A A' : AddSubgroup M, (∀ x : X, ∀ a ∈ A, x • a ∈ A) →
      (∀ x : X, ∀ a ∈ A', x • a ∈ A') → IsCompl A A' → A = ⊥ ∨ A' = ⊥) :
    Nat.card M ≤ Nat.card K * Nat.card (Fin m ⊕ Fin m → K) := by
  have hk : ∀ x ∈ (toGsp φ hφ).ker, ∀ a : M, x • a = a := by
    intro x hx a
    rw [ker_toGsp] at hx
    exact hker x hx a
  have hΦ := toGsp_surjective φ hφ
  letI : DistribMulAction (Gsp (spForm m K)) M := descendAction (toGsp φ hφ) hΦ hk
  have hsm : ∀ (x : X) (a : M), toGsp φ hφ x • a = x • a := fun x a =>
    descendAction_smul (toGsp φ hφ) hΦ hk x a
  refine stroth_2_2 spForm_isAlt spForm_nondegenerate hK (by rw [finrank_spSpace]; omega) h2 ι hι
    (fun g v => ?_) (fun g a => ?_) (fun A A' hA hA' hc => ?_)
  · obtain ⟨x, rfl⟩ := hΦ g
    rw [hsm]
    exact hιeq x v
  · obtain ⟨x, rfl⟩ := hΦ g
    rw [hsm]
    exact htriv x a
  · exact hind A A' (fun x a ha => by rw [← hsm]; exact hA _ a ha)
      (fun x a ha => by rw [← hsm]; exact hA' _ a ha) hc

end Transport

theorem mem_Lsp_app_iff {V : Type*} [AddCommGroup V] {F : Type*} [Field F] [Module F V]
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt) (g : Gsp B) (v : V) (h : Gsp B) :
    h ∈ Lsp B hB (g.app v) ↔ g⁻¹ * h * g ∈ Lsp B hB v := by
  constructor
  · intro hh
    have := conj_mem_Lsp hB g⁻¹ hh
    rwa [Gsp.app_inv_app, inv_inv] at this
  · intro hh
    have := conj_mem_Lsp hB g hh
    have e : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [e] at this

theorem LspGL_sup_eq {u u' : Fin m ⊕ Fin m → K} (huu' : spForm m K u u' ≠ 0) :
    LspGL m K u ⊔ LspGL m K u' = StatedSp m K := by
  have hu'u : spForm m K u' u ≠ 0 := by
    rw [← spForm_isAlt.neg_eq u u']
    exact neg_ne_zero.mpr huu'
  have hsup := pointRadical_sup_eq_bilinIsometryGroup spForm_isAlt spForm_nondegenerate
    (u := u') (v := u) hu'u
  have h := F2Swap.sup_subgroupOf_eq_top (pointRadical_le_bilinIsometryGroup spForm_isAlt u)
    (pointRadical_le_bilinIsometryGroup spForm_isAlt u') hsup
  show matrixOf (StatedSp m K) (spEquiv (m := m) (K := K)) (Lsp (spForm m K) spForm_isAlt u) ⊔
      matrixOf (StatedSp m K) (spEquiv (m := m) (K := K))
        (Lsp (spForm m K) spForm_isAlt u') = StatedSp m K
  rw [← matrixOf_sup]
  exact (congrArg _ h).trans matrixOf_top

theorem LspGL_inf_eq_bot_iff {u u' : Fin m ⊕ Fin m → K} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    LspGL m K u ⊓ LspGL m K u' = ⊥ ↔ spForm m K u u' ≠ 0 := by
  rw [← Lsp_inf_eq_bot_iff spForm_isAlt spForm_nondegenerate hu hu']
  exact matrixOf_inf_eq_bot_iff _ _

end CFSG.ClassicalGroups.Symplectic
