module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.Defs
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

open CFSG.Open CFSG.LieType.SeitzGeneration

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

variable {G : Type*} [Group G]

@[expose] def CentralInSylow (p : ℕ) (z : G) : Prop :=
  ∃ P : Sylow p G, ∀ x ∈ P, x * z = z * x

theorem isPGroup_of_pow_eq_one {p : ℕ} {H : Subgroup G} (h : ∀ x ∈ H, x ^ p = 1) :
    IsPGroup p H := fun g => ⟨1, Subtype.ext (by simpa using h g g.2)⟩

theorem isElemAbelian_closure {p : ℕ} {k : Set G} (hcomm : ∀ x ∈ k, ∀ y ∈ k, x * y = y * x)
    (hpow : ∀ x ∈ k, x ^ p = 1) : IsElemAbelian p (Subgroup.closure k) :=
  CFSG.Open.IsElemAbelian.closure_of_commute hcomm hpow

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 := congrArg (fun φ : MulAut G => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  rwa [hZ, Subgroup.mem_bot] at this

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
