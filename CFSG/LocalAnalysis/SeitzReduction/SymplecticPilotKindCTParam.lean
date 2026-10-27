module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N : ℕ}

structure CtLinParam (ε : ℕ) (e : L ≃* StatedSp N K) (k : Fin N) where
  Φ : q2Block ε K {k} →* G
  ker_le : Φ.ker ≤ center (q2Block ε K {k})
  range_eq : Φ.range = neighbourCore e k
  N1 : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ),
    Φ ⟨ctEmbed ε y, ctEmbed_mem_q2Block_iff.2 hy⟩ = ((e.symm y : L) : G)

variable {ε : ℕ} {e : L ≃* StatedSp N K}

@[expose] noncomputable def CtLinParam.twist {k : Fin N} (P : CtLinParam ε e k) :
    CtLinParam ε e k where
  Φ := P.Φ.comp (ctGraphBlock ε {k}).toMonoidHom
  ker_le := by
    intro x hx
    have hx' : ctGraphBlock ε {k} x ∈ P.Φ.ker := hx
    have h1 := P.ker_le hx'
    rw [mem_center_iff] at h1 ⊢
    intro g
    apply (ctGraphBlock (K := K) ε {k}).injective
    rw [map_mul, map_mul]
    exact h1 _
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    change P.Φ (ctGraphBlock ε {k} ⟨ctEmbed ε y, _⟩) = _
    rw [ctGraphBlock_fix (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)]
    exact P.N1 y hy

theorem CtLinParam.twist_Φ_apply {k : Fin N} (P : CtLinParam ε e k) (x : q2Block ε K {k}) :
    P.twist.Φ x = P.Φ (ctGraphBlock ε {k} x) :=
  rfl

@[expose] def CtLinParamAgree (P : ∀ k : Fin N, CtLinParam ε e k) : Prop :=
  ∀ (k l : Fin N) (x : SpecialLinearGroup (Fin (2 * N + ε)) K) (hx : x ∈ q2Block ε K {k})
    (hx' : x ∈ q2Block ε K {l}), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

end Param

end CFSG.SeitzReduction.SymplecticPilot
