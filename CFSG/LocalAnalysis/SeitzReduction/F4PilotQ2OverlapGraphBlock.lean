module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockEmbed reindexSpecialLinear)

variable {K : Type} [Field K] {n r : ℕ}

variable (K) in
@[expose] noncomputable def blockSpecialLinearMulEquivSL (I : Finset (Fin n)) :
    blockSpecialLinear (K := K) I ≃* SpecialLinearGroup I K :=
  ((MonoidHom.ofInjective (LinearPilot.blockEmbed_injective (K := K) I)).trans
    (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed I))).symm

theorem coe_blockSpecialLinearMulEquivSL_symm (I : Finset (Fin n)) (A : SpecialLinearGroup I K) :
    (((blockSpecialLinearMulEquivSL K I).symm A : blockSpecialLinear (K := K) I) :
      SpecialLinearGroup (Fin n) K) = blockEmbed I A :=
  rfl

theorem blockSpecialLinearMulEquivSL_apply (I : Finset (Fin n))
    (x : blockSpecialLinear (K := K) I) (i j : I) :
    ((blockSpecialLinearMulEquivSL K I x : SpecialLinearGroup I K) : Matrix I I K) i j =
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := by
  conv_rhs => rw [← (blockSpecialLinearMulEquivSL K I).symm_apply_apply x]
  rw [coe_blockSpecialLinearMulEquivSL_symm, LinearPilot.coe_blockEmbed,
    LinearPilot.blockMatrix_apply]
  simp [i.2, j.2]

section Two

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def slToGLTwo (β : K ≃+* ZMod 2) :
    SpecialLinearGroup ι K →* GL ι (ZMod 2) :=
  SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (β : K →+* ZMod 2))

theorem slToGLTwo_apply (β : K ≃+* ZMod 2) (A : SpecialLinearGroup ι K) (a b : ι) :
    ((slToGLTwo β A : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) a b = β ((A : Matrix ι ι K) a b) :=
  rfl

theorem slToGLTwo_bijective (β : K ≃+* ZMod 2) :
    Function.Bijective (slToGLTwo (ι := ι) β) := by
  constructor
  · intro A B h
    ext a b
    have := congrArg (fun g : GL ι (ZMod 2) => (g : Matrix ι ι (ZMod 2)) a b) h
    simp only [slToGLTwo_apply] at this
    exact β.injective this
  · intro g
    have hdet : (g : Matrix ι ι (ZMod 2)).det = 1 := by
      have h0 : (g : Matrix ι ι (ZMod 2)).det ≠ 0 := g.det_ne_zero
      generalize (g : Matrix ι ι (ZMod 2)).det = d at h0
      revert d
      decide
    refine ⟨⟨(g : Matrix ι ι (ZMod 2)).map (β.symm : ZMod 2 →+* K), by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]⟩, ?_⟩
    ext a b
    change β (((g : Matrix ι ι (ZMod 2)).map (β.symm : ZMod 2 →+* K)) a b) = _
    simp

end Two

@[expose] noncomputable def blockGLEquiv (I : Finset (Fin n)) (e : I ≃ Fin r)
    (β : K ≃+* ZMod 2) : blockSpecialLinear (K := K) I ≃* GL (Fin r) (ZMod 2) :=
  (blockSpecialLinearMulEquivSL K I).trans ((reindexSpecialLinear e).trans
    (MulEquiv.ofBijective (slToGLTwo β) (slToGLTwo_bijective β)))

theorem blockGLEquiv_apply (I : Finset (Fin n)) (e : I ≃ Fin r) (β : K ≃+* ZMod 2)
    (x : blockSpecialLinear (K := K) I) (a b : Fin r) :
    ((blockGLEquiv I e β x : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)) a b =
      β (((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (e.symm a)
        (e.symm b)) := by
  change β (((reindexSpecialLinear e (blockSpecialLinearMulEquivSL K I x) :
    SpecialLinearGroup (Fin r) K) : Matrix (Fin r) (Fin r) K) a b) = _
  change β ((reindex e e ((blockSpecialLinearMulEquivSL K I x : SpecialLinearGroup I K) :
    Matrix I I K)) a b) = _
  rw [reindex_apply, submatrix_apply, blockSpecialLinearMulEquivSL_apply]

theorem card_blockSpecialLinear_eq (I : Finset (Fin n)) (e : I ≃ Fin r) (β : K ≃+* ZMod 2) :
    Nat.card (blockSpecialLinear (K := K) I) = Nat.card (GL (Fin r) (ZMod 2)) :=
  Nat.card_congr (blockGLEquiv I e β).toEquiv

theorem card_centralizer_inf_blockSpecialLinear_eq (I : Finset (Fin n)) (e : I ≃ Fin r)
    (β : K ≃+* ZMod 2) {u : SpecialLinearGroup (Fin n) K} (hu : u ∈ blockSpecialLinear I)
    {g : GL (Fin r) (ZMod 2)}
    (hg : ∀ a b, (g : Matrix (Fin r) (Fin r) (ZMod 2)) a b =
      β ((u : Matrix (Fin n) (Fin n) K) (e.symm a) (e.symm b))) :
    Nat.card (centralizer ({u} : Set (SpecialLinearGroup (Fin n) K)) ⊓ blockSpecialLinear I :
      Subgroup (SpecialLinearGroup (Fin n) K)) =
      Nat.card (centralizer ({g} : Set (GL (Fin r) (ZMod 2)))) := by
  set B := blockSpecialLinear (K := K) I with hB
  set Ψ := blockGLEquiv I e β with hΨ
  have hΨu : Ψ ⟨u, hu⟩ = g := by
    ext a b
    rw [hΨ, blockGLEquiv_apply, hg]
  have hmap : (centralizer ({⟨u, hu⟩} : Set B)).map B.subtype =
      centralizer ({u} : Set (SpecialLinearGroup (Fin n) K)) ⊓ B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mem_centralizer_singleton_iff.2 ?_, y.2⟩
      have := mem_centralizer_singleton_iff.1 hy
      exact congrArg Subtype.val this
    · rintro ⟨hx, hxB⟩
      refine ⟨⟨x, hxB⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
        (mem_centralizer_singleton_iff.1 hx)), rfl⟩
  have hmapΨ : (centralizer ({⟨u, hu⟩} : Set B)).map Ψ.toMonoidHom =
      centralizer ({g} : Set (GL (Fin r) (ZMod 2))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff, ← hΨu]
      change Ψ x * Ψ ⟨u, hu⟩ = Ψ ⟨u, hu⟩ * Ψ x
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hx]
    · intro hy
      refine ⟨Ψ.symm y, mem_centralizer_singleton_iff.2 (Ψ.injective ?_), Ψ.apply_symm_apply y⟩
      rw [map_mul, map_mul, Ψ.apply_symm_apply, hΨu]
      exact mem_centralizer_singleton_iff.1 hy
  rw [← hmap, Subgroup.card_map_of_injective B.subtype_injective, ← hmapΨ,
    Subgroup.card_map_of_injective Ψ.injective]

end CFSG.SeitzReduction.F4Pilot
