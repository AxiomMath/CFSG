module

public import CFSG.LieType.CurtisTits.Amalgam
public import Mathlib.GroupTheory.PresentedGroup

public section

namespace CFSG.LieType.CurtisTits

universe u v

variable {K : Type u} [Group K] {ι : Type v} [Preorder ι] (L : ι → Subgroup K)

@[expose] def amalgamRels : Set (FreeGroup (Σ i, L i)) :=
  {w | ∃ i, ∃ x y : L i,
    w = FreeGroup.of ⟨i, x⟩ * FreeGroup.of ⟨i, y⟩ * (FreeGroup.of ⟨i, x * y⟩)⁻¹} ∪
  {w | ∃ i j, i ≤ j ∧ ∃ (x : L i) (y : L j), (x : K) = y ∧
    w = FreeGroup.of ⟨i, x⟩ * (FreeGroup.of ⟨j, y⟩)⁻¹}

@[expose] def amalgamEval (g : Σ i, L i) : K := g.2

theorem amalgamRels_hold : ∀ r ∈ amalgamRels L, FreeGroup.lift (amalgamEval L) r = 1 := by
  rintro r (⟨i, x, y, rfl⟩ | ⟨i, j, -, x, y, hxy, rfl⟩)
  · simp [amalgamEval]
  · simp [amalgamEval, hxy]

@[expose] def IsPresentedByAmalgam : Prop :=
  Function.Bijective (PresentedGroup.toGroup (amalgamRels_hold L))

variable {L}

private theorem mk_rel_eq_one {r : FreeGroup (Σ i, L i)} (hr : r ∈ amalgamRels L) :
    (QuotientGroup.mk r : PresentedGroup (amalgamRels L)) = 1 :=
  (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)

private theorem of_mul_of (i : ι) (x y : L i) :
    (PresentedGroup.of ⟨i, x⟩ : PresentedGroup (amalgamRels L)) * PresentedGroup.of ⟨i, y⟩ =
      PresentedGroup.of ⟨i, x * y⟩ := by
  have h := mk_rel_eq_one (L := L) (Or.inl ⟨i, x, y, rfl⟩)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h
  exact h

@[expose] def amalgamGenHom (i : ι) : L i →* PresentedGroup (amalgamRels L) where
  toFun x := PresentedGroup.of ⟨i, x⟩
  map_one' := by
    have h := of_mul_of (L := L) i 1 1
    rw [mul_one] at h
    exact mul_eq_left.mp h
  map_mul' x y := by exact (of_mul_of i x y).symm

theorem amalgamGenHom_apply (i : ι) (x : L i) :
    amalgamGenHom i x = (PresentedGroup.of ⟨i, x⟩ : PresentedGroup (amalgamRels L)) :=
  rfl

theorem isCompatible_amalgamGenHom : IsCompatible L (fun i => amalgamGenHom (L := L) i) := by
  intro i j hij x y hxy
  have h := mk_rel_eq_one (L := L) (Or.inr ⟨i, j, hij, x, y, hxy, rfl⟩)
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h
  exact h

theorem amalgamGenHom_eval (i : ι) (x : L i) :
    PresentedGroup.toGroup (amalgamRels_hold L) (amalgamGenHom i x) = x := by
  simp [amalgamGenHom_apply, PresentedGroup.toGroup.of, amalgamEval]

theorem amalgamGenHom_injective (i : ι) : Function.Injective (amalgamGenHom (L := L) i) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (PresentedGroup.toGroup (amalgamRels_hold L)) h
  simpa only [amalgamGenHom_eval] using h'

theorem isPresentedByAmalgam_of (hgen : ⨆ i, L i = ⊤)
    (hU : IsUniversalCompletion.{u, v, max u v} L) : IsPresentedByAmalgam L := by
  obtain ⟨ψ, hψ, -⟩ := hU (PresentedGroup (amalgamRels L)) (fun i => amalgamGenHom i)
    isCompatible_amalgamGenHom
  set π := PresentedGroup.toGroup (amalgamRels_hold L)
  have hπ : ∀ (i : ι) (x : L i), π (PresentedGroup.of ⟨i, x⟩) = x := fun i x => by
    simp [π, PresentedGroup.toGroup.of, amalgamEval]
  have hleft : ψ.comp π = MonoidHom.id _ := by
    refine PresentedGroup.ext fun g => ?_
    obtain ⟨i, x⟩ := g
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hπ, hψ, amalgamGenHom_apply]
  have hl : ∀ a, ψ (π a) = a := fun a => by
    simpa using congrArg (fun f => f a) hleft
  refine ⟨fun a b hab => by rw [← hl a, ← hl b, hab], fun y => ?_⟩
  · have hle : (⊤ : Subgroup K) ≤ π.range := by
      rw [← hgen]
      refine iSup_le fun i x hx => ?_
      exact ⟨PresentedGroup.of ⟨i, ⟨x, hx⟩⟩, hπ i ⟨x, hx⟩⟩
    exact hle (Subgroup.mem_top y)

end CFSG.LieType.CurtisTits
