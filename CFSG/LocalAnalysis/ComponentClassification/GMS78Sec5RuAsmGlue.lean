module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmDefs

public section

namespace CFSG.ComponentClassification.GMS78.RuAsm

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7

section Words

variable {H H' : Type*} [Group H] [Group H']

theorem map_lift_fin7 (θ : H →* H') (f : Fin 7 → H) (x : FreeGroup (Fin 7)) :
    θ (FreeGroup.lift f x) = FreeGroup.lift (θ ∘ f) x := by
  have h : θ.comp (FreeGroup.lift f) = FreeGroup.lift (θ ∘ f) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact DFunLike.congr_fun h x

theorem lift_mk_congr_fin7 {f f' : Fin 7 → H} {w : List (Fin 7 × Bool)}
    (h : ∀ p ∈ w, f p.1 = f' p.1) :
    FreeGroup.lift f (FreeGroup.mk w) = FreeGroup.lift f' (FreeGroup.mk w) := by
  rw [FreeGroup.lift_mk, FreeGroup.lift_mk]
  congr 1
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem pi7Word_eq_lift (w : List (Fin 7 × Bool)) :
    pi7Word w = FreeGroup.lift (fun i => (PresentedGroup.of i : Pi7)) (FreeGroup.mk w) := by
  have h : PresentedGroup.mk {r : FreeGroup (Fin 7) | r ∈ pi7Rels.map FreeGroup.mk} =
      FreeGroup.lift (fun i => (PresentedGroup.of i : Pi7)) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  exact DFunLike.congr_fun h (FreeGroup.mk w)

end Words

section Letters

variable {K : Type*} [Group K]

theorem lift_eq_of_letterSub {l : List (Fin 7)} (φ : ↥(letterSub l) →* K) {g : Fin 7 → K}
    (hg : ∀ i (hi : i ∈ l), φ ⟨PresentedGroup.of i, mem_letterSub hi⟩ = g i)
    {w : List (Fin 7 × Bool)} (hw : ∀ p ∈ w, p.1 ∈ l) :
    ∃ hm : pi7Word w ∈ letterSub l, φ ⟨pi7Word w, hm⟩ = FreeGroup.lift g (FreeGroup.mk w) := by
  classical
  set h : Fin 7 → ↥(letterSub l) := fun i =>
    if hi : i ∈ l then ⟨PresentedGroup.of i, mem_letterSub hi⟩ else 1 with hh
  have hhi : ∀ p (hp : p ∈ w), h p.1 = ⟨PresentedGroup.of p.1, mem_letterSub (hw p hp)⟩ :=
    fun p hp => by simp [hh, hw p hp]
  have hval : ((FreeGroup.lift h (FreeGroup.mk w) : ↥(letterSub l)) : Pi7) = pi7Word w := by
    rw [← (letterSub l).coe_subtype, map_lift_fin7, pi7Word_eq_lift]
    refine lift_mk_congr_fin7 fun p hp => ?_
    simp only [Function.comp_apply, hhi p hp, coe_subtype]
  refine ⟨hval ▸ (FreeGroup.lift h (FreeGroup.mk w)).2, ?_⟩
  have e : (⟨pi7Word w, hval ▸ (FreeGroup.lift h (FreeGroup.mk w)).2⟩ : ↥(letterSub l)) =
      FreeGroup.lift h (FreeGroup.mk w) := Subtype.ext hval.symm
  rw [e, map_lift_fin7]
  refine lift_mk_congr_fin7 fun p hp => ?_
  simp only [Function.comp_apply, hhi p hp]
  exact hg p.1 (hw p hp)

theorem lift_eq_one_of_letterSub {l : List (Fin 7)} (φ : ↥(letterSub l) →* K) {g : Fin 7 → K}
    (hg : ∀ i (hi : i ∈ l), φ ⟨PresentedGroup.of i, mem_letterSub hi⟩ = g i)
    {r : List (Fin 7 × Bool)} (hr : pi7Word r = 1) (hrl : ∀ p ∈ r, p.1 ∈ l) :
    FreeGroup.lift g (FreeGroup.mk r) = 1 := by
  obtain ⟨hm, h⟩ := lift_eq_of_letterSub φ hg hrl
  rw [← h]
  have e : (⟨pi7Word r, hm⟩ : ↥(letterSub l)) = 1 := Subtype.ext hr
  rw [e, map_one]

theorem pi7Word_eq_one {r : List (Fin 7 × Bool)} (hr : r ∈ pi7Rels) : pi7Word r = 1 := by
  have hmem : FreeGroup.mk r ∈ {x : FreeGroup (Fin 7) | x ∈ pi7Rels.map FreeGroup.mk} :=
    List.mem_map_of_mem (f := FreeGroup.mk) hr
  exact (QuotientGroup.eq_one_iff _).mpr (subset_normalClosure hmem)

end Letters

variable {K : Type*} [Group K]

end CFSG.ComponentClassification.GMS78.RuAsm
