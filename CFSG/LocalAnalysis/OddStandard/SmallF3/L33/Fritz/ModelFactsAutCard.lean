module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutRel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsSylow

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}
  (h : IsL33Model M)

private theorem liftA_congr (M : AutModel L (Equiv.Perm (Fin 26)))
    {g : Equiv.Perm (Fin 26)} (h1 h2 : g ∈ M.A) :
    liftA M g h1 = liftA M g h2 :=
  congrArg M.Φ.symm (Subtype.ext rfl)

theorem card_closure_elXY : Nat.card (Subgroup.closure ({h.elX, h.elY} : Set L)) = 16 := by
  apply card_closure_xy h.elX h.elY h.elX_pow_eight h.elY_sq h.elY_conj
  intro a b hab
  have h1 : modelX ^ (a.1 : ℕ) * modelY ^ (a.2 : ℕ) =
      modelX ^ (b.1 : ℕ) * modelY ^ (b.2 : ℕ) := by
    have h2 := congrArg (fun t : L => M.ι (MulAut.conj t)) hab
    simp only [map_mul, map_pow, h.ι_conj, h.e_elX, h.e_elY] at h2
    exact h2
  have h3 : (a.1, a.2, (0 : Fin 2)) = (b.1, b.2, (0 : Fin 2)) := by
    apply model_normalForm_injective
    simpa using h1
  exact Prod.ext (congrArg (fun p : Fin 8 × Fin 2 × Fin 2 => p.1) h3)
    (congrArg (fun p : Fin 8 × Fin 2 × Fin 2 => p.2.1) h3)

theorem card_closure_elT :
    Nat.card (Subgroup.closure
      ({MulAut.conj h.elX, MulAut.conj h.elY, h.elK} : Set (MulAut L))) = 32 := by
  refine card_closure_xyk (MulAut.conj h.elX) (MulAut.conj h.elY) h.elK ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply M.ι_injective
    rw [map_pow, map_one, h.ι_conj, h.e_elX]
    exact model_relations.1
  · apply M.ι_injective
    rw [map_pow, map_one, h.ι_conj, h.e_elY]
    exact model_relations.2.2.1
  · apply M.ι_injective
    rw [map_pow, map_one, h.ι_elK]
    exact model_relations.2.2.2.1
  · apply M.ι_injective
    simp only [map_mul, map_inv, map_pow, h.ι_conj, h.e_elX, h.e_elY]
    exact model_relations.2.2.2.2.1
  · apply M.ι_injective
    simp only [map_mul, map_inv, map_pow, h.ι_conj, h.e_elX, h.ι_elK]
    exact model_relations.2.2.2.2.2.1
  · apply M.ι_injective
    simp only [map_mul, h.ι_conj, h.e_elY, h.ι_elK]
    exact model_relations.2.2.2.2.2.2.1
  · intro a b hab
    apply model_normalForm_injective
    have h2 := congrArg M.ι hab
    simp only [map_mul, map_pow, h.ι_conj, h.e_elX, h.e_elY, h.ι_elK] at h2
    exact h2

theorem card_centralizer_elK :
    Nat.card (Subgroup.centralizer ({h.elK} : Set (MulAut L))) = 48 := by
  let F : {φ : MulAut L // φ ∈ Subgroup.centralizer ({h.elK} : Set (MulAut L))} ≃
      {g : QA.originalSubgroup //
        (g : Equiv.Perm (Fin 26)) * modelK = modelK * (g : Equiv.Perm (Fin 26))} :=
  { toFun := fun φ =>
      ⟨⟨M.ι φ, h.A_eq ▸ M.ι_mem φ⟩, by
        have hc := (Subgroup.mem_centralizer_iff.mp φ.2) h.elK (Set.mem_singleton h.elK)
        have hc' := congrArg M.ι hc
        simp only [map_mul, h.ι_elK] at hc'
        exact hc'.symm⟩
    invFun := fun g =>
      ⟨liftA M (g.1 : Equiv.Perm (Fin 26)) (h.A_eq.symm ▸ g.1.2), by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        apply M.ι_injective
        rw [map_mul, map_mul, ι_liftA, h.ι_elK]
        exact g.2.symm⟩
    left_inv := fun φ => by
      apply Subtype.ext
      exact (liftA_congr M _ (M.ι_mem φ)).trans (liftA_ι M φ)
    right_inv := fun g => by
      apply Subtype.ext
      apply Subtype.ext
      exact ι_liftA M (g.1 : Equiv.Perm (Fin 26)) (h.A_eq.symm ▸ g.1.2) }
  rw [Nat.card_congr F, card_model_centralizer_k]

theorem card_fixed_elK :
    Nat.card {a : L // h.elK a = a} = 24 := by
  let e' : L ≃ QP.originalSubgroup :=
    (M.e.trans (MulEquiv.subgroupCongr h.P_eq)).toEquiv
  have hiff : ∀ a : L, h.elK a = a ↔
      (e' a : Equiv.Perm (Fin 26)) * modelK =
        modelK * (e' a : Equiv.Perm (Fin 26)) := by
    intro a
    have hae : (e' a : Equiv.Perm (Fin 26)) = (M.e a : Equiv.Perm (Fin 26)) := rfl
    rw [hae]
    constructor
    · intro ha
      have h1 := congrArg (fun u : L => (M.e u : Equiv.Perm (Fin 26))) ha
      rw [e_apply, h.ι_elK] at h1
      calc (M.e a : Equiv.Perm (Fin 26)) * modelK
          = (modelK * (M.e a : Equiv.Perm (Fin 26)) * modelK⁻¹) * modelK := by rw [h1]
        _ = modelK * (M.e a : Equiv.Perm (Fin 26)) := by group
    · intro hc
      apply M.e.injective
      apply Subtype.ext
      rw [e_apply, h.ι_elK]
      rw [← hc]
      group
  have E : {a : L // h.elK a = a} ≃
      {g : QP.originalSubgroup // (g : Equiv.Perm (Fin 26)) * modelK =
        modelK * (g : Equiv.Perm (Fin 26))} := Equiv.subtypeEquiv e' hiff
  rw [Nat.card_congr E]
  exact card_model_centralizer_k_inner

end IsL33Model

end CFSG.OddStandard.SmallF3.L33
