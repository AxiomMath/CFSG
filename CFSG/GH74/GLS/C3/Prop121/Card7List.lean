module

public import CFSG.GH74.GLS.C3.Prop121.MooreFinite7Inputs

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Equiv Perm

theorem allPerms_nodup : ∀ m : ℕ, (allPerms m).Nodup
  | 0 => by simp [allPerms]
  | m + 1 => by
    unfold allPerms
    rw [List.nodup_flatMap]
    refine ⟨fun p _ => ?_, ?_⟩
    · refine (allPerms_nodup m).map (fun e e' h => ?_)
      have := Equiv.Perm.decomposeFin.symm.injective h
      exact (Prod.mk.inj this).2
    · refine (List.nodup_finRange (m + 1)).imp (fun {a b} hab => ?_)
      intro l h1 h2
      simp only [List.mem_map] at h1 h2
      obtain ⟨e1, -, he1⟩ := h1
      obtain ⟨e2, -, he2⟩ := h2
      have := Equiv.Perm.decomposeFin.symm.injective (he1.trans he2.symm)
      exact hab (Prod.mk.inj this).1

end CFSG.GH74.GLS.C3.Prop121.Card7
