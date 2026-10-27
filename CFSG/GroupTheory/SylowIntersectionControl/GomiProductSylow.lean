module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.PermSylowTwo.SymCore
import CFSG.Quasithin.Background.B6Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {G : Type} [Group G] [Finite G] {S : Set (Subgroup G)} {N H : Subgroup G}

theorem isSylowTwoOf_inf_of_forall (hN : IsDirectProduct S N) (hH : IsPGroup 2 H)
    (h : ∀ B ∈ S, IsSylowTwoOf (H ⊓ B) B) : IsSylowTwoOf (H ⊓ N) N := by
  obtain ⟨R, hR, hPR⟩ :=
    B6.exists_isSylowTwoOf_ge (hH.to_le inf_le_left) (inf_le_right : H ⊓ N ≤ N)
  suffices hRH : R ≤ H by rwa [le_antisymm hPR (le_inf hRH hR.1)]
  intro r hr
  refine hN.mem_of_coord_mem (hR.1 hr) fun B hB => ?_
  have hproj : projIn S B R ≤ H ⊓ B :=
    PermSylowTwo.le_of_isSylowTwoOf_of_isPGroup (h B hB) (fun x hx => (hN.mem_projIn_iff hB).mpr
      ⟨⟨x, hN.le hB hx.2⟩, hPR ⟨hx.1, hN.le hB hx.2⟩, hN.coord_of_mem hB hx.2⟩) (projIn_le B R)
      (hR.2.1.of_surjective (projInHom hN hB hR.1) (projInHom_surjective hN hB hR.1))
  exact (hproj ((hN.mem_projIn_iff hB).mpr ⟨⟨r, hR.1 hr⟩, hr, rfl⟩)).1

theorem exists_two_dvd_relIndex_of_not_isSylowTwoOf (hN : IsDirectProduct S N)
    (hH : IsPGroup 2 H) (hJ : ¬ IsSylowTwoOf (H ⊓ N) N) : ∃ A ∈ S, 2 ∣ (H ⊓ A).relIndex A := by
  by_contra! h
  exact hJ (isSylowTwoOf_inf_of_forall hN hH fun B hB =>
    ⟨inf_le_right, hH.to_le inf_le_left, h B hB⟩)

end CFSG.GroupTheory
