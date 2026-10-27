module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecClq

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {W : Subgroup Y}

theorem dConnected_of_wSet_clique5 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hW1 : WSet (CoreAssembly.conjClass (tightCore R)) = {W})
    (B : Fin 5 → Subgroup Y) (hB : ∀ i, B i ∈ CoreAssembly.conjClass (tightCore R))
    (hinj : Function.Injective B)
    (hadj : ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)) :
    DConnected (CoreAssembly.conjClass (tightCore R)) := by
  by_contra hnc
  have hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R)) := by rw [hW1]; rfl
  have c := Q3CL.T8.ctxOf hd.partIHypG hW
  have hDb := SecIdE2.not_dbarConnected_of_wSet hd hc hO2 hW1 hnc
  choose ρ hρ using fun i => SecIdE2.exists_rep_of_wSet hd hc hO2 hW1 (B i) (hB i)
  have hcl := Q3T8.Asc77.thompsonClique Y _ hd.partIHypG W hW hDb (T8.repElt (ρ 0))
    (T8.repElt_mem (ρ 0))
  have hsub : Set.range (fun i => T8.repElt (ρ i)) ⊆
      Star3T.cent (muDelta (CoreAssembly.conjClass (tightCore R)) W) (T8.repElt (ρ 0)) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨T8.repElt_mem (ρ i), ?_⟩
    by_cases hi : i = 0
    · subst hi
      rfl
    · have hne : (ρ 0).K ≠ (ρ i).K := by
        rw [hρ 0, hρ i]
        exact hinj.ne (Ne.symm hi)
      have h := (repElt_commute_iff_gen c (ρ 0) (ρ i) hne).mpr (by
        rw [hρ 0, hρ i]
        exact hadj 0 i (Ne.symm hi))
      exact h.symm
  have hinj' : Function.Injective (fun i => T8.repElt (ρ i)) := fun i j h => hinj (by
    rw [← hρ i, ← hρ j]
    exact (repElt_eq_iff_gen c (ρ i) (ρ j)).mp h)
  have h5 : (Set.range fun i => T8.repElt (ρ i)).ncard = 5 := by
    rw [Set.ncard_range_of_injective hinj', Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rcases hcl with h | h | ⟨h, -⟩ <;> omega

end CFSG.ClassicalInvolution.Q3.TL4.SecClq
