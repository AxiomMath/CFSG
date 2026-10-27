module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Inn
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUA6Fix

public section

namespace CFSG.EvenSporadicStandard.Fin76b.A6X

theorem a6AutFacts : A6AutFacts where
  fix_invol ζ h2 h1 := fix_invol h2 h1
  sq_A6 H hH Q hQH hQ γ hγ := by
    obtain ⟨e⟩ := hH
    have hHI := inn_unique e
    have hQr : Q ≤ (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))).range := hHI ▸ hQH
    have hmap := Subgroup.map_comap_eq_self hQr
    have hinj : Function.Injective (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))) :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
    have hcard : Nat.card ↥(Q.comap (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6)))) = 8 := by
      have h := Subgroup.card_map_of_injective (f := (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6)))) hinj
        (K := Q.comap (MulAut.conj : alternatingGroup (Fin 6) →*
          MulAut (alternatingGroup (Fin 6))))
      rw [hmap] at h
      rw [← h]
      exact hQ
    refine fix_sq_A hcard (fun a ha => fixed_of_comm_conj ?_)
    exact hγ _ (Subgroup.mem_comap.1 ha)
  cent_A6 H hH γ hγ := by
    obtain ⟨e⟩ := hH
    exact cent_A6' e hγ

end CFSG.EvenSporadicStandard.Fin76b.A6X
