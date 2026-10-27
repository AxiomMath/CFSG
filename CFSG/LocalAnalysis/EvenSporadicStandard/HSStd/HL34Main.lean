module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog
public import Certificates.Certificate27218

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification.PSL3Four
open CFSG.EvenSporadicStandard.HSStd.HL34

theorem eq_bot_of_normal_odd_of_zStar {D : Type} [Group D] (hZ : fusionZStar D = ⊥)
    (N : Subgroup D) (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h1 : N ≤ fusionOddCore D :=
    le_sSup (show N ∈ {N : Subgroup D | N.Normal ∧ Odd (Nat.card N)} from ⟨hN, hodd⟩)
  have h2 : fusionOddCore D ≤ fusionZStar D := by
    intro x hx
    show QuotientGroup.mk' (fusionOddCore D) x ∈ Subgroup.center (D ⧸ fusionOddCore D)
    rw [show QuotientGroup.mk' (fusionOddCore D) x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  exact le_bot_iff.1 (h1.trans (h2.trans hZ.le))

theorem haradaL34Data_proved :
    HaradaL34Data := by
  intro D _ _ hZ t K ht hC hd eK hL u hu hsw
  obtain ⟨φ⟩ := nonempty_equiv_of_stated _ (by
    rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals exact absurd h (by norm_num))
  have hHeq : (commutator ↥(commutator D)).map (commutator D).subtype =
      ⁅commutator D, commutator D⁆ := by
    rw [show commutator ↥(commutator D) = ⁅(⊤ : Subgroup ↥(commutator D)), ⊤⁆ from rfl,
      map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hHn : ((commutator ↥(commutator D)).map (commutator D).subtype).Normal := by
    rw [hHeq]
    infer_instance
  let ψ := (Subgroup.equivMapOfInjective (commutator ↥(commutator D)) (commutator D).subtype
    Subtype.val_injective).symm.trans φ
  exact hl34_main Certificates.certificate27218 (eq_bot_of_normal_odd_of_zStar hZ) ht hC hd
    eK _ ψ hu hsw

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
