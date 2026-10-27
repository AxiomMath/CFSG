module

public import Certificates.Certificate441664
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup

section Cert


theorem conj_E64_of_le_S {B : Subgroup ↥P1408} (hBS : B ≤ wordSubgroupP sWords)
    (he : CFSG.Open.IsElemAbelian 2 B) (h64 : Nat.card B = 64) :
    ∃ y : ↥P1408, B = (wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom :=
  Certificates.certificate441664 B hBS he h64

theorem conj_E64_P (hP : Nat.card ↥P1408 = 177408000) {B : Subgroup ↥P1408}
    (h64 : Nat.card B = 64) (he : CFSG.Open.IsElemAbelian 2 B) :
    ∃ y : ↥P1408, B = (wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom := by
  have hSsub : Nat.card (wordSubgroupP sWords) = 2 ^ (Nat.card ↥P1408).factorization 2 := by
    rw [hP, two_factorization_card_P1408, Certificates.certificate441664.card_S]
  haveI : Finite (Sylow 2 ↥P1408) :=
    Finite.of_injective (fun P : Sylow 2 ↥P1408 => (P : Subgroup ↥P1408))
      (fun _ _ h => Sylow.ext h)
  obtain ⟨Q, hBQ⟩ := he.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (↥P1408) Q (Sylow.ofCard (wordSubgroupP sWords) hSsub)
  have hsmul : ((g • Q : Sylow 2 ↥P1408) : Subgroup ↥P1408) =
      (Q : Subgroup ↥P1408).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hQS : (Q : Subgroup ↥P1408).map (MulAut.conj g).toMonoidHom = wordSubgroupP sWords := by
    rw [← hsmul, hg, Sylow.coe_ofCard]
  have hBmap_le : B.map (MulAut.conj g).toMonoidHom ≤ wordSubgroupP sWords := by
    rw [← hQS]
    exact Subgroup.map_mono hBQ
  have hcard : Nat.card (B.map (MulAut.conj g).toMonoidHom) = 64 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, h64]
  have habel : CFSG.Open.IsElemAbelian 2 (B.map (MulAut.conj g).toMonoidHom) :=
    he.map (MulAut.conj g).toMonoidHom
  obtain ⟨y, hy⟩ := conj_E64_of_le_S hBmap_le habel hcard
  have hcomp_id : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom
      = MonoidHom.id ↥P1408 := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  have hB_inv : B = (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.map_map, hcomp_id, Subgroup.map_id]
  have hcomp_y : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj y).toMonoidHom
      = (MulAut.conj (g⁻¹ * y)).toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨g⁻¹ * y, ?_⟩
  calc B = (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := hB_inv
    _ = ((wordSubgroupP uWords).map (MulAut.conj y).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom := by rw [hy]
    _ = (wordSubgroupP uWords).map (MulAut.conj (g⁻¹ * y)).toMonoidHom := by
        rw [Subgroup.map_map, hcomp_y]

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel