module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Min
import CFSG.Quasithin.Background.ConjTransport

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (IsFFStarOffender fixV)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset IsPStar PstarSet O2Trivial)
open CFSG.Open (pCoreOf)
open CFSG.LieType.BorelTits

variable {W : Type} [CommGroup W]

private theorem card_mul_fixV_map_conj_bstar (A : Subgroup (MulAut W)) (g : MulAut W) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) *
        Nat.card (fixV (A.map (MulAut.conj g).toMonoidHom)) =
      Nat.card A * Nat.card (fixV A) := by
  rw [CFSG.Quasithin.ConjTransport.card_fixV_map_conj A g,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem conj_comp_conj_inv_bstar (g : MulAut W) :
    (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id (MulAut W) := by
  ext x
  simp [MulAut.conj_apply]

private theorem conj_inv_comp_conj_bstar (g : MulAut W) :
    (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (MulAut W) := by
  ext x
  simp [MulAut.conj_apply]

private theorem map_sSup_le_of_forall_bstar {S : Set (Subgroup (MulAut W))} {g : MulAut W}
    (hS : ∀ A ∈ S, A.map (MulAut.conj g).toMonoidHom ∈ S) :
    (sSup S).map (MulAut.conj g).toMonoidHom ≤ sSup S := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun A hA => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (hS A hA)

private theorem map_sSup_eq_of_forall_mem_bstar {S : Set (Subgroup (MulAut W))} {g : MulAut W}
    (hS : ∀ A ∈ S, A.map (MulAut.conj g).toMonoidHom ∈ S)
    (hS' : ∀ A ∈ S, A.map (MulAut.conj g⁻¹).toMonoidHom ∈ S) :
    (sSup S).map (MulAut.conj g).toMonoidHom = sSup S := by
  refine le_antisymm (map_sSup_le_of_forall_bstar hS) ?_
  have hle' := map_sSup_le_of_forall_bstar hS'
  calc sSup S = (sSup S).map (MonoidHom.id (MulAut W)) := (Subgroup.map_id _).symm
    _ = (sSup S).map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) := by
          rw [conj_comp_conj_inv_bstar g]
    _ = ((sSup S).map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_map]
    _ ≤ (sSup S).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hle'

theorem map_conj_mem_pstarSet {Y : Subgroup (MulAut W)} {A : Subgroup (MulAut W)}
    (hA : A ∈ PstarSet Y) {g : MulAut W} (hg : g ∈ Y) :
    A.map (MulAut.conj g).toMonoidHom ∈ PstarSet Y := by
  obtain ⟨hAmem, hAmin⟩ := hA
  refine ⟨CFSG.Quasithin.isFFStarOffender_map_conj hAmem hg, fun B hBmem hBle hcard => ?_⟩
  have hB'mem : B.map (MulAut.conj g⁻¹).toMonoidHom ∈ Pset Y :=
    CFSG.Quasithin.isFFStarOffender_map_conj hBmem (Y.inv_mem hg)
  have hB'le : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ A := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hBle
    rwa [Subgroup.map_map, conj_inv_comp_conj_bstar g, Subgroup.map_id] at h
  have hcard' : Nat.card A * Nat.card (fixV A) =
      Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) *
        Nat.card (fixV (B.map (MulAut.conj g⁻¹).toMonoidHom)) := by
    rw [← card_mul_fixV_map_conj_bstar A g, hcard, card_mul_fixV_map_conj_bstar B g⁻¹]
  have hBeq : B.map (MulAut.conj g⁻¹).toMonoidHom = A := hAmin _ hB'mem hB'le hcard'
  calc B = B.map (MonoidHom.id (MulAut W)) := (Subgroup.map_id B).symm
    _ = B.map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) := by
          rw [conj_comp_conj_inv_bstar g]
    _ = (B.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
          rw [Subgroup.map_map]
    _ = A.map (MulAut.conj g).toMonoidHom := by rw [hBeq]

private theorem le_normalizer_inSubgroup_pPrimePCore_bstar (Y : Subgroup (MulAut W)) :
    Y ≤ Subgroup.normalizer
      (CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y : Set (MulAut W)) := by
  have h := Subgroup.le_normalizer_map (H := CFSG.GH74.GLS.pPrimePCore 2 ↥Y) (Y.subtype)
  rw [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.range_subtype] at h
  exact h

theorem map_conj_mem_gomiPstar0Set {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar0Set Y) {g : MulAut W} (hg : g ∈ Y) :
    A.map (MulAut.conj g).toMonoidHom ∈ gomiPstar0Set Y := by
  obtain ⟨hAstar, hAle⟩ := hA
  refine ⟨map_conj_mem_pstarSet hAstar hg, ?_⟩
  have heq : (CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y).map
        (MulAut.conj g).toMonoidHom = CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      (le_normalizer_inSubgroup_pPrimePCore_bstar Y hg)
  exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAle).trans (le_of_eq heq)

theorem map_conj_mem_gomiPstar1Set {Y : Subgroup (MulAut W)}
    {A : Subgroup (MulAut W)} (hA : A ∈ gomiPstar1Set Y) {g : MulAut W} (hg : g ∈ Y) :
    A.map (MulAut.conj g).toMonoidHom ∈ gomiPstar1Set Y := by
  obtain ⟨hAstar, hA0⟩ := hA
  refine ⟨map_conj_mem_pstarSet hAstar hg, fun hmem => hA0 ?_⟩
  have hmem' : (A.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom ∈ gomiPstar0Set Y :=
    map_conj_mem_gomiPstar0Set hmem (Y.inv_mem hg)
  rwa [Subgroup.map_map, conj_inv_comp_conj_bstar g, Subgroup.map_id] at hmem'

theorem pstarSet_nonempty [Finite W] {Y : Subgroup (MulAut W)} (hY : (Pset Y).Nonempty) :
    (PstarSet Y).Nonempty := by
  obtain ⟨A, hA⟩ := hY
  obtain ⟨A₀, hA₀, hmin⟩ := CFSG.QuasithinUnique.B42A57.exists_minimal_offender hA
  exact ⟨A₀, hA₀, fun B hB hBle _ => Subgroup.eq_of_le_of_card_ge hBle (hmin B hB)⟩

theorem o2Trivial_of_normal [Finite W] {Y K : Subgroup (MulAut W)} (hY : O2Trivial Y)
    (hKY : K ≤ Y) (hK : (K.subgroupOf Y).Normal) : O2Trivial K := by
  intro P hPK hPnorm hP2
  have hYK : Y ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mp hK
  have hYnorm : Y ≤ Subgroup.normalizer (pCoreOf 2 K : Set (MulAut W)) :=
    hYK.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hle : pCoreOf 2 K ≤ Y := (pCoreOf_le 2 K).trans hKY
  have hnorm : ((pCoreOf 2 K).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hYnorm
  have hp : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hbot : pCoreOf 2 K = ⊥ := hY _ hle hnorm hp
  have hPle : P ≤ pCoreOf 2 K := le_pCoreOf 2 hPK hPnorm hP2
  rw [hbot] at hPle
  exact le_bot_iff.mp hPle

theorem gomiGstar0_le (Y : Subgroup (MulAut W)) : gomiGstar0 Y ≤ Y :=
  sSup_le fun _ hA => hA.1.1.1

theorem gomiGstar0_subgroupOf_normal (Y : Subgroup (MulAut W)) :
    ((gomiGstar0 Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (gomiGstar0_le Y)]
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (sSup (gomiPstar0Set Y)).map (MulAut.conj g).toMonoidHom = sSup (gomiPstar0Set Y)
  exact map_sSup_eq_of_forall_mem_bstar
    (fun A hA => map_conj_mem_gomiPstar0Set hA hg)
    (fun A hA => map_conj_mem_gomiPstar0Set hA (Y.inv_mem hg))

theorem gomiGstar1_le (Y : Subgroup (MulAut W)) : gomiGstar1 Y ≤ Y :=
  sSup_le fun _ hA => hA.1.1.1

theorem gomiGstar1_subgroupOf_normal (Y : Subgroup (MulAut W)) :
    ((gomiGstar1 Y).subgroupOf Y).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (gomiGstar1_le Y)]
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (sSup (gomiPstar1Set Y)).map (MulAut.conj g).toMonoidHom = sSup (gomiPstar1Set Y)
  exact map_sSup_eq_of_forall_mem_bstar
    (fun A hA => map_conj_mem_gomiPstar1Set hA hg)
    (fun A hA => map_conj_mem_gomiPstar1Set hA (Y.inv_mem hg))

end CFSG.GroupTheory
