module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2Conj
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Transport

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (PstarSet)

variable {W : Type} [CommGroup W]

private theorem map_conj_inSubgroup_pPrimePCore_gn {Y : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut W))) :
    (CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y).map (MulAut.conj g).toMonoidHom =
      CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
  have hY : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let e : ↥Y ≃* ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    MulEquiv.subgroupMap (MulAut.conj g) Y
  have h1 : (CFSG.GH74.GLS.pPrimePCore 2 ↥Y).map e.toMonoidHom =
      CFSG.GH74.GLS.pPrimePCore 2 ↥(Y.map (MulAut.conj g).toMonoidHom) :=
    CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Transport.pPrimePCore_map_iso 2 e
  have hcomp : (Y.map (MulAut.conj g).toMonoidHom).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp Y.subtype := by
    ext x
    rfl
  have hmain : CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2)
        (Y.map (MulAut.conj g).toMonoidHom) =
      (CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y).map
        (MulAut.conj g).toMonoidHom := by
    unfold CFSG.inSubgroup
    rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [hY] at hmain
  exact hmain.symm

theorem map_conj_mem_pstarSet_of_mem_normalizer {Y A : Subgroup (MulAut W)} {g : MulAut W}
    (hA : A ∈ PstarSet Y) (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut W))) :
    A.map (MulAut.conj g).toMonoidHom ∈ PstarSet Y := by
  have hA' := (mem_pstarSet_iff_of_le (Y := ⊤) (S := Y) (A := A) le_top).mp hA
  refine (mem_pstarSet_iff_of_le (Y := ⊤) (S := Y)
    (A := A.map (MulAut.conj g).toMonoidHom) le_top).mpr
    ⟨map_conj_mem_pstarSet (Y := ⊤) hA'.1 (Subgroup.mem_top g), ?_⟩
  calc A.map (MulAut.conj g).toMonoidHom ≤ Y.map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hA'.2
    _ = Y := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

theorem map_conj_mem_gomiPstar0Set_of_mem_normalizer {Y A : Subgroup (MulAut W)}
    {g : MulAut W} (hA : A ∈ gomiPstar0Set Y)
    (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut W))) :
    A.map (MulAut.conj g).toMonoidHom ∈ gomiPstar0Set Y := by
  obtain ⟨hAstar, hAle⟩ := hA
  refine ⟨map_conj_mem_pstarSet_of_mem_normalizer hAstar hg, ?_⟩
  have heq := map_conj_inSubgroup_pPrimePCore_gn (Y := Y) (g := g) hg
  exact (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hAle).trans (le_of_eq heq)

theorem map_conj_mem_gomiPstar1Set_of_mem_normalizer {Y A : Subgroup (MulAut W)}
    {g : MulAut W} (hA : A ∈ gomiPstar1Set Y)
    (hg : g ∈ Subgroup.normalizer (Y : Set (MulAut W))) :
    A.map (MulAut.conj g).toMonoidHom ∈ gomiPstar1Set Y := by
  obtain ⟨hAstar, hA0⟩ := hA
  refine ⟨map_conj_mem_pstarSet_of_mem_normalizer hAstar hg, fun hmem => hA0 ?_⟩
  have hmem' : (A.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj g⁻¹).toMonoidHom ∈ gomiPstar0Set Y :=
    map_conj_mem_gomiPstar0Set_of_mem_normalizer hmem
      ((Subgroup.normalizer (Y : Set (MulAut W))).inv_mem hg)
  have hinv : MulAut.conj g⁻¹ = (MulAut.conj g).symm := by
    rw [← MulAut.inv_def, ← map_inv]
  rw [hinv, CFSG.LocalCores.map_map_symm] at hmem'
  exact hmem'

private theorem mem_normalizer_sSup_of_map_mem_gn {Γ : Type*} [Group Γ]
    {𝒦 : Set (Subgroup Γ)} {g : Γ} (h : ∀ K ∈ 𝒦, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦)
    (h' : ∀ K ∈ 𝒦, K.map (MulAut.conj g⁻¹).toMonoidHom ∈ 𝒦) :
    g ∈ Subgroup.normalizer ((sSup 𝒦 : Subgroup Γ) : Set Γ) := by
  have key : ∀ k : Γ, (∀ K ∈ 𝒦, K.map (MulAut.conj k).toMonoidHom ∈ 𝒦) →
      (sSup 𝒦).map (MulAut.conj k).toMonoidHom ≤ sSup 𝒦 := by
    intro k hk
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hk K hK)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g h ⟨x, hx, rfl⟩, fun hx => ?_⟩
  have h1 := key g⁻¹ h' ⟨_, hx, rfl⟩
  simpa [mul_assoc] using h1

theorem normalizer_le_normalizer_gomiGstar0 (Y : Subgroup (MulAut W)) :
    Subgroup.normalizer (Y : Set (MulAut W)) ≤
      Subgroup.normalizer (gomiGstar0 Y : Set (MulAut W)) := by
  intro g hg
  exact mem_normalizer_sSup_of_map_mem_gn
    (fun A hA => map_conj_mem_gomiPstar0Set_of_mem_normalizer hA hg)
    (fun A hA => map_conj_mem_gomiPstar0Set_of_mem_normalizer hA
      ((Subgroup.normalizer (Y : Set (MulAut W))).inv_mem hg))

theorem normalizer_le_normalizer_gomiGstar1 (Y : Subgroup (MulAut W)) :
    Subgroup.normalizer (Y : Set (MulAut W)) ≤
      Subgroup.normalizer (gomiGstar1 Y : Set (MulAut W)) := by
  intro g hg
  exact mem_normalizer_sSup_of_map_mem_gn
    (fun A hA => map_conj_mem_gomiPstar1Set_of_mem_normalizer hA hg)
    (fun A hA => map_conj_mem_gomiPstar1Set_of_mem_normalizer hA
      ((Subgroup.normalizer (Y : Set (MulAut W))).inv_mem hg))

end CFSG.GroupTheory
