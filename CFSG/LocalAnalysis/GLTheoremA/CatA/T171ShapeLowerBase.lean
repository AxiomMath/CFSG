module

public import CFSG.RankThree.PartTwo.Census.TripleCoverLift
public import CFSG.RankThree.CentralCover.SteinbergBNOddExtensionCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open

open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift (powOneSubgroup mem_powOneSubgroup)
open CFSG.RankThree.CentralCover (card_inf_ker_mul_card_map)

theorem exists_elemAbelian_index_of_lift {Y T : Type*} [Group Y] [Finite Y] [Group T]
    {φ : Y →* T} {p : ℕ} {D : Subgroup T}
    (hcomm : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x)
    (hlift : ∀ e ∈ D, ∃ y : Y, φ y = e ∧ y ^ p = 1) :
    ∃ E : Subgroup Y, IsElemAbelian p E ∧ E.map φ = D ∧
      Nat.card D * Nat.card ↥(E ⊓ φ.ker) = Nat.card E := by
  have hmap : (powOneSubgroup φ D p hcomm).map φ = D := by
    ext e
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_powOneSubgroup.mp hy).1
    · intro he
      obtain ⟨y, hy, hyp⟩ := hlift e he
      exact ⟨y, mem_powOneSubgroup.mpr ⟨hy ▸ he, hyp⟩, hy⟩
  refine ⟨powOneSubgroup φ D p hcomm, ?_, hmap, ?_⟩
  · refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (mem_powOneSubgroup.mp a.2).1 _
      (mem_powOneSubgroup.mp b.2).1)⟩⟩, fun x hx => (mem_powOneSubgroup.mp hx).2⟩
  · have h := card_inf_ker_mul_card_map φ (powOneSubgroup φ D p hcomm)
    rw [hmap] at h
    exact (Nat.mul_comm _ _).trans h

theorem inf_centralizer_map_eq {G : Type} [Group G] {L : Subgroup G} {E : Subgroup ↥L} :
    (E.map L.subtype) ⊓ Subgroup.centralizer (L : Set G) =
      (E ⊓ Subgroup.center ↥L).map L.subtype := by
  ext x
  constructor
  · rintro ⟨hxE, hxC⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hxE
    refine Subgroup.mem_map.mpr ⟨e, ⟨he, ?_⟩, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  · rintro ⟨e, ⟨he, hcen⟩, rfl⟩
    refine ⟨Subgroup.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨y, hy⟩)

theorem card_inf_center_map_eq {G : Type} [Group G] {L : Subgroup G} {E : Subgroup ↥L} :
    Nat.card ↥(E.map L.subtype) = Nat.card E ∧
      Nat.card ↥((E.map L.subtype) ⊓ Subgroup.centralizer (L : Set G)) =
        Nat.card ↥(E ⊓ Subgroup.center ↥L) := by
  refine ⟨Subgroup.card_map_of_injective L.subtype_injective, ?_⟩
  rw [inf_centralizer_map_eq]
  exact Subgroup.card_map_of_injective L.subtype_injective

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
