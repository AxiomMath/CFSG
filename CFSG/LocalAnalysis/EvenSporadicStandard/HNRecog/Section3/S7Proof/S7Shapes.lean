module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Dt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SymCent.Tt

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_Gxyz_equiv_centralizer {a x t : G} (ht : t ∈ Gxy a x) (φ : ↥(Gxy a x) ≃* Sym 7) :
    Nonempty (↥(Gxyz a t x) ≃* ↥(Subgroup.centralizer ({φ ⟨t, ht⟩} : Set (Sym 7)))) := by
  have hL : ∀ g : G, g ∈ Gxyz a t x ↔ g ∈ Gxy a x ∧ g * t = t * g := by
    intro g
    simp only [mem_Gxyz, mem_Gxy, mem_Gx]
    exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1.symm⟩,
      fun h => ⟨h.1.1, h.2.symm, h.1.2⟩⟩
  obtain ⟨e⟩ := s7_centralizer_subtype_equiv (Gxy a x) ⟨t, ht⟩ (Gxyz a t x) hL
  exact ⟨e.symm.trans (centralizerMulEquiv φ (rfl : φ ⟨t, ht⟩ = φ ⟨t, ht⟩))⟩

theorem s7_shape_i {a z x t : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (ht : t ∈ orb2A a a ∩ orb2A a x) : IsShapeZ2TimesSym 5 ↥(Gxyz a t x) := by
  exact H.perp.self.shape_3A t ht.1 x (s7_mem_sSet_four H hx.1 hx.2.1 ht) t ht

theorem s7_shape_ii [Finite G] {a z x t : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (ht : t ∈ orb2B a z a ∩ orb2B a z x) : IsShapeD8TimesS3 ↥(Gxyz a t x) := by
  obtain ⟨φ⟩ := s7_shape H hx
  have hmem : t ∈ Gxy a x := (s7_E2_subset H hx.1 ht).1
  obtain ⟨e1⟩ := s7_Gxyz_equiv_centralizer hmem φ
  obtain ⟨e2⟩ := symCent_dt 3 (σ := φ ⟨t, hmem⟩)
    ((s7_cycleType H x hx φ ⟨t, hmem⟩).2.1 ht)
  exact ⟨e1.trans e2⟩

theorem s7_shape_iii [Finite G] {a z x t : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (ht : t ∈ orb2BB a z a ∩ orb2BB a z x) : IsShapeZ2WrS3 ↥(Gxyz a t x) := by
  obtain ⟨φ⟩ := s7_shape H hx
  have hmem : t ∈ Gxy a x := (s7_E3_subset H hx.1 ht).1
  obtain ⟨e1⟩ := s7_Gxyz_equiv_centralizer hmem φ
  obtain ⟨e2⟩ := symCent_tt 1 (σ := φ ⟨t, hmem⟩)
    ((s7_cycleType H x hx φ ⟨t, hmem⟩).2.2 ht)
  exact ⟨e1.trans (e2.trans MulEquiv.prodUnique)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
