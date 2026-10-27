module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.ThreeTransp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Subtype
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Z2S5Equiv

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_closure_local {a z x d : G} (H : S7Hyps a z) (hx : x ∈ orb3A a a)
    (hd : d ∈ orb2A a a ∩ orb2A a x)
    (hstar : ∃ t ∈ orb2A a a ∩ orb2A a x, t ≠ d ∧ d * t = t * d) :
    Gxy a x ⊓ Gx d ≤ Subgroup.closure ((orb2A a a ∩ orb2A a x) ∩ (Gx d : Set G)) := by
  let M : Subgroup G := Gxy a x ⊓ Gx d
  let D : Set G := orb2A a a ∩ orb2A a x
  let Y : Set ↥M := M.subtype ⁻¹' (D ∩ (Gx d : Set G))
  have hx4 : x ∈ sSet a z d 4 := s7_mem_sSet_four H hx.1 hx.2.1 hd
  have hshape : IsShapeZ2TimesSym 5 ↥(Gxyz a d x) :=
    H.perp.self.shape_3A d hd.1 x hx4 d hd
  have hM_eq : M = Gxyz a d x := by
    show Gxy a x ⊓ Gx d = Gxyz a d x
    ext g
    simp only [mem_Gxyz, mem_Gxy, Subgroup.mem_inf]
    tauto
  have hshapeM : IsShapeZ2TimesSym 5 ↥M := by
    obtain ⟨e⟩ := hshape
    exact ⟨(MulEquiv.subgroupCongr hM_eq).trans e⟩
  obtain ⟨φ⟩ := hshapeM
  have hinv : ∀ y ∈ Y, y ^ 2 = 1 ∧ y ≠ 1 := by
    intro y hy
    have hyD : (y : G) ∈ D := (hy : (y : G) ∈ D ∩ (Gx d : Set G)).1
    have hsq : (y : G) ^ 2 = 1 := s7_sq_of_isConj_a H hyD.1.1
    have hne : (y : G) ≠ 1 := s7_ne_one_of_isConj_a H hyD.1.1
    refine ⟨Subtype.ext ?_, ?_⟩
    · simpa using hsq
    · intro h
      exact hne (by simpa using congrArg Subtype.val h)
  have hnorm : ∀ y ∈ Y, ∀ m : ↥M, m * y * m⁻¹ ∈ Y := by
    intro y hy m
    have hy' : (y : G) ∈ D ∩ (Gx d : Set G) := hy
    have hyD : (y : G) ∈ D := hy'.1
    have hyGx : (y : G) ∈ Gx d := hy'.2
    have hmGxy : (m : G) ∈ Gxy a x := m.2.1
    have hmGx : (m : G) ∈ Gx d := m.2.2
    have hconjD : (m : G) * (y : G) * (m : G)⁻¹ ∈ D := s7_conj_D hmGxy hyD
    have hconjGx : (m : G) * (y : G) * (m : G)⁻¹ ∈ Gx d :=
      mul_mem (mul_mem hmGx hyGx) (inv_mem hmGx)
    show M.subtype (m * y * m⁻¹) ∈ D ∩ (Gx d : Set G)
    simpa using And.intro hconjD hconjGx
  have h3 : ∀ y ∈ Y, ∀ y' ∈ Y, (y * y') ^ 3 = 1 ∨ (y * y') ^ 2 = 1 := by
    intro y hy y' hy'
    have hyD : (y : G) ∈ D := (hy : (y : G) ∈ D ∩ (Gx d : Set G)).1
    have hy'D : (y' : G) ∈ D := (hy' : (y' : G) ∈ D ∩ (Gx d : Set G)).1
    rcases s7_three H hx hyD hy'D with h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Subtype.ext (by simpa using h))
  have hdM : d ∈ M := ⟨(s7_D_subset H hx.1 hd).1, self_mem_Gx d⟩
  have hdY : (⟨d, hdM⟩ : ↥M) ∈ Y := by
    show M.subtype ⟨d, hdM⟩ ∈ D ∩ (Gx d : Set G)
    exact ⟨hd, self_mem_Gx d⟩
  have hdc : ∀ m : ↥M, m * (⟨d, hdM⟩ : ↥M) = (⟨d, hdM⟩ : ↥M) * m := by
    intro m
    apply Subtype.ext
    have hcomm : d * (m : G) = (m : G) * d := mem_Gx.1 m.2.2
    simpa using hcomm.symm
  obtain ⟨t, htD, htd, hdt⟩ := hstar
  have htM : t ∈ M := ⟨(s7_D_subset H hx.1 htD).1, mem_Gx.2 hdt⟩
  have htY : (⟨t, htM⟩ : ↥M) ∈ Y := by
    show M.subtype ⟨t, htM⟩ ∈ D ∩ (Gx d : Set G)
    exact ⟨htD, mem_Gx.2 hdt⟩
  have htne : (⟨t, htM⟩ : ↥M) ≠ (⟨d, hdM⟩ : ↥M) := by
    intro h
    exact htd (by simpa using congrArg Subtype.val h)
  have hclosure : Subgroup.closure Y = ⊤ :=
    s7_closure_top_of_equiv φ Y hinv hnorm h3 hdY hdc ⟨⟨t, htM⟩, htY, htne⟩
  have hS : D ∩ (Gx d : Set G) ⊆ (M : Set G) := by
    intro s hs
    exact ⟨(s7_D_subset H hx.1 hs.1).1, hs.2⟩
  intro g hg
  have hgM : (⟨g, hg⟩ : ↥M) ∈ Subgroup.closure Y := by
    rw [hclosure]
    exact Subgroup.mem_top _
  have hgcl : ((⟨g, hg⟩ : ↥M) : G) ∈ Subgroup.closure (D ∩ (Gx d : Set G)) :=
    (s7_mem_closure_subtype_iff M (D ∩ (Gx d : Set G)) hS ⟨g, hg⟩).2 hgM
  show g ∈ Subgroup.closure (D ∩ (Gx d : Set G))
  simpa using hgcl

end CFSG.EvenSporadicStandard.HNRecog.Section3
