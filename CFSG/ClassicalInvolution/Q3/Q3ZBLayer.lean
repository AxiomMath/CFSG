module

public import CFSG.ClassicalInvolution.Q3.Q3ZAStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6LinSp
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbLocal

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3Z
  CFSG.ClassicalInvolution.Q3.Q3ZA
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup stdPlane form IsHyperbolicPlane
  isHyperbolicPlane_stdPlane longBlock planeGroup_stdPlane)
open scoped MatrixGroups

section Core

theorem Ctx.nonempty_core {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G}
    {z : G} (h : Ctx G K z) : Nonempty (CCore3 (conjClass3 K) K z) := by
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_cdict h.setup.inClass hK h.setup.cls h.shape
  exact ⟨⟨h.setup.inClass, h.setup.setup.1, hK, h.setup.cls, h.setup.setup.2, h.odd3, d⟩⟩

end Core

section Members

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_plane_of_commutes {c : CCore3 Ω K z} (l : Layer3 c) {L : Subgroup G}
    (hL : L ∈ Ω) (hKL : Commutes K L) :
    ∃ P, IsHyperbolicPlane P ∧ L = (planeGroup P).map l.Θ := by
  have hmem : L ∈ centralizingMembers Ω {z} := by
    refine ⟨hL, fun y hy => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hKL _ c.hz.mem y hy
  have hne : L ≠ K := (ne_of_commutes_member c.hΩ c.hK hKL).symm
  obtain ⟨P, hP, hLP⟩ := c.exists_plane_of_ne hmem hne
  exact ⟨P, hP, l.eq_member hmem hP hLP⟩

theorem exists_plane_of_commutes_conj {c : CCore3 Ω K z} (l : Layer3 c) (g : G)
    {L : Subgroup G} (hL : L ∈ Ω) (hc : Commutes (conjSub g K) L) :
    ∃ P, IsHyperbolicPlane P ∧
      L = (planeGroup P).map ((MulAut.conj g).toMonoidHom.comp l.Θ) := by
  have hL' : conjSub g⁻¹ L ∈ Ω := c.hΩ.conjInvariant g⁻¹ L hL
  have hc' : Commutes K (conjSub g⁻¹ L) := by
    have := (commutes_conjSub_iff (K := conjSub g K) (L := L) g⁻¹).2 hc
    rwa [conjSub_inv_conjSub] at this
  obtain ⟨P, hP, hLP⟩ := exists_plane_of_commutes l hL' hc'
  refine ⟨P, hP, ?_⟩
  rw [← Subgroup.map_map]
  show L = conjSub g ((planeGroup P).map l.Θ)
  rw [← hLP, conjSub_conjSub_inv]

end Members

section Generation

theorem card_F3 : Nat.card F3 = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem eq_top_of_planeGroups_le {S : Subgroup (StatedSp 2 F3)}
    (hS : ∀ P, IsHyperbolicPlane P → planeGroup P ≤ S) : S = ⊤ := by
  have hq := Q3T6.isQuasisimple_sp4_of_three_le (K := F3) (by rw [card_F3])
  have : Group.IsPerfect (StatedSp 2 F3) := hq.1
  have hH : Subgroup.normalClosure (planeGroup (stdPlane F3 2 0) : Set (StatedSp 2 F3)) = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
      ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
      (Subgroup.normalClosure (planeGroup (stdPlane F3 2 0) : Set (StatedSp 2 F3))) with h | h
    · exact absurd (Subgroup.le_normalClosure.trans h)
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.planeGroup_not_le_center (by norm_num)
          (isHyperbolicPlane_stdPlane 0))
    · exact h
  rw [eq_top_iff, ← hH]
  show Subgroup.closure (Group.conjugatesOfSet _) ≤ S
  rw [Subgroup.closure_le]
  intro x hx
  rw [Group.mem_conjugatesOfSet_iff] at hx
  obtain ⟨a, ha, hc⟩ := hx
  obtain ⟨g, rfl⟩ := isConj_iff.1 hc
  obtain ⟨P, hP, hPg⟩ :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_planeGroup_eq_map_conj_longBlock
      (K := F3) (n := 2) g 0
  refine hS P hP ?_
  rw [← hPg]
  refine ⟨a, ?_, rfl⟩
  have : a ∈ planeGroup (stdPlane F3 2 0) := ha
  rwa [planeGroup_stdPlane] at this

end Generation

end CFSG.ClassicalInvolution.Q3.Q3ZB
