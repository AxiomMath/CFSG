module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification.HarrisLit

structure POmegaBlock (X : Type) [Group X] : Prop where
  quasisimple : IsQuasisimple X
  isPGroup_center : IsPGroup 2 ↥(center X)
  shape : ∃ n : ℕ, (n = 4 ∨ n = 6) ∧
    CFSG.Blueprint.LieModel (X ⧸ center X) .POmegaPlus n 3 1

@[expose] def POmegaShape (J : Type) [Group J] : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 6) ∧
    CFSG.Blueprint.LieModel (J ⧸ Open.fusionZStar J) .POmegaPlus n 3 1

structure IsPOmegaMember (L : Type) [Group L] (J : Subgroup L) (u : L) : Prop where
  orderOf_eq_two : orderOf u = 2
  mem : u ∈ J
  not_mem_center : u ∉ center L
  subnormal : IsSubnormal J (centralizer ({u} : Set L))
  block : POmegaBlock ↥J

@[expose] def HasPOmegaMember (L : Type) [Group L] : Prop :=
  ∃ (J : Subgroup L) (u : L), IsPOmegaMember L J u

@[expose] def HasPOmegaClassBMember (L : Type) [Group L] : Prop :=
  ∃ (J : Subgroup L) (u : L), IsClassBMember L J u ∧ POmegaShape ↥J

theorem POmegaShape.classBShape {J : Type} [Group J] (h : POmegaShape J) : ClassBShape J := by
  obtain ⟨n, hn, hm⟩ := h
  exact ⟨.POmegaPlus, n, hm, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hn⟩)))⟩

theorem HasPOmegaClassBMember.hasClassBMember {L : Type} [Group L]
    (h : HasPOmegaClassBMember L) : HasClassBMember L := by
  obtain ⟨J, u, hJ, hs⟩ := h
  exact ⟨J, u, hJ, hs.classBShape⟩

theorem POmegaBlock.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : POmegaBlock A) : POmegaBlock B := by
  have hc : (center A).map e.toMonoidHom = center B := Subgroup.map_center_eq e
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e h.quasisimple, ?_, ?_⟩
  · rw [← hc]
    exact h.isPGroup_center.map e.toMonoidHom
  · obtain ⟨n, hn, hm⟩ := h.shape
    exact ⟨n, hn, ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv
      (QuotientGroup.congr (center A) (center B) e hc) hm⟩

theorem IsPOmegaMember.mem_center {L : Type} [Group L] {J : Subgroup L} {u : L}
    (h : IsPOmegaMember L J u) : (⟨u, h.mem⟩ : ↥J) ∈ center ↥J := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hy := h.subnormal.le y.2
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  exact hy

theorem IsPOmegaMember.map_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    {J : Subgroup L} {u : L} (h : IsPOmegaMember L J u) :
    IsPOmegaMember L' (J.map e.toMonoidHom) (e u) := by
  have eJ : ↥J ≃* ↥(J.map e.toMonoidHom) := J.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨?_, Subgroup.mem_map_of_mem _ h.mem, ?_, ?_, POmegaBlock.of_mulEquiv eJ h.block⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.orderOf_eq_two
  · intro hc
    apply h.not_mem_center
    have hc' : e u ∈ (Subgroup.center L).map (e : L →* L') := by
      rwa [Subgroup.map_center_eq e]
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hc'
    rwa [← e.injective hxe]
  · have := h.subnormal.map e.toMonoidHom
    rwa [ComponentClassification.GSThmB.OddQuot.map_centralizer_singleton_equiv] at this

theorem HasPOmegaMember.of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : HasPOmegaMember L) : HasPOmegaMember L' := by
  obtain ⟨J, u, hJ⟩ := h
  exact ⟨J.map e.toMonoidHom, e u, hJ.map_mulEquiv e⟩

end CFSG.OddStandard.HigherRank.F3
