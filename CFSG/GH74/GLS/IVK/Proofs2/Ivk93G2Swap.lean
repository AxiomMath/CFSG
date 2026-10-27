module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Local.P34

section Conj

variable {X : Type} [Group X]

theorem map_subgroupOf_conj {C A B : Subgroup X} {s : X} (hs : s ∈ C)
    (h : A.map (MulAut.conj s).toMonoidHom = B) :
    (A.subgroupOf C).map (MulAut.conj (⟨s, hs⟩ : ↥C)).toMonoidHom = B.subgroupOf C := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [← h]
    exact Subgroup.mem_map.2 ⟨(a : X), ha, rfl⟩
  · intro hy
    have hy' : (y : X) ∈ A.map (MulAut.conj s).toMonoidHom := by
      rw [h]
      exact hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy'
    have haC : a ∈ C := by
      have h1 : a = s⁻¹ * (y : X) * s := by
        rw [← hay]
        show a = s⁻¹ * (s * a * s⁻¹) * s
        group
      rw [h1]
      exact C.mul_mem (C.mul_mem (C.inv_mem hs) y.2) hs
    refine Subgroup.mem_map.2 ⟨⟨a, haC⟩, Subgroup.mem_subgroupOf.2 ha, ?_⟩
    exact Subtype.ext hay

theorem map_conj_of_subgroupOf {C A B : Subgroup X} {s : X} (hs : s ∈ C) (hA : A ≤ C) (hB : B ≤ C)
    (h : (A.subgroupOf C).map (MulAut.conj (⟨s, hs⟩ : ↥C)).toMonoidHom = B.subgroupOf C) :
    A.map (MulAut.conj s).toMonoidHom = B := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 : (⟨s, hs⟩ : ↥C) * ⟨a, hA ha⟩ * ⟨s, hs⟩⁻¹ ∈ B.subgroupOf C := by
      rw [← h]
      exact Subgroup.mem_map.2 ⟨⟨a, hA ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hy
    have hy' : (⟨y, hB hy⟩ : ↥C) ∈ (A.subgroupOf C).map (MulAut.conj (⟨s, hs⟩ : ↥C)).toMonoidHom := by
      rw [h]
      exact Subgroup.mem_subgroupOf.2 hy
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 hy'
    refine Subgroup.mem_map.2 ⟨(a : X), Subgroup.mem_subgroupOf.1 ha, ?_⟩
    exact congrArg Subtype.val hay

theorem map_conj_map {Y : Type} [Group Y] (φ : X →* Y) {A B : Subgroup X} {s : X}
    (h : A.map (MulAut.conj s).toMonoidHom = B) :
    (A.map φ).map (MulAut.conj (φ s)).toMonoidHom = B.map φ := by
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

end Conj

section Bar

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem swap_to_bar (hctx : Stage2Ctx G z k S) {H : Subgroup G} (hCH : Cen z ≤ H)
    {L₁ L₂ : Subgroup (CentralizerBar z)} {B₁ B₂ : Subgroup (HBar H)}
    (hm₁ : (B₁.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₁)
    (hm₂ : (B₂.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L₂)
    {s : HBar H} (hsT : s ∈ barIn H S)
    (h12 : B₁.map (MulAut.conj s).toMonoidHom = B₂) (h21 : B₂.map (MulAut.conj s).toMonoidHom = B₁) :
    ∃ t ∈ SBar S z, L₁.map (MulAut.conj t).toMonoidHom = L₂ ∧
      L₂.map (MulAut.conj t).toMonoidHom = L₁ := by
  obtain ⟨a, ha, hsa⟩ := Subgroup.mem_map.1 hsT
  have haS : (a : G) ∈ S := Subgroup.mem_subgroupOf.1 ha
  have haC : (a : G) ∈ Cen z := hctx.S_le_Cen haS
  have hsC : s ∈ barIn H (Cen z) := Subgroup.mem_map.2 ⟨a, Subgroup.mem_subgroupOf.2 haC, hsa⟩
  let s' : ↥(barIn H (Cen z)) := ⟨s, hsC⟩
  have hs'eq : cenToBar H hCH s' = toBar z ⟨(a : G), haC⟩ := by
    have h1 := cenToBar_cenMk H hCH ⟨(a : G), haC⟩
    have h2 : (⟨cenMk H hCH ⟨(a : G), haC⟩, cenMk_mem H hCH ⟨(a : G), haC⟩⟩ : ↥(barIn H (Cen z))) = s' :=
      Subtype.ext hsa
    rw [← h2]
    exact h1
  refine ⟨cenToBar H hCH s', ?_, ?_, ?_⟩
  · rw [hs'eq]
    exact Subgroup.mem_map.2 ⟨⟨(a : G), haC⟩, Subgroup.mem_subgroupOf.2 haS, rfl⟩
  · rw [← hm₁, ← hm₂]
    exact map_conj_map (cenToBar H hCH) (map_subgroupOf_conj hsC h12)
  · rw [← hm₁, ← hm₂]
    exact map_conj_map (cenToBar H hCH) (map_subgroupOf_conj hsC h21)

end Bar

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
