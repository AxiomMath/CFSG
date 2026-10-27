module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Elements
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Stabilizer

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] noncomputable def Zq : Subgroup Q3 := Subgroup.closure ({aElt, bElt} ∪ Set.range epsElt)

@[expose] noncomputable def E0 : Subgroup Q3 := Subgroup.closure (Set.range epsElt)

@[expose] noncomputable def L0 : Subgroup Q3 :=
  Zp ⊓ MulAction.stabilizer Q3 x1

@[expose] noncomputable def Ze : Subgroup Q3 :=
  MulAction.stabilizer Q3 ({x0, x1} : Set Ω)

@[expose] noncomputable def Ze'' : Subgroup Q3 :=
  MulAction.stabilizer Q3 ({x1, x2} : Set Ω)

@[expose] noncomputable def Y0 : Subgroup Q3 := Zp ⊓ Ze''

@[expose] noncomputable def B0 : Subgroup Q3 := L0 ⊓ Zq

theorem aElt_mem_Zq : aElt ∈ Zq := Subgroup.subset_closure (Or.inl (Or.inl rfl))

theorem bElt_mem_Zq : bElt ∈ Zq := Subgroup.subset_closure (Or.inl (Or.inr rfl))

theorem epsElt_mem_E0 (j : Fin 11) : epsElt j ∈ E0 := Subgroup.subset_closure ⟨j, rfl⟩

theorem E0_le_Zq : E0 ≤ Zq := Subgroup.closure_mono Set.subset_union_right

theorem epsElt_mem_Zq (j : Fin 11) : epsElt j ∈ Zq := E0_le_Zq (epsElt_mem_E0 j)

theorem mem_stabilizer_pair_iff {G α : Type*} [Group G] [MulAction G α] {x y : α} {g : G} :
    g ∈ MulAction.stabilizer G ({x, y} : Set α) ↔
      (g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x) := by
  rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton,
    Set.pair_eq_pair_iff]

theorem mem_Ze_iff {g : Q3} :
    g ∈ Ze ↔ (g • x0 = x0 ∧ g • x1 = x1) ∨ (g • x0 = x1 ∧ g • x1 = x0) :=
  mem_stabilizer_pair_iff

theorem mem_Ze''_iff {g : Q3} :
    g ∈ Ze'' ↔ (g • x1 = x1 ∧ g • x2 = x2) ∨ (g • x1 = x2 ∧ g • x2 = x1) :=
  mem_stabilizer_pair_iff

theorem mem_L0_iff {g : Q3} : g ∈ L0 ↔ g ∈ Zp ∧ g • x1 = x1 :=
  by simp [L0, MulAction.mem_stabilizer_iff]

theorem tauElt_mem_Ze :
    tauElt ∈ Ze :=
  mem_Ze_iff.2 (Or.inr ⟨tauElt_smul_x0, tauElt_smul_x1⟩)

theorem L0_le_Zp : L0 ≤ Zp := inf_le_left

theorem B0_le_L0 : B0 ≤ L0 := inf_le_left

theorem B0_le_Zq : B0 ≤ Zq := inf_le_right

theorem Y0_le_Zp : Y0 ≤ Zp := inf_le_left

theorem Y0_le_Ze'' : Y0 ≤ Ze'' := inf_le_right

theorem L0_le_Ze :
    L0 ≤ Ze := by
  intro g hg
  obtain ⟨hg0, hg1⟩ := mem_L0_iff.1 hg
  rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff] at hg0
  exact mem_Ze_iff.2 (Or.inl ⟨hg0, hg1⟩)

theorem Ze_inf_stabilizer :
    Ze ⊓ MulAction.stabilizer Q3 x0 = L0 := by
  ext g
  rw [Subgroup.mem_inf, mem_L0_iff, Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, mem_Ze_iff]
  constructor
  · rintro ⟨hZ | hZ, h0⟩
    · exact ⟨h0, hZ.2⟩
    · exact absurd (hZ.1.symm.trans h0).symm x0_ne_x1
  · rintro ⟨h0, h1⟩
    exact ⟨Or.inl ⟨h0, h1⟩, h0⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
