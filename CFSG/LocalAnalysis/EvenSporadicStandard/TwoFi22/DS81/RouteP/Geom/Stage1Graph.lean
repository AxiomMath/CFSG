module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.S1

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom

open CFSG.Monster.B.Recog
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

section Swap

@[expose] noncomputable def s2 : Q3 := Classical.choose exists_s2

theorem s2_spec : s2 ∈ Zp ⊓ Zq ⊓ Ze'' ∧ s2 • x1 = x2 ∧ s2 • x2 = x1 :=
  Classical.choose_spec exists_s2

theorem s2_mem_Zp : s2 ∈ Zp := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 s2_spec.1).1).1

theorem s2_mem_Zq : s2 ∈ Zq := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 s2_spec.1).1).2

theorem s2_mem_Ze'' : s2 ∈ Ze'' := (Subgroup.mem_inf.1 s2_spec.1).2

theorem s2_smul_x1 : s2 • x1 = x2 := s2_spec.2.1

theorem s2_smul_x2 : s2 • x2 = x1 := s2_spec.2.2

@[expose] noncomputable def s2Z : Zp := ⟨s2, s2_mem_Zp⟩

theorem s2Z_smul_x1 : (s2Z : Q3) • x1 = x2 := s2_smul_x1

theorem s2Z_smul_x2 : (s2Z : Q3) • x2 = x1 := s2_smul_x2

end Swap

section Subgroups

@[expose] noncomputable def XpZ : Subgroup Zp := L0.subgroupOf Zp

@[expose] noncomputable def XqZ : Subgroup Zp := (Zp ⊓ Zq).subgroupOf Zp

@[expose] noncomputable def XeZ : Subgroup Zp := Y0.subgroupOf Zp

theorem mem_XpZ_iff {z : Zp} : z ∈ XpZ ↔ (z : Q3) • x1 = x1 := by
  rw [XpZ, Subgroup.mem_subgroupOf, mem_L0_iff]
  exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩

theorem mem_XqZ_iff {z : Zp} : z ∈ XqZ ↔ (z : Q3) ∈ Zq := by
  rw [XqZ, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩

theorem mem_XeZ_iff {z : Zp} :
    z ∈ XeZ ↔ ((z : Q3) • x1 = x1 ∧ (z : Q3) • x2 = x2) ∨
      ((z : Q3) • x1 = x2 ∧ (z : Q3) • x2 = x1) := by
  rw [XeZ, Subgroup.mem_subgroupOf, Y0, Subgroup.mem_inf, mem_Ze''_iff]
  exact ⟨fun h => h.2, fun h => ⟨z.2, h⟩⟩

theorem XpZ_eq_stabilizer : XpZ = MulAction.stabilizer Zp x1 := by
  ext z
  rw [mem_XpZ_iff, MulAction.mem_stabilizer_iff]
  rfl

end Subgroups

section SwapSubgroups

theorem s2Z_not_mem_XpZ : s2Z ∉ XpZ := by
  intro h
  rw [mem_XpZ_iff, s2Z_smul_x1] at h
  exact x1_ne_x2 h.symm

theorem s2Z_mul_self_mem_XpZ : s2Z * s2Z ∈ XpZ := by
  rw [mem_XpZ_iff, Subgroup.coe_mul, mul_smul, s2Z_smul_x1, s2Z_smul_x2]

theorem s2Z_mem_XqZ : s2Z ∈ XqZ := mem_XqZ_iff.2 s2_mem_Zq

end SwapSubgroups

section Points

@[expose] noncomputable def pt : Zp ⧸ XpZ → Ω :=
  cosetMap Zp.subtype XpZ x1 fun _ ha => mem_XpZ_iff.1 ha

theorem pt_mk (z : Zp) : pt (z : Zp ⧸ XpZ) = (z : Q3) • x1 := rfl

theorem pt_smul (g : Zp) (v : Zp ⧸ XpZ) : pt (g • v) = (g : Q3) • pt v := by
  induction v using QuotientGroup.induction_on with
  | H z =>
    have e : (g • (z : Zp ⧸ XpZ)) = ((g * z : Zp) : Zp ⧸ XpZ) := rfl
    rw [e, pt_mk, pt_mk, Subgroup.coe_mul, mul_smul]

theorem pt_injective : Function.Injective pt := by
  intro v w h
  induction v using QuotientGroup.induction_on with
  | H a =>
    induction w using QuotientGroup.induction_on with
    | H b =>
      rw [pt_mk, pt_mk] at h
      rw [QuotientGroup.eq, mem_XpZ_iff, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, ← h,
        inv_smul_smul]

@[expose] noncomputable def base : Zp ⧸ XpZ := ((1 : Zp) : Zp ⧸ XpZ)

theorem pt_base : pt base = x1 := by
  rw [base, pt_mk, Subgroup.coe_one, one_smul]

end Points

section PointsZp

theorem Δ_adj_x0_pt (v : Zp ⧸ XpZ) : Δ.Adj x0 (pt v) := by
  induction v using QuotientGroup.induction_on with
  | H z => exact Δ_adj_x0_iff.2 ⟨z, rfl⟩

theorem exists_pt {u : Ω} (hu : Δ.Adj x0 u) : ∃ v : Zp ⧸ XpZ, pt v = u := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := Δ_adj_x0_iff.1 hu
  exact ⟨((⟨k, hk⟩ : Zp) : Zp ⧸ XpZ), rfl⟩

end PointsZp

section Graph

@[expose] noncomputable def Γ23 : SimpleGraph (Zp ⧸ XpZ) := cosetGraph XpZ s2Z

theorem Γ23_adj_smul (g : Zp) (v w : Zp ⧸ XpZ) : Γ23.Adj (g • v) (g • w) ↔ Γ23.Adj v w := by
  refine ⟨fun h => ?_, cosetGraph_adj_smul g⟩
  have := cosetGraph_adj_smul g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at this

end Graph

section Adjacency

theorem Γ23_adj_iff (v w : Zp ⧸ XpZ) : Γ23.Adj v w ↔ Δ.Adj (pt v) (pt w) := by
  induction v using QuotientGroup.induction_on with
  | H a =>
    induction w using QuotientGroup.induction_on with
    | H b =>
      rw [Γ23, cosetGraph_adj_mk_iff s2Z_not_mem_XpZ s2Z_mul_self_mem_XpZ, pt_mk, pt_mk]
      constructor
      · rintro ⟨c, hc, h⟩
        have hpt : pt (b : Zp ⧸ XpZ) = pt ((a * c * s2Z : Zp) : Zp ⧸ XpZ) := congrArg pt h
        rw [pt_mk, pt_mk, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul,
          s2Z_smul_x1] at hpt
        rw [hpt]
        have hc1 : (c : Q3) • x1 = x1 := mem_XpZ_iff.1 hc
        have h1 := (Δ_adj_smul (c : Q3) x1 x2).2 Δ_adj_x1_x2
        rw [hc1] at h1
        exact (Δ_adj_smul (a : Q3) x1 ((c : Q3) • x2)).2 h1
      · intro h
        have hu0 : Δ.Adj x0 (((a⁻¹ * b : Zp) : Q3) • x1) := Δ_adj_x0_iff.2 ⟨a⁻¹ * b, rfl⟩
        have hu1 : Δ.Adj x1 (((a⁻¹ * b : Zp) : Q3) • x1) := by
          have := (Δ_adj_smul ((a : Q3)⁻¹) ((a : Q3) • x1) ((b : Q3) • x1)).2 h
          rw [inv_smul_smul] at this
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
          exact this
        have hmem : ((a⁻¹ * b : Zp) : Q3) • x1 ∈ MulAction.orbit A1gen x2 := by
          rw [← commonNeighbors_x0_x1_eq, SimpleGraph.mem_commonNeighbors]
          exact ⟨hu0, hu1⟩
        obtain ⟨⟨c, hc⟩, hcu⟩ := hmem
        have hcL := A1gen_le_L0 hc
        have hcZ : c ∈ Zp := (mem_L0_iff.1 hcL).1
        have hc1 : c • x1 = x1 := (mem_L0_iff.1 hcL).2
        refine ⟨⟨c, hcZ⟩, mem_XpZ_iff.2 hc1, ?_⟩
        apply pt_injective
        rw [pt_mk, pt_mk, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul, s2Z_smul_x1]
        have hcu' : c • x2 = ((a⁻¹ * b : Zp) : Q3) • x1 := hcu
        show (b : Q3) • x1 = (a : Q3) • c • x2
        rw [hcu']
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, smul_inv_smul]

theorem Γ23_adj_base_iff (v : Zp ⧸ XpZ) : Γ23.Adj base v ↔ Δ.Adj x1 (pt v) := by
  rw [Γ23_adj_iff, pt_base]

end Adjacency

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
