module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup

variable {G : Type} [Group G] [Finite G] (m : G23Model G)

theorem mn0_mem : mn0 m ∈ m.L :=
  mul_mem (mul_mem m.gX0_mem (pow_mem m.gY0_mem 2)) m.gX0_mem

theorem mn1_mem : mn1 m ∈ m.L :=
  mul_mem (mul_mem m.gX1_mem (pow_mem m.gY1_mem 2)) m.gX1_mem

theorem frame_u1_mem : (frameOf m).u₁ ∈ m.L :=
  mul_mem (mul_mem (mn0_mem m) m.gX1_mem) (inv_mem (mn0_mem m))

theorem frame_b1_mem : (frameOf m).b₁ ∈ m.L :=
  mul_mem (mul_mem (mn0_mem m) (mn1_mem m)) (inv_mem (mn0_mem m))

theorem frame_u2_mem : (frameOf m).u₂ ∈ m.L :=
  mul_mem (mul_mem (mn1_mem m) m.gX0_mem) (inv_mem (mn1_mem m))

theorem frame_b2_mem : (frameOf m).b₂ ∈ m.L :=
  mul_mem (mul_mem (mn1_mem m) (mn0_mem m)) (inv_mem (mn1_mem m))

theorem frame_h0_mem : (frameOf m).h₀ ∈ m.L := pow_mem (mn1_mem m) 2

theorem frame_a1_mem : (frameOf m).a₁ ∈ m.L :=
  mul_mem (mul_mem (frame_u1_mem m) (pow_mem (frame_b1_mem m) 3)) (inv_mem (frame_u1_mem m))

theorem frame_a2_mem : (frameOf m).a₂ ∈ m.L :=
  mul_mem (mul_mem (frame_u2_mem m) (pow_mem (frame_b2_mem m) 3)) (inv_mem (frame_u2_mem m))

theorem frame_z_mem : (frameOf m).z ∈ m.L := pow_mem (frame_b1_mem m) 2

theorem frame_S_le : (frameOf m).S ≤ m.L := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  exacts [frame_a1_mem m, frame_b1_mem m, frame_a2_mem m, frame_b2_mem m, frame_h0_mem m]

theorem frame_sigma_not_mem : (frameOf m).σ ∉ m.L := m.gS_not_mem

theorem frame_sigma_sq : (frameOf m).σ * (frameOf m).σ = 1 := m.gS_sq

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
