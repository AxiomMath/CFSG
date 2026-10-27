module

public import CFSG.ClassicalInvolution.ModelFacts.TG3D4Tri
public import CFSG.ClassicalInvolution.ModelFacts.TG3Common

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.CurtisTits (rankOne)
open CFSG.LieType.Universal.Spin (plusDatum quadPlus)
open CFSG.ClassicalInvolution.G2D4Models.Twin (z0 z2 z3 triPerm rankOne_zero rankOne_two
  rankOne_three triality_z0 triality_z2 triality_z3)
open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (fr ne01 ne23)

local notation "𝔽₃" => GaloisField 3 1

local notation "Spin₈" => spinGroup (quadPlus 4 (GaloisField 3 1))

@[expose] noncomputable def fkNode (k : Fin 4) : Subgroup Spin₈ :=
  rankOne (plusDatum 4 𝔽₃ (by norm_num)).rootGroup k

theorem fkNode_zero : fkNode 0 = ((fr 𝔽₃).longSL2 ne01 true false).range :=
  rankOne_zero

theorem fkNode_two : fkNode 2 = ((fr 𝔽₃).longSL2 ne23 true false).range :=
  rankOne_two

theorem fkNode_three : fkNode 3 = ((fr 𝔽₃).longSL2 ne23 true true).range :=
  rankOne_three

@[expose] def FKTri (ρ : MulAut Spin₈) : Prop :=
  ∀ k : Fin 4, (fkNode k).map ρ.toMonoidHom = fkNode (triPerm k)

theorem fkTri_exists : ∃ ρ : MulAut Spin₈, FKTri ρ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.ClassicalInvolution.ModelFacts.TG3.exists_triality3 ⟨Nat.prime_three, le_rfl, le_rfl⟩

theorem FKTri.apply_z0 {ρ : MulAut Spin₈} (h : FKTri ρ) : ρ (z0 𝔽₃) = z2 𝔽₃ :=
  triality_z0 CFSG.ClassicalInvolution.ModelFacts.TG3.two_ne_zero_three ρ h

theorem FKTri.apply_z2 {ρ : MulAut Spin₈} (h : FKTri ρ) : ρ (z2 𝔽₃) = z3 𝔽₃ :=
  triality_z2 CFSG.ClassicalInvolution.ModelFacts.TG3.two_ne_zero_three ρ h

theorem FKTri.apply_z3 {ρ : MulAut Spin₈} (h : FKTri ρ) : ρ (z3 𝔽₃) = z0 𝔽₃ :=
  triality_z3 CFSG.ClassicalInvolution.ModelFacts.TG3.two_ne_zero_three ρ h

theorem FKTri.map_node_zero {ρ : MulAut Spin₈} (h : FKTri ρ) :
    (fkNode 0).map ρ.toMonoidHom = fkNode 2 :=
  h 0

theorem FKTri.map_node_two {ρ : MulAut Spin₈} (h : FKTri ρ) :
    (fkNode 2).map ρ.toMonoidHom = fkNode 3 :=
  h 2

theorem FKTri.map_node_three {ρ : MulAut Spin₈} (h : FKTri ρ) :
    (fkNode 3).map ρ.toMonoidHom = fkNode 0 :=
  h 3

theorem FKTri.map_map_node_two {ρ : MulAut Spin₈} (h : FKTri ρ) :
    (fkNode 2).map (ρ * ρ).toMonoidHom = fkNode 0 := by
  rw [show (ρ * ρ).toMonoidHom = ρ.toMonoidHom.comp ρ.toMonoidHom from rfl,
    ← Subgroup.map_map, h.map_node_two, h.map_node_three]

theorem FKTri.map_map_node_three {ρ : MulAut Spin₈} (h : FKTri ρ) :
    (fkNode 3).map (ρ * ρ).toMonoidHom = fkNode 2 := by
  rw [show (ρ * ρ).toMonoidHom = ρ.toMonoidHom.comp ρ.toMonoidHom from rfl,
    ← Subgroup.map_map, h.map_node_three, h.map_node_zero]

end CFSG.OddStandard.SmallF3.Omega
