module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Cover

public section

namespace CFSG.QuasithinUnique.Fin257

namespace L3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [CharP F 2]

theorem modelData_L3 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ModelData (projectiveSL 3 F) (projUnitriangular 3 F) V1 V2 where
  center_trivial := center_trivial_M
  sylow := isSylowTwoOf_U
  elem₁ := isElemAbelian_V1
  elem₂ := isElemAbelian_V2
  le₁ := V1_le_U
  le₂ := V2_le_U
  sup := U_eq_sup
  ne := V1_ne_V2
  noncomm := V2_not_le_centralizer_V1
  inter_le_comm := Wg_le_commutator
  cent₁ := cent_V1
  cent₂ := cent_V2
  lt₁ := lt_normalizer_V1
  lt₂ := lt_normalizer_V2
  lt_top₁ := normalizer_V1_lt_top
  lt_top₂ := normalizer_V2_lt_top
  core₁ := core_V1
  core₂ := core_V2
  torus := torus_L3 hn hF

theorem modelPkg_L3 [Finite F] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ModelPkg (projectiveSL 3 F) (projUnitriangular 3 F) V1 V2 where
  data := modelData_L3 hn hF
  cov₁ := (coverElem_L3 hn hF).1
  cov₂ := (coverElem_L3 hn hF).2

end L3

end CFSG.QuasithinUnique.Fin257
