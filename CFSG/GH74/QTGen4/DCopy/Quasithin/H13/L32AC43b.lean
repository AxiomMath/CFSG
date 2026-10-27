module

public import CFSG.Quasithin.H13.L32AC43b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC43a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem mem_pCoreOf_iff_comm_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {f : G} (hf : f ∈ T) :
    f ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure V H, f * u * f⁻¹ * u⁻¹ ∈ W := by
  rw [← C.act_eq_one_iff_comm ⟨f, C.hTH hf⟩]
  refine ⟨fun h => C.act_eq_one_of_mem h, fun h1 => ?_⟩
  exact C.mem_pCoreOf_of_commute_F4 h1222 h1332 h1334 hf fun k hk => by rw [h1, one_mul, mul_one]

theorem isA2_autE_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    IsA2 C.act.range (C.autE B) :=
  C.toTopW.isA2_autOf hB fun _ hf h => (C.mem_pCoreOf_iff_comm_F4 h1222 h1332 h1334 (hBT hf)).mpr h

theorem index_fixV_autE_le_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    (fixV (C.autE B)).index ≤ Nat.card (C.autE B) ^ 2 :=
  C.toTopW.index_fixV_autOf_le hB fun _ hf h =>
    (C.mem_pCoreOf_iff_comm_F4 h1222 h1332 h1334 (hBT hf)).mpr h

end Top43

end CFSG.Quasithin.H13.L32A.C
