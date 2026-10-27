module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1L34QDiag

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem isDiagramNontrivial_F4
    (h510 : Stmt5_1_10_F4) :
    E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, -, -, K₁, hK₁, -, hcases⟩ := h510 G T M L H B D n h.hyp h.notation59
  rcases hcases with ⟨hlt, -⟩ | ⟨-, hBen⟩ | ⟨-, -, hd⟩
  · exfalso
    obtain ⟨hne, hperf, hsub, -⟩ := hK₁
    have hsubK : IsSubnormal K₁ (oTwoUpper H) :=
      A3.subnormal_of_le_of_le hsub hlt.le (oTwoUpper_le H)
    obtain ⟨P, hPK, hPn, hK₁P⟩ := A3.subnormal_exists_normal_of_lt hsubK hlt
    have hPO := h.le_pCoreOf_K_of_normal hPK.le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPK.le).mp hPn)
      (fun hKP => hPK.ne (le_antisymm hPK.le hKP))
    have h2 : IsPGroup 2 ↥K₁ := (pCoreOf_isPGroup 2 _).to_le (hK₁P.trans hPO)
    have hsolv : Group.IsSolvable ↥K₁ := by
      have := h2.isNilpotent
      infer_instance
    apply hne
    have h3 := (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot K₁).mp hsolv
    rwa [(CFSG.Quasithin.perfectCore_eq_self_iff K₁).mpr hperf] at h3
  · exact absurd hBen h.not_isBender
  · exact hd

end Hyp5_1_14

end CFSG.Quasithin.H13
