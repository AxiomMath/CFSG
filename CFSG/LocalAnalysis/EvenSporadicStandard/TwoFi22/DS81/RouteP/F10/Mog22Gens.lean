module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F10.Mog22Defs
public import CFSG.Quasithin.Background.HCocCode22

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Monster.B.TwoA CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.Code22

@[expose] def mog22ColsA : List ℕ := [1, 1563, 16, 285, 4, 1289, 1868, 405, 256, 1853, 60]

@[expose] def mog22ColsB : List ℕ := [694, 472, 1608, 703, 172, 195, 1898, 1098, 269, 948, 1637]

theorem mog22ColsA_eq : matOf 11 (act11 mogAArr) = mog22ColsA := by
  decide +kernel

theorem mog22ColsB_eq : matOf 11 (act11 mogBArr) = mog22ColsB := by
  decide +kernel

theorem mog22Cols_lt : ∀ c ∈ mog22ColsA ++ mog22ColsB, c < 2 ^ 11 := by
  decide +kernel

@[expose] noncomputable def mog22RhoA : MulAut W11 :=
  rho11 mog22 mog22_le_autPerm ⟨mogA, mogA_mem22⟩

@[expose] noncomputable def mog22RhoB : MulAut W11 :=
  rho11 mog22 mog22_le_autPerm ⟨mogB, mogB_mem22⟩

theorem actsBy_mog22RhoA : ActsBy mog22RhoA mog22ColsA := by
  rw [← mog22ColsA_eq]
  exact actsBy_of_xorLin (xorLin_act11 mogAArr) (rho11_toW mog22 mog22_le_autPerm _ hasArr_mogA)

theorem actsBy_mog22RhoB : ActsBy mog22RhoB mog22ColsB := by
  rw [← mog22ColsB_eq]
  exact actsBy_of_xorLin (xorLin_act11 mogBArr) (rho11_toW mog22 mog22_le_autPerm _ hasArr_mogB)

theorem mog22RhoA_mem : mog22RhoA ∈ (rho11 mog22 mog22_le_autPerm).range := ⟨_, rfl⟩

theorem mog22RhoB_mem : mog22RhoB ∈ (rho11 mog22 mog22_le_autPerm).range := ⟨_, rfl⟩

theorem range_rho11_mog22_le_closure :
    (rho11 mog22 mog22_le_autPerm).range ≤ Subgroup.closure {mog22RhoA, mog22RhoB} := by
  rw [MonoidHom.range_eq_map,
    ← CFSG.Sporadic.Mathieu.closure_pair_eq_top mog22_eq_closure mogA_mem22 mogB_mem22,
    MonoidHom.map_closure, Set.image_pair]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
