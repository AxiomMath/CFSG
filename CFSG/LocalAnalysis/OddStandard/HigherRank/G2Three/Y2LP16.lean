module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LPres

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

@[expose] def y2l_pu : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 4, 6, 2, 7, 5, 3, 10, 11, 9, 8, 14, 15, 12, 13]
  invFun := ![1, 0, 4, 7, 2, 6, 3, 5, 11, 10, 8, 9, 14, 15, 12, 13]
  left_inv := by decide
  right_inv := by decide

@[expose] def y2l_pv : Equiv.Perm (Fin 16) where
  toFun := ![1, 0, 4, 5, 2, 3, 7, 6, 10, 11, 9, 8, 13, 14, 15, 12]
  invFun := ![1, 0, 4, 5, 2, 3, 7, 6, 11, 10, 8, 9, 15, 12, 13, 14]
  left_inv := by decide
  right_inv := by decide

@[expose] def y2l_pw : Equiv.Perm (Fin 16) where
  toFun := ![4, 2, 0, 5, 1, 3, 7, 6, 9, 8, 11, 10, 13, 14, 15, 12]
  invFun := ![2, 4, 1, 5, 0, 3, 7, 6, 9, 8, 11, 10, 15, 12, 13, 14]
  left_inv := by decide
  right_inv := by decide

@[expose] def y2l_pr : Equiv.Perm (Fin 16) where
  toFun := ![3, 5, 6, 0, 7, 1, 2, 4, 12, 14, 15, 13, 8, 11, 9, 10]
  invFun := ![3, 5, 6, 0, 7, 1, 2, 4, 12, 14, 15, 13, 8, 11, 9, 10]
  left_inv := by decide
  right_inv := by decide

@[expose] def y2l_ps : Equiv.Perm (Fin 16) where
  toFun := ![12, 14, 15, 0, 13, 1, 4, 2, 3, 5, 6, 7, 11, 8, 10, 9]
  invFun := ![3, 5, 7, 8, 6, 9, 10, 11, 13, 15, 14, 12, 0, 4, 1, 2]
  left_inv := by decide
  right_inv := by decide

theorem y2l_p16_rels : Y2LRels 2 true y2l_pu y2l_pv y2l_pw y2l_pr y2l_ps where
  cuv := (by decide : y2l_pu * y2l_pv = y2l_pv * y2l_pu)
  cuw := (by decide : y2l_pu * y2l_pw = y2l_pw * y2l_pu)
  cvw := (by decide : y2l_pv * y2l_pw = y2l_pw * y2l_pv)
  pu := by decide
  pv := by decide
  pw := by decide
  r2 := by decide
  crs := by decide
  cru := by decide
  crv := by decide
  crw := by decide
  csu := by decide
  csv := by decide
  csw := by decide
  s4 := by decide

theorem y2l_p16_seven : ∀ y ∈ y2l_ws7 2, FreeGroup.lift
    (![y2l_pu, y2l_pv, y2l_pw, y2l_pr, y2l_ps] : Fin 5 → Equiv.Perm (Fin 16))
    (FreeGroup.mk y) ≠ 1 := by
  decide

theorem y2l_seven_of_pres {P : Type} [Group P] {u v w r s : P}
    (hP : IsPres26 2 true P u v w r s) :
    ∀ y ∈ y2l_ws7 2, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → P) (FreeGroup.mk y) ≠ 1 := by
  obtain ⟨h, hb⟩ := hP
  let e := MulEquiv.ofBijective (PresentedGroup.toGroup h) hb
  let ψ : P →* Equiv.Perm (Fin 16) :=
    (PresentedGroup.toGroup (y2l_rels_iff.mpr y2l_p16_rels)).comp e.symm.toMonoidHom
  have hψ : ∀ i : Fin 5, ψ ((![u, v, w, r, s] : Fin 5 → P) i) =
      (![y2l_pu, y2l_pv, y2l_pw, y2l_pr, y2l_ps] : Fin 5 → Equiv.Perm (Fin 16)) i := by
    intro i
    have he : e.symm ((![u, v, w, r, s] : Fin 5 → P) i) = PresentedGroup.of i := by
      rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, PresentedGroup.toGroup.of]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, PresentedGroup.toGroup.of]
  intro y hy h1
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
  apply y2l_p16_seven _ hy
  rw [y2l_lift_ws7_word] at h1 ⊢
  have h2 := congrArg ψ h1
  rwa [map_mul, map_mul, map_pow, map_pow, map_pow, map_one, hψ 0, hψ 1, hψ 2] at h2

end CFSG.OddStandard.HigherRank.G2Three.Sec2
