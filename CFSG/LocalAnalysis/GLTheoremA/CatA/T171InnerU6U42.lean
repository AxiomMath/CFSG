module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09U42E27

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem u42Rank_holds : U42Rank := by
  intro Y _ _ hY E hE
  obtain ⟨e⟩ := bridge_u4two hY
  have hE' : IsElemAbelian 3 (E.map (e.trans psp43EquivSU4).toMonoidHom) :=
    hE.map (e.trans psp43EquivSU4).toMonoidHom
  obtain ⟨F, hEF, _, hFcard⟩ := exists_E27_of_isElemAbelian _ hE'
  have hF27 : Nat.card F = 27 := by rw [hFcard]; norm_num
  have hdvd : Nat.card (E.map (e.trans psp43EquivSU4).toMonoidHom) ∣ 27 := by
    rw [← hF27]
    exact Subgroup.card_dvd_of_le hEF
  rw [Subgroup.card_map_of_injective (e.trans psp43EquivSU4).injective] at hdvd
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem u42E9_holds : U42E9 := by
  intro Y _ _ hY
  obtain ⟨e⟩ := bridge_u4two hY
  obtain ⟨z, hz2, hz1, A, hAz, hAel, hAcard⟩ := U42.psp43_exists_inv_E9
  refine ⟨e.symm z, ?_, ?_, A.map e.symm.toMonoidHom, hAel.map e.symm.toMonoidHom, ?_, ?_⟩
  · rw [← map_pow, hz2, map_one]
  · intro h
    apply hz1
    simpa using congrArg e h
  · rw [Subgroup.card_map_of_injective e.symm.injective, hAcard]
    norm_num
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    have hcomm : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp (hAz hx)
    calc e.symm x * e.symm z = e.symm (x * z) := (map_mul e.symm x z).symm
      _ = e.symm (z * x) := by rw [hcomm]
      _ = e.symm z * e.symm x := map_mul e.symm z x

theorem u42E27_holds : U42E27 := by
  intro Y _ _ hY
  obtain ⟨e⟩ := bridge_u4two hY
  obtain ⟨A, hAel, hAcard⟩ := U42.psp43_exists_E27
  refine ⟨A.map e.symm.toMonoidHom, hAel.map e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hAcard]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
