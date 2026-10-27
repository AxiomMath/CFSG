module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.PairF4Normal

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.StandardType.RootCentExc

section Ambient

variable {F : Type} [Field F]

theorem neg_one_zpow_eq_of_mod_two {a b : ℤ} (h : (a - b) % 2 = 0) :
    (-1 : Fˣ) ^ a = (-1 : Fˣ) ^ b := by
  have hev : Even (a - b) := Int.even_iff.2 h
  have : a = b + (a - b) := by omega
  rw [this, zpow_add, hev.neg_one_zpow, mul_one]


theorem f4_dtheta_eq_torusElt :
    rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) =
      torusElt .F4 F ⟨1, by decide⟩ (-1) * torusElt .F4 F ⟨3, by decide⟩ (-1) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext j
  have hmod : ∀ j : Fin (Tag.rank .F4),
      (((if j.val = 0 then (2 : ℤ) else 0) / 2) -
        (Tag.cartan .F4 ⟨1, by decide⟩ j + Tag.cartan .F4 ⟨3, by decide⟩ j)) % 2 = 0 := by
    decide
  simp only [Pi.mul_apply, corootDiagF4, iform_thetaF4_single, ← zpow_add]
  exact neg_one_zpow_eq_of_mod_two (hmod j)

theorem f4_dtheta_mem_layer :
    rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) ∈
      Subgroup.closure (leviGens .F4 F JF4) := by
  rw [f4_dtheta_eq_torusElt]
  have h : ∀ k : Fin (Tag.rank .F4), k ∈ JF4 →
      torusElt .F4 F k (-1) ∈ Subgroup.closure (leviGens .F4 F JF4) := fun k hk =>
    mul_mem (weylElt_mem_subsystemGroup hk _) (weylElt_mem_subsystemGroup hk _)
  exact mul_mem (h _ (by simp [JF4])) (h _ (by simp [JF4]))

theorem f4_dtheta_ne_one (hF : ringChar F ≠ 2) :
    rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) ≠ (1 : ModGL .F4 F) := by
  intro h
  rw [← rootDiagUnit_one] at h
  have h1 := congrFun (rootDiagUnit_injective h) ⟨0, by decide⟩
  simp only [corootDiagF4, iform_thetaF4_single, Pi.one_apply] at h1
  exact neg_one_ne_one_units_of_ringChar hF (by simpa using h1)


theorem f4_dtheta_commute_layer {x : ModGL .F4 F}
    (hx : x ∈ Subgroup.closure (leviGens .F4 F JF4)) :
    x * rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) =
      rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) * x := by
  rw [← rootTorusSL2_thetaF4 (-1)]
  exact f4_leviGens_commute_rootSL2 hx _

theorem exists_dtheta_f4 (hF : ringChar F ≠ 2) :
    ∃ d : ↥(adjointGroup .F4 F),
      (d : ModGL .F4 F) = rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) ∧ d ≠ 1 ∧
      (d : ModGL .F4 F) ∈ Subgroup.closure (leviGens .F4 F JF4) ∧
      ∀ x ∈ Subgroup.closure (leviGens .F4 F JF4),
        x * (d : ModGL .F4 F) = (d : ModGL .F4 F) * x := by
  have hmem : rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) ∈ adjointGroup .F4 F := by
    rw [← rootTorusSL2_thetaF4 (-1)]
    exact (exceptional_Lang_root_rank_one_data .F4 F thetaF4).2.2.2.2.1 _
  refine ⟨⟨_, hmem⟩, rfl, fun h => f4_dtheta_ne_one hF (congrArg Subtype.val h),
    f4_dtheta_mem_layer, fun x hx => f4_dtheta_commute_layer hx⟩

end Ambient

end CFSG.OddStandard.HigherRank.F3
