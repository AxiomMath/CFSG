module

public import CFSG.Dihedral.OriginalCharacterKernelBounds
public import CFSG.Dihedral.OriginalFourgroupsGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem R_eq_bot_of_psl2_model
    (i : Fin 2) (hi : d.E i = d.R)
    (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : G ≃* PSL2 K) : d.R = ⊥ := by
  classical
  by_contra hne
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let VP := (d.V i).map e.toMonoidHom
  let a : PSL2 K := e (x : G)
  let A : Subgroup (PSL2 K) := Subgroup.zpowers a
  have hVP : IsKleinFour VP :=
    isKleinFour_map_mulEquiv_cross (d.V i) (d.V_isKleinFour_general i) e
  have hAcyc : IsCyclic A := Subgroup.isCyclic_zpowers a
  have hAne : A ≠ ⊥ := by
    intro hbot
    have haone : a = 1 := by
      have haA : a ∈ A := Subgroup.mem_zpowers a
      rw [hbot] at haA
      exact Subgroup.mem_bot.mp haA
    exact hx (Subtype.ext (e.injective (by simpa [a] using haone)))
  have hAodd : Odd (Nat.card A) := by
    change Odd (Nat.card (Subgroup.zpowers (e (x : G))))
    rw [Nat.card_zpowers, e.orderOf_eq]
    exact d.R_odd.of_dvd_nat (d.R.orderOf_dvd_natCard x.property)
  have hcent : VP ≤ Subgroup.centralizer
      ((d.R.map e.toMonoidHom : Subgroup (PSL2 K)) : Set (PSL2 K)) :=
    centralizer_map_le_of_mulEquiv e d.R (d.V i) (d.fourgroup_le_R_centralizer i hi)
  have hAle : A ≤ d.R.map e.toMonoidHom :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem e.toMonoidHom x.property)
  have hVcent : VP ≤ Subgroup.centralizer (A : Set (PSL2 K)) :=
    hcent.trans (Subgroup.centralizer_le hAle)
  exact psl2_no_kleinFour_centralizes_odd_cyclic K hK A VP hAcyc hAne hAodd hVP hVcent

end CFSG.DihedralBlueprint.OriginalData
