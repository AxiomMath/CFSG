module

public import CFSG.CGT.PushingUpLit.BHS5.ThreeFour
public import CFSG.CGT.PushingUpLit.BHS.ThreeFive
public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {P T M W : Subgroup Γ}

omit [Finite Γ] in
theorem mem_ker_actOn' (hPW : P ≤ Subgroup.normalizer (W : Set Γ)) {g : ↥P} :
    g ∈ (actOn W P hPW).ker ↔ (g : Γ) ∈ Subgroup.centralizer (W : Set Γ) :=
  conjAct_eq_one_iff W (Subgroup.inclusion hPW g)

omit [Finite Γ] in
theorem autOn_eq_map_actOn {X : Subgroup Γ} (hPW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hX : X ≤ P) : autOn X W = (X.subgroupOf P).map (actOn W P hPW) := by
  unfold autOn actOn
  rw [← Subgroup.map_map]
  congr 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨y, hX hy⟩, hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx

theorem minPar_autOn (hmin : MinPar P T M) (hPW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hker : P ⊓ Subgroup.centralizer (W : Set Γ) ≤ M) :
    MinPar (autOn P W) (autOn T W) (autOn M W) := by
  have hker' : (actOn W P hPW).ker ⊓ (⊤ : Subgroup ↥P) ≤ M.subgroupOf P := by
    intro g hg
    have h1 : (g : Γ) ∈ Subgroup.centralizer (W : Set Γ) := (mem_ker_actOn' hPW).mp hg.1
    exact Subgroup.mem_subgroupOf.mpr (hker ⟨g.2, h1⟩)
  have h := BHS5.MinPar.map_of_ker_le (actOn W P hPW) hmin.subgroupOf_top hker'
  rwa [← Subgroup.subgroupOf_self P, ← autOn_eq_map_actOn hPW le_rfl,
    ← autOn_eq_map_actOn hPW hmin.T_le, ← autOn_eq_map_actOn hPW hmin.M_le] at h

theorem pCoreOf_autOn_eq_bot (hmin : MinPar P T M) (hPW : P ≤ Subgroup.normalizer (W : Set Γ))
    (hker : P ⊓ Subgroup.centralizer (W : Set Γ) ≤ M)
    (hO2 : pCoreOf 2 P ≤ Subgroup.centralizer (W : Set Γ)) :
    pCoreOf 2 (autOn P W) = ⊥ := by
  have hker' : (actOn W P hPW).ker ⊓ (⊤ : Subgroup ↥P) ≤ M.subgroupOf P := by
    intro g hg
    have h1 : (g : Γ) ∈ Subgroup.centralizer (W : Set Γ) := (mem_ker_actOn' hPW).mp hg.1
    exact Subgroup.mem_subgroupOf.mpr (hker ⟨g.2, h1⟩)
  have hO2' : pCoreOf 2 (⊤ : Subgroup ↥P) ≤ (actOn W P hPW).ker := by
    intro q hq
    refine (mem_ker_actOn' hPW).mpr (hO2 ?_)
    have hn : (pCoreOf 2 (⊤ : Subgroup ↥P)).Normal :=
      ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf_self (⊤ : Subgroup ↥P) (Subgroup.mem_top g)) x).1 hx⟩
    have hN : (pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype ≤ pCoreOf 2 P := by
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        (Subgroup.map_subtype_le _) ?_
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _).map _)
      have h1 : ((pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype).subgroupOf P =
          pCoreOf 2 (⊤ : Subgroup ↥P) :=
        Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
      rw [h1]
      exact hn
    exact hN ⟨q, hq, rfl⟩
  have h := BHS5.pCoreOf_map_eq_bot_of_ker_le (actOn W P hPW) hmin.subgroupOf_top hker' hO2'
  rwa [← Subgroup.subgroupOf_self P, ← autOn_eq_map_actOn hPW le_rfl] at h

end CFSG.CGT.PushingUpLit.BHS7
