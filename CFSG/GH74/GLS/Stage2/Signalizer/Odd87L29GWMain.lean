module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWXa
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWXb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29LayerD
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29LayerHat
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29GWSetup
import CFSG.GH74.GLS.Stage2.Final.ModelLayerQuot

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GorensteinWalter

namespace L29GW

theorem layer_classification (hGW : gorensteinWalterStatement.{0}) {D : Type} [Group D]
    [Finite D] (hO : pPrimeCore 2 D = ⊥) (M : Subgroup D) [M.Normal]
    (hq : IsPGroup 2 (D ⧸ M)) (hns : ¬ Group.IsSolvable ↥M)
    (hS : ∀ S : Sylow 2 ↥M, IsCyclic ↥S ∨ IsDihedral ↥S) :
    Nonempty (↥(layer D) ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 ↥(layer D) Odd := by
  have hOM := pPrimeCore_eq_bot_of_normal hO M
  have hdih := hasDihedralSylowTwo_of_cyclic_or_dihedral hns hS
  obtain ⟨L₀, hLn, hsimp, hnab, hperf, hcase⟩ := dgroup_structure hGW hOM hns hdih
  have hqs : Group.IsSolvable (D ⧸ M) := by
    have : Group.IsNilpotent (D ⧸ M) := hq.isNilpotent
    infer_instance
  obtain ⟨e⟩ := layer_eq_of_simple_normal M hqs L₀ hsimp hnab hperf
  rcases hcase with hA | hL
  · obtain ⟨eA⟩ := hA
    exact Or.inl ⟨e.trans eA⟩
  · obtain ⟨F, hF, hFin, hodd, ⟨eL⟩⟩ := hL
    exact Or.inr ⟨F, hF, hFin, hodd, ⟨e.trans eL⟩⟩

theorem hat_layer_classification (hGW : gorensteinWalterStatement.{0}) {Y : Type} [Group Y]
    [Finite Y] (hns : ¬ Group.IsSolvable Y)
    (hD : ∀ P : Sylow 2 ↥(oResidual 2 Y), IsCyclic ↥P ∨ IsDihedral ↥P) :
    IVK.IsL2 (↥(pLayer Y 2) ⧸ pPrimeCore 2 ↥(pLayer Y 2)) Odd ∨
      Nonempty ((↥(pLayer Y 2) ⧸ pPrimeCore 2 ↥(pLayer Y 2)) ≃* alternatingGroup (Fin 7)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMn, hq, hMns, hMS⟩ := quotient_setup hns hD
  have hO : pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := Y) 2
  obtain ⟨eh⟩ := hat_pLayer_equiv_layer (Y := Y)
  rcases layer_classification hGW hO M hq hMns hMS with hA | hL
  · obtain ⟨e⟩ := hA
    exact Or.inr ⟨eh.trans e⟩
  · obtain ⟨F, hF, hFin, hodd, ⟨eL⟩⟩ := hL
    exact Or.inl ⟨F, hF, hFin, hodd, ⟨eh.trans eL⟩⟩

end L29GW

section GroupLevel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hat_pLayerOf_equiv_gw (X : Subgroup G) :
    Nonempty ((↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) ≃*
      (↥(pLayer ↥X 2) ⧸ pPrimeCore 2 ↥(pLayer ↥X 2))) := by
  have h : pLayerOf 2 X = (pLayer ↥X 2).map X.subtype := Stage2.Final.ModelLQ.pLayerOf_eq_map 2 X
  let e : ↥(pLayerOf 2 X) ≃* ↥(pLayer ↥X 2) :=
    (MulEquiv.subgroupCongr h).trans
      (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective).symm
  exact ⟨QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)⟩

theorem sylow_oResidual_of_le {C X : Subgroup G} (hXC : X ≤ C)
    (hC : ∀ P : Sylow 2 ↥(O2Of C), IsDihedral ↥P) :
    ∀ P : Sylow 2 ↥(oResidual 2 ↥X), IsCyclic ↥P ∨ IsDihedral ↥P := by
  have hX := dihedral_or_cyclic_of_le hXC hC
  let eX : ↥(O2Of X) ≃* ↥(oResidual 2 ↥X) :=
    (Subgroup.equivMapOfInjective (oResidual 2 ↥X) X.subtype X.subtype_injective).symm
  refine L29GW.cyclic_or_dihedral_of_surj_odd_ker eX.toMonoidHom eX.surjective ?_ hX
  have : Nat.card (MonoidHom.ker eX.toMonoidHom) = 1 := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr eX.injective, Subgroup.card_bot]
  rw [this]
  exact odd_one

theorem lemma29NonSolv_classical (hGW : gorensteinWalterStatement.{0}) {C X : Subgroup G}
    (hXC : X ≤ C) (hC : ∀ P : Sylow 2 ↥(O2Of C), IsDihedral ↥P) (hns : ¬ Group.IsSolvable ↥X) :
    IVK.IsL2 (↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) Odd ∨
      Nonempty ((↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X)) ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨eh⟩ := hat_pLayerOf_equiv_gw X
  rcases L29GW.hat_layer_classification hGW (Y := ↥X) hns (sylow_oResidual_of_le hXC hC) with
    hL | hA
  · obtain ⟨F, hF, hFin, hodd, ⟨eL⟩⟩ := hL
    exact Or.inl ⟨F, hF, hFin, hodd, ⟨eh.trans eL⟩⟩
  · obtain ⟨eA⟩ := hA
    exact Or.inr ⟨eh.trans eA⟩

end GroupLevel

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
