module

public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutAbstract
public import CFSG.LieType.ChevTwo.Defs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

theorem innerAut_eq_inner (S : Type) [Group S] :
    innerAut S = CFSG.ComponentClassification.OuterAutomorphisms.inner S := rfl

@[expose] def OddCoreFact (p : ℕ) (S : Type) [Group S] : Prop :=
  CFSG.LieType.ChevTwo.OutTwoNilpConcl S ∧
    ∀ x : MulAut S, orderOf x = p →
      Odd (Nat.card (GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))))

@[expose] def CyclicCoreFact (p : ℕ) (S : Type) [Group S] : Prop :=
  ⁅(⊤ : Subgroup (MulAut S)), ⊤⁆ ≤ innerAut S ∧
    ∀ x : MulAut S, orderOf x = p →
      IsCyclic (GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))))

variable {p : ℕ}

def gLAPPrimeCoreOf_inf_centralizer_mulAutCongr {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (p : ℕ) (x : MulAut S) :
    GLAPPrimeCoreOf p (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) ≃*
      GLAPPrimeCoreOf p (innerAut S' ⊓
        Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut S'))) := by
  have hinner : (innerAut S).map (MulAut.congr e : MulAut S →* MulAut S') = innerAut S' :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_innerAut_congr e
  have hcen : (Subgroup.centralizer ({x} : Set (MulAut S))).map
        (MulAut.congr e : MulAut S →* MulAut S') =
      Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut S')) :=
    CFSG.centralizer_singleton_map (MulAut.congr e) x
  have hK : (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))).map
        (MulAut.congr e : MulAut S →* MulAut S') =
      innerAut S' ⊓ Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut S')) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.congr e).injective, hinner, hcen]
  have hcore := gLAPPrimeCoreOf_map_mulEquiv p (MulAut.congr e)
    (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))
  rw [hK] at hcore
  rw [hcore]
  exact MulEquiv.subgroupMap (MulAut.congr e) _

theorem outTwoNilpConcl_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : CFSG.LieType.ChevTwo.OutTwoNilpConcl S) : CFSG.LieType.ChevTwo.OutTwoNilpConcl S' := by
  obtain ⟨M, hMn, hIM, hodd, hpow⟩ := h
  rw [← innerAut_eq_inner S] at hIM hodd
  have hinner : (innerAut S).map (MulAut.congr e : MulAut S →* MulAut S') = innerAut S' :=
    CFSG.HardMathSupport.Solomon.Coordinator.map_innerAut_congr e
  refine ⟨M.map (MulAut.congr e).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact hMn.map _ (MulAut.congr e).surjective
  · rw [← innerAut_eq_inner S', ← CFSG.HardMathSupport.Solomon.Coordinator.map_innerAut_congr e]
    exact Subgroup.map_mono hIM
  · rw [← innerAut_eq_inner S', ← CFSG.HardMathSupport.Solomon.Coordinator.map_innerAut_congr e,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.congr e).injective]
    exact hodd
  · intro g
    obtain ⟨k, hk⟩ := hpow ((MulAut.congr e).symm g)
    refine ⟨k, ?_⟩
    have h1 : MulAut.congr e (((MulAut.congr e).symm g) ^ (2 ^ k)) ∈
        M.map (MulAut.congr e).toMonoidHom := Subgroup.mem_map_of_mem _ hk
    rwa [map_pow, MulEquiv.apply_symm_apply] at h1

theorem odd_card_gLAPPrimeCoreOf_inf_centralizer_congr {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (p : ℕ) (x : MulAut S) :
    Odd (Nat.card (GLAPPrimeCoreOf p
        (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))))) ↔
      Odd (Nat.card (GLAPPrimeCoreOf p
        (innerAut S' ⊓ Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut S'))))) := by
  rw [Nat.card_congr (gLAPPrimeCoreOf_inf_centralizer_mulAutCongr e p x).toEquiv]

theorem isCyclic_gLAPPrimeCoreOf_inf_centralizer_congr {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (p : ℕ) (x : MulAut S) :
    IsCyclic (GLAPPrimeCoreOf p
        (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))) ↔
      IsCyclic (GLAPPrimeCoreOf p
        (innerAut S' ⊓ Subgroup.centralizer ({MulAut.congr e x} : Set (MulAut S')))) :=
  (gLAPPrimeCoreOf_inf_centralizer_mulAutCongr e p x).isCyclic

theorem oddCoreFact_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    OddCoreFact p S ↔ OddCoreFact p S' := by
  have key : ∀ {A B : Type} [Group A] [Group B] (f : A ≃* B), OddCoreFact p A → OddCoreFact p B := by
    intro A B _ _ f h
    obtain ⟨hOut, hcore⟩ := h
    refine ⟨outTwoNilpConcl_of_mulEquiv f hOut, fun x hx => ?_⟩
    have hx' : orderOf ((MulAut.congr f).symm x) = p := by
      have h1 : orderOf ((MulAut.congr f).symm x) =
          orderOf (MulAut.congr f ((MulAut.congr f).symm x)) :=
        (MulEquiv.orderOf_eq (MulAut.congr f) ((MulAut.congr f).symm x)).symm
      rw [h1, MulEquiv.apply_symm_apply, hx]
    have h := (odd_card_gLAPPrimeCoreOf_inf_centralizer_congr f p
      ((MulAut.congr f).symm x)).1 (hcore _ hx')
    rw [(MulAut.congr f).apply_symm_apply x] at h
    exact h
  exact ⟨key e, key e.symm⟩

theorem commutator_top_map_mulAutCongr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    (⁅(⊤ : Subgroup (MulAut S)), ⊤⁆ : Subgroup (MulAut S)).map
        (MulAut.congr e).toMonoidHom = ⁅(⊤ : Subgroup (MulAut S')), ⊤⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top,
    MonoidHom.range_eq_top.2 (MulAut.congr e).surjective]

theorem cyclicCoreFact_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') :
    CyclicCoreFact p S ↔ CyclicCoreFact p S' := by
  have key : ∀ {A B : Type} [Group A] [Group B] (f : A ≃* B), CyclicCoreFact p A → CyclicCoreFact p B := by
    intro A B _ _ f h
    obtain ⟨hOut, hcore⟩ := h
    have hinner : (innerAut A).map (MulAut.congr f : MulAut A →* MulAut B) = innerAut B :=
      CFSG.HardMathSupport.Solomon.Coordinator.map_innerAut_congr f
    have hmap : (⁅(⊤ : Subgroup (MulAut A)), ⊤⁆ : Subgroup (MulAut A)).map
        (MulAut.congr f : MulAut A →* MulAut B) = ⁅(⊤ : Subgroup (MulAut B)), ⊤⁆ :=
      commutator_top_map_mulAutCongr f
    have hOut' : (⁅(⊤ : Subgroup (MulAut B)), ⊤⁆ : Subgroup (MulAut B)) ≤ innerAut B := by
      have h := Subgroup.map_mono (f := (MulAut.congr f : MulAut A →* MulAut B)) hOut
      rwa [hmap, hinner] at h
    refine ⟨hOut', fun x hx => ?_⟩
    have hx' : orderOf ((MulAut.congr f).symm x) = p := by
      have h1 : orderOf ((MulAut.congr f).symm x) =
          orderOf (MulAut.congr f ((MulAut.congr f).symm x)) :=
        (MulEquiv.orderOf_eq (MulAut.congr f) ((MulAut.congr f).symm x)).symm
      rw [h1, MulEquiv.apply_symm_apply, hx]
    have h := (isCyclic_gLAPPrimeCoreOf_inf_centralizer_congr f p
      ((MulAut.congr f).symm x)).1 (hcore _ hx')
    rw [(MulAut.congr f).apply_symm_apply x] at h
    exact h
  exact ⟨key e, key e.symm⟩

end CFSG.LocalAnalysis.GLTheoremA.KD1912
