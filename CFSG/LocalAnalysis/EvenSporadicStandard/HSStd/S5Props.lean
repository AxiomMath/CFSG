module

public import CFSG.Open.FusionDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open

@[expose] def HaradaOneList (G : Type) [Group G] [Finite G] : Prop :=
  Nonempty (↥(GorensteinWalter.componentLayerOf (⊤ : Subgroup G)) ≃*
      alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
    LieModel ↥(commutator G) .PSL 2 5 2 ∨ LieModel ↥(commutator G) .PSL 3 5 1 ∨
    LieModel ↥(commutator (commutator G)) .PSU 3 5 1 ∨ Nonempty (G ≃* Equiv.Perm (Fin 7)) ∨
    IsSporadic G .M12 ∨ LieModel ↥(commutator (commutator G)) .PSL 3 2 2

@[expose] def Harada39One : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G → fusionZStar G = ⊥ →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) → HaradaOneList G

@[expose] def Harada39Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G → fusionZStar G = ⊥ →
    ∀ t v : G, orderOf t = 2 →
    v * v = 1 → ∀ J : Subgroup G, Nonempty (↥J ≃* Equiv.Perm (Fin 5)) →
      (zpowers t ⊔ zpowers v) ⊓ J = ⊥ → (∀ a ∈ zpowers t ⊔ zpowers v, ∀ b ∈ J, a * b = b * a) →
      centralizer ({t} : Set G) = (zpowers t ⊔ zpowers v) ⊔ J →
      centralizer ({v} : Set G) = centralizer ({t} : Set G) →
      centralizer ({t * v} : Set G) = centralizer ({t} : Set G) →
        (zpowers t ⊔ zpowers v).Normal ∨
          Nonempty (G ≃* alternatingGroup (Fin 5) × Equiv.Perm (Fin 5))

@[expose] def autCentralizer {G : Type*} [Group G] (y : MulAut G) : Subgroup G where
  carrier := {g | y g = g}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    rw [ha, hb]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
    rw [ha]

theorem autCentralizer_conj {G : Type*} [Group G] (g : G) :
    autCentralizer (MulAut.conj g) = centralizer ({g} : Set G) := by
  ext x
  show MulAut.conj g x = x ↔ x ∈ centralizer ({g} : Set G)
  rw [MulAut.conj_apply, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

@[expose] def normalClosureOf {G : Type*} [Group G] (L : Subgroup G) : Subgroup G :=
  Subgroup.normalClosure (L : Set G)

@[expose] def centralizerDerived {G : Type*} [Group G] (t : G) : Subgroup G :=
  (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype

@[expose] def HarrisOutcome (K : Type) [Group K] : Prop :=
  Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (K ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∨
    LieModel K .PSU 4 3 1 ∨ IsSporadic K .HS ∨ LieModel K .PSL 3 3 2 ∨ LieModel K .PSL 4 3 1

@[expose] def Harris311 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G → fusionOddCore G = ⊥ →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
    HarrisOutcome ↥(normalClosureOf (centralizerDerived t))

@[expose] def Harris311HiS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.SectionRank.IsKGroupCat G → fusionOddCore G = ⊥ →
    ∀ t : G, orderOf t = 2 →
    Nonempty (↥(centralizer ({t} : Set G)) ≃*
      Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) →
      ∀ g : G, orderOf g = 3 →
        Nonempty (↥(centralizer ({g} : Set G)) ⧸ fusionOddCore ↥(centralizer ({g} : Set G)) ≃*
          Equiv.Perm (Fin 5)) →
        IsSporadic ↥(normalClosureOf (centralizerDerived t)) .HS

end CFSG.EvenSporadicStandard.HSStd
