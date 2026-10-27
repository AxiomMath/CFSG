module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatLeaf

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ProperFixedComponent.isComponent_of_oddCore {S : Type} [Group S] [Finite S]
    {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥) :
    IsComponent (P.subgroupOf (fixedSubgroup σ)) ∧
      Nonempty (P ⧸ Open.fusionZStar P ≃* (P.subgroupOf (fixedSubgroup σ)) ⧸
        center (P.subgroupOf (fixedSubgroup σ))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hPF, hP, -⟩ := h
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq := Sporadic.HeldB.pComponent_quasisimple_of_oddCore_eq_bot hcore L hP
  have hsub : L.IsSubnormal := hP.choose_spec.2.1
  have hL0 : pPrimeCore 2 L = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hsub,
      ← Sporadic.HeldB.oddCore_eq_pPrimeCore_two', hcore, bot_subgroupOf]
  have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hZ : Open.fusionZStar L = center L :=
    fusionZStar_eq_center_of_quasisimple hq (by rw [hL0]; exact bot_ne_top)
  obtain ⟨eP⟩ := GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (subgroupOfEquivOfLe hPF).symm
  exact ⟨⟨hq, hsub⟩, ⟨eP.trans (QuotientGroup.quotientMulEquivOfEq hZ)⟩⟩

theorem card_quotient_center_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ center A) = Nat.card (B ⧸ center B) :=
  Nat.card_congr (QuotientGroup.congr (center A) (center B) e (Subgroup.map_center_eq e)).toEquiv

end CFSG.ComponentClassification.CatLeaf
