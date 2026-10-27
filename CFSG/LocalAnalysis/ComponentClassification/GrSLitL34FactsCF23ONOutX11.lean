module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutCard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.Sporadic.ONOddCore.LocalComp

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem cf81X11ON_of_local
    (hloc : SolMax.ONOuterLocalInput) :
    ∀ (G : Type) [Group G] [Finite G] (N : Subgroup G), N.Normal →
      centralizer (N : Set G) = ⊥ → Blueprint.NativeSporadic.IsSporadic ↥N .ONan →
      ∀ t : G, orderOf t = 2 →
        Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 161280 ∨
          Nat.card ↥(N ⊓ centralizer ({t} : Set G)) = 175560 := by
  intro G _ _ N hN hC hON t ht
  have := hN
  obtain ⟨e⟩ := hON
  have e' : ↥N ≃* NativeSporadic.ON := e
  by_cases htN : t ∈ N
  ·
    left
    set θ : ↥N ≃* ONSchreier.Pv := e'.trans ONSchreier.onEquivPv
    set a : ↥N := ⟨t, htN⟩
    have ha : orderOf (θ a) = 2 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact ht
    obtain ⟨eM⟩ := Sporadic.ONOddCore.centralizer_P_equiv_M ha
    calc Nat.card ↥(N ⊓ centralizer ({t} : Set G))
        = Nat.card (centralizer ({a} : Set ↥N)) :=
          Nat.card_congr (Sporadic.ONOddCore.centralizerSubtypeEquiv N a).symm.toEquiv
      _ = Nat.card (centralizer ({θ a} : Set ONSchreier.Pv)) :=
          Nat.card_congr (Sporadic.ONOddCore.centralizerCongr θ a).toEquiv
      _ = Nat.card ONSchreier.onM := Nat.card_congr eM.toEquiv
      _ = 161280 := ONSchreier.card_onM
  ·
    right
    have hβ2 : Soc.beta N t * Soc.beta N t = 1 := by
      rw [← map_mul, ← sq, ← ht, pow_orderOf_eq_one, map_one]
    have hβ : Soc.beta N t ∉ inner ↥N := by
      rintro ⟨s, hs⟩
      have hc : MulAut.conjNormal (s : G) = (MulAut.conjNormal t : MulAut N) := by
        rw [MulAut.conjNormal_val]
        exact hs
      apply htN
      rw [← Soc.conjNormal_injective hC hc]
      exact s.2
    have hfix : Sporadic.Schreier.fixSub (Soc.beta N t) = fixedSubgroup (Soc.beta N t) :=
      Subgroup.ext fun _ => Iff.rfl
    have hcard : Nat.card ↥(N ⊓ centralizer ({t} : Set G)) =
        Nat.card (Sporadic.Schreier.fixSub (Soc.beta N t)) := by
      rw [hfix, Soc.fixedSubgroup_beta, inf_comm, ← subgroupOf_map_subtype]
      exact Nat.card_congr
        (((centralizer ({t} : Set G)).subgroupOf N).equivMapOfInjective N.subtype
          N.subtype_injective).symm.toEquiv
    rw [hcard]
    exact SolMax.card_fixSub_of_local hloc ⟨e'⟩ _ hβ2 hβ

end CFSG.ComponentClassification.GSThmB
