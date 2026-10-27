module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTData
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31Two

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G}

theorem no_three_comps (hL : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hzH : z ∈ H) (J₁ J₂ J₃ : Subgroup (HBar H)) (h₁ : IsComponent J₁) (h₂ : IsComponent J₂)
    (h₃ : IsComponent J₃) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) : False := by
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  exact sec31_two hL h.ctx (SecOfG.of_sec hzH (H_ne_top h) hodd) h₁ h₂ h₃ h12 h13 h23

theorem dbar (h : Cfg55E G z k S T Tstar p H P g X Y) : L52Two.DBar H P := by
  intro D hD x hx
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective D
  have hd : (d : G) ∈ O22Of H := ⟨d, hD, rfl⟩
  have hxP : (x : G) ∈ P := hx
  have hc : ⁅(d : G), (x : G)⁆ ∈ pPrimeCoreOf 2 H :=
    h.l52.2.2.1 (Subgroup.commutator_mem_commutator hd hxP)
  obtain ⟨w, hw, hwe⟩ := hc
  have hw' : w = ⁅d, x⁆ := Subtype.ext hwe
  have hk : ⁅d, x⁆ ∈ pPrimeCore 2 ↥H := hw' ▸ hw
  have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥H) ⁅d, x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hk
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem pCore_two_le_centralizer (h : Cfg55E G z k S T Tstar p H P g X Y) :
    pCore 2 (HBar H) ≤
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨g, g_mem_H h⟩} : Set (HBar H)) := by
  intro D hD
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact dbar h D hD ⟨g, g_mem_H h⟩ (Subgroup.mem_subgroupOf.mpr (g_mem h))

theorem P_centralizes (h : Cfg55E G z k S T Tstar p H P g X Y) :
    barIn H P ≤ centralizer ((centralizer ((layer (HBar H) : Subgroup (HBar H)) : Set (HBar H)) :
      Subgroup (HBar H)) : Set (HBar H)) :=
  h.l52.2.2.2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
