module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSecG
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecClosure

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Transport
variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem sec31_two (hL : Lemma31Narrow) (hctx : Stage2Ctx G z k S) {B : Type} [Group B] [Finite B] {b : B}
    (hB : SecOfG G z B b) {J₁ J₂ J₃ : Subgroup B} (h₁ : IsComponent J₁) (h₂ : IsComponent J₂)
    (h₃ : IsComponent J₃) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) : False := by
  obtain ⟨H₀, -, π, hH₀, hπ, hodd, -⟩ := subsec_exists_hom hB
  obtain ⟨u₀, hu₀⟩ := exists_orderOf_eq_two_of_isQuasisimple h₂.1
  have hu : orderOf (u₀ : B) = 2 := by rw [Subgroup.orderOf_coe]; exact hu₀
  have hcomm : ⁅J₁, J₂⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute h₁ h₂).resolve_left h12
  have hJ₂c : J₂ ≤ centralizer (J₁ : Set B) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hW2 : IsPGroup 2 ↥(Subgroup.zpowers (u₀ : B)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu]; norm_num)
  have hWJ : Subgroup.zpowers (u₀ : B) ≤ centralizer (J₁ : Set B) :=
    Subgroup.zpowers_le.mpr (hJ₂c u₀.2)
  have hW1 : Subgroup.zpowers (u₀ : B) ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  obtain ⟨Jt₁, R, ρ, hJt₁, hmap₁, -, hconcl, -, -⟩ :=
    sec31_core_hom hL hctx hH₀ π hπ hodd h₁ hW2 hWJ hW1
  obtain ⟨Jt₂, hJt₂, hmap₂, -, -⟩ := exists_pcomp_lift π hπ hodd h₂
  obtain ⟨Jt₃, hJt₃, hmap₃, -, -⟩ := exists_pcomp_lift π hπ hodd h₃
  have hle : ∀ {Jt : Subgroup G}, IsPCompIn 2 H₀ Jt → Jt ≤ pLayerOf 2 H₀ := fun h => le_sSup h
  have hne : Jt₁ ≠ pLayerOf 2 H₀ := by
    intro h
    have hJ₂₁ : J₂ ≤ J₁ := by
      rw [← hmap₂, ← hmap₁]
      exact Subgroup.map_mono fun x hx => (h ▸ hle hJt₂ : Jt₂ ≤ Jt₁) hx
    exact h12 (comp_eq_of_le_quasisimple h₁.1 h₂ hJ₂₁).symm
  have hcomp : ∀ {Jt : Subgroup G}, IsPCompIn 2 H₀ Jt → IsComponent (barIn H₀ Jt) := by
    intro Jt hJt
    obtain ⟨K₀, hK₀, -, hLK₀, -⟩ := hJt.2
    change IsComponent ((Jt.subgroupOf H₀).map (QuotientGroup.mk' (pPrimeCore 2 ↥H₀)))
    rw [hLK₀]
    exact hK₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbar_ne : ∀ {Ja Jb : Subgroup B} {Ta Tb : Subgroup G}, IsPCompIn 2 H₀ Ta → IsPCompIn 2 H₀ Tb →
      (Ta.subgroupOf H₀).map π = Ja → (Tb.subgroupOf H₀).map π = Jb → Ja ≠ Jb →
      barIn H₀ Ta ≠ barIn H₀ Tb := by
    intro Ja Jb Ta Tb hTa hTb ha hb hJ heq
    apply hJ
    rw [← ha, ← hb]
    exact congrArg (Subgroup.map π)
      (CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq hTa.2 hTb.2 heq)
  have hle' : ∀ {Jt : Subgroup G}, Jt ≤ pLayerOf 2 H₀ → barIn H₀ Jt ≤ barIn H₀ (pLayerOf 2 H₀) :=
    fun h => Subgroup.map_mono fun x hx => h hx
  obtain ⟨-, -, hd, -⟩ := hconcl
  obtain ⟨K₁, K₂, hsup, hcommK, hs₁, hs₂⟩ := hd (hle hJt₁) hne
  have hne12 := hbar_ne hJt₁ hJt₂ hmap₁ hmap₂ h12
  have hne13 := hbar_ne hJt₁ hJt₃ hmap₁ hmap₃ h13
  have hne23 := hbar_ne hJt₂ hJt₃ hmap₂ hmap₃ h23
  exact three_comps_false hcommK hs₁ hs₂ (hcomp hJt₁) (hcomp hJt₂) (hcomp hJt₃)
    (hsup ▸ hle' (hle hJt₁)) (hsup ▸ hle' (hle hJt₂)) (hsup ▸ hle' (hle hJt₃)) hne12 hne13 hne23

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
