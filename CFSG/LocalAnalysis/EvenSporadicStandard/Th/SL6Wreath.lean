module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.FusionCriterion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Card
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Wreath

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {SL : Subgroup G}

theorem ThCyc.card_centralizer_eq (H : ThCyc G L R t) (hS : IsThSylow L SL) {k : ℕ}
    (hk : Nat.card SL = 2 ^ k) :
    ∃ m : ℕ, Odd m ∧ Nat.card (centralizer ({t} : Set G)) = 2 ^ (k + 1) * m := by
  have hRSL := H.le_centralizer_sylow hS
  have hinf : SL ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ L ⊓ R := ⟨hS.le hx.1, hx.2⟩
    rw [disjoint_iff.1 H.disjoint, mem_bot] at hx'
    exact hx'
  have hR2 : Nat.card R = 2 := by
    rw [H.eq_zpowers, Nat.card_zpowers, H.order_two]
  have hK : Nat.card ↥(SL ⊔ R) = 2 ^ (k + 1) := by
    rw [natCard_sup_of_commute (fun h hh r hr => (mem_centralizer_iff.1 (hRSL hr) h hh)) hinf,
      hk, hR2, pow_succ]
  have hCsup : SL ⊔ R ≤ centralizer ({t} : Set G) := H.sup_le_centralizer hS
  have hrel := Subgroup.relIndex_mul_card (SL ⊔ R) (centralizer ({t} : Set G))
  rw [inf_of_le_left hCsup] at hrel
  have hodd : ¬ 2 ∣ (SL ⊔ R).relIndex (centralizer ({t} : Set G)) :=
    H.not_two_dvd_relIndex_centralizer hS le_rfl
  refine ⟨(SL ⊔ R).relIndex (centralizer ({t} : Set G)), ?_, ?_⟩
  · exact Nat.odd_iff.2 (by omega)
  · rw [← hrel, hK, mul_comm]

theorem ThCyc.false_of_wreath (H : ThCyc G L R t) (hS : IsThSylow L SL) {X : Subgroup G}
    (hX : Nat.card X = Nat.card SL)
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * (t * b * t⁻¹) = (t * b * t⁻¹) * a)
    (hinter : ∀ a ∈ X, t * a * t⁻¹ ∈ X → a = 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.pgroup
  obtain ⟨m, hm, hC⟩ := H.card_centralizer_eq hS hk
  have := H.simple
  exact _root_.CFSG.EvenSporadicStandard.false_of_wreath
    (fun ψ => hom_units_eq_one_of_simple H.nonabelian ψ) H.order_two hm hC (hX.trans hk) hcomm
    hinter

end CFSG.EvenSporadicStandard.ThStd
