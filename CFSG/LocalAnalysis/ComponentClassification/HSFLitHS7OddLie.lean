module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Facts
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7OuterAut
import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpOrders

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_card_ne_A7 (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (hX : Blueprint.LieModel X t n p f) : Nat.card X ≠ 2520 :=
  CFSG.ComponentClassification.SolMax.lieModel_card_ne_alt_seven hO hadm hX

theorem not_A7_of_properFixedComponent_oddLie
    (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hodd : OddLieType S) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) :
    ¬ Nonempty (P ⧸ Open.fusionZStar P ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e7⟩
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hq : IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L h.2.2.1
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.fusionZStar_equiv_of_quasisimple hq
  have hcard : Nat.card (L ⧸ center L) = 2520 := by
    rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr e7.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hm⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨-, -, -, h8⟩
  · exact lieModel_card_ne_A7 hO hadm' hm' hcard
  · have h504 := card_of_lieModel_psl_two_eight hO h8
    have hle : Nat.card (L ⧸ center L) ≤ 504 := by
      rw [← h504]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega

theorem fixedSubgroup_conj {X : Type*} [Group X] (t : X) :
    fixedSubgroup (MulAut.conj t) = centralizer ({t} : Set X) := by
  ext x
  change t * x * t⁻¹ = x ↔ x ∈ centralizer ({t} : Set X)
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * t = t * x * t⁻¹ * t := by rw [h]
      _ = t * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

theorem hs7OddLieFact_of_inputs
    (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) : HS7OddLieFact := by
  intro X _ _ _ hna hodd t ht L hLt hL ⟨e7⟩
  have hfix := fixedSubgroup_conj t
  have hσ : ∀ y, MulAut.conj t (MulAut.conj t y) = y := by
    intro y
    change t * (t * y * t⁻¹) * t⁻¹ = y
    have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [hti, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hLtop : L ≠ ⊤ := by
    intro htop
    have hc : t ∈ center X := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ centralizer ({t} : Set X) := hLt (htop ▸ mem_top g)
      exact mem_centralizer_singleton_iff.mp hg
    rw [Helpers.center_eq_bot _ hna, mem_bot] at hc
    rw [hc, orderOf_one] at ht
    exact absurd ht (by decide)
  have hP : ProperFixedComponent (MulAut.conj t) L :=
    ⟨hσ, hfix ▸ hLt, hfix ▸ hL, hLtop⟩
  exact not_A7_of_properFixedComponent_oddLie hGLS hO hna hodd hP (nonempty_zStar_equiv_A7 e7)

theorem false_of_outer_oddLie
    (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {G : Type} [Group G] [Finite G]
    (hF : IsSimpleGroup ↥(generalizedFitting G)) (hodd : OddLieType ↥(generalizedFitting G))
    {t : G} (ht : orderOf t = 2) (htF : t ∉ generalizedFitting G) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))) : False := by
  obtain ⟨σ, -, -, hP, he⟩ := exists_outer_properFixedComponent hF ht htF hLt hL h7
  exact not_A7_of_properFixedComponent_oddLie hGLS hO (generalizedFitting_nonabelian hF h7) hodd
    hP he

end CFSG.ComponentClassification.HSFLit.HS7
