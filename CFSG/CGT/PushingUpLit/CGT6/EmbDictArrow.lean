module

public import CFSG.CGT.PushingUpLit.CGT6.EmbDictMod

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

section Arrow

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)

theorem image_phi_eq {A B : Subgroup G} (hAB : A ≤ B) (hKB : KTwo V B) :
    (((yuHolOf hV (autOn A V)).subgroupOf (yuHolOf hV (autOn B V))).map
        (QuotientGroup.mk' (pCore 2 ↥(yuHolOf hV (autOn B V))))).map
          (ePhi hV B hKB).toMonoidHom =
      (A.subgroupOf B).map (QuotientGroup.mk' (pCore 2 ↥B)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨l, hl, rfl⟩, rfl⟩
    have hl' : ((l : HolOf hV).right : MulAut ↥V) ∈ autOn A V := hl.2
    rw [← map_ambRho V A] at hl'
    obtain ⟨a, ha, hal⟩ := hl'
    have hρ : rhoA V B ⟨a, hAB ha⟩ = projPhi hV B l := Subtype.ext hal
    refine ⟨⟨a, hAB ha⟩, ha, ?_⟩
    show ((⟨a, hAB ha⟩ : ↥B) : ↥B ⧸ pCore 2 ↥B) =
      ePhi hV B hKB (l : ↥(yuHolOf hV (autOn B V)) ⧸ pCore 2 ↥(yuHolOf hV (autOn B V)))
    rw [ePhi_mk]
    change _ = lamHat B hKB (projPhi hV B l)
    rw [← hρ, lamHat_rhoA]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(QuotientGroup.mk' (pCore 2 ↥(yuHolOf hV (autOn B V)))) (sigPhi hV B y),
      ⟨sigPhi hV B y, ?_, rfl⟩, ?_⟩
    · show ((sigPhi hV B y : ↥(yuHolOf hV (autOn B V))) : HolOf hV) ∈ yuHolOf hV (autOn A V)
      refine ⟨one_mem _, ?_⟩
      show ((rhoA V B y : ↥(autOn B V)) : MulAut ↥V) ∈ autOn A V
      rw [← map_ambRho V A]
      exact ⟨(y : G), hy, rfl⟩
    · show ePhi hV B hKB ((sigPhi hV B y : ↥(yuHolOf hV (autOn B V))) :
        ↥(yuHolOf hV (autOn B V)) ⧸ _) = (QuotientGroup.mk' (pCore 2 ↥B)) y
      rw [ePhi_mk, lamPhi_sigPhi]
      rfl

end Arrow

theorem embDictArrow_holds : EmbDictArrow := by
  intro G _ _ V Y X _ hV hYX hY hX _ hUY _ hUX hK2 hne harr
  have hDX : DictHyp V X :=
    { hK := kTwo_of_isPGroup hK2
      hR := SubTwo.noTwoQuotient_of_oResidualTwo hX.1.residual_eq
      hP := hUX
      hZ := fun u hu q hq => blockU_comm_of_short hX.1 u hu q hq }
  have hKY : KTwo V Y := kTwo_of_isPGroup
    (hK2.to_le (inf_le_inf_right _ hYX))
  have hDY : DictHyp V Y :=
    { hK := hKY
      hR := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
      hP := hUY
      hZ := fun u hu q hq => blockU_comm_of_short hY.1 u hu q hq }
  let SX := shortIsoPhi hV hDX
  let SY := shortIsoPhi hV hDY
  rcases harr with h | ⟨a, b, φ, F, hYb, hXa, hF, hU, hΦ, himg⟩
  · exact absurd h hne
  · right
    refine ⟨a, b, SX.e.trans φ, F, ?_, SX.altModule hXa, hF, ?_, hYX, ?_⟩
    · obtain ⟨ψ⟩ := hYb
      exact ⟨SY.e.trans ψ⟩
    · rw [SixThree.map_shortU Y, SixThree.map_shortU X, ← hUY, ← hUX]
      exact Subgroup.commutator_mono le_rfl hYX
    · rw [← himg, ← image_phi_eq hV hYX hDX.hK, Subgroup.map_map]
      congr 1
      refine MonoidHom.ext fun x => ?_
      show φ ((ePhi hV X hDX.hK).symm (ePhi hV X hDX.hK x)) = φ x
      rw [MulEquiv.symm_apply_apply]

end CFSG.CGT.PushingUpLit.CGT6
