module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompExit
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
public import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk centerQuotientHom_injective)
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley



@[expose] def TwE6ComponentAction :
    Prop :=
  ExcKernelCompAction → TwE6CentralizerConnOdd →
    ∀ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
      {q : TauCeti.PrimePower} (hq2 : q.p = 2)
      {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
      (hKcard : Nat.card K = (q.p ^ q.exponent) ^ 2)
      (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
      (hnot3 : p = 3 → ¬ 3 ∣ q.p ^ q.exponent + 1)
      (x w : ↥(twistedE6RootGroup K σ)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
      (hxw : x * w = w * x)
      (Kc : Subgroup ↥(twistedE6RootGroup K σ))
      (hKc : CFSG.Assembly.IsComponentOf Kc (fixedSubgroup (MulAut.conj x)))
      (hstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc)
      (h360 : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360),
      centerQuotientHom ↥Kc (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hstab⟩) ∈
        innAutDerived (↥Kc ⧸ Subgroup.center ↥Kc)

theorem twE6_indAut_of_twistedModel {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hK : ExcKernelCompAction) (hC : TwE6CentralizerConnOdd)
    (hAct : TwE6ComponentAction) (hS : Setup p L J A d b)
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    (hcat : catalogIs (PSimple p L) (onLie fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2)) :
    MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) ∨
      Nat.card (PSimple p J) = 360 := by
  have hJleL : J ≤ L := hS.comp.1.1.trans inf_le_left
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime hS.pcomp
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hLself : GLAPComponent p L L := glaPComponent_self_of_dvd_card hS.prime hS.qs hpL
  haveI hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hS.qs.1
  have hdin : InducesInnerMod p L d := inducesInnerMod_of_mem_not_shape hS hshape hS.d_mem
  obtain ⟨eP, heP⟩ := exists_pSimpleEquivCenterQuot_mk hS.prime hS.qs hpL
  obtain ⟨r, hr⟩ : ∃ r : PSimple p L, MulAut.conj r = MI.indAut p L d hdN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hdN).2 hdin
  obtain ⟨r', hr'⟩ : ∃ r' : PSimple p L, MulAut.conj r' = MI.indAut p L b hbN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hbN).2 hin
  obtain ⟨i₀, hi₀, ⟨eCat⟩⟩ := hcat
  cases i₀ with
  | cyclic _ _ => exact absurd hi₀ (by simp [onLie])
  | alternating _ _ => exact absurd hi₀ (by simp [onLie])
  | sporadic _ => exact absurd hi₀ (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hex, hPchar⟩ := hi₀
    cases idx with
    | twistedE6 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_twistedE6]; exact hPchar
      obtain ⟨K, hKf, σ, hKcard, hσ, ⟨eAd⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
      letI := hKf
      haveI : Finite K := Nat.finite_of_card_ne_zero
        (by rw [hKcard]; positivity)
      have hnot3 : p = 3 → ¬ 3 ∣ q.p ^ q.exponent + 1 := by
        intro hp3 h3
        refine hshape ⟨.lie ⟨.twistedE6 q, hv⟩, ⟨hp3, hq2, ?_⟩, ⟨eCat⟩⟩
        rw [TauCeti.PrimePower.card_def]
        exact h3
      by_cases h360 : Nat.card (PSimple p J) = 360
      · exact Or.inr h360
      · refine Or.inl ?_
        let θ : ↥L ⧸ Subgroup.center ↥L ≃*
            ↥(twistedE6RootGroup K σ) := eP.trans (eCat.trans eAd)
        have hθmk : ∀ l : ↥L, θ (QuotientGroup.mk l) =
            (eCat.trans eAd) (QuotientGroup.mk (QuotientGroup.mk l)) := by
          intro l
          show (eCat.trans eAd) (eP (QuotientGroup.mk l)) = _
          rw [heP l]
        set x : ↥(twistedE6RootGroup K σ) := (eCat.trans eAd) r with hxdef
        set w : ↥(twistedE6RootGroup K σ) := (eCat.trans eAd) r' with hwdef
        have hxind : LargeEvenInduces θ (conjRel d) (MulAut.conj x) := by
          intro l l' hll
          have hrel : indRel p L d (QuotientGroup.mk l) (QuotientGroup.mk l') :=
            ⟨l, l', rfl, rfl, hll⟩
          have h1 : MI.indAut p L d hdN (QuotientGroup.mk (QuotientGroup.mk l)) =
              QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk hdN hrel
          have h3 : r * (QuotientGroup.mk (QuotientGroup.mk l) : PSimple p L) * r⁻¹ =
              QuotientGroup.mk (QuotientGroup.mk l') := by
            rw [← MulAut.conj_apply, hr]
            exact h1
          rw [hθmk l, hθmk l', MulAut.conj_apply]
          change (eCat.trans eAd) r * (eCat.trans eAd)
              (QuotientGroup.mk (QuotientGroup.mk l)) * ((eCat.trans eAd) r)⁻¹ =
            (eCat.trans eAd) (QuotientGroup.mk (QuotientGroup.mk l'))
          rw [← map_inv, ← map_mul, ← map_mul, h3]
        have hwind : LargeEvenInduces θ (conjRel b) (MulAut.conj w) := by
          intro l l' hll
          have hrel : indRel p L b (QuotientGroup.mk l) (QuotientGroup.mk l') :=
            ⟨l, l', rfl, rfl, hll⟩
          have h1 : MI.indAut p L b hbN (QuotientGroup.mk (QuotientGroup.mk l)) =
              QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk hbN hrel
          have h3 : r' * (QuotientGroup.mk (QuotientGroup.mk l) : PSimple p L) * r'⁻¹ =
              QuotientGroup.mk (QuotientGroup.mk l') := by
            rw [← MulAut.conj_apply, hr']
            exact h1
          rw [hθmk l, hθmk l', MulAut.conj_apply]
          change (eCat.trans eAd) r' * (eCat.trans eAd)
              (QuotientGroup.mk (QuotientGroup.mk l)) * ((eCat.trans eAd) r')⁻¹ =
            (eCat.trans eAd) (QuotientGroup.mk (QuotientGroup.mk l'))
          rw [← map_inv, ← map_mul, ← map_mul, h3]
        have hxp : x ^ p = 1 :=
          pow_eq_one_of_conj_pow_eq_one' (center_graphFixedRootGroup_eq_bot σ.surjective)
            (largeEvenInduces_pow_eq_one hdN hxind (hS.elem.2 d hS.d_mem))
        have hwp : w ^ p = 1 :=
          pow_eq_one_of_conj_pow_eq_one' (center_graphFixedRootGroup_eq_bot σ.surjective)
            (largeEvenInduces_pow_eq_one hbN hwind (hS.elem.2 b hS.b_mem))
        have hxw : x * w = w * x :=
          mul_comm_of_largeEvenInduces hS θ hdN hbN
            (center_graphFixedRootGroup_eq_bot σ.surjective) hxind hwind
        have hx1 : x ≠ 1 := by
          intro hx1
          have htriv : LargeEvenInduces θ (conjRel d) (1 : MulAut _) := by
            simpa [hx1] using hxind
          have hZ : ∀ l l' : ↥L, (l' : G) = d⁻¹ * (l : G) * d →
              (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk l' := by
            intro l l' hll
            have h := htriv l l' hll
            exact θ.injective (by simpa using h)
          have hmem := mem_centralizer_of_action_trivial hS.qs.1 hdN hZ
          have hbot : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hmem⟩
          rw [hS.faithful] at hbot
          exact hS.d_ne (Subgroup.mem_bot.1 hbot)
        have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
          (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
        have hcomp := componentDescent_holds G L hS.qs ↥(twistedE6RootGroup K σ) θ d hdN
          (MulAut.conj x) hxind J hJc
          ((CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).trans hS.comp.2)
        have hwstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut
            ((J.subgroupOf L).map (piCenterQuot θ)) :=
          conj_mem_subgroupStabAut hS hbN θ hwind
        obtain ⟨e, he⟩ := exists_indAut_eq_centerQuotient hS θ w hwind hwstab
        have hKc360 : Nat.card
            (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
              Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))) ≠ 360 := by
          intro hc
          exact h360 ((Nat.card_congr e.toEquiv).trans hc)
        have hcKc := hAct hK hC hS.prime hS.odd hq2 σ hKcard hσ hnot3 x w hx1 hxp hxw
          ((J.subgroupOf L).map (piCenterQuot θ)) hcomp.1 hwstab hKc360
        exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).1
          (he ▸ hcKc)
    | _ => exact absurd hex (by
        obtain ⟨q', hq'⟩ := hex
        exact absurd hq' (by simp))

theorem innerCompNonShape_twistedE6_charTwo_of (hK : ExcKernelCompAction)
    (hC : TwE6CentralizerConnOdd) (hX : TwE6SmallExit) (hAct : TwE6ComponentAction) :
    InnerCompNonShape fun i => (∃ q, i = .twistedE6 q) ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat hshape hin
  have hcatE : catalogIs (PSimple p L) (onLie fun i : TauCeti.LieTypeIndex =>
      (∃ q : TauCeti.PrimePower, i = .twistedE6 q) ∧ i.characteristic = 2) := hcat
  exact exit_twE6_of_indAut hX hS hcatE hshape hin
    (twE6_indAut_of_twistedModel hK hC hAct hS hshape hin hcat)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
