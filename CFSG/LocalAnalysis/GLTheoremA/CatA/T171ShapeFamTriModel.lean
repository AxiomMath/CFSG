module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Model
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.Assembly.LargeEvenGLABridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10


private theorem triModel_of_equiv {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hdata : TriFieldData f K σ) (eAd : PSimple p L ≃* TriGrp K σ) :
    TriModelData p L J d b := by
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
  let θ : ↥L ⧸ Subgroup.center ↥L ≃* TriGrp K σ := eP.trans eAd
  have hθmk : ∀ l : ↥L, θ (QuotientGroup.mk l) =
      eAd (QuotientGroup.mk (QuotientGroup.mk l)) := by
    intro l
    show eAd (eP (QuotientGroup.mk l)) = _
    rw [heP l]
  set x : TriGrp K σ := eAd r with hxdef
  set w : TriGrp K σ := eAd r' with hwdef
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
    change eAd r * eAd (QuotientGroup.mk (QuotientGroup.mk l)) * (eAd r)⁻¹ =
      eAd (QuotientGroup.mk (QuotientGroup.mk l'))
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
    change eAd r' * eAd (QuotientGroup.mk (QuotientGroup.mk l)) * (eAd r')⁻¹ =
      eAd (QuotientGroup.mk (QuotientGroup.mk l'))
    rw [← map_inv, ← map_mul, ← map_mul, h3]
  have hZtri : Subgroup.center (TriGrp K σ) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot
      (t := CFSG.Blueprint.Chevalley.TwistTag.D4) (K := K) (σ := σ.toRingHom) σ.surjective
  have hxp : x ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one' hZtri
      (largeEvenInduces_pow_eq_one hdN hxind (hS.elem.2 d hS.d_mem))
  have hxw : x * w = w * x :=
    mul_comm_of_largeEvenInduces hS θ hdN hbN hZtri hxind hwind
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
  have hcomp := componentDescent_holds G L hS.qs
    (TriGrp K σ) θ d hdN (MulAut.conj x) hxind J hJc
    ((CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).trans hS.comp.2)
  exact ⟨f, K, inferInstance, inferInstance, σ, θ, x, w, hdata, hxind, hwind, hxp, hx1, hxw,
    hcomp.1⟩

theorem triModel_of_setup
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hS : Setup p L J A d b) (hshape : ¬ I171.I171LieShapeAt p L)
    (hin : InducesInnerMod p L b)
    (hcat : catalogIs (PSimple p L)
      (onLie fun i => KD264Lie.isTrialityIdx i ∧ i.characteristic = 2)) :
    TriModelData p L J d b := by
  obtain ⟨i₀, hi₀, ⟨eCat⟩⟩ := hcat
  cases i₀ with
  | cyclic _ _ => exact absurd hi₀ (by simp [onLie])
  | alternating _ _ => exact absurd hi₀ (by simp [onLie])
  | sporadic _ => exact absurd hi₀ (by simp [onLie])
  | lie dd =>
    obtain ⟨idx, hv⟩ := dd
    obtain ⟨hPtri, hPchar⟩ := hi₀
    cases idx with
    | trialityD4 q =>
      have hq2 : q.p = 2 := by
        rw [← TauCeti.LieTypeIndex.characteristic_trialityD4]; exact hPchar
      obtain ⟨K, hKf, hKfin, σ, hK, hσ, -, ⟨eK⟩⟩ :=
        CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
      letI := hKf
      letI := hKfin
      have hdata : TriFieldData q.exponent K σ :=
        ⟨q.exponent_pos, by simpa [hq2] using hK, fun c => by simpa [hq2] using hσ c⟩
      exact triModel_of_equiv hS hshape hin hdata (eCat.trans eK)
    | _ => exact hPtri.elim

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
