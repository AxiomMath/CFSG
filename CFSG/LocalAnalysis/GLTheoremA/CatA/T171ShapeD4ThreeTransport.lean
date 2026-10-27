module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcU2Model
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
import CFSG.Assembly.LargeEvenGLABridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

set_option linter.unusedSectionVars false


private theorem largeEvenInduces_trans_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {L : Subgroup G} {M : Type} [Group M] [Finite M]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* M) (eM : PSimple p L ≃* M)
    (hθmk : ∀ l : ↥L, θ (QuotientGroup.mk l) =
      eM (QuotientGroup.mk (QuotientGroup.mk l)))
    {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) {r : PSimple p L}
    (hr : MulAut.conj r = MI.indAut p L a haN) :
    LargeEvenInduces θ (conjRel a) (MulAut.conj (eM r)) := by
  intro l l' hll
  have hrel : indRel p L a (QuotientGroup.mk l) (QuotientGroup.mk l') :=
    ⟨l, l', rfl, rfl, hll⟩
  have h1 : MI.indAut p L a haN (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk haN hrel
  have h3 : r * (QuotientGroup.mk (QuotientGroup.mk l) : PSimple p L) * r⁻¹ =
      QuotientGroup.mk (QuotientGroup.mk l') := by
    rw [← MulAut.conj_apply, hr]
    exact h1
  rw [hθmk l, hθmk l', MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul, h3]

private theorem modelElement_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {M : Type} [Group M] [Finite M] (θ : ↥L ⧸ Subgroup.center ↥L ≃* M) {x : M}
    (hdN : d ∈ Subgroup.normalizer (L : Set G))
    (hxind : LargeEvenInduces θ (conjRel d) (MulAut.conj x)) : x ≠ 1 := by
  intro hx1
  have htriv : LargeEvenInduces θ (conjRel d) (1 : MulAut M) := by
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

private theorem exists_model_lift_pair {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    {M : Type} [Group M] [Finite M] (eM : PSimple p L ≃* M) :
    ∃ (x w : M) (θ : ↥L ⧸ Subgroup.center ↥L ≃* M),
      LargeEvenInduces θ (conjRel d) (MulAut.conj x) ∧
      LargeEvenInduces θ (conjRel b) (MulAut.conj w) := by
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
  have hdin : InducesInnerMod p L d := inducesInnerMod_of_mem_not_shape hS hshape hS.d_mem
  obtain ⟨eP, heP⟩ := exists_pSimpleEquivCenterQuot_mk hS.prime hS.qs hpL
  obtain ⟨r, hr⟩ : ∃ r : PSimple p L, MulAut.conj r = MI.indAut p L d hdN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hdN).2 hdin
  obtain ⟨r', hr'⟩ : ∃ r' : PSimple p L, MulAut.conj r' = MI.indAut p L b hbN :=
    (MI.indAut_mem_inner_iff hS.prime hLself hbN).2 hin
  let θ : ↥L ⧸ Subgroup.center ↥L ≃* M := eP.trans eM
  let x : M := eM r
  let w : M := eM r'
  have hθmk : ∀ l : ↥L, θ (QuotientGroup.mk l) =
      eM (QuotientGroup.mk (QuotientGroup.mk l)) := by
    intro l
    show eM (eP (QuotientGroup.mk l)) = _
    rw [heP l]
  exact ⟨x, w, θ, largeEvenInduces_trans_conj θ eM hθmk hdN hr,
    largeEvenInduces_trans_conj θ eM hθmk hbN hr'⟩

private theorem lift_pair_properties {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* M} {x w : M}
    (hxind : LargeEvenInduces θ (conjRel d) (MulAut.conj x))
    (hwind : LargeEvenInduces θ (conjRel b) (MulAut.conj w)) :
    x ≠ 1 ∧ x ^ p = 1 ∧ w ^ p = 1 ∧ x * w = w * x := by
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hxp : x ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one' hZ
      (largeEvenInduces_pow_eq_one hdN hxind (hS.elem.2 d hS.d_mem))
  have hwp : w ^ p = 1 :=
    pow_eq_one_of_conj_pow_eq_one' hZ
      (largeEvenInduces_pow_eq_one hbN hwind (hS.elem.2 b hS.b_mem))
  have hxw : x * w = w * x :=
    mul_comm_of_largeEvenInduces hS θ hdN hbN hZ hxind hwind
  exact ⟨modelElement_ne_one hS θ hdN hxind, hxp, hwp, hxw⟩

theorem exists_model_component {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    (hshape : ¬ I171.I171LieShapeAt p L) (hin : InducesInnerMod p L b)
    {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥) (eM : PSimple p L ≃* M) :
    ∃ (x w : M) (Kc : Subgroup M) (hw : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc)
      (e : PSimple p J ≃* (↥Kc ⧸ Subgroup.center ↥Kc)),
      x ≠ 1 ∧ x ^ p = 1 ∧ w ^ p = 1 ∧ x * w = w * x ∧
      CFSG.Assembly.IsComponentOf Kc
        (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (MulAut.conj x)) ∧
      MulAut.congr e (MI.indAut p J b hS.b_norm) =
        centerQuotientHom ↥Kc
          (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hw⟩) := by
  obtain ⟨x, w, θ, hxind, hwind⟩ := exists_model_lift_pair hS hshape hin eM
  obtain ⟨hx1, hxp, hwp, hxw⟩ := lift_pair_properties hS hZ hxind hwind
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  have hJc : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
  have hcomp := componentDescent_holds G L hS.qs M θ d hdN (MulAut.conj x) hxind J hJc
    ((CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).trans hS.comp.2)
  have hwstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut
      ((J.subgroupOf L).map (piCenterQuot θ)) :=
    conj_mem_subgroupStabAut hS hbN θ hwind
  obtain ⟨e, he⟩ := exists_indAut_eq_centerQuotient hS θ w hwind hwstab
  exact ⟨x, w, (J.subgroupOf L).map (piCenterQuot θ), hwstab, e, hx1, hxp, hwp, hxw,
    hcomp.1, he⟩

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
