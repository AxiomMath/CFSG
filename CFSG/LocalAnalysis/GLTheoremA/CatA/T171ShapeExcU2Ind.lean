module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndNat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172AGrp
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyBalance
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d
public import CFSG.GroupActions.SubgroupStabilizerOuterBound
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)

theorem exists_pSimpleEquivCenterQuot_mk {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}
    (hp : p.Prime) {K : Subgroup Ω} (hq : CFSG.Open.IsQuasisimple ↥K) (hd : p ∣ Nat.card ↥K) :
    ∃ e : (↥K ⧸ Subgroup.center ↥K) ≃* PSimple p K,
      ∀ l : ↥K, e (QuotientGroup.mk l) = QuotientGroup.mk (QuotientGroup.mk l) := by
  haveI : Group.IsPerfect ↥K := ⟨hq.1⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hOne : GLAPPrimeCore p ↥K ≠ ⊤ := by
    intro htop
    have hc : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) :=
      CFSG.pPrimeCore_coprime_card (p := p) (G := ↥K)
    rw [htop, Subgroup.card_top] at hc
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hc hd)
  have hO := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq inferInstance hOne
  have hOZ := CFSG.LocalAnalysis.GLTheoremA.S172A.center_quotient_eq_map (X := ↥K) hO
  let f : ↥K →* PSimple p K :=
    (QuotientGroup.mk' (Subgroup.center (PQuot p K))).comp
      (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p K))).comp
      (QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥K))
  have hker : f.ker = Subgroup.center ↥K := by
    ext x
    constructor
    · intro hx
      have h2 : (QuotientGroup.mk x : PQuot p K) ∈ Subgroup.center (PQuot p K) := by
        rw [← QuotientGroup.eq_one_iff]
        exact hx
      rw [hOZ] at h2
      obtain ⟨z, hz, hzx⟩ := h2
      have hmem : z⁻¹ * x ∈ GLAPPrimeCore p ↥K := by
        have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) (z⁻¹ * x) = 1 := by
          rw [map_mul, map_inv]
          rw [show (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) z =
            (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) x from hzx]
          exact inv_mul_cancel _
        exact (QuotientGroup.eq_one_iff _).1 h1
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have h1c : y * (z⁻¹ * x) = (z⁻¹ * x) * y := Subgroup.mem_center_iff.1 (hO hmem) y
      have h3c : y * z = z * y := Subgroup.mem_center_iff.1 hz y
      calc y * x = y * (z * (z⁻¹ * x)) := by group
        _ = (y * z) * (z⁻¹ * x) := by group
        _ = (z * y) * (z⁻¹ * x) := by rw [h3c]
        _ = z * (y * (z⁻¹ * x)) := by group
        _ = z * ((z⁻¹ * x) * y) := by rw [h1c]
        _ = z * (z⁻¹ * x) * y := by group
        _ = x * y := by group
    · intro hx
      show f x = 1
      have h2 : (QuotientGroup.mk x : PQuot p K) ∈ Subgroup.center (PQuot p K) := by
        rw [hOZ]
        exact ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).2 h2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf), fun l => rfl⟩

private theorem isQuasisimple_image_piCenterQuot {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    CFSG.Open.IsQuasisimple ↥((J.subgroupOf L).map (piCenterQuot θ)) := by
  have hJL : J ≤ L := hS.comp.1.1.trans inf_le_left
  have hπker : (piCenterQuot θ).ker ≤ Subgroup.center ↥L := by
    rw [show (piCenterQuot θ).ker = Subgroup.center ↥L from by
      dsimp only [piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  let πJ : ↥J →* R := (piCenterQuot θ).comp (Subgroup.inclusion hJL)
  have hkerJ : πJ.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have h2 : Subgroup.inclusion hJL j ∈ (piCenterQuot θ).ker := hj
    have h3 := hπker h2
    rw [Subgroup.mem_center_iff] at h3 ⊢
    intro k
    exact Subtype.ext (congrArg (fun t : ↥L => (t : G)) (h3 (Subgroup.inclusion hJL k)))
  have hmap : (⊤ : Subgroup ↥J).map πJ = (J.subgroupOf L).map (piCenterQuot θ) := by
    rw [Subgroup.map_top]
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 j.2)
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩
  have hq : CFSG.Open.IsQuasisimple ↥J := hS.comp.1.2.2
  have hq' : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup ↥J) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv (G := ↥J)).symm hq
  rw [← hmap]
  exact CFSG.ClassicalInvolution.Balance.Bootstrap.isQuasisimple_map_of_ker_le_center πJ hkerJ
    (R := ⊤) hq'

private theorem glapComponent_image_piCenterQuot {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    GLAPComponent p
      (((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L).map (piCenterQuot θ))
      ((J.subgroupOf L).map (piCenterQuot θ)) := by
  have hπker : (piCenterQuot θ).ker ≤ Subgroup.center ↥L := by
    rw [show (piCenterQuot θ).ker = Subgroup.center ↥L from by
      dsimp only [piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  have hXle : L ⊓ Subgroup.centralizer ({d} : Set G) ≤ L := inf_le_left
  have hJ' : GLAPComponent p ((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L)
      (J.subgroupOf L) :=
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hS.prime hXle hS.pcomp
  have hc : ∀ z ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L ⊓
      (piCenterQuot θ).ker, ∀ x ∈ (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L,
      x * z = z * x := by
    intro z hz x _
    exact Subgroup.mem_center_iff.1 (hπker hz.2) x
  exact CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_map_central hS.prime
    (piCenterQuot θ) hc hJ'

private theorem glapPrimeCore_le_center_image {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) :
    GLAPPrimeCore p ↥((J.subgroupOf L).map (piCenterQuot θ)) ≤
      Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ)) := by
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hpbar : p ∣ Nat.card ↥((J.subgroupOf L).map (piCenterQuot θ)) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime (glapComponent_image_piCenterQuot hS θ)
  have hne : GLAPPrimeCore p ↥((J.subgroupOf L).map (piCenterQuot θ)) ≠ ⊤ := by
    intro htop
    have hc' : Nat.Coprime p (Nat.card (GLAPPrimeCore p
        ↥((J.subgroupOf L).map (piCenterQuot θ)))) :=
      CFSG.pPrimeCore_coprime_card
    rw [htop, Subgroup.card_top] at hc'
    exact hS.prime.ne_one (Nat.Coprime.eq_one_of_dvd hc' hpbar)
  exact CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple
    (isQuasisimple_image_piCenterQuot hS θ) inferInstance hne

theorem exists_indAut_eq_centerQuotient {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J A : Subgroup G} {d b : G} (hS : Setup p L J A d b)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (y : R)
    (hind : LargeEvenInduces θ (conjRel b) (MulAut.conj y))
    (hstab : MulAut.conj y ∈ CFSG.GroupActions.subgroupStabAut
      ((J.subgroupOf L).map (piCenterQuot θ))) :
    ∃ e : PSimple p J ≃*
        (↥((J.subgroupOf L).map (piCenterQuot θ)) ⧸
          Subgroup.center ↥((J.subgroupOf L).map (piCenterQuot θ))),
      MulAut.congr e (MI.indAut p J b hS.b_norm) =
        centerQuotientHom ↥((J.subgroupOf L).map (piCenterQuot θ))
          (CFSG.GroupActions.subgroupStabRestrict _ ⟨MulAut.conj y, hstab⟩) := by
  classical
  haveI : Fact p.Prime := ⟨hS.prime⟩
  set Jbar : Subgroup R := (J.subgroupOf L).map (piCenterQuot θ) with hJbardef
  have hN : y ∈ Subgroup.normalizer (Jbar : Set R) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hstab
  obtain ⟨e0, he0⟩ := componentDescentIndAut_inv_holds p L J A d b θ y hS hind hN
  have hq : CFSG.Open.IsQuasisimple ↥Jbar := isQuasisimple_image_piCenterQuot hS θ
  have hO : GLAPPrimeCore p ↥Jbar ≤ Subgroup.center ↥Jbar := glapPrimeCore_le_center_image hS θ
  have hpbar : p ∣ Nat.card ↥Jbar :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      hS.prime (glapComponent_image_piCenterQuot hS θ)
  obtain ⟨e1, he1⟩ := exists_pSimpleEquivCenterQuot_mk hS.prime hq hpbar
  have hN' : y⁻¹ ∈ Subgroup.normalizer (Jbar : Set R) := Subgroup.inv_mem _ hN
  have hkey : MulAut.congr e1.symm (MI.indAut p Jbar y⁻¹ hN') =
      centerQuotientHom ↥Jbar (CFSG.GroupActions.subgroupStabRestrict Jbar
        ⟨MulAut.conj y, hstab⟩) := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    show e1.symm (MI.indAut p Jbar y⁻¹ hN' (e1 (QuotientGroup.mk x))) =
      centerQuotientHom ↥Jbar (CFSG.GroupActions.subgroupStabRestrict Jbar
        ⟨MulAut.conj y, hstab⟩) (QuotientGroup.mk x)
    rw [he1 x]
    have hl : MI.indAut p Jbar y⁻¹ hN' (QuotientGroup.mk (QuotientGroup.mk x)) =
        QuotientGroup.mk (QuotientGroup.mk (Jbar.normalizerMonoidHom
          ⟨(y⁻¹)⁻¹, Subgroup.inv_mem _ hN'⟩ x)) := by
      show CFSG.LocalAnalysis.GLTheoremA.chevAut p Jbar
        ⟨(y⁻¹)⁻¹, Subgroup.inv_mem _ hN'⟩
        (CFSG.LocalAnalysis.GLTheoremA.chevQuotHom p Jbar x) = _
      rw [CFSG.LocalAnalysis.GLTheoremA.chevAut_chevQuotHom]
      rfl
    rw [hl]
    have hl2 : e1.symm (QuotientGroup.mk (QuotientGroup.mk (Jbar.normalizerMonoidHom
        ⟨(y⁻¹)⁻¹, Subgroup.inv_mem _ hN'⟩ x))) =
        QuotientGroup.mk (Jbar.normalizerMonoidHom ⟨(y⁻¹)⁻¹, Subgroup.inv_mem _ hN'⟩ x) := by
      rw [← he1, MulEquiv.symm_apply_apply]
    rw [hl2]
    show QuotientGroup.mk (Jbar.normalizerMonoidHom ⟨(y⁻¹)⁻¹, Subgroup.inv_mem _ hN'⟩ x) =
        (QuotientGroup.mk (CFSG.GroupActions.subgroupStabRestrict Jbar
          ⟨MulAut.conj y, hstab⟩ x) : ↥Jbar ⧸ Subgroup.center ↥Jbar)
    congr 1
    exact Subtype.ext (by
      rw [CFSG.GroupActions.subgroupStabRestrict_apply,
        Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      group)
  refine ⟨e0.trans e1.symm, ?_⟩
  rw [show MulAut.congr (e0.trans e1.symm) (MI.indAut p J b hS.b_norm) =
      MulAut.congr e1.symm (MulAut.congr e0 (MI.indAut p J b hS.b_norm)) from by
    ext z
    rfl, he0, hkey]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
