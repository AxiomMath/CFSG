module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TwoCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseIINbrSQ8
public import CFSG.Timmesfeld.Bridge.SchurNarrowCore
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LieType.BorelTits.CentralQuotient
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc73Central
public import CFSG.Timmesfeld.Moufang.Exceptional
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem pCoreOf_top (p : ℕ) {X : Type*} [Group X] :
    CFSG.Open.pCoreOf p (⊤ : Subgroup X) = CFSG.pCore p X := by
  unfold CFSG.Open.pCoreOf
  rw [show (⊤ : Subgroup X).subtype = (Subgroup.topEquiv (G := X)).toMonoidHom from rfl]
  exact CFSG.pCore_map_iso p (Subgroup.topEquiv (G := X))

theorem pCore_iso_of_oddCentralCover {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    {ψ : A →* B} (h : OddCentralCover ψ) :
    Nonempty (↥(CFSG.pCore 2 A) ≃* ↥(CFSG.pCore 2 B)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z : Subgroup A := ψ.ker
  haveI : Z.Normal := MonoidHom.normal_ker ψ
  have hZ : Z ≤ Subgroup.center A := h.ker_le_center
  have hcop : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr h.odd_card_ker
  have hle : CFSG.pCore 2 B ≤ (CFSG.pCore 2 A).map ψ := by
    have hBT := CFSG.LieType.BorelTits.pCoreOf_le_map_pCoreOf_comap (G := A) (r := 2) Z hZ hcop
      (⊤ : Subgroup (A ⧸ Z))
    have htop : (⊤ : Subgroup (A ⧸ Z)).comap (QuotientGroup.mk' Z) = (⊤ : Subgroup A) :=
      Subgroup.comap_top _
    rw [pCoreOf_top, htop, pCoreOf_top] at hBT
    let e : (A ⧸ Z) ≃* B := QuotientGroup.quotientKerEquivOfSurjective ψ h.surjective
    have he : (CFSG.pCore 2 (A ⧸ Z)).map e.toMonoidHom = CFSG.pCore 2 B :=
      CFSG.pCore_map_iso 2 e
    have hecomp : e.toMonoidHom.comp (QuotientGroup.mk' Z) = ψ := by
      ext a
      exact QuotientGroup.kerLift_mk ψ a
    have hmap : ((CFSG.pCore 2 A).map (QuotientGroup.mk' Z)).map e.toMonoidHom =
        (CFSG.pCore 2 A).map ψ := by
      rw [Subgroup.map_map, hecomp]
    calc CFSG.pCore 2 B = (CFSG.pCore 2 (A ⧸ Z)).map e.toMonoidHom := he.symm
      _ ≤ ((CFSG.pCore 2 A).map (QuotientGroup.mk' Z)).map e.toMonoidHom :=
          Subgroup.map_mono hBT
      _ = (CFSG.pCore 2 A).map ψ := hmap
  have hge : (CFSG.pCore 2 A).map ψ ≤ CFSG.pCore 2 B :=
    CFSG.LieType.BorelTits.map_pCore_le (r := 2) ψ h.surjective
  have hEq : (CFSG.pCore 2 A).map ψ = CFSG.pCore 2 B := le_antisymm hge hle
  let f : ↥(CFSG.pCore 2 A) →* ↥(CFSG.pCore 2 B) :=
    ((ψ.comp (CFSG.pCore 2 A).subtype)).codRestrict (CFSG.pCore 2 B) fun a =>
      hEq ▸ Subgroup.mem_map_of_mem ψ a.2
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hψab : ψ (a : A) = ψ (b : A) := congrArg Subtype.val hab
    have hker : (a : A)⁻¹ * (b : A) ∈ Z := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hψab, inv_mul_cancel]
    have hmem : (a : A)⁻¹ * (b : A) ∈ CFSG.pCore 2 A :=
      (CFSG.pCore 2 A).mul_mem ((CFSG.pCore 2 A).inv_mem a.2) b.2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := A)) ⟨_, hmem⟩
    have hk' : ((a : A)⁻¹ * (b : A)) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hdvd : orderOf ((a : A)⁻¹ * (b : A)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd' : orderOf ((a : A)⁻¹ * (b : A)) ∣ Nat.card Z :=
      Subgroup.orderOf_dvd_natCard Z hker
    have hc := (Nat.coprime_two_left.mpr h.odd_card_ker).pow_left k
    have hone : orderOf ((a : A)⁻¹ * (b : A)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hc hdvd hdvd'
    have hprod : (a : A)⁻¹ * (b : A) = 1 := orderOf_eq_one_iff.mp hone
    exact Subtype.ext ((inv_mul_eq_one).mp hprod)
  have hf_surj : Function.Surjective f := by
    intro b
    have hb : (b : B) ∈ (CFSG.pCore 2 A).map ψ := by rw [hEq]; exact b.2
    obtain ⟨a, ha, haψ⟩ := Subgroup.mem_map.mp hb
    exact ⟨⟨a, ha⟩, Subtype.ext haψ⟩
  exact ⟨MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩⟩

theorem mem_twoCoreIn_of_lift {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    {L : Subgroup G} {φ : ↥L →* P} (h : OddCentralCover φ) {K : Subgroup P}
    (R : Subgroup P) (hRK : R ≤ K) (hRn : (R.subgroupOf K).Normal) (hR2 : IsPGroup 2 ↥R)
    {r : P} (hr : r ∈ R) {w : ↥L} (hw : w * w = 1) (hwr : φ w = r) :
    (w : G) ∈ twoCoreIn ((K.comap φ).map L.subtype) := by
  obtain ⟨x, hxr, hx⟩ := exists_lift_mem_pCore L φ h hRK hRn hR2 hr
  have hr2 : r * r = 1 := by
    rw [← hwr, ← map_mul, hw, map_one]
  have hx2ker : x ^ 2 ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hxr, pow_two, hr2]
  have hx2one : x * x = 1 := by
    have hodd : Odd (orderOf (x ^ 2)) :=
      h.odd_card_ker.of_dvd_nat (Subgroup.orderOf_dvd_natCard φ.ker hx2ker)
    have h2mem : (x : G) ^ 2 ∈ twoCoreIn ((K.comap φ).map L.subtype) :=
      (twoCoreIn _).pow_mem hx 2
    obtain ⟨k, hk⟩ := (isPGroup_twoCoreIn ((K.comap φ).map L.subtype)) ⟨_, h2mem⟩
    have hk' : ((x : G) ^ 2) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hdvd2 : orderOf (x ^ 2) ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe (H := L) (a := x ^ 2)]
      simpa using orderOf_dvd_of_pow_eq_one hk'
    have hdvdodd : orderOf (x ^ 2) ∣ Nat.card φ.ker :=
      Subgroup.orderOf_dvd_natCard φ.ker hx2ker
    have hcop : Nat.Coprime (2 ^ k) (Nat.card φ.ker) :=
      (Nat.coprime_two_left.mpr h.odd_card_ker).pow_left k
    have hone : orderOf (x ^ 2) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd2 hdvdodd
    rw [← pow_two]
    exact orderOf_eq_one_iff.mp hone
  have hwx : w = x := h.eq_of_mul_self_eq_one hw hx2one (hwr.trans hxr.symm)
  rwa [hwx]

noncomputable def twoCoreInEquivPCore {G : Type} [Group G] (X : Subgroup G) :
    ↥(twoCoreIn X) ≃* ↥(CFSG.pCore 2 ↥X) :=
  (Subgroup.subgroupOfEquivOfLe (twoCoreIn_le_self X)).symm.trans
    (MulEquiv.subgroupCongr (CFSG.openPCoreOf_subgroupOf 2 X))

private def f0I : SL23 := ⟨!![0, 1; -1, 0], by decide⟩

private def f0J : SL23 := ⟨!![1, 1; 1, -1], by decide⟩

private def q8ToSl23 : QuaternionGroup 2 →* SL23 where
  toFun
    | QuaternionGroup.a i => f0I ^ i.val
    | QuaternionGroup.xa i => f0J * f0I ^ i.val
  map_one' := by
    decide
  map_mul' := by
    decide

private theorem q8ToSl23_injective : Function.Injective q8ToSl23 := by
  decide

private theorem q8ToSl23_pow_four (x : QuaternionGroup 2) : q8ToSl23 x ^ 4 = 1 := by
  revert x
  decide

private theorem q8ToSl23_range : q8ToSl23.range = sl23Q8 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rw [mem_sl23Q8]
    exact q8ToSl23_pow_four x
  · have h1 : Nat.card ↥sl23Q8 = 8 := by
      rw [← sl23_pCore_eq_Q8]
      exact sl23_card_pCore
    have h2 : Nat.card ↥q8ToSl23.range = 8 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective q8ToSl23_injective).toEquiv,
        Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [h1, h2]

noncomputable def sl23Q8EquivQuaternionGroup2 : ↥sl23Q8 ≃* QuaternionGroup 2 :=
  ((MonoidHom.ofInjective q8ToSl23_injective).trans
    (MulEquiv.subgroupCongr q8ToSl23_range)).symm

end CFSG.OddStandard.SmallF3.Omega
