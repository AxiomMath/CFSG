module

public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Orbit
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaPlus.Commutant
public import CFSG.LargeExtraspecial.S14NQNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

private theorem omega_data (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g t)) (hQ : Q.polarBilin.Nondegenerate),
      CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ Q.polarBilin = beta H C ht ht1 hVQ ∧
        RmodN S g t = omegaGroup Q hQ := by
  obtain ⟨Q, hQ, hpol, hR, -, hsing⟩ := hΩ.exists_form
  have hplusQ : CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    obtain ⟨P₀, hP₀2, hP₀⟩ := hplus
    refine ⟨P₀, by rw [hP₀2, h4], fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
    · exact (hsing v hv0).mpr (hP₀ v hv hv0)
  exact ⟨Q, hQ, hplusQ, hpol, hR⟩

theorem inf_Nbar_eq_bot (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hP9 : Nat.card P = 9) :
    P ⊓ Nbar S g t = ⊥ := by
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have hle : P ⊓ Nbar S g t ≤ ⊥ := by
    intro w hw
    rw [Subgroup.mem_inf] at hw
    rw [hN] at hw
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_zpowers_of_mem_card_nine H ht hP9 hw.2 hw.1)
  exact le_antisymm hle bot_le

theorem card_map_resV (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) {P : Subgroup S.O} (hPR : P ≤ Rbar S g t)
    (hP9 : Nat.card P = 9) :
    Nat.card ((P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t)) = 9 := by
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have hKP : ∀ x : P.subgroupOf (Rbar S g t), ((x : Rbar S g t) : S.O) ∈ P :=
    fun x => mem_subgroupOf.mp x.2
  obtain ⟨f, hfdef⟩ :
      ∃ f : P.subgroupOf (Rbar S g t) →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t),
      f = (resV H.conj_mem t).comp (P.subgroupOf (Rbar S g t)).subtype := ⟨_, rfl⟩
  have hfx : ∀ x : P.subgroupOf (Rbar S g t), f x = resV H.conj_mem t (x : Rbar S g t) :=
    fun x => by rw [hfdef]; rfl
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : f (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : (((a⁻¹ * b : P.subgroupOf (Rbar S g t)) : Rbar S g t) : S.O) ∈ Nbar S g t := by
      rw [hfx] at h1
      exact (resV_eq_one_iff H.conj_mem _).mp h1
    rw [hN] at h2
    have h3 := eq_one_of_mem_zpowers_of_mem_card_nine H ht hP9 h2 (hKP (a⁻¹ * b))
    have h4' : a⁻¹ * b = 1 := Subtype.ext (Subtype.ext h3)
    rw [inv_mul_eq_one] at h4'
    exact h4'
  have hKcard : Nat.card (P.subgroupOf (Rbar S g t)) = 9 := by
    rw [← hP9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hrange : f.range = (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← hKcard]
  exact Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

private theorem map_subgroupOf_resV_le_omegaGroup (H : Hyp4 S g) {t : S.O}
    {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (hQ : Q.polarBilin.Nondegenerate) (hR : RmodN S g t = omegaGroup Q hQ)
    {P : Subgroup S.O} (hPR : P ≤ Rbar S g t) :
    (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) ≤ omegaGroup Q hQ := by
  rw [← hR, ← range_resV H.conj_mem t]
  intro p hp
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
  exact ⟨y, rfl⟩

theorem pow_three_of_mem (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) : ∀ x ∈ P, x ^ 3 = 1 := by
  obtain ⟨Q, hQ, hplusQ, hpol, hR⟩ := omega_data H C ht ht1 hVQ hΩ h4 hplus
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have hinf := inf_Nbar_eq_bot hCE hw H hNo C ht ht1 hVQ hΩ h4 hP9
  have hbarΩ := map_subgroupOf_resV_le_omegaGroup H hQ hR hPR
  intro x hxP
  have h9x : x ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨x, hxP⟩)
    rw [hP9] at h
    exact congrArg Subtype.val h
  have hmem : resV H.conj_mem t ⟨x, hPR hxP⟩ ∈
      (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) :=
    Subgroup.mem_map.mpr ⟨⟨x, hPR hxP⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hφ3 : (resV H.conj_mem t ⟨x, hPR hxP⟩) ^ 3 = 1 := by
    apply pow_three_of_pow_nine_omega hQ h4 hplusQ (hbarΩ hmem)
    rw [← map_pow]
    have hx9 : (⟨x, hPR hxP⟩ : Rbar S g t) ^ 9 = 1 := Subtype.ext h9x
    rw [hx9, map_one]
  have hx3N : x ^ 3 ∈ Nbar S g t := by
    refine ⟨Subgroup.pow_mem (Rbar S g t) (hPR hxP) 3, fun v hv => ?_⟩
    have h1 : resV H.conj_mem t
        (⟨x ^ 3, Subgroup.pow_mem (Rbar S g t) (hPR hxP) 3⟩ : Rbar S g t) = 1 := by
      rw [show (⟨x ^ 3, Subgroup.pow_mem (Rbar S g t) (hPR hxP) 3⟩ : Rbar S g t) =
        (⟨x, hPR hxP⟩ : Rbar S g t) ^ 3 from Subtype.ext rfl, map_pow]
      exact hφ3
    have h3 := coe_resV_apply H.conj_mem
      (⟨x ^ 3, Subgroup.pow_mem (Rbar S g t) (hPR hxP) 3⟩ : Rbar S g t) ⟨v, hv⟩
    rw [h1] at h3
    simpa using h3.symm
  have hx3P : x ^ 3 ∈ P := Subgroup.pow_mem P hxP 3
  have hmem' : x ^ 3 ∈ P ⊓ Nbar S g t := ⟨hx3P, hx3N⟩
  rw [hinf] at hmem'
  simpa using hmem'

theorem eq_of_le_Rbar_card_nine (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) {P' : Subgroup S.O}
    (hP'R : P' ≤ Rbar S g t) (hP'9 : Nat.card P' = 9) : P' = P := by
  obtain ⟨Q, hQ, hplusQ, hpol, hR⟩ := omega_data H C ht ht1 hVQ hΩ h4 hplus
  have hN : Nbar S g t = zpowers t :=
    W4As.Nbar_eq_zpowers_omega4 hCE hw H hNo C ht ht1 hVQ hΩ h4
  have hP3 := pow_three_of_mem hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9
  have hP'3 := pow_three_of_mem hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hP'R hP'9
  have hbar : (P'.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) =
      (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) := by
    refine eq_of_card_nine_omega
      (P := (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t))
      (P' := (P'.subgroupOf (Rbar S g t)).map (resV H.conj_mem t)) hQ h4 hplusQ
      (map_subgroupOf_resV_le_omegaGroup (P := P) H hQ hR hPR)
      (card_map_resV (P := P) hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP9)
      (map_subgroupOf_resV_le_omegaGroup (P := P') H hQ hR hP'R)
      (card_map_resV (P := P') hCE hw H hNo C ht ht1 hVQ hΩ h4 hP'R hP'9)
  have ht2 : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have ht3 : t ^ 3 = t := by
    rw [pow_succ, pow_two, ht2, one_mul]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hP9, hP'9])
  intro x' hx'
  have hx'R : x' ∈ Rbar S g t := hP'R hx'
  have hmem : resV H.conj_mem t ⟨x', hx'R⟩ ∈
      (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t) := by
    rw [← hbar]
    exact Subgroup.mem_map.mpr ⟨⟨x', hx'R⟩, Subgroup.mem_subgroupOf.mpr hx', rfl⟩
  obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.mp hmem
  have hyP : (y : S.O) ∈ P := Subgroup.mem_subgroupOf.mp hy
  have hker : ((y⁻¹ * ⟨x', hx'R⟩ : Rbar S g t) : S.O) ∈ Nbar S g t := by
    apply (resV_eq_one_iff (t := t) H.conj_mem (y⁻¹ * ⟨x', hx'R⟩)).mp
    rw [map_mul, map_inv, hyφ, inv_mul_cancel]
  rw [hN] at hker
  rcases eq_one_or_eq_of_mem_zpowers (mul_self_of_mem_Lbar S H.conj_mem ht) hker with hw | hw
  · have hw' : (y : S.O)⁻¹ * x' = 1 := by simpa using hw
    have hx'y : x' = (y : S.O) := (inv_mul_eq_one.mp hw').symm
    rw [hx'y]
    exact hyP
  · have hw' : (y : S.O)⁻¹ * x' = t := by simpa using hw
    have hx't : x' = (y : S.O) * t := by
      have := congrArg (fun z => (y : S.O) * z) hw'
      simpa [mul_assoc] using this
    have hyt : (y : S.O) * t = t * (y : S.O) :=
      commute_of_mem_Rbar H.conj_mem (y.2)
    have hcube : ((y : S.O) * t) ^ 3 = (y : S.O) ^ 3 * t ^ 3 :=
      Commute.mul_pow hyt 3
    have hx'3 : x' ^ 3 = t := by
      rw [hx't, hcube, hP3 (y : S.O) hyP, ht3, one_mul]
    exact absurd (hx'3.symm.trans (hP'3 x' hx')) ht1

theorem conj_mem_of_mem_Ct (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) :
    ∀ c ∈ S14.Ct S t, ∀ x ∈ P, c * x * c⁻¹ ∈ P := by
  intro c hc x hx
  have hR : P.map (MulAut.conj c).toMonoidHom ≤ Rbar S g t := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact S14.conj_mem_Rbar_of_mem_Ct hc (hPR hy)
  have hcard : Nat.card (P.map (MulAut.conj c).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hP9]
  have heq := eq_of_le_Rbar_card_nine hCE hw H hNo C ht ht1 hVQ hΩ h4 hplus hPR hP9 hR hcard
  rw [← heq]
  exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

theorem card_commutant_le (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) :
    Nat.card {f : Vt S g t →ₗ[ZMod 2] Vt S g t //
      (∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
      ∀ v, beta H C ht ht1 hVQ (f v) v = 0} ≤ 4 := by
  obtain ⟨Q, hQ, hplusQ, hpol, hR⟩ := omega_data H C ht ht1 hVQ hΩ h4 hplus
  have hbarΩ := map_subgroupOf_resV_le_omegaGroup H hQ hR hPR
  have hPbar9 := card_map_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP9
  have hiff : ∀ f : Vt S g t →ₗ[ZMod 2] Vt S g t,
      ((∀ p ∈ (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t), ∀ w, f (p w) = p (f w)) ∧
        ∀ w, Q.polarBilin (f w) w = 0) ↔
      ((∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
        f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v)) ∧
       ∀ v, beta H C ht ht1 hVQ (f v) v = 0) := by
    intro f
    rw [hpol]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun x hx v => h1 _ (Subgroup.mem_map.mpr
        ⟨⟨x, hPR hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩) v, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun p hp => ?_, h2⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
      exact h1 (y : S.O) (Subgroup.mem_subgroupOf.mp hy)
  rw [← Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_commutant_alt_le hQ h4 hplusQ hbarΩ hPbar9

theorem eq_id_of_commute_resV (hCE : CentralExtInput.{0}) (hw : S.width = 4) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) {f : Vt S g t →ₗ[ZMod 2] Vt S g t}
    (hfP : ∀ (x : S.O) (hx : x ∈ P) (v : Vt S g t),
      f (resV H.conj_mem t ⟨x, hPR hx⟩ v) = resV H.conj_mem t ⟨x, hPR hx⟩ (f v))
    (halt : ∀ v, beta H C ht ht1 hVQ (f v) v = 0) (hinj : Function.Injective f) :
    f = LinearMap.id := by
  obtain ⟨Q, hQ, hplusQ, hpol, hR⟩ := omega_data H C ht ht1 hVQ hΩ h4 hplus
  have hbarΩ := map_subgroupOf_resV_le_omegaGroup H hQ hR hPR
  have hPbar9 := card_map_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP9
  have hfP' : ∀ p ∈ (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t),
      ∀ w, f (p w) = p (f w) := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
    have hmem : (⟨(y : S.O), hPR (Subgroup.mem_subgroupOf.mp hy)⟩ : Rbar S g t) = y :=
      Subtype.ext rfl
    rw [← hmem]
    exact hfP (y : S.O) (Subgroup.mem_subgroupOf.mp hy)
  have halt' : ∀ w, Q.polarBilin (f w) w = 0 := by
    intro w
    rw [hpol]
    exact halt w
  exact eq_id_of_commute_alt hQ h4 hplusQ hbarΩ hPbar9 hfP' halt' hinj

theorem pow_three_of_commute_resV (hCE : CentralExtInput.{0}) (hw : S.width = 4)
    (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (h4 : finrank (ZMod 2) (Vt S g t) = 4) (hplus : PlusTypeAt S g ht) {P : Subgroup S.O}
    (hPR : P ≤ Rbar S g t) (hP9 : Nat.card P = 9) {φ : Vt S g t ≃ₗ[ZMod 2] Vt S g t}
    (hφP : ∀ (x : S.O) (hx : x ∈ P),
      φ * resV H.conj_mem t ⟨x, hPR hx⟩ = resV H.conj_mem t ⟨x, hPR hx⟩ * φ) :
    φ ^ 3 = 1 := by
  obtain ⟨Q, hQ, hplusQ, hpol, hR⟩ := omega_data H C ht ht1 hVQ hΩ h4 hplus
  have hbarΩ := map_subgroupOf_resV_le_omegaGroup H hQ hR hPR
  have hPbar9 := card_map_resV hCE hw H hNo C ht ht1 hVQ hΩ h4 hPR hP9
  have hφP' : ∀ p ∈ (P.subgroupOf (Rbar S g t)).map (resV H.conj_mem t), φ * p = p * φ := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hp
    have hmem : (⟨(y : S.O), hPR (Subgroup.mem_subgroupOf.mp hy)⟩ : Rbar S g t) = y :=
      Subtype.ext rfl
    rw [← hmem]
    exact hφP (y : S.O) (Subgroup.mem_subgroupOf.mp hy)
  exact pow_three_of_commute hQ h4 hplusQ hbarΩ hPbar9 hφP'

end CFSG.GF2Type.Smith1979.OmegaPlus
