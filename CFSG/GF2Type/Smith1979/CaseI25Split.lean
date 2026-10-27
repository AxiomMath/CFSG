module

public import CFSG.GF2Type.Smith1979.CaseI25Nu
public import CFSG.GF2Type.Smith1979.CaseI25Transfer
public import CFSG.LargeExtraspecial.S14Perfect
public import CFSG.LargeExtraspecial.S7SevenB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem commutatorElement_mul_left_of_commute {x y z : X} (hzy : Commute z y) :
    ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : z * y * z⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzy.eq
  rw [commutatorElement_def, commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem commutatorElement_mul_right_of_commute {x y z : X} (hzx : Commute z x) :
    ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h : z * x⁻¹ * z⁻¹ = x⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzx.inv_right.eq
  rw [commutatorElement_def, commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem commutatorElement_mul_mul_of_commute {x y z z' : X} (hzy : Commute z y)
    (hzz' : Commute z z') (hz'x : Commute z' x) : ⁅x * z, y * z'⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_mul_left_of_commute (hzy.mul_right hzz'),
    commutatorElement_mul_right_of_commute hz'x]

end Generic

section OmegaCard

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {Q : QuadraticForm (ZMod 2) W}

theorem card_omegaGroup_of_ncard_singular (hV : finrank (ZMod 2) W = 6)
    (hQ : Q.polarBilin.Nondegenerate) {a : W} (ha0 : a ≠ 0) (ha : Q a = 0)
    (h27 : {v : W | v ≠ 0 ∧ Q v = 0}.ncard = 27) : Nat.card (omegaGroup Q hQ) = 25920 := by
  classical
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W ≃ₗ[ZMod 2] W) := O62.finite_linearEquiv
  set Ω := omegaGroup Q hQ
  have horb : MulAction.orbit Ω a = {v : W | v ≠ 0 ∧ Q v = 0} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨?_, ?_⟩
      · intro h
        apply ha0
        exact (LinearEquiv.map_eq_zero_iff (x : W ≃ₗ[ZMod 2] W)).mp h
      · have := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
          (omegaGroup_le Q hQ x.2) a
        exact this.trans ha
    · rintro ⟨hv0, hv⟩
      obtain ⟨x, hx, hxa⟩ := O62.exists_mem_omegaGroup_apply_eq hQ (by omega) ha0 hv0
        (by rw [ha, hv])
      exact ⟨⟨x, hx⟩, hxa⟩
  have key : Nat.card (MulAction.orbit Ω a) * Nat.card (MulAction.stabilizer Ω a) =
      Nat.card Ω := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Ω a)
  have horbcard : Nat.card (MulAction.orbit Ω a) = 27 := by
    rw [horb, Nat.card_coe_set_eq]
    exact h27
  rw [horbcard] at key
  rcases O62.card_omegaGroup hV hQ with h | h
  · rw [h] at key
    omega
  · exact h

end OmegaCard

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

section Light

variable (H : Hyp4 S g) {t : S.O}
include H

theorem commute_zpowers_Rbar {s r : S.O} (hs : s ∈ zpowers t) (hr : r ∈ Rbar S g t) :
    Commute s r := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
  exact (Commute.zpow_right (commute_of_mem_Rbar H.conj_mem hr) k).symm

end Light

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem Rbar_eq_commutator_sup : Rbar S g t = ⁅Rbar S g t, Rbar S g t⁆ ⊔ zpowers t := by
  obtain ⟨hs, hn⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6.ge
  have hperf := commutator_RmodN hs hn
  have hnab : ¬ IsMulCommutative (RmodN S g t) := fun hc => by
    have h1 : ⁅RmodN S g t, RmodN S g t⁆ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr hc
    rw [hperf] at h1
    haveI : Nontrivial (RmodN S g t) := hs.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this h1
  refine le_antisymm ?_ (sup_le (Subgroup.commutator_le_self _) (zpowers_le.mpr
    (Lbar_le_Rbar ht ht)))
  have := CFSG.LargeExtraspecial.S14.Rbar_le_commutator_sup_Nbar H.conj_mem hs hnab
  rwa [hN] at this

theorem exists_mul_of_mem_Rbar {x : S.O} (hx : x ∈ Rbar S g t) :
    ∃ a ∈ ⁅Rbar S g t, Rbar S g t⁆, ∃ s ∈ zpowers t, x = a * s := by
  have hle : zpowers t ≤ normalizer ((⁅Rbar S g t, Rbar S g t⁆ : Subgroup S.O) : Set S.O) := by
    rw [le_normalizer_iff]
    intro s hs k hk
    have hkR : k ∈ Rbar S g t := Subgroup.commutator_le_self _ hk
    rw [(commute_zpowers_Rbar H hs hkR).eq, mul_inv_cancel_right]
    exact hk
  have h := coe_mul_of_right_le_normalizer_left _ _ hle
  rw [← Rbar_eq_commutator_sup hCE H hNo C ht ht1 hVQ hΩ hN h6] at h
  have hx' : x ∈ (↑(Rbar S g t) : Set S.O) := hx
  rw [h] at hx'
  obtain ⟨a, ha, s, hs, rfl⟩ := hx'
  exact ⟨a, ha, s, hs, rfl⟩

theorem commutator_commutator_Rbar :
    ⁅⁅Rbar S g t, Rbar S g t⁆, ⁅Rbar S g t, Rbar S g t⁆⁆ = ⁅Rbar S g t, Rbar S g t⁆ := by
  refine le_antisymm (Subgroup.commutator_le_self _) (Subgroup.commutator_le.mpr ?_)
  intro x hx y hy
  obtain ⟨a, ha, s, hs, rfl⟩ := exists_mul_of_mem_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hx
  obtain ⟨b, hb, s', hs', rfl⟩ := exists_mul_of_mem_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hy
  have haR : a ∈ Rbar S g t := Subgroup.commutator_le_self _ ha
  have hbR : b ∈ Rbar S g t := Subgroup.commutator_le_self _ hb
  have hss' : Commute s s' := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨k', rfl⟩ := mem_zpowers_iff.mp hs'
    exact Commute.zpow_zpow_self t k k'
  rw [commutatorElement_mul_mul_of_commute (commute_zpowers_Rbar H hs hbR) hss'
    (commute_zpowers_Rbar H hs' haR)]
  exact Subgroup.commutator_mem_commutator ha hb

theorem not_mem_commutator_Mbar_of_delta (hΔ : (Delta S g t).ncard = 6) :
    t ∉ ⁅S.Mbar, S.Mbar⁆ := by
  obtain ⟨ν, hν, -⟩ := exists_nu_ker hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have := CaseI25Transfer.not_mem_commutator_Mbar hCE H hNo C ht ht1 hVQ hΩ hN h6 ν hν
  rwa [Subgroup.map_subtype_commutator] at this

theorem not_mem_commutator_Rbar (hΔ : (Delta S g t).ncard = 6) :
    t ∉ ⁅Rbar S g t, Rbar S g t⁆ := fun h =>
  not_mem_commutator_Mbar_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
    (Subgroup.commutator_mono Rbar_le_Mbar Rbar_le_Mbar h)

theorem conj_not_mem_commutator_Mbar (hΔ : (Delta S g t).ncard = 6) {x : S.O}
    (hx : x ∈ S.Mbar) : x * t * x⁻¹ ∉ ⁅S.Mbar, S.Mbar⁆ := by
  intro hxc
  apply not_mem_commutator_Mbar_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have h1 := (mem_normalizer_iff.mp (normalizer_commutator_ge_left (H₁ := S.Mbar)
    (H₂ := S.Mbar) (inv_mem hx)) _).mp hxc
  have e : x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t := by group
  rwa [e] at h1

theorem conj_not_mem_of_perfect (hΔ : (Delta S g t).ncard = 6) {P : Subgroup S.O}
    (hP : P ≤ S.Mbar) (hperf : ⁅P, P⁆ = P) {x : S.O} (hx : x ∈ S.Mbar) : x * t * x⁻¹ ∉ P := by
  intro h
  refine conj_not_mem_commutator_Mbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hx ?_
  have hle : P ≤ ⁅S.Mbar, S.Mbar⁆ :=
    calc P = ⁅P, P⁆ := hperf.symm
      _ ≤ ⁅S.Mbar, S.Mbar⁆ := Subgroup.commutator_mono hP hP
  exact hle h

theorem Delta_not_mem_commutator_Rbar (hΔ : (Delta S g t).ncard = 6) {x : S.O}
    (hx : x ∈ Delta S g t) : x ∉ ⁅Rbar S g t, Rbar S g t⁆ := by
  intro hxc
  obtain ⟨n, hn, rfl⟩ := hx
  exact conj_not_mem_commutator_Mbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hn.1
    (Subgroup.commutator_mono Rbar_le_Mbar Rbar_le_Mbar hxc)

theorem mul_mem_commutator_Rbar_of_mem_Delta (hΔ : (Delta S g t).ncard = 6) {x : S.O}
    (hx : x ∈ Delta S g t) : x * t ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
  have hxL : x ∈ S.Lbar g := delta_subset_Lbar ht hx
  obtain ⟨a, ha, s, hs, hxe⟩ :=
    exists_mul_of_mem_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 (Lbar_le_Rbar ht hxL)
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hs with rfl | rfl
  · rw [mul_one] at hxe
    exact absurd (hxe ▸ ha) (Delta_not_mem_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hx)
  · rw [hxe, mul_assoc, htt, mul_one]
    exact ha

theorem Kbar_le_commutator_Rbar (hΔ : (Delta S g t).ncard = 6) :
    Kbar S g t ≤ ⁅Rbar S g t, Rbar S g t⁆ := by
  refine (closure_le _).mpr ?_
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hx' := mul_mem_commutator_Rbar_of_mem_Delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hx
  have hy' := mul_mem_commutator_Rbar_of_mem_Delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hy
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hyy : y * y = 1 := mul_self_of_mem_Lbar S H.conj_mem (delta_subset_Lbar ht hy)
  have e : x * y = (x * t) * (y * t)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right hyy]
    calc x * y = x * (t * t) * y := by rw [htt, mul_one]
      _ = x * t * (t * y) := by group
  rw [e]
  exact mul_mem hx' (inv_mem hy')

theorem commutator_Rbar_inf_Lbar (hΔ : (Delta S g t).ncard = 6) :
    ⁅Rbar S g t, Rbar S g t⁆ ⊓ S.Lbar g = Kbar S g t := by
  obtain ⟨-, f, -, -, hKmap, -, hnot, -⟩ :=
    invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  have hK := Kbar_le_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine le_antisymm (fun l hl => ?_) (le_inf hK (Kbar_le_Lbar ht))
  obtain ⟨hlR, hlL⟩ := Subgroup.mem_inf.mp hl
  by_contra hlK
  have hfl : f ⟨l, hlL⟩ ≠ 1 := fun h => hlK (by rw [← hKmap]; exact ⟨⟨l, hlL⟩, h, rfl⟩)
  have hft : f ⟨t, ht⟩ ≠ 1 := fun h => hnot (MonoidHom.mem_ker.mpr h)
  have heq : f ⟨l, hlL⟩ = f ⟨t, ht⟩ := SixGen.eq_of_ne_one_of_ne_one _ _ hfl hft
  have hsq : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide
  have hlt : l * t ∈ Kbar S g t := by
    rw [← hKmap]
    refine ⟨⟨l * t, mul_mem hlL ht⟩, ?_, rfl⟩
    show f ⟨l * t, mul_mem hlL ht⟩ = 1
    change f (⟨l, hlL⟩ * ⟨t, ht⟩) = 1
    rw [map_mul, heq]
    exact hsq _
  have h1 : t ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
    have := mul_mem (inv_mem hlR) (hK hlt)
    rwa [inv_mul_cancel_left] at this
  exact not_mem_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ h1

theorem nonempty_mulEquiv_commutator_Rbar (hΔ : (Delta S g t).ncard = 6) :
    Nonempty (↥(⁅Rbar S g t, Rbar S g t⁆) ≃* ↥(RmodN S g t)) := by
  have hle : ⁅Rbar S g t, Rbar S g t⁆ ≤ Rbar S g t := Subgroup.commutator_le_self _
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  let f : ↥(⁅Rbar S g t, Rbar S g t⁆) →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
    (resV H.conj_mem t).comp (Subgroup.inclusion hle)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : S.O) ∈ Nbar S g t := (resV_eq_one_iff H.conj_mem ⟨x, hle x.2⟩).mp hx
    rw [hN] at h1
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp h1 with h | h
    · exact Subtype.ext h
    · have hx2 : (x : S.O) ∈ ⁅Rbar S g t, Rbar S g t⁆ := x.2
      rw [h] at hx2
      exact absurd hx2 (not_mem_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ)
  have hrange : f.range = RmodN S g t := by
    rw [← range_resV H.conj_mem t]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨⟨x, hle x.2⟩, rfl⟩
    · rintro _ ⟨r, rfl⟩
      obtain ⟨a, ha, s, hs, hrs⟩ :=
        exists_mul_of_mem_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 r.2
      have hsR : s ∈ Rbar S g t := zpowers_le.mpr (Lbar_le_Rbar ht ht) hs
      have hr : r = ⟨a, hle ha⟩ * ⟨s, hsR⟩ := Subtype.ext hrs
      refine ⟨⟨a, ha⟩, ?_⟩
      change resV H.conj_mem t ⟨a, hle ha⟩ = resV H.conj_mem t r
      rw [hr, map_mul, (resV_eq_one_iff H.conj_mem ⟨s, hsR⟩).mpr (hN ▸ hs), mul_one]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem simple_card_commutator_Rbar (hΔ : (Delta S g t).ncard = 6) :
    IsSimpleGroup ↥(⁅Rbar S g t, Rbar S g t⁆) ∧
      Nat.card ↥(⁅Rbar S g t, Rbar S g t⁆) = 25920 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := hΩ.exists_form
  obtain ⟨hs, -⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6.ge
  have h27 := ncard_singular_of_delta hCE H hNo C ht ht1 hVQ hΩ hN h6 hpol hX hE hsing hΔ
  refine ⟨(MulEquiv.isSimpleGroup_congr e).mpr hs, ?_⟩
  rw [Nat.card_congr e.toEquiv, hX]
  exact card_omegaGroup_of_ncard_singular h6 hQ (aV_ne_zero H ht)
    (CaseIClosure.Q_aV_eq_zero H ht hsing) h27

theorem Rbar_split (hΔ : (Delta S g t).ncard = 6) :
    Rbar S g t = ⁅Rbar S g t, Rbar S g t⁆ ⊔ zpowers t ∧
      Disjoint ⁅Rbar S g t, Rbar S g t⁆ (zpowers t) ∧
      t ∉ ⁅Rbar S g t, Rbar S g t⁆ ∧
      (∀ r ∈ Rbar S g t, t * r = r * t) ∧
      ⁅⁅Rbar S g t, Rbar S g t⁆, ⁅Rbar S g t, Rbar S g t⁆⁆ = ⁅Rbar S g t, Rbar S g t⁆ ∧
      ⁅Rbar S g t, Rbar S g t⁆ ⊓ S.Lbar g = Kbar S g t ∧
      (∀ x ∈ Delta S g t, x ∉ ⁅Rbar S g t, Rbar S g t⁆) ∧
      IsSimpleGroup ↥(⁅Rbar S g t, Rbar S g t⁆) ∧
      Nat.card ↥(⁅Rbar S g t, Rbar S g t⁆) = 25920 := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hnt := not_mem_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine ⟨Rbar_eq_commutator_sup hCE H hNo C ht ht1 hVQ hΩ hN h6, ?_, hnt,
    fun r hr => (commute_of_mem_Rbar H.conj_mem hr).symm,
    commutator_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6,
    commutator_Rbar_inf_Lbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ,
    fun x hx => Delta_not_mem_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ hx,
    simple_card_commutator_Rbar hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ⟩
  rw [Subgroup.disjoint_def]
  intro x hx hxt
  rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hxt with h | h
  · exact h
  · exact absurd (h ▸ hx) hnt

end Context

end Case25

end CFSG.GF2Type.Smith1979
