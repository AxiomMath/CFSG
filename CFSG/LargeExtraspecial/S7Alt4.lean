module

public import CFSG.LargeExtraspecial.S7SevenMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.Open

universe u

theorem eq_bot_of_normal_of_isPGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (hperf : commutator X = ⊤) {P : Subgroup X} (hPn : P.Normal) (hP : IsPGroup 2 P) :
    P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h | h
  · exact h
  · exfalso
    have hX : IsPGroup 2 X := (h ▸ hP).of_equiv Subgroup.topEquiv
    have hc := hX.center_nontrivial
    have hZ : center X = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h' | h'
      · exfalso
        rw [h'] at hc
        exact not_nontrivial _ hc
      · exact h'
    have hcomm : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top (G := X)).mpr hZ
    rw [hperf] at hcomm
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    have ha : a ∈ (⊥ : Subgroup X) := hcomm ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup X) := hcomm ▸ mem_top b
    rw [mem_bot] at ha hb
    exact hab (ha.trans hb.symm)

theorem zpowers_subgroupOf_normal {X : Type*} [Group X] {R : Subgroup X} {x : X}
    (hcomm : ∀ r ∈ R, r * x = x * r) : ((zpowers x).subgroupOf R).Normal := by
  refine ⟨fun n hn r => ?_⟩
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
  have hrk : (r : X) * x ^ k = x ^ k * r := (Commute.zpow_right (hcomm r r.2) k).eq
  have e : ((r * n * r⁻¹ : R) : X) = (n : X) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk, hrk, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [e]
  exact hn

theorem subgroupOf_centralizer_normal {X : Type*} [Group X] {R : Subgroup X} {x : X}
    (hconj : ∀ c ∈ centralizer ({x} : Set X), ∀ r ∈ R, c * r * c⁻¹ ∈ R) :
    (R.subgroupOf (centralizer ({x} : Set X))).Normal :=
  ⟨fun n hn c => by
    rw [mem_subgroupOf] at hn ⊢
    exact hconj c c.2 n hn⟩

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem commutator_eq_top_RmodN {t : S.O} (hs : IsSimpleGroup (RmodN S g t))
    (hn : S5.NonabelianSylowTwo (RmodN S g t)) : commutator (RmodN S g t) = ⊤ := by
  have h := commutator_RmodN hs hn
  apply Subgroup.map_injective (RmodN S g t).subtype_injective
  rw [map_subtype_commutator, h, ← MonoidHom.range_eq_map, range_subtype]

theorem mem_zpowers_Mbar_iff {t : S.O} (htM : t ∈ S.Mbar) {x : S.Mbar} :
    x ∈ zpowers (⟨t, htM⟩ : S.Mbar) ↔ (x : S.O) ∈ zpowers t := by
  have h := MonoidHom.map_zpowers S.Mbar.subtype (⟨t, htM⟩ : S.Mbar)
  constructor
  · intro hx
    rw [← show S.Mbar.subtype (⟨t, htM⟩ : S.Mbar) = t from rfl, ← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← show S.Mbar.subtype (⟨t, htM⟩ : S.Mbar) = t from rfl, ← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [S.Mbar.subtype_injective hyx] at hy

variable (S g) in
@[expose] noncomputable def resRM (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    (Rbar S g t).subgroupOf S.Mbar →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  (resV haQ t).comp (subgroupOfEquivOfLe (Rbar_le_Mbar (S := S) (g := g) (t := t))).toMonoidHom

theorem range_resRM (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    (resRM S g haQ t).range = RmodN S g t := by
  rw [← range_resV haQ t, resRM, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _), ← MonoidHom.range_eq_map]

theorem resRM_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (x : (Rbar S g t).subgroupOf S.Mbar) :
    resRM S g haQ t x = 1 ↔ ((x : S.Mbar) : S.O) ∈ Nbar S g t :=
  resV_eq_one_iff haQ _

section Six

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
  (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hΩ : OmegaCase H C ht ht1 hVQ)
  (hN : Nbar S g t = zpowers t) (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
include H C ht ht1 hVQ hΩ hN h6

omit hN in
theorem pCore_le_ker :
    CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar) ≤ (resRM S g H.conj_mem t).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hrange := range_resRM H.conj_mem t
  obtain ⟨hs, hn⟩ := (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6
  have hperf := commutator_eq_top_RmodN hs hn
  have hP'R : (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (resRM S g H.conj_mem t) ≤ RmodN S g t := hrange ▸ map_le_range _ _
  have hP'p : IsPGroup 2 ((CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (resRM S g H.conj_mem t)) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := (Rbar S g t).subgroupOf S.Mbar) 2).map _
  have hP'n : (((CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (resRM S g H.conj_mem t)).subgroupOf (RmodN S g t)).Normal := by
    refine ⟨fun z hz y => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨p, hp, hpz⟩ := hz
    have hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resRM S g H.conj_mem t).range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x * p * x⁻¹, (CFSG.LieType.BorelTits.pCore_normal 2).conj_mem p hp x, ?_⟩
    simp only [map_mul, map_inv, hx, hpz, Subgroup.coe_mul, Subgroup.coe_inv]
  have : IsSimpleGroup (RmodN S g t) := hs
  have hbot := eq_bot_of_normal_of_isPGroup hperf hP'n
    (hP'p.of_equiv (subgroupOfEquivOfLe hP'R).symm)
  rw [subgroupOf_eq_bot] at hbot
  have hP'bot : (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (resRM S g H.conj_mem t) = ⊥ :=
    eq_bot_iff.mpr fun z hz => (disjoint_iff_inf_le.mp hbot ⟨hz, hP'R hz⟩)
  rwa [Subgroup.map_eq_bot_iff] at hP'bot

theorem pCoreOf_eq_zpowers :
    CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar) =
      zpowers (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    have h1 := pCore_le_ker H C ht ht1 hVQ hΩ h6 hp
    rw [MonoidHom.mem_ker, resRM_eq_one_iff, hN] at h1
    exact (mem_zpowers_Mbar_iff _).mpr h1
  · have htR : (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) ∈ (Rbar S g t).subgroupOf S.Mbar :=
      mem_subgroupOf.mpr (Lbar_le_Rbar ht ht)
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 (zpowers_le.mpr htR)
      (zpowers_subgroupOf_normal fun r hr => Subtype.ext
        (commute_of_mem_Rbar H.conj_mem (mem_subgroupOf.mp hr))) ?_
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (Subtype.ext (by
      rw [pow_two]
      exact mul_self_of_mem_Lbar S H.conj_mem ht)) fun h => ht1 (congrArg Subtype.val h)

theorem quotientIso_omega {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    {hQ : Q.polarBilin.Nondegenerate} (hX : RmodN S g t = omegaGroup Q hQ) :
    timmesfeldQuotientIso (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar))
      (timmesfeldOmega (Q : Vt S g t → ZMod 2)) := by
  have hmem : ∀ x, resRM S g H.conj_mem t x ∈ timmesfeldOmega (Q : Vt S g t → ZMod 2) := by
    intro x
    rw [timmesfeldOmega_eq Q hQ, ← hX, ← range_resRM H.conj_mem t]
    exact ⟨x, rfl⟩
  refine ⟨(resRM S g H.conj_mem t).codRestrict _ hmem, fun y => ?_, ?_⟩
  · have hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resRM S g H.conj_mem t).range := by
      rw [range_resRM, hX, ← timmesfeldOmega_eq Q hQ]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  · rw [MonoidHom.ker_codRestrict]
    refine le_antisymm (fun x hx => ?_) (pCore_le_ker H C ht ht1 hVQ hΩ h6)
    rw [MonoidHom.mem_ker, resRM_eq_one_iff, hN] at hx
    have h1 : (x : S.Mbar) ∈ CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar) := by
      rw [pCoreOf_eq_zpowers H C ht ht1 hVQ hΩ hN h6]
      exact (mem_zpowers_Mbar_iff _).mpr hx
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [Subtype.ext hyx] at hy

end Six

theorem Rbar_subgroupOf_le_centralizer (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) :
    (Rbar S g t).subgroupOf S.Mbar ≤
      centralizer ({(⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)} : Set S.Mbar) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact Subtype.ext (commute_of_mem_Rbar H.conj_mem (mem_subgroupOf.mp hx))

theorem Rbar_subgroupOf_normal {t : S.O} (ht : t ∈ S.Lbar g) :
    (((Rbar S g t).subgroupOf S.Mbar).subgroupOf
      (centralizer ({(⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar)} : Set S.Mbar))).Normal := by
  refine subgroupOf_centralizer_normal fun c hc n hn => ?_
  rw [mem_subgroupOf] at hn ⊢
  have hct : ((c : S.Mbar) : S.O) * t = t * (c : S.Mbar) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
  have hcM : ((c : S.Mbar) : S.O) ∈ S.Mbar := c.2
  obtain ⟨κ, hκ⟩ := MonoidHom.mem_range.mp hcM
  have hct' : S.ρ κ * t = t * S.ρ κ := by rw [hκ]; exact hct
  have h1 := conj_mem_Rbar hct' hn
  rw [hκ] at h1
  exact h1

theorem exists_quotientIso_fin (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
    (h6 : finrank (ZMod 2) (Vt S g t) = 6) :
    ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
      timmesfeldQuotientIso (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar))
        (timmesfeldOmega q) := by
  obtain ⟨Q, hQ, -, hX, -, -⟩ := hΩ.exists_form
  have hiso := quotientIso_omega H C ht ht1 hVQ hΩ hN h6.ge hX
  obtain ⟨q', hq', -, hiso'⟩ := Bridge.exists_fin_quotientIso_omega Q h6
    ((Bridge.polarBilin_nondegenerate_iff Q).mp hQ) hiso
  exact ⟨q', hq', hiso'⟩

theorem alt4_data (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hN : Nbar S g t = zpowers t) (hn : S.width = 6) :
    ∃ tM : S.Mbar, orderOf tM = 2 ∧ ∃ R : Subgroup S.Mbar,
      R ≤ centralizer ({tM} : Set S.Mbar) ∧
      (R.subgroupOf (centralizer ({tM} : Set S.Mbar))).Normal ∧
      (frattini (CFSG.Open.pCoreOf 2 R)).map (CFSG.Open.pCoreOf 2 R).subtype ≤ zpowers tM ∧
      CFSG.Open.pCoreOf 2 R = zpowers tM ∧
      ∃ q : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2), timmesfeldNondegenerate q ∧
        timmesfeldQuotientIso (CFSG.Open.pCore 2 R) (timmesfeldOmega q) := by
  obtain ⟨hVQ, hΩ, hw, -⟩ := timmesfeld_7_6 hCE H hNo C ht ht1 hR hN (by omega)
  have h6 : finrank (ZMod 2) (Vt S g t) = 6 := by omega
  have hpc := pCoreOf_eq_zpowers H C ht ht1 hVQ hΩ hN h6.ge
  have hto : orderOf (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) = 2 :=
    orderOf_eq_prime (Subtype.ext (by
      rw [pow_two]
      exact mul_self_of_mem_Lbar S H.conj_mem ht)) fun h => ht1 (congrArg Subtype.val h)
  have hfr : (frattini (CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar))).map
      (CFSG.Open.pCoreOf 2 ((Rbar S g t).subgroupOf S.Mbar)).subtype ≤
        zpowers (⟨t, S.Lbar_le_Mbar g ht⟩ : S.Mbar) :=
    hpc ▸ map_subtype_le _
  exact ⟨_, hto, _, Rbar_subgroupOf_le_centralizer H ht, Rbar_subgroupOf_normal ht, hfr, hpc,
    exists_quotientIso_fin H C hΩ hN h6⟩

theorem timmesfeldAlt4 (hCE : CentralExtInput.{u}) (hIrr : S5.Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hN : Nbar S g t = zpowers t) (hn : S.width = 6) :
    Bridge.TimmesfeldAlt4 S.width S.Mbar := by
  obtain ⟨h3, hq, -⟩ := S5.timmesfeld_5_5 hCE hIrr H hNo C (S45Q.hyp45Q H C) (by omega)
  obtain ⟨tM, hto, R, hRc, hRn, hFr, hpc, q, hq', hiso⟩ := alt4_data hCE H hNo C ht ht1 hR hN hn
  exact ⟨hn, hq, Nat.le_of_dvd (by norm_num) h3, tM, hto, R, hRc, hRn, hFr,
    Or.inr (Or.inr ⟨hpc, q, hq', hiso⟩)⟩

end CFSG.LargeExtraspecial.S7
