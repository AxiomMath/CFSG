module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Equiv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem oddCore_eq_bot_of_isTwoU43 {Q : Type} [Group Q] [Finite Q] (hq : CFSG.IsQuasisimple Q)
    (h : IsTwoU43 Q) : oddCore Q = ⊥ := by
  have h' : CFSG.Open.IsQuasisimple Q := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hO : CFSG.oddCore Q ≤ Subgroup.center Q :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple h'
  have hd : Nat.card (oddCore Q) ∣ 2 := h.1 ▸ Subgroup.card_dvd_of_le hO
  have h1 : Nat.card (oddCore Q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr odd_card_oddCore) hd (dvd_refl _)
  exact Subgroup.card_eq_one.mp h1

theorem isComponentIn_map_of_injective {A G : Type} [Group A] [Group G] {K H : Subgroup A}
    (φ : A →* G) (hφ : Function.Injective φ) (h : IsComponentIn K H) :
    IsComponentIn (K.map φ) (H.map φ) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let e : ↥H ≃* ↥(H.map φ) := H.equivMapOfInjective φ hφ
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv e h.2
  have heq : (K.subgroupOf H).map e.toMonoidHom = (K.map φ).subgroupOf (H.map φ) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (H.map φ))
    rw [Subgroup.map_map]
    have hcomp : ((H.map φ).subtype).comp e.toMonoidHom = φ.comp H.subtype := by
      ext m
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_mono h.1)]
  rw [heq] at hc
  exact hc

theorem map_subtype_centralizer {G : Type} [Group G] (Y : Subgroup G) {w : G} (hwY : w ∈ Y) :
    (centralizer ({(⟨w, hwY⟩ : ↥Y)} : Set ↥Y)).map Y.subtype =
      Y ⊓ centralizer ({w} : Set G) := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz))⟩
  · rintro ⟨hgY, hgC⟩
    exact ⟨⟨g, hgY⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)), rfl⟩

@[expose] def InnerData (P : Type) [Group P] (z : P) : Prop :=
  ∃ X : Subgroup P, IsComponentIn X (centralizer ({z} : Set P)) ∧ z ∈ X ∧ IsTwoU43 ↥X ∧
    ∃ u : ↥X, IsI4PlusIn (⊤ : Subgroup ↥X) u ∧ ∃ a : P, a⁻¹ * z * a = (u : P) * z

theorem exists_inner_of_innerData {G : Type} [Group G] [Finite G] (Y : Subgroup G)
    {P : Type} [Group P] [Finite P] (ρ : ↥Y →* P) (hρ : OddCentralCover ρ)
    {w : G} (hwY : w ∈ Y) (hw : orderOf w = 2) (hdata : InnerData P (ρ ⟨w, hwY⟩)) :
    ∃ (X : Subgroup G) (u : G), IsComponentIn X (Y ⊓ centralizer ({w} : Set G)) ∧ w ∈ X ∧
      IsTwoU43 (↥X ⧸ oddCore ↥X) ∧ IsI4PlusIn X u ∧ ∃ a ∈ Y, a⁻¹ * w * a = u * w := by
  have hw' : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := by
    apply Subtype.ext
    change w * w = 1
    rw [← pow_two]
    exact hw ▸ pow_orderOf_eq_one w
  obtain ⟨Xb, hXc, hzX, hX2, ub, hub, a₀, ha₀⟩ := hdata
  have hXq : CFSG.IsQuasisimple ↥Xb := hXc.isQuasisimple
  have hub2 : ub * ub = 1 := by
    rw [← pow_two]
    exact hub.1 ▸ pow_orderOf_eq_one ub
  have hubP : (ub : P) * (ub : P) = 1 := by
    rw [← Subgroup.coe_mul, hub2]
    rfl
  have hDcomp := hρ.isComponentIn_coverDerived hw' hXc
  have hDle : coverDerived ρ Xb ≤ centralizer ({(⟨w, hwY⟩ : ↥Y)} : Set ↥Y) := hDcomp.1
  obtain ⟨u₀, hu₀D, hu₀u₀, hρu₀⟩ := hρ.exists_mul_self_eq_one_mem_coverDerived hXq hubP ub.2
  have hcov := hρ.oddCentralCover_coverDerivedHom hXq
  have hker : oddCore ↥(coverDerived ρ Xb) = (coverDerivedHom ρ Xb).ker :=
    hcov.oddCore_eq_ker (oddCore_eq_bot_of_isTwoU43 hXq hX2)
  let e : ↥(coverDerived ρ Xb) ⧸ oddCore ↥(coverDerived ρ Xb) ≃* ↥Xb :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hcov.surjective)
  have he : ∀ d : ↥(coverDerived ρ Xb), e (QuotientGroup.mk d) = coverDerivedHom ρ Xb d :=
    fun d => rfl
  let ι : ↥(coverDerived ρ Xb) ≃* ↥((coverDerived ρ Xb).map Y.subtype) :=
    (coverDerived ρ Xb).equivMapOfInjective Y.subtype Y.subtype_injective
  have hXcomp : IsComponentIn ((coverDerived ρ Xb).map Y.subtype)
      (Y ⊓ centralizer ({w} : Set G)) := by
    have := isComponentIn_map_of_injective Y.subtype Y.subtype_injective hDcomp
    rwa [map_subtype_centralizer Y hwY] at this
  have hwD : (⟨w, hwY⟩ : ↥Y) ∈ coverDerived ρ Xb := hρ.mem_coverDerived hXq hw' hzX
  have hwX : w ∈ (coverDerived ρ Xb).map Y.subtype := ⟨_, hwD, rfl⟩
  have hu₀X : ((u₀ : ↥Y) : G) ∈ (coverDerived ρ Xb).map Y.subtype := ⟨u₀, hu₀D, rfl⟩
  obtain ⟨ε⟩ := nonempty_quotient_oddCore_mulEquiv ι
  have hTwo : IsTwoU43 (↥((coverDerived ρ Xb).map Y.subtype) ⧸
      oddCore ↥((coverDerived ρ Xb).map Y.subtype)) :=
    isTwoU43_of_mulEquiv ε (isTwoU43_of_mulEquiv e.symm hX2)
  have hu₀ne : u₀ ≠ 1 := by
    rintro rfl
    have h1 : ub = 1 := Subtype.ext (by rw [← hρu₀]; exact map_one ρ)
    have := hub.1
    rw [h1, orderOf_one] at this
    omega
  have hord : orderOf (⟨u₀, hu₀D⟩ : ↥(coverDerived ρ Xb)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      change u₀ ^ 2 = 1
      rw [pow_two]
      exact hu₀u₀
    · intro h1
      exact hu₀ne (congrArg Subtype.val h1)
  have hmk : e (QuotientGroup.mk (⟨u₀, hu₀D⟩ : ↥(coverDerived ρ Xb))) = ub :=
    Subtype.ext hρu₀
  have hpQ : IsI4PlusIn (⊤ : Subgroup (↥(coverDerived ρ Xb) ⧸ oddCore ↥(coverDerived ρ Xb)))
      (QuotientGroup.mk (⟨u₀, hu₀D⟩ : ↥(coverDerived ρ Xb))) := by
    have := isI4PlusIn_top_map_mulEquiv e.symm hub
    rwa [← hmk, MulEquiv.symm_apply_apply] at this
  have hpD := isI4PlusIn_top_of_quotient hord hpQ
  have hpX := isI4PlusIn_top_map_mulEquiv ι hpD
  have hιu : ι ⟨u₀, hu₀D⟩ =
      (⟨((u₀ : ↥Y) : G), hu₀X⟩ : ↥((coverDerived ρ Xb).map Y.subtype)) := Subtype.ext rfl
  rw [hιu] at hpX
  have hpocket := isI4PlusIn_of_top hu₀X hpX
  obtain ⟨b, hb⟩ := hρ.surjective a₀
  have hcomm : u₀ * ⟨w, hwY⟩ = ⟨w, hwY⟩ * u₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (hDle hu₀D)
  have h1 : (b⁻¹ * ⟨w, hwY⟩ * b) * (b⁻¹ * ⟨w, hwY⟩ * b) = 1 := by
    calc (b⁻¹ * ⟨w, hwY⟩ * b) * (b⁻¹ * ⟨w, hwY⟩ * b)
        = b⁻¹ * (⟨w, hwY⟩ * ⟨w, hwY⟩) * b := by group
      _ = 1 := by rw [hw']; group
  have h2 : (u₀ * ⟨w, hwY⟩) * (u₀ * ⟨w, hwY⟩) = 1 := by
    calc (u₀ * ⟨w, hwY⟩) * (u₀ * ⟨w, hwY⟩) = u₀ * (⟨w, hwY⟩ * u₀) * ⟨w, hwY⟩ := by group
      _ = u₀ * (u₀ * ⟨w, hwY⟩) * ⟨w, hwY⟩ := by rw [hcomm]
      _ = (u₀ * u₀) * (⟨w, hwY⟩ * ⟨w, hwY⟩) := by group
      _ = 1 := by rw [hu₀u₀, hw']; group
  have himg : ρ (b⁻¹ * ⟨w, hwY⟩ * b) = ρ (u₀ * ⟨w, hwY⟩) := by
    rw [map_mul, map_mul, map_mul, map_inv, hb, hρu₀]
    exact ha₀
  have hconj := hρ.eq_of_mul_self_eq_one h1 h2 himg
  refine ⟨(coverDerived ρ Xb).map Y.subtype, ((u₀ : ↥Y) : G), hXcomp, hwX, hTwo, hpocket,
    (b : G), b.2, ?_⟩
  have := congrArg Subtype.val hconj
  simpa using this

end CFSG.OddStandard.SmallF3.Omega
