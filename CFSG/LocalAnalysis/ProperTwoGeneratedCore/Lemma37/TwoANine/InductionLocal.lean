module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Isolated
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.IsolatedSubgroup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup CFSG.ProperTwoGeneratedCore.Assembly

@[expose] def IsolatedFor (X : Type) [Group X] : Prop :=
  ∀ (S : Sylow 2 X) (t : X), IsCentralInvolution (S : Subgroup X) t →
    IsTwoANine (EscapingQuotient t) → ∀ g : X, g⁻¹ * t * g ∈ (S : Subgroup X) → g⁻¹ * t * g = t

structure MinimalCounterexample (X : Type) [Group X] [Finite X] (S : Sylow 2 X) (t : X) :
    Prop where
  central : IsCentralInvolution (S : Subgroup X) t
  twoANine : IsTwoANine (EscapingQuotient t)
  exists_conj : ∃ g : X, g⁻¹ * t * g ∈ (S : Subgroup X) ∧ g⁻¹ * t * g ≠ t
  oddCore_eq_bot : CFSG.pPrimeCore 2 X = ⊥
  isolatedFor : ∀ H : Subgroup X, H ≠ ⊤ → IsolatedFor H

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

namespace MinimalCounterexample

variable {X : Type} [Group X] [Finite X] {S : Sylow 2 X} {t : X}
  (hX : MinimalCounterexample X S t)
include hX

theorem isConj {a : X} (ha : orderOf a = 2) : IsConj t a := by
  obtain ⟨g, hgS, hgt⟩ := hX.exists_conj
  exact isConj_of_orderOf_eq_two_of_conj_ne S hX.central hX.twoANine hgS hgt ha

theorem isTwoANine {a : X} (ha : orderOf a = 2) : IsTwoANine (EscapingQuotient a) :=
  hX.twoANine.of_isConj_escapingQuotient (hX.isConj ha)

section Local

variable {H : Subgroup X} (hSH : (S : Subgroup X) ≤ H)
include hSH

theorem isCentralInvolution_subtype :
    IsCentralInvolution ((S.subtype hSH : Sylow 2 H) : Subgroup H) ⟨t, hSH hX.central.1⟩ := by
  rw [Sylow.coe_subtype]
  exact ⟨Subgroup.mem_subgroupOf.mpr hX.central.1, by rw [Subgroup.orderOf_mk, hX.central.2.1],
    fun s hs => Subtype.ext (hX.central.2.2 s (Subgroup.mem_subgroupOf.mp hs))⟩

variable (hcov : ∀ m ∈ centralizer ({t} : Set X), ∃ n ∈ H, n ∈ centralizer ({t} : Set X) ∧
  n⁻¹ * m ∈ oddCentralizer t)
include hcov

theorem isTwoANine_escapingQuotient_subtype :
    IsTwoANine (EscapingQuotient (⟨t, hSH hX.central.1⟩ : H)) :=
  hX.twoANine.escapingQuotient_of_subgroup ⟨t, hSH hX.central.1⟩ hcov

variable (hH : H ≠ ⊤)
include hH

theorem isolated_subtype : ∀ g : H, g⁻¹ * ⟨t, hSH hX.central.1⟩ * g ∈
    ((S.subtype hSH : Sylow 2 H) : Subgroup H) → g⁻¹ * ⟨t, hSH hX.central.1⟩ * g =
      ⟨t, hSH hX.central.1⟩ :=
  hX.isolatedFor H hH (S.subtype hSH) _ (hX.isCentralInvolution_subtype hSH)
    (hX.isTwoANine_escapingQuotient_subtype hSH hcov)

theorem zStar :
    (∀ g : H, ∃ c ∈ centralizer ({(⟨t, hSH hX.central.1⟩ : H)} : Set H),
      c⁻¹ * g ∈ CFSG.pPrimeCore 2 H) ∧
    ∀ g : H, g * ⟨t, hSH hX.central.1⟩ * g⁻¹ * (⟨t, hSH hX.central.1⟩ : H)⁻¹ ∈
      CFSG.pPrimeCore 2 H := by
  set t' : H := ⟨t, hSH hX.central.1⟩ with ht'_def
  have ht' := hX.isCentralInvolution_subtype hSH
  obtain ⟨h1, h2⟩ := CFSG.Adapters.glauberman_zStar (S.subtype hSH) ⟨t', ht'.1⟩
    (Subgroup.mem_center_iff.mpr fun s => Subtype.ext (ht'.2.2 s s.2))
    (by rw [Subgroup.orderOf_mk, ht'.2.1]) (hX.isolated_subtype hSH hcov hH)
  rw [oddCore_eq_pPrimeCore_two] at h1
  refine ⟨fun g => ?_, fun g => ?_⟩
  · obtain ⟨c, hc, k, hk, rfl⟩ := h1 g
    exact ⟨c, hc, by rwa [inv_mul_cancel_left]⟩
  · have h3 := Subgroup.mem_center_iff.mp h2 (g : H ⧸ CFSG.oddCore H)
    have h4 : ((g * t' * g⁻¹ * t'⁻¹ : H) : H ⧸ CFSG.oddCore H) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, h3]
      group
    rw [← oddCore_eq_pPrimeCore_two]
    exact (QuotientGroup.eq_one_iff _).mp h4

theorem commutator_mem_oddCoreOf {h : X} (hh : h ∈ H) : h * t * h⁻¹ * t⁻¹ ∈ oddCoreOf H :=
  ⟨_, (hX.zStar hSH hcov hH).2 ⟨h, hh⟩, rfl⟩

theorem isTwoANine_quotient : IsTwoANine (H ⧸ CFSG.pPrimeCore 2 H) := by
  set t' : H := ⟨t, hSH hX.central.1⟩
  have hsurj : Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore 2 H)).comp
      (centralizer ({t'} : Set H)).subtype) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨c, hc, hcg⟩ := (hX.zStar hSH hcov hH).1 g
    exact ⟨⟨c, hc⟩, QuotientGroup.eq.mpr hcg⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_quotient_pPrimeCore (centralizer ({t'} : Set H)).subtype
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr (centralizer ({t'} : Set H)).subtype_injective,
      Subgroup.card_bot]; exact odd_one) hsurj
  exact (hX.isTwoANine_escapingQuotient_subtype hSH hcov).of_mulEquiv e

omit hSH hH in
theorem oddCoreOf_inf_centralizer_le :
    oddCoreOf H ⊓ centralizer ({t} : Set X) ≤ oddCentralizer t := by
  set D := oddCoreOf H ⊓ centralizer ({t} : Set X)
  have hD : Odd (Nat.card D) :=
    (odd_card_oddCoreOf H).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hnorm : normalizer (escapingImage D t : Set (EscapingQuotient t)) = ⊤ := by
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨n, hnH, hnt, hnm⟩ := hcov m m.2
    have hmn : escapingMk t m = escapingMk t ⟨n, hnt⟩ := by
      have h := (coe_mem_oddCentralizer_iff (c := (⟨n, hnt⟩ : centralizer ({t} : Set X))⁻¹ * m)).mp
        hnm
      rw [map_mul, map_inv, inv_mul_eq_one] at h
      exact h.symm
    rw [show QuotientGroup.mk' _ m = escapingMk t m from rfl, hmn]
    refine Subgroup.le_normalizer_map (escapingMk t)
      (Subgroup.mem_map_of_mem _ (mem_normalizer_subgroupOf_of_mem ?_))
    exact inf_mem_normalizer (le_normalizer_oddCoreOf H hnH) (Subgroup.le_normalizer hnt)
  have himage : escapingImage D t = ⊥ :=
    hX.twoANine.eq_bot_of_odd_of_sylow_le_normalizer default
      (hD.of_dvd_nat ((Subgroup.card_map_dvd _ _).trans
        (Subgroup.card_comap_dvd_of_injective _ _ (centralizer ({t} : Set X)).subtype_injective)))
      (by rw [hnorm]; exact le_top)
  intro x hx
  exact inf_centralizer_le_oddCentralizer_of_map_eq_bot himage ⟨hx, hx.2⟩

end Local

end MinimalCounterexample

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
