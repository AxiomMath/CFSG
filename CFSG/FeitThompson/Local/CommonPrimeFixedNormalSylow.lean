module

public import CFSG.FeitThompson.Definitions.NormalSylowHallCore
public import CFSG.FeitThompson.Local.PrimeActionChiefFactorsBelowFitting
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.CommonFixedOddActionFittingBound
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.SolvableKernelFixedFreePrimeNilpotent
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
public import CFSG.FeitThompson.Foundations.HallImageQuotient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

universe u

theorem not_dvd_natCard_of_isNilpotent_of_pCore_eq_bot {G : Type*} [Group G] [Finite G] {q : ℕ}
    (hq : q.Prime) [Group.IsNilpotent G] (h : pCore q G = ⊥) : ¬ q ∣ Nat.card G := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ : Nonempty (Sylow q G) := inferInstance
  have hle : (P : Subgroup G) = ⊥ :=
    le_bot_iff.1 (h ▸ le_pCore hq (sylow_normal_of_isNilpotent P) P.isPGroup')
  have hcard : Nat.card ((P : Subgroup G)) = q ^ (Nat.card G).factorization q :=
    P.card_eq_multiplicity
  rw [hle, Subgroup.card_bot] at hcard
  intro hdvd
  have h1 : 1 ≤ (Nat.card G).factorization q :=
    (Nat.Prime.dvd_iff_one_le_factorization hq Nat.card_pos.ne').1 hdvd
  have := hq.one_lt
  have : 1 < q ^ (Nat.card G).factorization q := Nat.one_lt_pow (by omega) (by omega)
  omega

theorem subgroupOf_pCoreIn {X : Type*} [Group X] [Finite X] (q : ℕ) (S : Subgroup X) :
    (pCoreIn q S).subgroupOf S = pCore q ↥S := by
  rw [pCoreIn_eq]
  exact Subgroup.comap_map_eq_self_of_injective S.subtype_injective _

theorem natCard_pCoreIn_eq_natCard_pCore {X : Type*} [Group X] [Finite X] (q : ℕ)
    (S : Subgroup X) : Nat.card ↥(pCoreIn q S) = Nat.card ↥(pCore q ↥S) := by
  rw [pCoreIn_eq]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ S.subtype_injective).toEquiv).symm

structure IsCommonPrimeFixedSetup (X : Type u) [Group X] (q : ℕ) (S K Z : Subgroup X) : Prop where
  prime : q.Prime
  odd_natCard : Odd (Nat.card X)
  isSolvable : Group.IsSolvable X
  normal_S : S.Normal
  isComplement : S.IsComplement' K
  coprime : (Nat.card ↥S).Coprime (Nat.card ↥K)
  K_ne_bot : K ≠ ⊥
  not_isNilpotent_S : ¬ Group.IsNilpotent ↥S
  commutator_eq : ⁅S, K⁆ = S
  Z_eq : Z = S ⊓ centralizer (K : Set X)
  natCard_Z : Nat.card ↥Z = q
  inf_centralizer_S : ∀ k ∈ K, k ≠ 1 → S ⊓ centralizer ({k} : Set X) = Z

namespace IsCommonPrimeFixedSetup

variable {X : Type u} [Group X] {q : ℕ} {S K Z : Subgroup X}
  (h : IsCommonPrimeFixedSetup X q S K Z)

include h

theorem finite : Finite X :=
  Nat.finite_of_card_ne_zero fun h0 => by simpa [h0, Nat.odd_iff] using h.odd_natCard

theorem Z_le_S : Z ≤ S := by rw [h.Z_eq]; exact inf_le_left

theorem Z_ne_bot : Z ≠ ⊥ := by
  intro hb
  have hc := h.natCard_Z
  rw [hb, Subgroup.card_bot] at hc
  exact h.prime.one_lt.ne hc

theorem isPGroup_Z : IsPGroup q ↥Z := IsPGroup.of_card (n := 1) (by rw [pow_one, h.natCard_Z])

theorem forall_inf_centralizer_eq :
    ∀ x ∈ K, x ≠ 1 → S ⊓ centralizer ({x} : Set X) = S ⊓ centralizer (K : Set X) :=
  fun x hx hx1 => by rw [h.inf_centralizer_S x hx hx1, h.Z_eq]

theorem dvd_natCard_S [Finite X] : q ∣ Nat.card ↥S :=
  h.natCard_Z ▸ Subgroup.card_dvd_of_le h.Z_le_S

variable [Finite X]

theorem eq_bot_or_eq_Z_of_le {A : Subgroup X} (hA : A ≤ Z) : A = ⊥ ∨ A = Z := by
  have hdvd : Nat.card ↥A ∣ q := h.natCard_Z ▸ Subgroup.card_dvd_of_le hA
  rcases h.prime.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact Or.inl (Subgroup.card_eq_one.1 h1)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hA (by rw [h.natCard_Z, h1]))

theorem Z_le_fittingOfNormal : Z ≤ fittingOfNormal S := by
  have : Group.IsSolvable X := h.isSolvable
  have hSn := h.normal_S
  have hFS : fittingOfNormal S ≤ S := fittingOfNormal_le S
  have hCF : fittingOfNormal S ⊓ centralizer (K : Set X) = fittingOfNormal S ⊓ Z := by
    rw [h.Z_eq, ← inf_assoc, inf_eq_left.2 hFS]
  rcases h.eq_bot_or_eq_Z_of_le (A := fittingOfNormal S ⊓ Z) inf_le_right with hb | hb
  · refine absurd ?_ h.not_isNilpotent_S
    have hcomm : S ≤ fittingOfNormal S := by
      have := commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq_of_coprime h.odd_natCard
        h.isComplement h.coprime h.forall_inf_centralizer_eq (by rw [hCF, hb])
      rwa [h.commutator_eq] at this
    rw [le_antisymm hcomm hFS]
    exact isNilpotent_fittingOfNormal hSn
  · exact (le_of_eq hb.symm).trans inf_le_left

theorem Z_le_pCoreIn : Z ≤ pCoreIn q S := by
  rw [pCoreIn_eq]
  exact le_map_pCore_of_isPGroup_of_le_map_fittingRaw h.prime h.isPGroup_Z
    (by rw [map_fittingRaw_subtype_eq_fittingOfNormal]; exact h.Z_le_fittingOfNormal)

theorem normal_pCoreIn : (pCoreIn q S).Normal := by
  have := h.normal_S
  rw [pCoreIn_eq]
  exact normal_map_subtype_of_characteristic S (pCore q ↥S)

theorem bot_lt_pCoreIn : ⊥ < pCoreIn q S :=
  bot_lt_iff_ne_bot.2 fun hb => h.Z_ne_bot (le_bot_iff.1 (hb ▸ h.Z_le_pCoreIn))

theorem isPGroup_pCoreIn : IsPGroup q ↥(pCoreIn q S) := by
  rw [pCoreIn_eq]
  exact (isPGroup_pCore h.prime ↥S).map S.subtype

theorem isNilpotent_quotient_pCore : Group.IsNilpotent (↥S ⧸ pCore q ↥S) := by
  have : Group.IsSolvable X := h.isSolvable
  have hSn := h.normal_S
  have hQn := h.normal_pCoreIn
  set Q : Subgroup X := pCoreIn q S with hQ
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := Nat.card ↥K)
    (fun hone => h.K_ne_bot (Subgroup.card_eq_one.1 hone))
  obtain ⟨t, ht, htr⟩ := exists_mem_orderOf_eq_of_dvd hr hrd
  have ht1 : t ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at htr
    exact hr.one_lt.ne htr
  have hSK : S ⊓ K = ⊥ := disjoint_iff.1 h.isComplement.disjoint
  set T : Subgroup X := zpowers t with hTdef
  have htK : T ≤ K := zpowers_le_of_mem ht
  have hTcard : Nat.card ↥T = r := by rw [hTdef, Nat.card_zpowers, htr]
  have hcopT : (Nat.card ↥T).Coprime (Nat.card ↥S) :=
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le htK) h.coprime).symm
  set H : Subgroup (X ⧸ Q) := S.map (mk' Q) with hH
  set R : Subgroup (X ⧸ Q) := T.map (mk' Q) with hR
  have hCH : H ⊓ centralizer (R : Set (X ⧸ Q)) = ⊥ := by
    rw [hH, hR, inf_centralizer_map_mk'_eq_map hcopT le_normalizer_of_normal,
      centralizer_coe_zpowers, h.inf_centralizer_S t ht ht1, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact h.Z_le_pCoreIn
  have hTQ : Q ⊓ T = ⊥ :=
    le_bot_iff.1 (le_trans (inf_le_inf (pCoreIn_le q S) htK) (le_of_eq hSK))
  have hRcard : Nat.card ↥R = r := by rw [hR, natCard_map_mk'_of_inf_eq_bot hTQ, hTcard]
  have hHR : H ⊓ R = ⊥ := by
    have hcopHR : (Nat.card ↥H).Coprime (Nat.card ↥R) :=
      Nat.Coprime.coprime_dvd_left (natCard_map_mk'_dvd S Q)
        (Nat.Coprime.coprime_dvd_right (hRcard ▸ hTcard ▸ Subgroup.card_dvd_of_le htK) h.coprime)
    exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcopHR
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hnil : Group.IsNilpotent ↥(H.subgroupOf (H ⊔ R)) :=
    isNilpotent_of_isSolvable_of_natCard_eq_prime coe_subgroupOf_mul_coe_subgroupOf_eq_univ
      (subgroupOf_inf_subgroupOf_eq_bot hHR le_rfl) hr
      (by rw [Nat.card_eq_of_bijective _
            (Subgroup.subgroupOfEquivOfLe (le_sup_right (a := H))).bijective]
          exact hRcard)
      (subgroupOf_inf_centralizer_eq_bot hCH le_rfl)
  have hHnil : Group.IsNilpotent ↥H := Group.nilpotent_of_mulEquiv (_h := hnil)
    (Subgroup.subgroupOfEquivOfLe (le_sup_left (b := R)))
  exact Group.nilpotent_of_mulEquiv (_h := hHnil)
    ((quotientSubgroupOfEquivMapMk' S Q).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreIn q S)))

theorem not_dvd_natCard_quotient_pCore : ¬ q ∣ Nat.card (↥S ⧸ pCore q ↥S) := by
  have := h.isNilpotent_quotient_pCore
  exact not_dvd_natCard_of_isNilpotent_of_pCore_eq_bot h.prime
    (CFSG.FeitThompson.pCore_quotient_pCore q ↥S)

theorem natCard_pCoreIn_eq_pow_factorization_S :
    Nat.card ↥(pCoreIn q S) = q ^ (Nat.card ↥S).factorization q := by
  have : Fact q.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := (isPGroup_pCore h.prime ↥S).exists_card_eq
  have hcard : Nat.card ↥S = Nat.card (↥S ⧸ pCore q ↥S) * Nat.card ↥(pCore q ↥S) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hfac : (Nat.card ↥S).factorization q = n := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd h.not_dvd_natCard_quotient_pCore, hn,
      h.prime.factorization_pow]
  rw [natCard_pCoreIn_eq_natCard_pCore q S, hn, hfac]

theorem factorization_natCard_eq :
    (Nat.card X).factorization q = (Nat.card ↥S).factorization q := by
  have hX : Nat.card ↥S * Nat.card ↥K = Nat.card X := h.isComplement.card_mul_card
  have hnd : ¬ q ∣ Nat.card ↥K := fun hd =>
    h.prime.one_lt.ne' (Nat.eq_one_of_dvd_one (h.coprime ▸ Nat.dvd_gcd h.dvd_natCard_S hd))
  rw [← hX, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

theorem natCard_pCoreIn : Nat.card ↥(pCoreIn q S) = q ^ (Nat.card X).factorization q := by
  rw [h.natCard_pCoreIn_eq_pow_factorization_S, h.factorization_natCard_eq]

noncomputable def sylow : haveI : Fact q.Prime := ⟨h.prime⟩; Sylow q X :=
  haveI : Fact q.Prime := ⟨h.prime⟩
  Sylow.ofCard (pCoreIn q S) h.natCard_pCoreIn

theorem coe_sylow : haveI : Fact q.Prime := ⟨h.prime⟩; (h.sylow : Subgroup X) = pCoreIn q S :=
  haveI : Fact q.Prime := ⟨h.prime⟩
  Sylow.coe_ofCard _ _

theorem pCoreIn_le_hallCore : pCoreIn q S ≤ hallCore X := by
  have : Fact q.Prime := ⟨h.prime⟩
  have hn := h.normal_pCoreIn
  have : ((h.sylow : Sylow q X) : Subgroup X).Normal := h.coe_sylow ▸ hn
  exact h.coe_sylow ▸ sylow_le_hallCore h.sylow

section HallCompl

variable {D : Subgroup X} (hDS : D ≤ S) (hDq : ¬ q ∣ Nat.card ↥D)
  (hDidx : ∃ a : ℕ, D.relIndex S = q ^ a)

include hDS hDq hDidx

theorem natCard_mul_natCard_pCoreIn :
    Nat.card ↥D * Nat.card ↥(pCoreIn q S) = Nat.card ↥S := by
  have : Fact q.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := hDidx
  have hmul : Nat.card ↥D * D.relIndex S = Nat.card ↥S := by
    have hc := Subgroup.card_mul_index (D.subgroupOf S)
    rwa [Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hDS).bijective] at hc
  have hfac : (Nat.card ↥S).factorization q = a := by
    rw [← hmul, ha, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero a h.prime.pos.ne')]
    simp [Nat.factorization_eq_zero_of_not_dvd hDq, h.prime.factorization_pow]
  rw [h.natCard_pCoreIn_eq_pow_factorization_S, hfac, ← ha, hmul]

theorem inf_pCoreIn_eq_bot : pCoreIn q S ⊓ D = ⊥ := by
  have hcop : (Nat.card ↥(pCoreIn q S)).Coprime (Nat.card ↥D) := by
    rw [h.natCard_pCoreIn_eq_pow_factorization_S]
    exact Nat.Coprime.pow_left _ (h.prime.coprime_iff_not_dvd.2 hDq)
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop
    (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))

theorem isComplement'_subgroupOf_of_hallQCompl :
    ((pCoreIn q S).subgroupOf S).IsComplement' (D.subgroupOf S) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
  · rw [Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe (pCoreIn_le q S)).bijective,
      Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hDS).bijective,
      mul_comm, h.natCard_mul_natCard_pCoreIn hDS hDq hDidx]
  · rw [disjoint_iff]
    have he : (pCoreIn q S).subgroupOf S ⊓ D.subgroupOf S = (pCoreIn q S ⊓ D).subgroupOf S :=
      (Subgroup.comap_inf _ _ _).symm
    rw [he, h.inf_pCoreIn_eq_bot hDS hDq hDidx, Subgroup.bot_subgroupOf]

theorem sup_pCoreIn_eq : pCoreIn q S ⊔ D = S := by
  have hc := h.isComplement'_subgroupOf_of_hallQCompl hDS hDq hDidx
  have h2 := congrArg (Subgroup.map S.subtype) hc.sup_eq_top
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (pCoreIn_le q S),
    Subgroup.map_subgroupOf_eq_of_le hDS, ← MonoidHom.range_eq_map, S.range_subtype] at h2

theorem isNilpotent_of_hallQCompl : Group.IsNilpotent ↥D := by
  have hnil := h.isNilpotent_quotient_pCore
  have hQn : ((pCoreIn q S).subgroupOf S).Normal := (subgroupOf_pCoreIn q S) ▸ pCore_normal q ↥S
  have hc := h.isComplement'_subgroupOf_of_hallQCompl hDS hDq hDidx
  have hD' : Group.IsNilpotent ↥(D.subgroupOf S) := by
    have e2 : ↥S ⧸ (pCoreIn q S).subgroupOf S ≃* ↥(D.subgroupOf S) := hc.symm.QuotientMulEquiv
    exact Group.nilpotent_of_mulEquiv (_h := hnil)
      ((QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreIn q S).symm).trans e2)
  exact Group.nilpotent_of_mulEquiv (_h := hD') (Subgroup.subgroupOfEquivOfLe hDS)

end HallCompl

end IsCommonPrimeFixedSetup

theorem le_pCoreIn_and_normal_sylow_and_le_hallCore {X : Type u} [Group X] {q : ℕ}
    {S K Z : Subgroup X} (h : IsCommonPrimeFixedSetup X q S K Z) :
    haveI := h.finite
    Z ≤ pCoreIn q S ∧ (pCoreIn q S).Normal ∧
      Nat.card ↥(pCoreIn q S) = q ^ (Nat.card X).factorization q ∧
      ⊥ < pCoreIn q S ∧ pCoreIn q S ≤ hallCore X :=
  haveI := h.finite
  ⟨h.Z_le_pCoreIn, h.normal_pCoreIn, h.natCard_pCoreIn, h.bot_lt_pCoreIn, h.pCoreIn_le_hallCore⟩

theorem isNilpotent_quotient_pCore_and_not_dvd {X : Type u} [Group X] {q : ℕ}
    {S K Z : Subgroup X} (h : IsCommonPrimeFixedSetup X q S K Z) :
    haveI := h.finite
    Group.IsNilpotent (↥S ⧸ pCore q ↥S) ∧ ¬ q ∣ Nat.card (↥S ⧸ pCore q ↥S) :=
  haveI := h.finite
  ⟨h.isNilpotent_quotient_pCore, h.not_dvd_natCard_quotient_pCore⟩

theorem isNilpotent_and_isComplement'_of_hallQCompl {X : Type u} [Group X] {q : ℕ}
    {S K Z D : Subgroup X} (h : IsCommonPrimeFixedSetup X q S K Z) (hDS : D ≤ S)
    (hDq : ¬ q ∣ Nat.card ↥D) (hDidx : ∃ a : ℕ, D.relIndex S = q ^ a) :
    haveI := h.finite
    Group.IsNilpotent ↥D ∧ pCoreIn q S ⊔ D = S ∧ pCoreIn q S ⊓ D = ⊥ ∧
      ((pCoreIn q S).subgroupOf S).IsComplement' (D.subgroupOf S) :=
  haveI := h.finite
  ⟨h.isNilpotent_of_hallQCompl hDS hDq hDidx, h.sup_pCoreIn_eq hDS hDq hDidx,
    h.inf_pCoreIn_eq_bot hDS hDq hDidx, h.isComplement'_subgroupOf_of_hallQCompl hDS hDq hDidx⟩

end CFSG.FeitThompson
