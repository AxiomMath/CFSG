module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.MixedFittingInvariantPrimeExclusion
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
import CFSG.FeitThompson.Local.NilpotentHallCharacteristic
import CFSG.FeitThompson.Local.NormalPSubgroupPComplCoreTransfer
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

@[expose]
def pComplCoreIn (q : ℕ) (X : Subgroup G) : Subgroup G := (pComplCore q ↥X).map X.subtype

theorem pComplCoreIn_eq (q : ℕ) (X : Subgroup G) :
    pComplCoreIn q X = (pComplCore q ↥X).map X.subtype := (rfl)

theorem pComplCoreIn_le (q : ℕ) (X : Subgroup G) : pComplCoreIn q X ≤ X :=
  Subgroup.map_subtype_le _

theorem not_dvd_natCard_pComplCoreIn {q : ℕ} (hq : q.Prime) (X : Subgroup G) :
    ¬ q ∣ Nat.card ↥(pComplCoreIn q X) := by
  have hcard : Nat.card ↥(pComplCoreIn q X) = Nat.card ↥(pComplCore q ↥X) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ X.subtype X.subtype_injective).toEquiv).symm
  rw [hcard]
  exact not_dvd_natCard_pComplCore hq ↥X

theorem le_normalizer_pComplCoreIn (q : ℕ) (X : Subgroup G) :
    X ≤ normalizer ((pComplCoreIn q X : Subgroup G) : Set G) :=
  le_normalizer_map_pComplCore q X

omit [Finite G] in
theorem isNilpotent_of_le_of_isNilpotent {A B : Subgroup G} (hAB : A ≤ B)
    (hB : Group.IsNilpotent ↥B) : Group.IsNilpotent ↥A :=
  have := hB
  Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAB)

theorem pCoreIn_ne_bot_of_dvd_natCard {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (hnil : Group.IsNilpotent ↥X) (hdvd : q ∣ Nat.card ↥X) : pCoreIn q X ≠ ⊥ := by
  have := hnil
  have : Fact q.Prime := ⟨hq⟩
  obtain P := (default : Sylow q ↥X)
  have hPne : (P : Subgroup ↥X) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  have hle : (P : Subgroup ↥X) ≤ pCore q ↥X := le_pCore hq (sylow_normal_of_isNilpotent P) P.2
  intro hb
  rw [pCoreIn_eq, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective] at hb
  exact hPne (le_bot_iff.1 (hb ▸ hle))

theorem pCoreIn_eq_bot_of_notMem_primeFactors {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (hqX : q ∉ (Nat.card ↥X).primeFactors) : pCoreIn q X = ⊥ := by
  rw [pCoreIn_eq, pCore_eq_bot_of_notMem_primeFactors hq hqX, Subgroup.map_bot]

theorem inf_eq_bot_of_isPGroup_of_not_dvd {q : ℕ} (hq : q.Prime) {A B : Subgroup G}
    (hA : IsPGroup q ↥A) (hB : ¬ q ∣ Nat.card ↥B) : A ⊓ B = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (IsPGroup.to_le hA (inf_le_left : A ⊓ B ≤ A))
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero, Subgroup.card_eq_one] at hn; exact hn
  · exact absurd (dvd_trans (hn ▸ dvd_pow_self q hpos.ne')
      (Subgroup.card_dvd_of_le (inf_le_right : A ⊓ B ≤ B))) hB

omit [Finite G] in
theorem le_centralizer_of_le_normalizer_of_inf_eq_bot {H A B : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H) (hA : H ≤ normalizer (A : Set G))
    (hB : H ≤ normalizer (B : Set G)) (hAB : A ⊓ B = ⊥) : A ≤ centralizer (B : Set G) := by
  intro a ha
  refine mem_centralizer_iff.2 fun b hb => ?_
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B := by
    have hn := hB (hAH ha)
    rw [mem_normalizer_iff] at hn
    exact B.mul_mem ((hn b).1 hb) (B.inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have hn := hA (hBH hb)
    rw [mem_normalizer_iff] at hn
    have he : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [he]
    exact A.mul_mem ha ((hn a⁻¹).1 (A.inv_mem ha))
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [hAB, mem_bot] at h3
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)).symm

theorem le_centralizer_pComplCoreIn {q : ℕ} (hq : q.Prime) {H A : Subgroup G} (hAH : A ≤ H)
    (hnorm : H ≤ normalizer (A : Set G)) (hA : IsPGroup q ↥A) :
    A ≤ centralizer ((pComplCoreIn q H : Subgroup G) : Set G) :=
  le_centralizer_of_le_normalizer_of_inf_eq_bot hAH (pComplCoreIn_le q H) hnorm
    (le_normalizer_pComplCoreIn q H)
    (inf_eq_bot_of_isPGroup_of_not_dvd hq hA (not_dvd_natCard_pComplCoreIn hq H))

theorem pComplCore_le_of_forall_pCore_le {X : Type*} [Group X] [Finite X]
    (hnil : Group.IsNilpotent X) {q : ℕ} {K : Subgroup X}
    (h : ∀ r : ℕ, r.Prime → r ≠ q → pCore r X ≤ K) : pComplCore q X ≤ K := by
  have := hnil
  have hpi : IsPiSubgroup (({q} : Set ℕ)ᶜ) (pComplCore q X) := by
    rw [pComplCore_eq_piCore]
    exact (isPiSubgroup_piCore _ X).mono fun r hr => by simpa using hr.2
  refine (IsHallSubgroup.le_of_isPiSubgroup hpi (isHallSubgroup_sylowPiPart _ X)).trans ?_
  refine sylowPiPart_le fun r hr hrq P => ?_
  have : Fact r.Prime := ⟨hr⟩
  exact (le_pCore hr (sylow_normal_of_isNilpotent P) P.2).trans (h r hr (by simpa using hrq))

theorem pComplCoreIn_le_of_forall_pCoreIn_le {q : ℕ} {X K : Subgroup G}
    (hnil : Group.IsNilpotent ↥X) (h : ∀ r : ℕ, r.Prime → r ≠ q → pCoreIn r X ≤ K) :
    pComplCoreIn q X ≤ K := by
  rw [pComplCoreIn_eq, Subgroup.map_le_iff_le_comap]
  refine pComplCore_le_of_forall_pCore_le hnil fun r hr hrq => ?_
  rw [← Subgroup.map_le_iff_le_comap, ← pCoreIn_eq]
  exact h r hr hrq

theorem eq_iSup_pCoreIn_of_isNilpotent {D : Subgroup G} (hnil : Group.IsNilpotent ↥D) :
    D = ⨆ q : (Nat.card ↥D).primeFactors, pCoreIn (q : ℕ) D := by
  have := hnil
  have h2 : ⨆ q : (Nat.card ↥D).primeFactors, pCore (q : ℕ) ↥D = ⊤ :=
    (iSup_pCore_primeFactors ↥D).trans (fittingRaw_eq_top_of_isNilpotent ↥D)
  calc D = (⊤ : Subgroup ↥D).map D.subtype := (map_top_subtype D).symm
    _ = (⨆ q : (Nat.card ↥D).primeFactors, pCore (q : ℕ) ↥D).map D.subtype := by rw [h2]
    _ = ⨆ q : (Nat.card ↥D).primeFactors, pCoreIn (q : ℕ) D := by
        rw [Subgroup.map_iSup]; simp [pCoreIn_eq]

theorem piCore_subgroupPrimeSupportCompl_mixedFitting_eq_bot {H : Subgroup G}
    (hsolv : Group.IsSolvable ↥H) :
    piCore (subgroupPrimeSupportCompl (mixedFitting H)) ↥H = ⊥ := by
  have := hsolv
  have hset : subgroupPrimeSupportCompl (mixedFitting H)
      = {q : ℕ | q.Prime ∧ q ∉ subgroupPrimeSupport (mixedFitting H)} := by
    ext q; exact mem_subgroupPrimeSupportCompl_iff
  have hpi : IsPiSubgroup (subgroupPrimeSupport (mixedFitting H)) (fittingRaw ↥H) := by
    refine isPiSubgroup_iff.2 fun s hs => mem_subgroupPrimeSupport_iff.2 ?_
    rwa [natCard_mixedFitting H]
  rw [hset]
  exact piCore_primesNotMem_eq_bot _ ↥H hpi

instance isNilpotent_mixedFittingCentralizer (M E : Subgroup G) :
    Group.IsNilpotent ↥(mixedFittingCentralizer M E) :=
  isNilpotent_of_le_of_isNilpotent (mixedFittingCentralizer_le M E) (isNilpotent_mixedFitting M)

variable {p : ℕ} {M E H : Subgroup G}

namespace IsMixedFittingSetup

variable (h : IsMixedFittingSetup p M E)

include h

theorem pCoreIn_mixedFittingCentralizer_ne_bot {r : ℕ}
    (hr : r ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    pCoreIn r (mixedFittingCentralizer M E) ≠ ⊥ := by
  refine pCoreIn_ne_bot_of_dvd_natCard (Nat.prime_of_mem_primeFactors hr)
    (isNilpotent_mixedFittingCentralizer M E) (Nat.dvd_of_mem_primeFactors ?_)
  rw [h.primeFactors_mixedFittingCentralizer]
  exact hr

theorem pCoreIn_mixedFittingCentralizer_eq_bot {r : ℕ} (hr : r.Prime)
    (hrπ : r ∉ (Nat.card ↥(mixedFitting M)).primeFactors) :
    pCoreIn r (mixedFittingCentralizer M E) = ⊥ := by
  refine pCoreIn_eq_bot_of_notMem_primeFactors hr ?_
  rw [h.primeFactors_mixedFittingCentralizer]
  exact hrπ

theorem mem_primeFactors_mixedFitting_of_mem_primeFactors_competing [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hTH : mixedFittingCentralizer M E ≤ H) {q : ℕ}
    (hq : q ∈ (Nat.card ↥(mixedFitting H)).primeFactors) :
    q ∈ (Nat.card ↥(mixedFitting M)).primeFactors := by
  by_contra hqπ
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hDq : pCoreIn q (mixedFitting H) = ⊥ :=
    h.eq_bot_of_isPGroup_of_le_normalizer_mixedFittingCentralizer hna hodd hsolv
      (mem_subgroupPrimeSupportCompl_iff.2
        ⟨hqp, fun hcon => hqπ (mem_subgroupPrimeSupport_iff.1 hcon)⟩)
      (isPGroup_pCoreIn hqp _)
      (hTH.trans (le_normalizer_pCoreIn q (le_normalizer_mixedFitting H)))
  exact pCoreIn_ne_bot_of_dvd_natCard hqp (isNilpotent_mixedFitting H)
    (Nat.dvd_of_mem_primeFactors hq) hDq

theorem mem_primeFactors_competing_of_mem_primeFactors_mixedFitting [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) {r : ℕ}
    (hr : r ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    r ∈ (Nat.card ↥(mixedFitting H)).primeFactors := by
  by_contra hrσ
  have hmem : ∀ q ∈ subgroupPrimeSupport (mixedFitting H),
      pCoreIn r (mixedFittingCentralizer M E) ≤ (pComplCore q ↥H).map H.subtype := by
    intro q hq
    have hqπ : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors :=
      h.mem_primeFactors_mixedFitting_of_mem_primeFactors_competing hna hodd hsolv hTH
        (mem_subgroupPrimeSupport_iff.1 hq)
    have hqr : q ≠ r := fun hcon => hrσ (hcon ▸ mem_subgroupPrimeSupport_iff.1 hq)
    exact h.pCoreIn_le_map_pComplCore hna hodd hsolv hqπ hr hqr hH.1 hTH
  have hle := le_map_piCore_subgroupPrimeSupportCompl_of_forall
    ((pCoreIn_le r _).trans hTH) hmem
  rw [piCore_subgroupPrimeSupportCompl_mixedFitting_eq_bot (hsolv H hH.1), Subgroup.map_bot,
    le_bot_iff] at hle
  exact h.pCoreIn_mixedFittingCentralizer_ne_bot hr hle

theorem primeFactors_mixedFitting_competing [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    (Nat.card ↥(mixedFitting H)).primeFactors = (Nat.card ↥(mixedFitting M)).primeFactors :=
  Finset.Subset.antisymm
    (fun _ hq => h.mem_primeFactors_mixedFitting_of_mem_primeFactors_competing hna hodd hsolv
      hTH hq)
    (fun _ hr => h.mem_primeFactors_competing_of_mem_primeFactors_mixedFitting hna hodd hsolv
      hH hTH hr)

theorem pCoreIn_competing_le_centralizer_pComplCoreIn [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) {q : ℕ}
    (hq : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    pCoreIn q (mixedFitting H)
      ≤ centralizer ((pComplCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G) := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hcent : pCoreIn q (mixedFitting H) ≤
      centralizer ((pComplCoreIn q H : Subgroup G) : Set G) :=
    le_centralizer_pComplCoreIn hqp ((pCoreIn_le q _).trans (mixedFitting_le H))
      (le_normalizer_pCoreIn q (le_normalizer_mixedFitting H)) (isPGroup_pCoreIn hqp _)
  refine le_centralizer_of_le_centralizer ?_
  refine pComplCoreIn_le_of_forall_pCoreIn_le (isNilpotent_mixedFittingCentralizer M E)
    fun r hr hrq => ?_
  by_cases hrπ : r ∈ (Nat.card ↥(mixedFitting M)).primeFactors
  · refine le_trans ?_ (le_centralizer_of_le_centralizer hcent)
    rw [pComplCoreIn_eq]
    exact h.pCoreIn_le_map_pComplCore hna hodd hsolv hq hrπ (Ne.symm hrq) hH.1 hTH
  · rw [h.pCoreIn_mixedFittingCentralizer_eq_bot hr hrπ]
    exact bot_le

theorem mixedFitting_competing_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    mixedFitting H ≤ M := by
  rw [eq_iSup_pCoreIn_of_isNilpotent (isNilpotent_mixedFitting H)]
  refine iSup_le fun q => ?_
  have hqπ : (q : ℕ) ∈ (Nat.card ↥(mixedFitting M)).primeFactors :=
    h.mem_primeFactors_mixedFitting_of_mem_primeFactors_competing hna hodd hsolv hTH q.2
  obtain ⟨r, hr, hrq⟩ := Finset.exists_mem_ne h.two_le_card_primeFactors (q : ℕ)
  have hTr : pCoreIn r (mixedFittingCentralizer M E) ≤ pComplCoreIn (q : ℕ) H := by
    rw [pComplCoreIn_eq]
    exact h.pCoreIn_le_map_pComplCore hna hodd hsolv hqπ hr (Ne.symm hrq) hH.1 hTH
  have hcent : pCoreIn (q : ℕ) (mixedFitting H) ≤
      centralizer ((pComplCoreIn (q : ℕ) H : Subgroup G) : Set G) :=
    le_centralizer_pComplCoreIn (Nat.prime_of_mem_primeFactors hqπ)
      ((pCoreIn_le _ _).trans (mixedFitting_le H))
      (le_normalizer_pCoreIn _ (le_normalizer_mixedFitting H))
      (isPGroup_pCoreIn (Nat.prime_of_mem_primeFactors hqπ) _)
  refine le_trans ?_ (h.centralizer_pCoreIn_le (Nat.prime_of_mem_primeFactors hr) hr)
  exact hcent.trans (Subgroup.centralizer_le fun x hx => hTr hx)

end IsMixedFittingSetup

end

end CFSG.FeitThompson
