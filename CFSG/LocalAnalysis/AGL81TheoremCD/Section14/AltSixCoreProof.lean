module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreStepOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreFrattini
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreCritical
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreClassTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.AltSixCoreModule

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

private theorem card_le_pow_three_of_isMulCommutative {r : ℕ} [Fact r.Prime] {N B : Subgroup K}
    (hBN : B ≤ N) (hB : IsMulCommutative ↥B) (hexp : ∀ x ∈ B, x ^ r = 1)
    (hrank : CFSG.Open.pRank r N ≤ 3) : Nat.card B ≤ r ^ 3 := by
  have hBp : IsPGroup r B := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hexp x x.2)⟩
  obtain ⟨k, hk⟩ := hBp.exists_card_eq
  have hk3 : k ≤ CFSG.Open.pRank r N :=
    CFSG.SectionRank.le_pRank (Fact.out : r.Prime).one_lt hBN ⟨hB, hexp⟩ hk
  calc Nat.card B = r ^ k := hk
    _ ≤ r ^ 3 := Nat.pow_le_pow_right (Fact.out : r.Prime).pos (hk3.trans hrank)

private theorem eq_bot_of_isPGroup_of_dvd_six {r : ℕ} [Fact r.Prime] {N R : Subgroup K}
    (hRN : R ≤ N) (hR : IsPGroup r R) (hdr : r ∣ 6) (hcop : Nat.Coprime (Nat.card N) 6) :
    R = ⊥ := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hcopRN : Nat.Coprime (Nat.card R) (Nat.card N) := by
    rw [hk]
    exact ((hcop.coprime_dvd_right hdr).symm).pow_left k
  have h : R ⊓ N = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcopRN).eq_bot
  rwa [inf_eq_left.mpr hRN] at h

private theorem card_inf_centralizer_le_pow_four {r : ℕ} [Fact r.Prime] {N D : Subgroup K}
    (hDN : D ≤ N) (hexp : ∀ x ∈ D, x ^ r = 1) (hrank : CFSG.Open.pRank r N ≤ 3) :
    Nat.card ↥(D ⊓ centralizer (D : Set K)) ≤ r ^ 4 := by
  have hZcomm : IsMulCommutative ↥(D ⊓ centralizer (D : Set K)) :=
    ⟨⟨fun x y => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp x.2.2 (y : K) y.2.1).symm⟩⟩
  calc Nat.card ↥(D ⊓ centralizer (D : Set K)) ≤ r ^ 3 :=
        card_le_pow_three_of_isMulCommutative (inf_le_left.trans hDN) hZcomm
          (fun x hx => hexp x hx.1) hrank
    _ ≤ r ^ 4 := Nat.pow_le_pow_right (Fact.out : r.Prime).pos (by norm_num)

private theorem card_le_pow_four_mul_card_inf_centralizer_of_rank {r : ℕ} [Fact r.Prime]
    {N D : Subgroup K} (hDN : D ≤ N) (hexp : ∀ x ∈ D, x ^ r = 1)
    (hclass : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set K))
    (hrank : CFSG.Open.pRank r N ≤ 3) :
    Nat.card D ≤ r ^ 4 * Nat.card ↥(D ⊓ centralizer (D : Set K)) := by
  refine card_le_pow_four_mul_card_inf_centralizer (r := r) hexp hclass ?_
  intro B hBD hB
  exact card_le_pow_three_of_isMulCommutative (hBD.trans hDN)
    ⟨⟨fun x y => Subtype.ext (hB x x.2 y y.2)⟩⟩ (fun x hx => hexp x (hBD hx)) hrank

private theorem commutator_eq_one_of_mem_inf_centralizer {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) {ψ : K →* alternatingGroup (Fin 6)} (hcop : Nat.Coprime (Nat.card ψ.ker) 6)
    (hsol : IsSolvable ψ.ker) (hrank : CFSG.Open.pRank r ψ.ker ≤ 3) {Y D : Subgroup K}
    (hY : ⁅Y, Y⁆ = Y) (hYψ : Y.map ψ = ⊤) (hDN : D ≤ ψ.ker)
    (hYZ : Y ≤ normalizer ((D ⊓ centralizer (D : Set K) : Subgroup K) : Set K))
    (hexp : ∀ x ∈ D, x ^ r = 1) :
    ∀ y ∈ Y, ∀ z ∈ D ⊓ centralizer (D : Set K), ⁅z, y⁆ = 1 := by
  have hcard : Nat.card ↥(D ⊓ centralizer (D : Set K)) ≤ r ^ 4 * Nat.card ↥(⊥ : Subgroup K) := by
    rw [Subgroup.card_bot, mul_one]
    exact card_inf_centralizer_le_pow_four hDN hexp hrank
  have hYbot : Y ≤ normalizer ((⊥ : Subgroup K) : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup K).Normal)]
    exact le_top
  intro y hy z hz
  refine Subgroup.mem_bot.mp (commutator_mem_of_card_le_pow_four hr2 hr3 ψ hcop hsol hY hYψ
    bot_le hYZ hYbot (fun x hx => Subgroup.mem_bot.mpr (hexp x hx.1)) ?_ hcard y hy z hz)
  intro x hx w hw
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp hx.2 w hw.1).symm

private theorem commutator_mem_inf_centralizer {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) {ψ : K →* alternatingGroup (Fin 6)} (hcop : Nat.Coprime (Nat.card ψ.ker) 6)
    (hsol : IsSolvable ψ.ker) (hrank : CFSG.Open.pRank r ψ.ker ≤ 3) {Y D : Subgroup K}
    (hY : ⁅Y, Y⁆ = Y) (hYψ : Y.map ψ = ⊤) (hDN : D ≤ ψ.ker) (hYD : Y ≤ normalizer (D : Set K))
    (hYZ : Y ≤ normalizer ((D ⊓ centralizer (D : Set K) : Subgroup K) : Set K))
    (hexp : ∀ x ∈ D, x ^ r = 1)
    (hclass : ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set K)) :
    ∀ y ∈ Y, ∀ x ∈ D, ⁅x, y⁆ ∈ D ⊓ centralizer (D : Set K) :=
  commutator_mem_of_card_le_pow_four hr2 hr3 ψ hcop hsol hY hYψ inf_le_left hYD hYZ
    (fun x hx => by rw [hexp x hx]; exact one_mem _) hclass
    (card_le_pow_four_mul_card_inf_centralizer_of_rank hDN hexp hclass hrank)

private theorem exists_perfect_supplement_le_centralizer {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) {ψ : K →* alternatingGroup (Fin 6)} (hψ : Function.Surjective ψ)
    (hcop : Nat.Coprime (Nat.card ψ.ker) 6) (hsol : IsSolvable ψ.ker)
    (hrank : CFSG.Open.pRank r ψ.ker ≤ 3) {R : Subgroup K} (hRN : R ≤ ψ.ker)
    (hR : IsPGroup r R) :
    ∃ Y : Subgroup K, Y ≤ centralizer (R : Set K) ∧ ψ.ker ⊔ Y = ⊤ := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  obtain ⟨S, hRS, hSN, hSp, Y, hYS, hY, hYψ⟩ := exists_isPGroup_perfect_supplement ψ hψ hRN hR
  obtain ⟨D, hDS, hND, hNZ, hexp, hclass, hkey⟩ := exists_critical_reduction (p := r) hr2 hSp
  have hDN : D ≤ ψ.ker := hDS.trans hSN
  refine ⟨Y, (hkey Y hYS hY ?_ ?_).trans (centralizer_le (show (R : Set K) ⊆ S from hRS)), ?_⟩
  · exact commutator_eq_one_of_mem_inf_centralizer hr2 hr3 hcop hsol hrank hY hYψ hDN
      (hYS.trans hNZ) hexp
  · exact commutator_mem_inf_centralizer hr2 hr3 hcop hsol hrank hY hYψ hDN (hYS.trans hND)
      (hYS.trans hNZ) hexp hclass
  · have h : Y.map ψ = (⊤ : Subgroup K).map ψ := by rw [hYψ, map_top_of_surjective ψ hψ]
    rw [map_eq_map_iff, top_sup_eq] at h
    rwa [sup_comm]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A6Core

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Subgroup

theorem kFactAltSixCoreCentral_holds : KFactAltSixCoreCentral := by
  intro K _ _ hperf N hN hsol hcop ⟨e⟩ hrank
  haveI : Group.IsPerfect K := hperf
  let ψ : K →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hψ : Function.Surjective ψ := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hψN : ψ.ker = N := by
    ext x
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  refine A6Core.le_center_of_forall_exists_le_centralizer hsol fun r hr R hRN hR => ?_
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases h6 : r ∣ 6
  · refine ⟨⊤, ?_, sup_top_eq N⟩
    simp [A6Core.eq_bot_of_isPGroup_of_dvd_six hRN hR h6 hcop]
  have hr2 : r ≠ 2 := by rintro rfl; exact h6 (by norm_num)
  have hr3 : r ≠ 3 := by rintro rfl; exact h6 (by norm_num)
  rw [← hψN] at hRN hsol hcop hrank ⊢
  exact A6Core.exists_perfect_supplement_le_centralizer hr2 hr3 hψ hcop hsol (hrank r hr) hRN hR

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
