module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3E0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G}
  {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}

private lemma sec8t84g3a_af_mem_normalizer_of_conj_le {H : Subgroup G} {c : G}
    (h : ∀ x ∈ H, c * x * c⁻¹ ∈ H) : c ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨s, hs, rfl⟩
    change c * s * c⁻¹ ∈ H
    exact h s hs
  · exact (Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective).ge

private lemma sec8t84g3a_af_oddCoreIn_le (X : Subgroup G) : oddCoreIn X ≤ X := by
  show (CFSG.oddCore ↥X).map X.subtype ≤ X
  exact Subgroup.map_subtype_le (CFSG.oddCore ↥X)

private lemma sec8t84g3a_af_odd_card_oddCoreIn (X : Subgroup G) :
    Odd (Nat.card (oddCoreIn X)) := by
  show Odd (Nat.card ((CFSG.oddCore ↥X).map X.subtype))
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  have hEq : CFSG.oddCore ↥X = CFSG.Open.componentClassificationOddCore ↥X := rfl
  rw [hEq]
  exact CFSG.ComponentClassification.OddCore.odd_card ↥X

private lemma sec8t84g3a_af_le_normalizer_oddCoreIn (X : Subgroup G) :
    X ≤ normalizer (oddCoreIn X : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  change y ∈ (CFSG.oddCore ↥X).map X.subtype at hy
  change x * y * x⁻¹ ∈ (CFSG.oddCore ↥X).map X.subtype
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨n, hn, rfl⟩ := hy
  refine ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (CFSG.oddCore ↥X).Normal).conj_mem n hn ⟨x, hx⟩

private noncomputable def sec8t84g3a_af_sylow {A N : Subgroup G}
    (hAN : A ≤ normalizer (N : Set G))
    (hA : IsPGroup 2 A) (hNodd : Odd (Nat.card N)) :
    Sylow 2 ↥(A ⊔ N) :=
  { toSubgroup := A.subgroupOf (A ⊔ N)
    isPGroup' := hA.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
    is_maximal' := by
      intro Q hQ hle
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply le_antisymm _ hle
      intro q hq
      have hqAN : (q : G) ∈ (A : Set G) * (N : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N hAN]
        exact q.2
      obtain ⟨a, ha, n, hn, han⟩ := hqAN
      have haH : a ∈ A ⊔ N := Subgroup.mem_sup_left ha
      have hnH : n ∈ A ⊔ N := Subgroup.mem_sup_right hn
      have hqeq : q = (⟨a, haH⟩ : ↥(A ⊔ N)) * ⟨n, hnH⟩ := by
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subtype.coe_mk] using han.symm
      have haQ : (⟨a, haH⟩ : ↥(A ⊔ N)) ∈ Q :=
        hle (by rw [Subgroup.mem_subgroupOf]; exact ha)
      have hnQ : (⟨n, hnH⟩ : ↥(A ⊔ N)) ∈ Q := by
        have h1 : (⟨a, haH⟩ : ↥(A ⊔ N))⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem haQ) hq
        have h2 : (⟨a, haH⟩ : ↥(A ⊔ N))⁻¹ * q = ⟨n, hnH⟩ := by
          rw [hqeq, inv_mul_cancel_left]
        rwa [h2] at h1
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨⟨n, hnH⟩, hnQ⟩
      have h1 : orderOf (⟨n, hnH⟩ : ↥(A ⊔ N)) = 2 ^ k := by
        change orderOf ((⟨⟨n, hnH⟩, hnQ⟩ : Q) : ↥(A ⊔ N)) = 2 ^ k
        rw [Subgroup.orderOf_coe]
        exact hk
      have horder : orderOf n = 2 ^ k := by
        rw [← Subgroup.orderOf_mk n hnH]
        exact h1
      have hdiv : orderOf n ∣ Nat.card N := by
        have h := orderOf_dvd_natCard (⟨n, hn⟩ : N)
        rwa [Subgroup.orderOf_mk n hn] at h
      have hodd : Odd (orderOf n) := Odd.of_dvd_nat hNodd hdiv
      have hcop : (orderOf n).Coprime (2 ^ k) := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · rw [hk0]; simp
        · exact (Nat.coprime_pow_right_iff hkpos _ _).mpr hodd.coprime_two_right
      have hone : orderOf n = 1 := by
        refine Nat.eq_one_of_dvd_coprimes hcop dvd_rfl ?_
        rw [horder]
      have hn1 : n = 1 := orderOf_eq_one_iff.mp hone
      rw [Subgroup.mem_subgroupOf]
      simp only [hn1, mul_one] at han
      rwa [← han] }

private lemma sec8t84g3a_af_frattini_aux {A N : Subgroup G} (hAN : A ≤ normalizer (N : Set G))
    (hA : IsPGroup 2 A) (hNodd : Odd (Nat.card N)) {x : G}
    (hxN : x ∈ normalizer (N : Set G))
    (hxH : x ∈ normalizer ((A ⊔ N : Subgroup G) : Set G)) :
    ∃ m ∈ N, x * m ∈ normalizer (A : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSylow2Of A (A ⊔ N) := by
    let hP := sec8t84g3a_af_sylow hAN hA hNodd
    have h := isSylow2Of_map_sylow hP
    rw [show (hP : Subgroup ↥(A ⊔ N)) = A.subgroupOf (A ⊔ N) from rfl,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ N)] at h
    exact h
  obtain ⟨c, hcH, hcA⟩ := exists_conj_le_of_isSylow2Of hS
    (hA.map (MulAut.conj x).toMonoidHom) (by
      calc A.map (MulAut.conj x).toMonoidHom
          ≤ (A ⊔ N).map (MulAut.conj x).toMonoidHom :=
            Subgroup.map_mono (le_sup_left : A ≤ A ⊔ N)
        _ = A ⊔ N := Subgroup.mem_normalizer_iff_map_conj_eq.mp hxH)
  have hcx : c * x ∈ normalizer (A : Set G) := by
    refine sec8t84g3a_af_mem_normalizer_of_conj_le (H := A) (c := c * x) fun a ha => ?_
    have hk : x * a * x⁻¹ ∈ A.map (MulAut.conj x).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h := hcA (x * a * x⁻¹) hk
    convert h using 1
    group
  have hcAN : c ∈ (A : Set G) * (N : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N hAN]
    exact hcH
  obtain ⟨a, ha, n, hn, han⟩ := hcAN
  have hnx : n * x ∈ normalizer (A : Set G) := by
    have h1 : a⁻¹ * (c * x) ∈ normalizer (A : Set G) :=
      (normalizer (A : Set G)).mul_mem
        ((normalizer (A : Set G)).inv_mem (Subgroup.le_normalizer ha)) hcx
    have h2 : a⁻¹ * (c * x) = n * x := by
      rw [← han]
      group
    rwa [h2] at h1
  refine ⟨x⁻¹ * n * x, ((Subgroup.mem_normalizer_iff''.mp hxN) n).mp hn, ?_⟩
  have : x * (x⁻¹ * n * x) = n * x := by group
  rwa [this]

theorem sec8t84g3a_frattini (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) {x : G}
    (hx : x ∈ normalizer (E : Set G))
    (hx0 : x ∈ normalizer (((F1 ⊔ F2) ⊔ oddCoreIn (normalizer (E : Set G)) : Subgroup G) :
      Set G)) :
    ∃ n ∈ oddCoreIn (normalizer (E : Set G)), x * n ∈ sec8t84g_Q E (F1 ⊔ F2) := by
  set X : Subgroup G := normalizer (E : Set G) with hXdef
  set N : Subgroup G := oddCoreIn X with hNdef
  set A : Subgroup G := F1 ⊔ F2 with hAdef
  have hAN : A ≤ normalizer (N : Set G) :=
    ((sec8t84_E0_le_T h.D).trans h.T_syl.1).trans
      (sec8t84g3a_af_le_normalizer_oddCoreIn X)
  have hA2 : IsPGroup 2 A :=
    CFSG.Open.IsElemAbelian.isPGroup (sec8t84_E0_isElemAb2 h.D).1
  have hNodd : Odd (Nat.card N) := sec8t84g3a_af_odd_card_oddCoreIn X
  have hxN : x ∈ normalizer (N : Set G) := sec8t84g3a_af_le_normalizer_oddCoreIn X hx
  have hxH : x ∈ normalizer ((A ⊔ N : Subgroup G) : Set G) := hx0
  obtain ⟨m, hmN, hmA⟩ :=
    sec8t84g3a_af_frattini_aux (A := A) (N := N) hAN hA2 hNodd hxN hxH
  refine ⟨m, hmN, ?_⟩
  have hNX : N ≤ X := sec8t84g3a_af_oddCoreIn_le X
  have hxE : x * m ∈ normalizer (E : Set G) :=
    (normalizer (E : Set G)).mul_mem hx (hNX hmN)
  unfold sec8t84g_Q
  exact Subgroup.mem_inf.mpr ⟨hxE, hmA⟩

end CFSG.OddStandard.SmallF3.Omega
