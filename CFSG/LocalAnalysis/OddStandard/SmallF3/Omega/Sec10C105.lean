module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10BurnMod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JMax
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private lemma mem_zpowers_of_conj_zpowers {G : Type*} [Group G] {x y c : G}
    (hxc : x * c = c * x) (h : x * y * x⁻¹ ∈ zpowers c) : y ∈ zpowers c := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  have hc : Commute x c := hxc
  have hxci : x⁻¹ * c ^ i * x = c ^ i := by
    rw [(hc.inv_left.zpow_right i).eq]
    group
  have hy : y = x⁻¹ * (x * y * x⁻¹) * x := by group
  rw [hy, ← hi]
  exact hxci.symm

private lemma zpowers_two_cases {G : Type*} [Group G] {z ε : G} (hz : orderOf z = 2)
    (hzsq : z * z = 1) (h : ε ∈ zpowers z) : ε = 1 ∨ ε = z := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  have hzi : z ^ i = z ^ (i % 2) := by
    refine (zpow_eq_zpow_iff_modEq).mpr ?_
    rw [hz]
    exact (Int.mod_modEq i 2).symm
  rw [← hi, hzi]
  rcases Int.emod_two_eq_zero_or_one i with h0 | h1
  · left; rw [h0]; simp
  · right; rw [h1]; simp

theorem asc82Step105C_of (hS : Asc82Step105S) (h102 : Asc82Lemma102) (hb : Asc82Basic10)
    (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) (hF : Asc82Fact1051) :
    Asc82Step105C := by
  intro G _ _ t L S z K1 K2 hctx hneg h hh hmem
  let W : Subgroup G := secW t K1 K2
  let H : Subgroup G := centralizer ({z} : Set G)
  have hhH : h ∈ H := hh
  have hmemW : h⁻¹ * t * h ∈ W ⊔ zpowers z := hmem
  have hSyl : IsSylow2Of S ⊤ := hS G t L S z K1 K2 hctx hneg
  obtain ⟨hpsp, htC, htnotL, htS, hSN, hsylL⟩ := hb G t L S z hctx.toSec10Z
  have hWelem : z ∈ W ∧ IsElemAbelianMod z W := sec10J_W_elem hP5 hC5 hb hctx
  have hzW : z ∈ W := hWelem.1
  have hWmod : IsElemAbelianMod z W := hWelem.2
  have hWS : W ≤ S := sec10J_W_le hP5 hb hctx
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hctx.pocket1.2.1 hctx.pocket1.1)).1
  have hzS : z ∈ S := hctx.mem_S
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hSH : S ≤ H := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hctx.central s hs)
  have hSylH : IsSylow2Of S H := by
    refine ⟨hSH, hSyl.2.1, ?_⟩
    intro hdvd
    have hmul := Subgroup.relIndex_mul_relIndex (H := S) (K := H) (L := ⊤) hSH le_top
    exact hSyl.2.2 (hmul ▸ dvd_mul_of_dvd_left hdvd _)
  have hHz : ∀ x ∈ H, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hweak : ∀ x ∈ H, CFSG.conjugate W x ≤ S → CFSG.conjugate W x = W := by
    intro x hxH hxS
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxH
    have hzV : z ∈ CFSG.conjugate W x := by
      rw [mem_conjugate_iff', hxz, mul_assoc, mul_inv_cancel, mul_one]
      exact hzW
    have hVmod : IsElemAbelianMod z (CFSG.conjugate W x) := by
      intro a ha b hb
      have hax : x * a * x⁻¹ ∈ W := mem_conjugate_iff'.mp ha
      have hbx : x * b * x⁻¹ ∈ W := mem_conjugate_iff'.mp hb
      constructor
      · apply mem_zpowers_of_conj_zpowers hxz
        have h2 : x * (a * b * a⁻¹ * b⁻¹) * x⁻¹
            = (x * a * x⁻¹) * (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ * (x * b * x⁻¹)⁻¹ := by
          group
        rw [h2]
        exact (hWmod (x * a * x⁻¹) hax (x * b * x⁻¹) hbx).1
      · apply mem_zpowers_of_conj_zpowers hxz
        have h2 : x * (a * a) * x⁻¹ = (x * a * x⁻¹) * (x * a * x⁻¹) := by group
        rw [h2]
        exact (hWmod (x * a * x⁻¹) hax (x * a * x⁻¹) hax).2
    have hcardV : Nat.card ↥(CFSG.conjugate W x) = Nat.card ↥W := by
      rw [CFSG.conjugate]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
        (MulEquiv.injective (MulAut.conj x⁻¹))
    rcases sec10J_key h102 hP5 hC5 hF hb hctx hxS hzV hVmod with hle | hlt
    · exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardV.symm)
    · exact absurd hlt (not_lt.mpr (le_of_eq hcardV.symm))
  have htW : t ∈ W := by
    change t ∈ secQ K1 K2 ⊔ zpowers t
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have ht_comm : ∀ w ∈ W, t * w = w * t := by
    intro w hw
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 (hWS hw))).symm
  have hmemW' : h⁻¹ * t * h ∈ W := by
    have hzle : zpowers z ≤ W := Subgroup.zpowers_le.mpr hzW
    rwa [sup_eq_left.mpr hzle] at hmemW
  obtain ⟨n, hn, ε, hε, hnε⟩ :=
    sec10_burnside_mod (H := H) (S := S) (W := W) (z := z) hSylH hzS hHz hWS hzW
      (fun a ha b hb => (hWmod a ha b hb).1) hweak htW (H.inv_mem hhH) (by simpa using hmemW')
  have hnε' : h⁻¹ * t * h = n * t * n⁻¹ * ε := by simpa using hnε
  have hnH : n ∈ H := (Subgroup.mem_inf.mp hn).1
  have hnN : n ∈ normalizer (W : Set G) := (Subgroup.mem_inf.mp hn).2
  have hntnW : n * t * n⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hnN t).mp htW
  have hcentral_ntn : ∀ w ∈ W, (n * t * n⁻¹) * w = w * (n * t * n⁻¹) := by
    intro w hw
    have hninvN : n⁻¹ ∈ normalizer (W : Set G) := (normalizer (W : Set G)).inv_mem hnN
    have hw' : n⁻¹ * w * n ∈ W := by
      simpa using (Subgroup.mem_normalizer_iff.mp hninvN w).mp hw
    have htcomm : t * (n⁻¹ * w * n) = (n⁻¹ * w * n) * t := ht_comm _ hw'
    calc (n * t * n⁻¹) * w
        = n * (t * (n⁻¹ * w * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * w * n) * t) * n⁻¹ := by rw [htcomm]
      _ = w * (n * t * n⁻¹) := by group
  have hcenter : n * t * n⁻¹ ∈ zpowers t ⊔ zpowers z :=
    sec10J_W_center hP5 hC5 hb hctx (n * t * n⁻¹) hntnW hcentral_ntn
  have hcenter' : n * t * n⁻¹ ∈ zpowers z ⊔ zpowers t := by
    rw [sup_comm]
    exact hcenter
  have hntn_order : orderOf (n * t * n⁻¹) = 2 := by
    have h1 : orderOf ((MulAut.conj n) t) = orderOf t := MulEquiv.orderOf_eq _ _
    have h2 : (MulAut.conj n) t = n * t * n⁻¹ := MulAut.conj_apply n t
    rw [h2] at h1
    exact h1.trans hctx.involution
  have hzt : z * t = t * z := (hctx.central t htS).symm
  rcases sec10_two_elem_cases hzt hz2 hctx.involution hcenter' hntn_order with
    hzcase | htcase | htzcase
  · exfalso
    have hnz : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp hnH
    have hzn : n⁻¹ * z * n = z := by
      calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
        _ = n⁻¹ * (n * z) := by rw [← hnz]
        _ = z := by group
    have ht_eq_z : t = z := by
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = n⁻¹ * z * n := by rw [hzcase]
        _ = z := hzn
    exact htnotL (by rw [ht_eq_z]; exact hzL)
  · have hzeps : ε = 1 ∨ ε = z := zpowers_two_cases hz2 hzsq hε
    rcases hzeps with heps | heps
    · left; rw [hnε', htcase, heps, mul_one]
    · right; rw [hnε', htcase, heps]
  · have hzeps : ε = 1 ∨ ε = z := zpowers_two_cases hz2 hzsq hε
    rcases hzeps with heps | heps
    · right; rw [hnε', htzcase, heps, mul_one]
    · left; rw [hnε', htzcase, heps, mul_assoc, hzsq, mul_one]

end CFSG.OddStandard.SmallF3.Omega
