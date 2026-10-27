module

public import CFSG.GH74.GLS.C3.Layer1.St1P47Rank

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpGen

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ABGLocalTools CFSG.GH74.Uniqueness.SU.SU1 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.C3.Layer1.P47

variable {G : Type} [Group G] [Finite G]

theorem five_le_pRank_of_not_mem_normalizer {x : G} {K : Subgroup G}
    (hpair : IsIL2Pair x K) (hq : CFSG.IsQuasisimple (kBar K)) (hcen : center (kBar K) = ⊥)
    {a : G} (haX : a ∈ centralizer ({x} : Set G)) (haN : a ∉ normalizer (K : Set G)) :
    5 ≤ pRank 2 G := by
  have hx2 : orderOf x = 2 := hpair.1
  have hxsq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  have hKX : K ≤ centralizer ({x} : Set G) := hpair.2.1
  have hax : a * x = x * a := mem_centralizer_singleton_iff.1 haX
  have hK' : cmap a K ≠ K := fun h => haN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hcX' : cmap a (centralizer ({x} : Set G)) = centralizer ({x} : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer haX)
  have hK'c : IsPCompIn 2 (centralizer ({x} : Set G)) (cmap a K) := by
    have := isPCompIn_cmap hpair.2 a
    rwa [hcX'] at this
  have hsec : cmap a K ≤ cSec K := le_cSec_of_ne hK'c hpair.2 hK'
  have hZ : ∀ z : kBar K, (∀ w : kBar K, z * w = w * z) → z = 1 := by
    intro z hz
    have : z ∈ center (kBar K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hz g).symm
    rw [hcen, Subgroup.mem_bot] at this
    exact this
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨P, hPK, hPsq, hP4⟩ := exists_lift_klein K V hVsq (by rw [hV4])
  set P' : Subgroup G := cmap a P with hP'
  have hP'K' : P' ≤ cmap a K := Subgroup.map_mono hPK
  have hP'X : P' ≤ centralizer ({x} : Set G) := hP'K'.trans ((Subgroup.map_mono hKX).trans hcX'.le)
  have hP'sq : ∀ e ∈ P', e * e = 1 := by
    rintro _ ⟨p, hp, rfl⟩
    have := hPsq p hp
    show a * p * a⁻¹ * (a * p * a⁻¹) = 1
    calc a * p * a⁻¹ * (a * p * a⁻¹) = a * (p * p) * a⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hP'card : 4 ∣ Nat.card ↥P' := by
    rw [hP', cmap, Subgroup.card_map_of_injective (MulAut.conj a).injective]
    exact hP4
  have hxP' : x ∉ P' := by
    intro hxP'
    have hxP : x ∈ P := by
      have h1 : a⁻¹ * x * a ∈ P := mem_cmap.1 hxP'
      have e : a⁻¹ * x * a = x := by
        calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
          _ = a⁻¹ * (a * x) := by rw [hax]
          _ = x := by group
      rwa [e] at h1
    exact x_not_mem_of_le hpair hZ hPK hxP
  obtain ⟨hcommB, hBsq, hBcard⟩ := zpowers_sup_facts hxsq hx1 hP'X hP'sq hxP'
  set B : Subgroup G := zpowers x ⊔ P' with hB
  have hBea : CFSG.IsElementaryAbelian 2 ↥B := isElementaryAbelian_two_of_mul_self B hBsq
  have hxsecK : x ∈ centralizerSection K (pPrimeCoreOf 2 K) :=
    Back.mem_centralizerSection_of_centralizes
      (fun k hk => (mem_centralizer_singleton_iff.1 (hKX hk)).symm) (TwoThin.pPrimeCoreOf_le K)
  have hBsec : B ≤ centralizerSection K (pPrimeCoreOf 2 K) :=
    sup_le ((Subgroup.zpowers_le).2 hxsecK) (hP'K'.trans hsec)
  obtain ⟨m, Q, hm2, hQsq, hQcard⟩ := exists_big_elemAbelian K B hBea hBsec V hVsq
    (by rw [hV4]) hZ
  have hQea : CFSG.IsElementaryAbelian 2 ↥Q := isElementaryAbelian_two_of_mul_self Q hQsq
  have hBpg : IsPGroup 2 ↥B := by
    have := hBea
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  obtain ⟨j, hj⟩ := hBpg.exists_card_eq
  have hP'ge : 4 ≤ Nat.card ↥P' := Nat.le_of_dvd Nat.card_pos hP'card
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank := le_pRank_group_of_elem hQea (k := j + m) (by rw [hQcard, hj, pow_add])
  omega

theorem mem_normalizer_of_centerless (hr4 : pRank 2 G = 4) {x : G} {K : Subgroup G}
    (hpair : IsIL2Pair x K) (hq : CFSG.IsQuasisimple (kBar K)) (hcen : center (kBar K) = ⊥)
    {a : G} (haX : a ∈ centralizer ({x} : Set G)) : a ∈ normalizer (K : Set G) := by
  by_contra haN
  exact absurd (five_le_pRank_of_not_mem_normalizer hpair hq hcen haX haN) (by omega)

end CFSG.GH74.GLS.C3.Layer1.PumpGen
