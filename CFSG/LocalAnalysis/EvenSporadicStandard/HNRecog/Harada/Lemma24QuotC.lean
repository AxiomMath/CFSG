module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Cfg

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

theorem centralizer_quot_eq {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)) =
      (centralizer ({t} : Set Y)).map (QuotientGroup.mk' (zpowers a)) := by
  let π : Y →* Y ⧸ zpowers a := QuotientGroup.mk' (zpowers a)
  apply le_antisymm
  · intro q hq
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (zpowers a) q
    have hcomm : π t * π y = π y * π t :=
      (Subgroup.mem_centralizer_iff.mp hq) (π t) (Set.mem_singleton _)
    have hconjπ : π (y * t * y⁻¹) = π t := by
      simp only [map_mul, map_inv]
      rw [← hcomm]
      group
    have hmem : (y * t * y⁻¹) * t⁻¹ ∈ zpowers a := by
      rw [← QuotientGroup.ker_mk' (zpowers a), MonoidHom.mem_ker]
      rw [map_mul, hconjπ, map_inv, mul_inv_cancel]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hweq : y * t * y⁻¹ = a ^ k * t := by
      rw [hk]
      group
    have hsq1 : (y * t * y⁻¹) ^ 2 = 1 := by
      rw [pow_two]
      calc y * t * y⁻¹ * (y * t * y⁻¹)
          = y * (t * t) * y⁻¹ := by group
        _ = 1 := by
              rw [show t * t = 1 by simpa [pow_two] using h.t_sq]
              group
    have hcomm_at : Commute a t := ((Subgroup.mem_center_iff.mp h.a_central) t).symm
    have hct : Commute (a ^ k) t := hcomm_at.zpow_left k
    have hb2 : (a ^ k) ^ 2 = 1 := by
      have hsq : (a ^ k * t) ^ 2 = 1 := by rw [← hweq]; exact hsq1
      rw [hct.mul_pow 2, h.t_sq, mul_one] at hsq
      exact hsq
    have h1 : orderOf (a ^ k) = 1 := by
      have h2 : orderOf (a ^ k) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hb2
      have h3 : orderOf (a ^ k) ∣ 3 := by
        rw [← h.orderOf_a]
        exact orderOf_dvd_of_mem_zpowers (Subgroup.zpow_mem_zpowers a k)
      have hgcd : orderOf (a ^ k) ∣ 1 := by
        have h := Nat.dvd_gcd h3 h2
        rw [show Nat.gcd 3 2 = 1 from by norm_num] at h
        exact h
      exact Nat.dvd_one.mp hgcd
    have hak : a ^ k = 1 := orderOf_eq_one_iff.mp h1
    have hconjEq : y * t * y⁻¹ = t := by rw [hweq, hak, one_mul]
    have hyt : y * t = t * y := by
      calc y * t = (y * t * y⁻¹) * y := by group
        _ = t * y := by rw [hconjEq]
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hyt, rfl⟩
  · have hle := Subgroup.map_centralizer_le_centralizer_image ({t} : Set Y)
      (QuotientGroup.mk' (zpowers a))
    simpa only [Set.image_singleton] using hle

theorem card_centralizer_quot {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    Nat.card ↥(centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a))) = 480 := by
  let C : Subgroup Y := centralizer ({t} : Set Y)
  let π : Y →* Y ⧸ zpowers a := QuotientGroup.mk' (zpowers a)
  have haC : a ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_center_iff.mp h.a_central) t).symm
  have hle : zpowers a ≤ C := Subgroup.zpowers_le.mpr haC
  have hQ : centralizer ({π t} : Set (Y ⧸ zpowers a)) = C.map π := by
    show centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)) =
      (centralizer ({t} : Set Y)).map (QuotientGroup.mk' (zpowers a))
    exact centralizer_quot_eq h
  have hker : Nat.card (π.domRestrict C).ker = 3 := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
      h.orderOf_a]
  have hrange : (π.domRestrict C).range = C.map π :=
    MonoidHom.domRestrict_range (f := π) (K := C)
  have hrel := Subgroup.card_ker_mul_card_range (π.domRestrict C)
  rw [hker, hrange, ← hQ, h.card_C] at hrel
  change Nat.card ↥(centralizer ({π t} : Set (Y ⧸ zpowers a))) = 480
  omega

theorem quot_perfect60 {Y : Type} [Group Y] [Finite Y] {a t : Y} {τ : Y → Prop}
    {F P : Subgroup Y} [(zpowers a).Normal] (h : Cfg24 Y a t τ F P) :
    ∃ M : Subgroup (Y ⧸ zpowers a),
      M ≤ centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)) ∧
      ⁅M, M⁆ = M ∧ Nat.card M = 60 := by
  let π : Y →* Y ⧸ zpowers a := QuotientGroup.mk' (zpowers a)
  let C : Subgroup Y := centralizer ({t} : Set Y)
  obtain ⟨M, hM_le, hM_perf, hM_card, hM_inf⟩ := h.perfect60
  have hQ : centralizer ({π t} : Set (Y ⧸ zpowers a)) = C.map π := by
    show centralizer ({QuotientGroup.mk' (zpowers a) t} : Set (Y ⧸ zpowers a)) =
      (centralizer ({t} : Set Y)).map (QuotientGroup.mk' (zpowers a))
    exact centralizer_quot_eq h
  refine ⟨M.map π, ?_, ?_, ?_⟩
  · rw [hQ]
    exact Subgroup.map_mono hM_le
  · rw [← Subgroup.map_commutator (H₁ := M) (H₂ := M) (f := π), hM_perf]
  · have hinj : Function.Injective (π.domRestrict M) := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
      exact (Subgroup.subgroupOf_eq_bot).mpr (by
        rw [disjoint_iff, inf_comm]
        exact hM_inf)
    rw [← MonoidHom.domRestrict_range (f := π) (K := M),
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hM_card

end CFSG.EvenSporadicStandard.HNRecog.Harada
