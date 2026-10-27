module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapThompson

import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_commute {D Q : Subgroup G} (hcomm : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d)
    {t : G} : t ∈ D ⊔ Q ↔ ∃ d ∈ D, ∃ q ∈ Q, t = d * q := by
  have hle : D ≤ Subgroup.normalizer (Q : Set G) := fun d hd =>
    Subgroup.centralizer_le_normalizer (Q : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun q hq => (hcomm d hd q hq).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D Q hle, Set.mem_mul]
  constructor
  · rintro ⟨d, hd, q, hq, hdq⟩
    exact ⟨d, hd, q, hq, hdq.symm⟩
  · rintro ⟨d, hd, q, hq, rfl⟩
    exact ⟨d, hd, q, hq, rfl⟩

theorem isPGroup_sup_of_commute {D Q : Subgroup G} {p : ℕ} [Fact p.Prime] [Finite G]
    (hD : IsPGroup p D) (hQ : IsPGroup p Q) (hcomm : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) :
    IsPGroup p (D ⊔ Q : Subgroup G) := by
  refine IsPGroup.to_sup_of_normal_right' hD hQ ?_
  exact (fun d hd =>
    Subgroup.centralizer_le_normalizer (Q : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun q hq => (hcomm d hd q hq).symm))

theorem card_sup_of_commute {D Q : Subgroup G} (hcomm : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d)
    (hDQ : D ⊓ Q = ⊥) : Nat.card (D ⊔ Q : Subgroup G) = Nat.card D * Nat.card Q := by
  classical
  have hcomm' : ∀ (x : D) (y : Q), Commute (D.subtype x) (Q.subtype y) :=
    fun x y => show (D.subtype x) * (Q.subtype y) = (Q.subtype y) * (D.subtype x) from
      hcomm x x.2 y y.2
  let μ : D × Q →* G := MonoidHom.noncommCoprod D.subtype Q.subtype hcomm'
  have hμ : ∀ x : D × Q, μ x = (x.1 : G) * (x.2 : G) := fun _ => rfl
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, q⟩ h
    rw [hμ] at h
    have hd : (d : G) = (q : G)⁻¹ := (mul_eq_one_iff_eq_inv).1 h
    have hdQ : (d : G) ∈ Q := by rw [hd]; exact Q.inv_mem q.2
    have hd1 : (d : G) = 1 := Subgroup.mem_bot.mp (by
      rw [← hDQ]
      exact Subgroup.mem_inf.mpr ⟨d.2, hdQ⟩)
    have hq1 : (q : G) = 1 := by
      rw [hd1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext hd1) (Subtype.ext hq1)
  have hrange : μ.range = (D ⊔ Q : Subgroup G) := by
    change (MonoidHom.noncommCoprod D.subtype Q.subtype hcomm').range = _
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have e : D × Q ≃* (D ⊔ Q : Subgroup G) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hc := Nat.card_congr e.toEquiv
  rw [Nat.card_prod] at hc
  exact hc.symm

theorem false_of_thompson_product [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {D Q : Subgroup G} (hD : IsPGroup 2 D)
    (hQ : IsPGroup 2 Q) (hcomm : ∀ d ∈ D, ∀ q ∈ Q, d * q = q * d) (hDQ : D ⊓ Q = ⊥)
    (ε : D →* ℤˣ) (ψ : Q →* ℤˣ) {z : G} (hz : orderOf z = 2) (hzD : z ∈ D)
    (hεz : ε ⟨z, hzD⟩ = -1) (hidx : ¬ 2 ∣ (D ⊔ Q : Subgroup G).index)
    (hnc : ∀ (d : D) (q : Q), ((d : G) * (q : G)) * ((d : G) * (q : G)) = 1 →
      ε d * ψ q = 1 → ∀ a : G, a⁻¹ * z * a ≠ (d : G) * (q : G)) : False := by
  classical
  have hTp : IsPGroup 2 (D ⊔ Q : Subgroup G) := isPGroup_sup_of_commute hD hQ hcomm
  have hcomm' : ∀ (x : D) (y : Q), Commute (D.subtype x) (Q.subtype y) :=
    fun x y => show (D.subtype x) * (Q.subtype y) = (Q.subtype y) * (D.subtype x) from
      hcomm x x.2 y y.2
  let μ : D × Q →* G := MonoidHom.noncommCoprod D.subtype Q.subtype hcomm'
  have hμ : ∀ x : D × Q, μ x = (x.1 : G) * (x.2 : G) := fun _ => rfl
  have hinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, q⟩ h
    rw [hμ] at h
    have hd : (d : G) = (q : G)⁻¹ := (mul_eq_one_iff_eq_inv).1 h
    have hdQ : (d : G) ∈ Q := by rw [hd]; exact Q.inv_mem q.2
    have hd1 : (d : G) = 1 := Subgroup.mem_bot.mp (by
      rw [← hDQ]
      exact Subgroup.mem_inf.mpr ⟨d.2, hdQ⟩)
    have hq1 : (q : G) = 1 := by
      rw [hd1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext hd1) (Subtype.ext hq1)
  have hrange : μ.range = (D ⊔ Q : Subgroup G) := by
    change (MonoidHom.noncommCoprod D.subtype Q.subtype hcomm').range = _
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  let χ : D × Q →* ℤˣ :=
    (ε.comp (MonoidHom.fst D Q)) * (ψ.comp (MonoidHom.snd D Q))
  have hχ : ∀ x : D × Q, χ x = ε x.1 * ψ x.2 := by
    intro x
    simp [χ, MonoidHom.mul_apply]
  have hχz : χ (⟨z, hzD⟩, 1) = -1 := by
    rw [hχ]
    simp [hεz]
  have hχrange : χ.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · exact ⟨(⟨z, hzD⟩, 1), hχz⟩
  have hkeridx : χ.ker.index = 2 := by
    rw [Subgroup.index_ker, hχrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  let U : Subgroup G := χ.ker.map μ
  have hUT : U ≤ (D ⊔ Q : Subgroup G) := by
    rw [← hrange]
    exact Subgroup.map_le_range μ χ.ker
  have hUidx : U.relIndex (D ⊔ Q : Subgroup G) = 2 := by
    have hmap : U = χ.ker.map μ := rfl
    have htop : (D ⊔ Q : Subgroup G) = (⊤ : Subgroup (D × Q)).map μ := by
      rw [Subgroup.map_top, hrange]
    rw [hmap, htop, Subgroup.relIndex_map_map_of_injective (f := μ) χ.ker ⊤ hinj,
      Subgroup.relIndex_top_right]
    exact hkeridx
  have hzT : z ∈ (D ⊔ Q : Subgroup G) := Subgroup.mem_sup_left hzD
  have hzU : z ∉ U := by
    intro hmem
    obtain ⟨x, hxker, hxμ⟩ := Subgroup.mem_map.1 hmem
    have hx1 : x = (⟨z, hzD⟩, 1) := by
      apply hinj
      rw [hxμ, hμ]
      simp
    rw [hx1, MonoidHom.mem_ker, hχz] at hxker
    exact (by decide : ¬ ((-1 : ℤˣ) = 1)) hxker
  have hconj : ∀ a : G, a⁻¹ * z * a ∉ U := by
    intro a ha
    obtain ⟨x, hxker, hxμ⟩ := Subgroup.mem_map.1 ha
    obtain ⟨d, q⟩ := x
    rw [MonoidHom.mem_ker] at hxker
    have hχker : ε d * ψ q = 1 := by rwa [hχ (d, q)] at hxker
    have hμx : (d : G) * (q : G) = a⁻¹ * z * a := by
      have h := hxμ
      rw [hμ] at h
      exact h
    have hz2 : z * z = 1 := by
      rw [← pow_two, ← hz]
      exact pow_orderOf_eq_one z
    have hsq : ((d : G) * (q : G)) * ((d : G) * (q : G)) = 1 := by
      rw [hμx]
      calc (a⁻¹ * z * a) * (a⁻¹ * z * a) = a⁻¹ * (z * z) * a := by group
        _ = 1 := by rw [hz2]; group
    exact hnc d q hsq hχker a hμx.symm
  exact false_of_thompson_involution (T := D ⊔ Q) (U := U)
    hnonab hTp hidx hUT hUidx hz hzT hzU hconj

end CFSG.OddStandard.AltStdSec.SwapPartner
