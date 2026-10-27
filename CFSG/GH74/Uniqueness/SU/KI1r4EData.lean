module

public import CFSG.GH74.Uniqueness.SU.KI1r4EComp
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.SU.KI1r4TG1

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

structure L85Data (T : Sylow 2 H) (x y : H) (A R : Subgroup H) : Prop where
  rdata : RData T x A R y
  h64 : Nat.card R = 64
  hZ4 : Nat.card (center ↥R) = 4
  hfr : frattini ↥R = center ↥R
  hcom : ∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R
  hLT : (T : Subgroup H) ⊓ layer H ≤ R
  hRL : R ≤ layer H
  hAc : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a
  hcenA : ∀ z : ↥R, z ∈ center ↥R ↔ (z : H) ∈ A
  hAE : ∀ a ∈ A, a ∈ layer H ∧ ∀ g ∈ layer H, a * g = g * a
  hZEA : ∀ z ∈ layer H, (∀ g ∈ layer H, z * g = g * z) → z ∈ A
  hKinv : ∀ K : Subgroup H, IsComponent K →
    ∃ a ∈ K, (∀ k ∈ K, a * k = k * a) ∧ a ≠ 1 ∧ a * a = 1

theorem L85Data.of_basic {T : Sylow 2 H} {x y : H} {A R : Subgroup H} (hR : RData T x A R y)
    (h64 : Nat.card R = 64) (hZ4 : Nat.card (center ↥R) = 4) (hfr : frattini ↥R = center ↥R)
    (hcom : ∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R)
    (hAE : ∀ a ∈ A, a ∈ layer H ∧ ∀ g ∈ layer H, a * g = g * a)
    (hEz : ∀ z ∈ layer H, (∀ g ∈ layer H, z * g = g * z) → z ∈ (T : Subgroup H))
    (hK1 : ∀ K : Subgroup H, IsComponent K →
      ∃ z ∈ K, (∀ k ∈ K, z * k = k * z) ∧ z ≠ 1)
    (hcomp : ∃ K : Subgroup H, IsComponent K) : L85Data T x y A R := by
  classical
  have hEn : (layer H).Normal := layer_normal H
  have hLT : (T : Subgroup H) ⊓ layer H ≤ R := by
    intro g hg
    rw [hR.R_eq]
    exact ⟨hg.1, Subgroup.mem_centralizer_iff.mpr fun a ha => (hAE a ha).2 g hg.2⟩
  have hAc : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a := by
    intro a ha r hr
    rw [hR.R_eq] at hr
    exact Subgroup.mem_centralizer_iff.mp hr.2 a ha
  have hcenA : ∀ z : ↥R, z ∈ center ↥R ↔ (z : H) ∈ A := by
    intro z
    have hAcen : ∀ a : ↥A, (⟨(a : H), hR.A_le a.2⟩ : ↥R) ∈ center ↥R := fun a =>
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hAc _ a.2 g g.2).symm
    let ι : ↥A → ↥(center ↥R) := fun a => ⟨⟨(a : H), hR.A_le a.2⟩, hAcen a⟩
    have hι : Function.Injective ι := fun a b hab =>
      Subtype.ext (congrArg (fun c : ↥(center ↥R) => ((c : ↥R) : H)) hab)
    have hbij : Function.Bijective ι :=
      hι.bijective_of_nat_card_le (by rw [hZ4, hR.A_card])
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := hbij.2 ⟨z, hz⟩
      have := congrArg (fun c : ↥(center ↥R) => ((c : ↥R) : H)) ha
      rw [← this]
      exact a.2
    · intro hz
      exact hAcen ⟨z, hz⟩
  have hKinv : ∀ K : Subgroup H, IsComponent K →
      ∃ a ∈ K, (∀ k ∈ K, a * k = k * a) ∧ a ≠ 1 ∧ a * a = 1 := by
    intro K hK
    obtain ⟨z, hzK, hzc, hz1⟩ := hK1 K hK
    have hzE : ∀ g ∈ layer H, z * g = g * z := center_of_component_central hK hzK hzc
    have hzT : z ∈ (T : Subgroup H) := hEz z (component_le_layer hK hzK) hzE
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨z, hzT⟩
    have hn' : z ^ 2 ^ n = 1 := congrArg Subtype.val hn
    have hord : orderOf z ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hz1' : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
    have hj1 : j ≠ 0 := by
      rintro rfl
      exact hz1' (by simpa using hj)
    have hord0 : orderOf z ≠ 0 := by rw [hj]; positivity
    have h2dvd : 2 ∣ orderOf z := by rw [hj]; exact dvd_pow_self 2 hj1
    set a : H := z ^ (orderOf z / 2) with ha
    have hao : orderOf a = 2 := orderOf_pow_orderOf_div hord0 h2dvd
    have haK : a ∈ K := Subgroup.pow_mem K hzK _
    have hac : ∀ k ∈ K, a * k = k * a := fun k hk =>
      ((Commute.pow_left (show Commute z k from hzc k hk) _)).eq
    have ha1 : a ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hao
      omega
    have ha2 : a * a = 1 := by
      have : a ^ 2 = 1 := hao ▸ pow_orderOf_eq_one a
      rwa [pow_two] at this
    exact ⟨a, haK, hac, ha1, ha2⟩
  have hRL : R ≤ layer H := by
    obtain ⟨K₀, hK₀⟩ := hcomp
    obtain ⟨a₀, ha₀K, ha₀c, ha₀1, ha₀2⟩ := hKinv K₀ hK₀
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_inf_of_component T hK₀ ha₀K ha₀c ha₀1 ha₀2
    have hxL : ∀ r ∈ R ⊓ layer H, x * r * x⁻¹ ∈ R ⊓ layer H :=
      fun r hr => ⟨hR.x_norm r hr.1, hEn.conj_mem r hr.2 x⟩
    have hyL : ∀ r ∈ R ⊓ layer H, y * r * y⁻¹ ∈ R ⊓ layer H :=
      fun r hr => ⟨hR.y_norm r hr.1, hEn.conj_mem r hr.2 y⟩
    have h82 := hR.lemma82 (inf_le_left) hxL hyL
    unfold Lemma82Concl at h82
    rcases h82 with ⟨hab', -⟩ | ⟨h64', -⟩
    · exfalso
      exact hab (hab' a ⟨hLT ⟨ha.1.1, ha.1.2⟩, ha.1.2⟩ b ⟨hLT ⟨hb.1.1, hb.1.2⟩, hb.1.2⟩)
    · have : R ⊓ layer H = R :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h64', h64])
      intro r hr
      have hr' : r ∈ R ⊓ layer H := by rw [this]; exact hr
      exact hr'.2
  have hZEA : ∀ z ∈ layer H, (∀ g ∈ layer H, z * g = g * z) → z ∈ A := by
    intro z hzE hzc
    have hzT := hEz z hzE hzc
    have hzR : z ∈ R := hLT ⟨hzT, hzE⟩
    have hzcen : (⟨z, hzR⟩ : ↥R) ∈ center ↥R := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hzc g (hRL g.2)).symm
    exact (hcenA _).mp hzcen
  exact ⟨hR, h64, hZ4, hfr, hcom, hLT, hRL, hAc, hcenA, hAE, hZEA, hKinv⟩

end CFSG.GH74.Uniqueness.SU.K.R4
