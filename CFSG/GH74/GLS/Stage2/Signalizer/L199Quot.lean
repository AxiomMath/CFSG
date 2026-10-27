module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L199

open Subgroup
open scoped commutatorElement

structure SigData (X : Type*) [Group X] (z : X) (r : ℕ) (R : Subgroup X) : Prop where
  orderOf_z : orderOf z = 2
  prime : r.Prime
  ne_two : r ≠ 2
  pgroup : IsPGroup r R
  inv : ∀ c ∈ centralizer ({z} : Set X), c ∈ normalizer (R : Set X)
  comm : ⁅R, zpowers z⁆ = R

theorem exists_lift_centralizer {A : Type*} [Group A] [Finite A] (N : Subgroup A) [N.Normal]
    (hN : Odd (Nat.card ↥N)) {z : A} (hz : z * z = 1) {a : A}
    (h : (QuotientGroup.mk z : A ⧸ N) * QuotientGroup.mk a =
      QuotientGroup.mk a * QuotientGroup.mk z) :
    ∃ c : A, c * z = z * c ∧ (QuotientGroup.mk c : A ⧸ N) = QuotientGroup.mk a := by
  classical
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let T : Type _ := {x : A // (QuotientGroup.mk x : A ⧸ N) = QuotientGroup.mk a}
  have : Finite T := inferInstance
  have : Fintype T := Fintype.ofFinite T
  let f : T → T := fun x => ⟨z * x.1 * z⁻¹, by
    have hx := x.2
    show (QuotientGroup.mk (z * x.1 * z⁻¹) : A ⧸ N) = QuotientGroup.mk a
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hx, h, QuotientGroup.mk_inv,
      mul_inv_cancel_right]⟩
  have hf : Function.Involutive f := by
    intro x
    apply Subtype.ext
    show z * (z * x.1 * z⁻¹) * z⁻¹ = x.1
    rw [hzi]
    calc z * (z * x.1 * z) * z = (z * z) * x.1 * (z * z) := by group
      _ = x.1 := by rw [hz]; group
  let σ : Equiv.Perm T := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [σ, pow_two, hf x]
  have hcard : Fintype.card T = Nat.card ↥N := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun x => ⟨a⁻¹ * x.1, ?_⟩, fun n => ⟨a * n.1, ?_⟩, ?_, ?_⟩
    · have hx := x.2
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx, inv_mul_cancel]
    · show (QuotientGroup.mk (a * n.1) : A ⧸ N) = QuotientGroup.mk a
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n.1).mpr n.2, mul_one]
    · intro x; apply Subtype.ext; simp
    · intro n; apply Subtype.ext; simp
  have hnd : ¬ 2 ∣ Fintype.card T := by
    rw [hcard]
    exact (Nat.not_even_iff_odd.mpr hN) ∘ even_iff_two_dvd.mpr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hσ
  refine ⟨x.1, ?_, x.2⟩
  have : f x = x := hx
  have h2 := congrArg Subtype.val this
  simp only [f] at h2
  rw [hzi] at h2
  calc x.1 * z = (z * x.1 * z) * z := by rw [h2]
    _ = z * x.1 := by
      calc (z * x.1 * z) * z = z * x.1 * (z * z) := by group
        _ = z * x.1 := by rw [hz]; group

theorem mul_self_eq_one_of_orderOf_eq_two {X : Type*} [Group X] {z : X} (hz : orderOf z = 2) :
    z * z = 1 := by
  have := pow_orderOf_eq_one z
  rw [hz] at this
  simpa [pow_two] using this

theorem SigData.quotient {X : Type*} [Group X] [Finite X] {z : X} {r : ℕ} {R : Subgroup X}
    (h : SigData X z r R) (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card ↥N)) :
    SigData (X ⧸ N) (QuotientGroup.mk z) r (R.map (QuotientGroup.mk' N)) := by
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_z
  refine ⟨?_, h.prime, h.ne_two, h.pgroup.map _, ?_, ?_⟩
  · have h1 : (QuotientGroup.mk z : X ⧸ N) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, pow_two, hz2]; rfl
    have h2 : (QuotientGroup.mk z : X ⧸ N) ≠ 1 := by
      intro h'
      have hzN : z ∈ N := (QuotientGroup.eq_one_iff z).1 h'
      have : orderOf z ∣ Nat.card ↥N := Subgroup.orderOf_dvd_natCard N hzN
      rw [h.orderOf_z] at this
      exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 this)
    exact orderOf_eq_prime h1 h2
  · intro cbar hc
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cbar
    have hc' : (QuotientGroup.mk z : X ⧸ N) * QuotientGroup.mk c =
        QuotientGroup.mk c * QuotientGroup.mk z :=
      (Subgroup.mem_centralizer_singleton_iff.1 hc).symm
    obtain ⟨c₀, hc₀, hc₀a⟩ := exists_lift_centralizer N hN hz2 hc'
    have hcz : c₀ ∈ centralizer ({z} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.2 hc₀
    have hn := h.inv c₀ hcz
    rw [← hc₀a]
    exact Subgroup.le_normalizer_map (QuotientGroup.mk' N) ⟨c₀, hn, rfl⟩
  · have hmk : (QuotientGroup.mk z : X ⧸ N) = QuotientGroup.mk' N z := rfl
    rw [hmk, ← MonoidHom.map_zpowers, ← Subgroup.map_commutator, h.comm]

end CFSG.GH74.GLS.Stage2.Signalizer.L199
