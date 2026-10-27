module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup

variable {G : Type} [Group G]

namespace FP

@[instance_reducible] def normalizedAction (A H : Subgroup G)
    (hAH : ∀ a ∈ A, ∀ y ∈ H, a * y * a⁻¹ ∈ H) : MulDistribMulAction ↥A ↥H where
  smul a y := ⟨a * y * a⁻¹, hAH a a.2 y y.2⟩
  one_smul y := Subtype.ext (by change (1 : G) * y * 1⁻¹ = y; group)
  mul_smul a b y := Subtype.ext (by
    change (a * b : G) * y * (a * b : G)⁻¹ = a * (b * y * (b : G)⁻¹) * (a : G)⁻¹
    group)
  smul_mul a y z := Subtype.ext (by
    change (a : G) * (y * z) * (a : G)⁻¹ = (a * y * (a : G)⁻¹) * (a * z * (a : G)⁻¹)
    group)
  smul_one a := Subtype.ext (by change (a : G) * 1 * (a : G)⁻¹ = 1; group)

theorem exists_invariant_two_subgroup [Finite G] {A H : Subgroup G} (hA : IsPGroup 2 ↥A)
    (hAH : ∀ a ∈ A, ∀ y ∈ H, a * y * a⁻¹ ∈ H) {x : G} (hxH : x ∈ H)
    (hx : IsPGroup 2 ↥(zpowers x)) :
    ∃ P : Subgroup G, IsPGroup 2 ↥P ∧ (∀ a ∈ A, ∀ y ∈ P, a * y * a⁻¹ ∈ P) ∧
      ∃ k ∈ H, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let := normalizedAction A H hAH
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥H)
    (not_dvd_card_sylow 2 ↥H)
  obtain ⟨Q, hQ⟩ := (hx.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq ↥H Q P
  refine ⟨(P : Subgroup H).map H.subtype, P.isPGroup'.map H.subtype, ?_, ?_⟩
  · rintro a ha _ ⟨y, hy, rfl⟩
    have hfix : (⟨a, ha⟩ : ↥A) • P = P := MulAction.mem_fixedPoints.mp hP ⟨a, ha⟩
    have hmem := Subgroup.smul_mem_pointwise_smul y (⟨a, ha⟩ : ↥A) (P : Subgroup H) hy
    rw [← Sylow.pointwise_smul_def, hfix] at hmem
    exact ⟨_, hmem, rfl⟩
  · have hx₀ : (⟨x, hxH⟩ : ↥H) ∈ (Q : Subgroup H) := hQ (mem_zpowers x)
    have hmem := Subgroup.smul_mem_pointwise_smul (⟨x, hxH⟩ : ↥H) (MulAut.conj c)
      (Q : Subgroup H) hx₀
    rw [← Sylow.coe_subgroup_smul, hc] at hmem
    exact ⟨c, c.2, _, hmem, by simp [MulAut.conj_apply]⟩

end FP

theorem exists_conj_centralized_by_two_group [Finite G] {A N : Subgroup G} {v : G}
    (hv : orderOf v = 2) (hA : IsPGroup 2 ↥A) (hN : Odd (Nat.card ↥N))
    (hvN : ∀ n ∈ N, v * n * v⁻¹ ∈ N) (hAN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (hAv : ∀ a ∈ A, a * v * a⁻¹ * v⁻¹ ∈ N) :
    ∃ n ∈ N, ∀ a ∈ A, a * (n * v * n⁻¹) * a⁻¹ = n * v * n⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvv : v * v = 1 := by
    rw [← sq]
    exact hv ▸ pow_orderOf_eq_one v
  have hvnorm : v ∈ normalizer (N : Set G) := by
    refine mem_normalizer_iff.mpr fun n => ⟨hvN n, fun hn => ?_⟩
    have h := hvN _ hn
    rwa [show v * (v * n * v⁻¹) * v⁻¹ = (v * v) * n * (v * v)⁻¹ by group, hvv, inv_one, one_mul,
      mul_one] at h
  have hzN : zpowers v ≤ normalizer (N : Set G) := zpowers_le.mpr hvnorm
  have hvH : v ∈ N ⊔ zpowers v := mem_sup_right (mem_zpowers v)
  have hAH : ∀ a ∈ A, ∀ y ∈ N ⊔ zpowers v, a * y * a⁻¹ ∈ N ⊔ zpowers v := by
    intro a ha
    have hle : N ⊔ zpowers v ≤ (N ⊔ zpowers v).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le (fun n hn => mem_sup_left (hAN a ha n hn)) (zpowers_le.mpr ?_)
      have e : a * v * a⁻¹ = (a * v * a⁻¹ * v⁻¹) * v := by group
      change a * v * a⁻¹ ∈ N ⊔ zpowers v
      rw [e]
      exact mul_mem (mem_sup_left (hAv a ha)) hvH
    exact fun y hy => hle hy
  have h2 : IsPGroup 2 ↥(zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  obtain ⟨P, hP2, hPinv, k, hkH, hkP⟩ := FP.exists_invariant_two_subgroup hA hAH hvH h2
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N (zpowers v) hzN] at hkH
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.mp hkH
  have hyv : y * v * y⁻¹ = v := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (Commute.refl v) m).mul_inv_cancel
  have hw : n * v * n⁻¹ ∈ P := by
    have e : n * y * v * (n * y)⁻¹ = n * v * n⁻¹ := by
      calc n * y * v * (n * y)⁻¹ = n * (y * v * y⁻¹) * n⁻¹ := by group
        _ = n * v * n⁻¹ := by rw [hyv]
    rwa [e] at hkP
  refine ⟨n, hn, fun a ha => ?_⟩
  have hu : a * (n * v * n⁻¹) * a⁻¹ ∈ P := hPinv a ha _ hw
  have hNu : a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹ ∈ N := by
    have hn' := hAN a ha n hn
    have e : a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹ =
        (a * n * a⁻¹) * (a * v * a⁻¹ * v⁻¹) * (v * ((a * n * a⁻¹)⁻¹ * n) * v⁻¹) * n⁻¹ := by group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn' (hAv a ha))
      (hvN _ (N.mul_mem (N.inv_mem hn') hn))) (N.inv_mem hn)
  have hdisj : Disjoint P N := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP2
    rw [hm]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hN)
  have h1 : a * (n * v * n⁻¹) * a⁻¹ * (n * v * n⁻¹)⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hdisj (P.mul_mem hu (P.inv_mem hw)) hNu
  exact mul_inv_eq_one.mp h1

end CFSG.GH74.GLS.C3.Layer1.U1a
