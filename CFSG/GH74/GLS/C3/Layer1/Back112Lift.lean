module

public import CFSG.GH74.GLS.C3.Layer1.U1a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG.GH74.GLS.C3.Layer1.U1a
open scoped commutatorElement

theorem exists_centralizing_mem_coset {G : Type} [Group G] [Finite G] {K Q : Subgroup G}
    (hQ2 : IsPGroup 2 ↥Q) (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hQt : ∀ q ∈ Q, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K) {k : G} (hk : k ∈ K) :
    ∃ c ∈ K, (∀ q ∈ Q, c * q = q * c) ∧ k⁻¹ * c ∈ pPrimeCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set G := {x | x ∈ K ∧ k⁻¹ * x ∈ pPrimeCoreOf 2 K}
  have hS : ∀ q ∈ Q, ∀ x ∈ S, q * x * q⁻¹ ∈ S := by
    intro q hq x hx
    obtain ⟨hxK, hxO⟩ := hx
    refine ⟨hQK q hq x hxK, ?_⟩
    have hw : (⁅k, q⁆)⁻¹ ∈ pPrimeCoreOf 2 K := (pPrimeCoreOf 2 K).inv_mem (hQt q hq k hk)
    have h1 := TwoThin.pPrimeCoreOf_normalized K (K.inv_mem hk) hw
    have h2 := pPrimeCoreOf_norm hQK hq hxO
    have h3 := (pPrimeCoreOf 2 K).mul_mem h1 h2
    convert h3 using 1
    simp only [commutatorElement_def]
    group
  let inst : MulAction ↥Q ↥S :=
    { smul := fun q x => ⟨(q : G) * x * (q : G)⁻¹, hS q q.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : ↥Q) : G) * x * ((1 : ↥Q) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : ↥Q) : G) * x * ((a * b : ↥Q) : G)⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ 2 ∣ Nat.card ↥S := by
    let e : ↥(pPrimeCoreOf 2 K) ≃ ↥S :=
      { toFun := fun o => ⟨k * o, K.mul_mem hk (TwoThin.pPrimeCoreOf_le K o.2), by simp⟩
        invFun := fun x => ⟨k⁻¹ * x, x.2.2⟩
        left_inv := fun o => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    rw [← Nat.card_congr e]
    exact fun hd => (Nat.not_even_iff_odd.2 (TwoThin.card_pPrimeCoreOf_odd K))
      (even_iff_two_dvd.2 hd)
  obtain ⟨⟨x, hxK, hxO⟩, hfix⟩ := hQ2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hcard
  refine ⟨x, hxK, fun q hq => ?_, hxO⟩
  have h : q * x * q⁻¹ = x := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hfix ⟨q, hq⟩)
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem exists_conj_centralizing {G : Type} [Group G] [Finite G] {K Q : Subgroup G}
    (hQ2 : IsPGroup 2 ↥Q)
    (hQK : ∀ q ∈ Q, ∀ k ∈ K, q * k * q⁻¹ ∈ K)
    (hQt : ∀ q ∈ Q, ∀ k ∈ K, ⁅k, q⁆ ∈ pPrimeCoreOf 2 K)
    {p z : G} (hp : p ∈ K) (hz : z ∈ K) (hpo : orderOf p = 2) (hzo : orderOf z = 2)
    (hpQ : ∀ q ∈ Q, p * q = q * p) (hzQ : ∀ q ∈ Q, z * q = q * z)
    (hbar : ∃ k ∈ K, k⁻¹ * p * k * z⁻¹ ∈ pPrimeCoreOf 2 K) :
    ∃ h ∈ K, (∀ q ∈ Q, h * q = q * h) ∧ h⁻¹ * p * h = z := by
  have _ := hz
  obtain ⟨k, hk, hkO⟩ := hbar
  obtain ⟨c, hcK, hcQ, hcO⟩ := exists_centralizing_mem_coset hQ2 hQK hQt hk
  have hZ : ∀ {g : G}, g ∈ centralizer (Q : Set G) ↔ ∀ q ∈ Q, g * q = q * g := fun {g} => by
    rw [mem_centralizer_iff]
    exact ⟨fun h q hq => (h q hq).symm, fun h q hq => (h q hq).symm⟩
  have hcZ : c ∈ centralizer (Q : Set G) := hZ.2 hcQ
  have hpZ : p ∈ centralizer (Q : Set G) := hZ.2 hpQ
  have hzZ : z ∈ centralizer (Q : Set G) := hZ.2 hzQ
  have hp2 : p * p = 1 := by
    have := pow_orderOf_eq_one p
    rwa [hpo, sq] at this
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, sq] at this
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have ho₁ : c⁻¹ * k ∈ pPrimeCoreOf 2 K := by
    simpa using (pPrimeCoreOf 2 K).inv_mem hcO
  have huK : c⁻¹ * p * c ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hcK) hp) hcK
  have hn : c⁻¹ * p * c * z⁻¹ ∈ pPrimeCoreOf 2 K := by
    have h1 := TwoThin.pPrimeCoreOf_normalized K huK ho₁
    have h2 := (pPrimeCoreOf 2 K).mul_mem
      ((pPrimeCoreOf 2 K).inv_mem ((pPrimeCoreOf 2 K).mul_mem ((pPrimeCoreOf 2 K).inv_mem ho₁) h1))
      hkO
    convert h2 using 1
    group
  obtain ⟨n, hnd⟩ : ∃ n : G, n = c⁻¹ * p * c * z⁻¹ := ⟨_, rfl⟩
  rw [← hnd] at hn
  have hnu : c⁻¹ * p * c = n * z := by rw [hnd]; group
  have hnZ : n ∈ centralizer (Q : Set G) := by
    rw [hnd]
    exact mul_mem (mul_mem (mul_mem (inv_mem hcZ) hpZ) hcZ) (inv_mem hzZ)
  have hupp : n * z * (n * z) = 1 := by
    rw [← hnu]
    calc c⁻¹ * p * c * (c⁻¹ * p * c) = c⁻¹ * (p * p) * c := by group
      _ = 1 := by rw [hp2]; group
  have hznz : z * n * z⁻¹ = n⁻¹ := by
    rw [hzinv]
    calc z * n * z = n⁻¹ * (n * z * (n * z)) := by group
      _ = n⁻¹ := by rw [hupp, mul_one]
  obtain ⟨j, hj⟩ : Odd (orderOf n) :=
    Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd K) (Subgroup.orderOf_dvd_natCard _ hn)
  obtain ⟨r, hr⟩ : ∃ r : G, r = n ^ (j + 1) := ⟨_, rfl⟩
  have hrr : r * r = n := by
    calc r * r = n ^ (2 * j + 1) * n := by
          rw [hr, ← pow_add, ← pow_succ]
          congr 1
          omega
      _ = n := by rw [← hj, pow_orderOf_eq_one, one_mul]
  have hzr : z * r * z⁻¹ = r⁻¹ := by
    rw [hr, ← conj_pow, hznz, inv_pow]
  have hrO : r ∈ pPrimeCoreOf 2 K := by rw [hr]; exact (pPrimeCoreOf 2 K).pow_mem hn _
  have hrZ : r ∈ centralizer (Q : Set G) := by rw [hr]; exact pow_mem hnZ _
  refine ⟨c * r, K.mul_mem hcK (TwoThin.pPrimeCoreOf_le K hrO), fun q hq => ?_, ?_⟩
  · exact hZ.1 (mul_mem hcZ hrZ) q hq
  · have hzr' : z * r = r⁻¹ * z := by
      rw [mul_inv_eq_iff_eq_mul] at hzr
      exact hzr
    calc (c * r)⁻¹ * p * (c * r) = r⁻¹ * (c⁻¹ * p * c) * r := by group
      _ = r⁻¹ * (n * z) * r := by rw [hnu]
      _ = r⁻¹ * (r * r * z) * r := by rw [hrr]
      _ = r * (z * r) := by group
      _ = z := by rw [hzr']; group

end CFSG.GH74.GLS.C3.Layer1.Back
