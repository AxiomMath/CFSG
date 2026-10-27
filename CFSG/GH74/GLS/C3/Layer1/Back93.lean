module

public import CFSG.GH74.GLS.C3.Layer1.P34Proj

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem exists_central_involution [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQne : Q ≠ ⊥) :
    ∃ u ∈ Q, u ≠ 1 ∧ u * u = 1 ∧ ∀ q ∈ Q, q * u = u * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  have hZ : Nontrivial ↥(Subgroup.center ↥Q) := hQ.center_nontrivial
  have hZp : IsPGroup 2 ↥(Subgroup.center ↥Q) := hQ.to_subgroup _
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center ↥Q) := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card ↥(Subgroup.center ↥Q) = 1 := by simpa using hn
      have := Nat.card_eq_one_iff_unique.1 this
      exact not_subsingleton _ this.1
    rw [hn]; exact dvd_pow_self 2 hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Q)) 2 h2
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; omega
  have hz2 : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    rwa [sq] at this
  refine ⟨((z : ↥Q) : G), (z : ↥Q).2, fun h => hz1 ?_, ?_, fun q hq => ?_⟩
  · apply Subtype.ext; apply Subtype.ext; simpa using h
  · have := congrArg (fun w : ↥(Subgroup.center ↥Q) => (((w : ↥Q)) : G)) hz2
    simpa using this
  · have hc := (Subgroup.mem_center_iff.1 z.2) ⟨q, hq⟩
    exact congrArg Subtype.val hc

theorem exists_mul_of_mem_sup_of_commute {P Q : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) {v : G} (hv : v ∈ P ⊔ Q) :
    ∃ p ∈ P, ∃ q ∈ Q, v = p * q := by
  have hQN : Q ≤ normalizer (P : Set G) := P34.W_le_normalizer_of (fun w hw a ha => by
    have e : w * a * w⁻¹ = a := by rw [← hcomm a ha w hw]; group
    rw [e]; exact ha)
  have hv' : v ∈ ((P ⊔ Q : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Q hQN] at hv'
  obtain ⟨p, hp, q, hq, hpq⟩ := hv'
  exact ⟨p, hp, q, hq, hpq.symm⟩

theorem eq_of_mul_eq_of_inf_bot {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥) {p p' q q' : G} (hp : p ∈ P)
    (hp' : p' ∈ P) (hq : q ∈ Q) (hq' : q' ∈ Q) (h : p * q = p' * q') : p = p' ∧ q = q' := by
  have h1 : p'⁻¹ * p = q' * q⁻¹ := by
    calc p'⁻¹ * p = p'⁻¹ * (p * q) * q⁻¹ := by group
      _ = p'⁻¹ * (p' * q') * q⁻¹ := by rw [h]
      _ = q' * q⁻¹ := by group
  have hm : p'⁻¹ * p ∈ P ⊓ Q := ⟨P.mul_mem (P.inv_mem hp') hp, h1 ▸ Q.mul_mem hq' (Q.inv_mem hq)⟩
  rw [hPQ, Subgroup.mem_bot] at hm
  have hpp : p = p' := by
    calc p = p' * (p'⁻¹ * p) := by group
      _ = p' := by rw [hm, mul_one]
  refine ⟨hpp, ?_⟩
  rw [hpp] at h
  exact mul_left_cancel h

@[expose] def projQ (P Q V₁ : Subgroup G) (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) : Subgroup G where
  carrier := {q | q ∈ Q ∧ ∃ v ∈ V₁, ∃ p ∈ P, v = p * q}
  one_mem' := ⟨Q.one_mem, 1, V₁.one_mem, 1, P.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haQ, v, hv, p, hp, hva⟩ ⟨hbQ, w, hw, p', hp', hwb⟩
    refine ⟨Q.mul_mem haQ hbQ, v * w, V₁.mul_mem hv hw, p * p', P.mul_mem hp hp', ?_⟩
    rw [hva, hwb]
    calc p * a * (p' * b) = p * (a * p') * b := by group
      _ = p * (p' * a) * b := by rw [← hcomm p' hp' a haQ]
      _ = (p * p') * (a * b) := by group
  inv_mem' := by
    rintro a ⟨haQ, v, hv, p, hp, hva⟩
    refine ⟨Q.inv_mem haQ, v⁻¹, V₁.inv_mem hv, p⁻¹, P.inv_mem hp, ?_⟩
    rw [hva]
    calc (p * a)⁻¹ = a⁻¹ * p⁻¹ := by group
      _ = p⁻¹ * a⁻¹ := (hcomm p⁻¹ (P.inv_mem hp) a⁻¹ (Q.inv_mem haQ)).symm

variable [Finite G]

theorem q_le_of_projections {P Q V₁ Mg : Subgroup G}
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hPQ : P ⊓ Q = ⊥)
    (hQ2 : IsPGroup 2 Q) (hQne : Q ≠ ⊥)
    (hV₁R : V₁ ≤ P ⊔ Q) (hV₁ab : ∀ u ∈ V₁, ∀ v ∈ V₁, u * v = v * u)
    (hV₁2 : ∀ u ∈ V₁, u * u = 1) (hV₁ne : V₁ ≠ ⊥)
    (hcent : ∀ v ∈ V₁, v ≠ 1 → ∀ c : G, c * v = v * c → c ∈ Mg)
    (hmax : ∀ U : Subgroup G, U ≤ Q → U ≤ Mg → (∀ u ∈ U, ∀ v ∈ U, u * v = v * u) →
      (∀ u ∈ U, u * u = 1) → Nat.card ↥U ≤ Nat.card ↥V₁) :
    Q ≤ Mg := by
  by_cases hP1 : ∃ v ∈ V₁, v ∈ P ∧ v ≠ 1
  ·
    obtain ⟨v, hvV, hvP, hv1⟩ := hP1
    intro q hq
    exact hcent v hvV hv1 q (hcomm v hvP q hq).symm
  push Not at hP1
  set V₀ := projQ P Q V₁ hcomm with hV₀
  have hV₀Q : V₀ ≤ Q := fun q hq => hq.1
  have hV₀ab : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := by
    rintro a ⟨haQ, v, hv, p, hp, hva⟩ b ⟨hbQ, w, hw, p', hp', hwb⟩
    have hvw := hV₁ab v hv w hw
    rw [hva, hwb] at hvw
    have e1 : p * a * (p' * b) = (p * p') * (a * b) := by
      calc p * a * (p' * b) = p * (a * p') * b := by group
        _ = p * (p' * a) * b := by rw [← hcomm p' hp' a haQ]
        _ = (p * p') * (a * b) := by group
    have e2 : p' * b * (p * a) = (p' * p) * (b * a) := by
      calc p' * b * (p * a) = p' * (b * p) * a := by group
        _ = p' * (p * b) * a := by rw [← hcomm p hp b hbQ]
        _ = (p' * p) * (b * a) := by group
    rw [e1, e2] at hvw
    exact (eq_of_mul_eq_of_inf_bot hPQ (P.mul_mem hp hp') (P.mul_mem hp' hp) (Q.mul_mem haQ hbQ)
      (Q.mul_mem hbQ haQ) hvw).2
  have hV₀2 : ∀ a ∈ V₀, a * a = 1 := by
    rintro a ⟨haQ, v, hv, p, hp, hva⟩
    have h1 := hV₁2 v hv
    rw [hva] at h1
    have e : p * a * (p * a) = (p * p) * (a * a) := by
      calc p * a * (p * a) = p * (a * p) * a := by group
        _ = p * (p * a) * a := by rw [← hcomm p hp a haQ]
        _ = (p * p) * (a * a) := by group
    rw [e] at h1
    exact (eq_of_mul_eq_of_inf_bot hPQ (P.mul_mem hp hp) P.one_mem (Q.mul_mem haQ haQ) Q.one_mem
      (by rw [h1, one_mul])).2
  have hV₀V₁ : ∀ a ∈ V₀, ∀ v ∈ V₁, a * v = v * a := by
    rintro a haV v hv
    obtain ⟨p, hp, q, hq, hvpq⟩ := exists_mul_of_mem_sup_of_commute hcomm (hV₁R hv)
    have hqV₀ : q ∈ V₀ := ⟨hq, v, hv, p, hp, hvpq⟩
    rw [hvpq]
    calc a * (p * q) = (a * p) * q := by group
      _ = (p * a) * q := by rw [(hcomm p hp a haV.1).symm]
      _ = p * (a * q) := by group
      _ = p * (q * a) := by rw [hV₀ab a haV q hqV₀]
      _ = p * q * a := by group
  have hcardV : Nat.card ↥V₁ ≤ Nat.card ↥V₀ := by
    have hdec : ∀ v : ↥V₁, ∃ q : ↥V₀, ∃ p ∈ P, (v : G) = p * q := by
      intro v
      obtain ⟨p, hp, q, hq, hvpq⟩ := exists_mul_of_mem_sup_of_commute hcomm (hV₁R v.2)
      exact ⟨⟨q, hq, v, v.2, p, hp, hvpq⟩, p, hp, hvpq⟩
    choose f hf using hdec
    refine Nat.card_le_card_of_injective f ?_
    intro v w hvw
    obtain ⟨p, hp, hvp⟩ := hf v
    obtain ⟨p', hp', hwp⟩ := hf w
    have hpp : p * (f v : G) = p' * (f v : G) → p = p' := fun h => mul_right_cancel h
    have hfv : (f w : G) = f v := by rw [hvw]
    have h1 : (v : G) * (w : G)⁻¹ = p * p'⁻¹ := by
      rw [hvp, hwp, hfv]
      calc p * (f v : G) * (p' * (f v : G))⁻¹ = p * ((f v : G) * (f v : G)⁻¹) * p'⁻¹ := by
            calc p * (f v : G) * (p' * (f v : G))⁻¹
                = p * (f v : G) * ((f v : G)⁻¹ * p'⁻¹) := by group
              _ = p * ((f v : G) * (f v : G)⁻¹) * p'⁻¹ := by group
        _ = p * p'⁻¹ := by group
    have hmemP : (v : G) * (w : G)⁻¹ ∈ P := by rw [h1]; exact P.mul_mem hp (P.inv_mem hp')
    have hmemV : (v : G) * (w : G)⁻¹ ∈ V₁ := V₁.mul_mem v.2 (V₁.inv_mem w.2)
    have h2 : (v : G) * (w : G)⁻¹ = 1 := hP1 _ hmemV hmemP
    apply Subtype.ext
    calc (v : G) = ((v : G) * (w : G)⁻¹) * w := by group
      _ = w := by rw [h2, one_mul]
  obtain ⟨u, huQ, hu1, hu2, huc⟩ := exists_central_involution hQ2 hQne
  have huV₀ : u ∈ V₀ := by
    by_contra hu
    have hu_zp : ∀ k : ℤ, u ^ k = 1 ∨ u ^ k = u := fun k => by
      have hsq : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu2
      obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
      · left; rw [hj, zpow_mul, hsq, one_zpow]
      · right; rw [hj, zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]
    have hzc : ∀ a ∈ V₀, ∀ w ∈ zpowers u, a * w = w * a := by
      intro a ha w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have hcu : Commute a u := huc a ha.1
      exact (hcu.zpow_right k).eq
    have huV : ∀ v ∈ V₁, u * v = v * u := by
      intro v hv
      obtain ⟨p, hp, q, hq, hvpq⟩ := exists_mul_of_mem_sup_of_commute hcomm (hV₁R hv)
      rw [hvpq]
      calc u * (p * q) = (u * p) * q := by group
        _ = (p * u) * q := by rw [(hcomm p hp u huQ).symm]
        _ = p * (u * q) := by group
        _ = p * (q * u) := by rw [(huc q hq).symm]
        _ = p * q * u := by group
    have hzN : zpowers u ≤ normalizer (V₀ : Set G) := P34.W_le_normalizer_of (fun w hw a ha => by
      have e : w * a * w⁻¹ = a := by rw [← hzc a ha w hw]; group
      rw [e]; exact ha)
    have hUcoe : ((V₀ ⊔ zpowers u : Subgroup G) : Set G) = (V₀ : Set G) * (zpowers u : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left V₀ (zpowers u) hzN
    obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
      by_contra hno
      push Not at hno
      exact hV₁ne (eq_bot_iff.2 fun v hv => (Subgroup.mem_bot).2 (hno v hv))
    have hUMg : V₀ ⊔ zpowers u ≤ Mg := by
      intro c hc
      have hc' : c ∈ ((V₀ ⊔ zpowers u : Subgroup G) : Set G) := hc
      rw [hUcoe] at hc'
      obtain ⟨a, ha, w, hw, hcaw⟩ := hc'
      rw [← hcaw]
      refine hcent v₀ hv₀V hv₀1 _ ?_
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have h1 : a * v₀ = v₀ * a := hV₀V₁ a ha v₀ hv₀V
      have h2 : u ^ k * v₀ = v₀ * u ^ k := ((Commute.zpow_left (huV v₀ hv₀V) k).eq)
      calc a * u ^ k * v₀ = a * (u ^ k * v₀) := by group
        _ = a * (v₀ * u ^ k) := by rw [h2]
        _ = (a * v₀) * u ^ k := by group
        _ = (v₀ * a) * u ^ k := by rw [h1]
        _ = v₀ * (a * u ^ k) := by group
    have hUQ : V₀ ⊔ zpowers u ≤ Q := sup_le hV₀Q (Subgroup.zpowers_le.2 huQ)
    have hUab : ∀ c ∈ V₀ ⊔ zpowers u, ∀ d ∈ V₀ ⊔ zpowers u, c * d = d * c := by
      intro c hc d hd
      have hc' : c ∈ ((V₀ ⊔ zpowers u : Subgroup G) : Set G) := hc
      have hd' : d ∈ ((V₀ ⊔ zpowers u : Subgroup G) : Set G) := hd
      rw [hUcoe] at hc' hd'
      obtain ⟨a, ha, w, hw, rfl⟩ := hc'
      obtain ⟨a', ha', w', hw', rfl⟩ := hd'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hw'
      have hww : u ^ k * u ^ k' = u ^ k' * u ^ k := (Commute.zpow_zpow_self u k k').eq
      calc a * u ^ k * (a' * u ^ k') = a * (u ^ k * a') * u ^ k' := by group
        _ = a * (a' * u ^ k) * u ^ k' := by rw [← hzc a' ha' _ (mem_zpowers_iff.2 ⟨k, rfl⟩)]
        _ = (a * a') * (u ^ k * u ^ k') := by group
        _ = (a' * a) * (u ^ k' * u ^ k) := by rw [hV₀ab a ha a' ha', hww]
        _ = a' * (a * u ^ k') * u ^ k := by group
        _ = a' * (u ^ k' * a) * u ^ k := by rw [hzc a ha _ (mem_zpowers_iff.2 ⟨k', rfl⟩)]
        _ = a' * u ^ k' * (a * u ^ k) := by group
    have hUsq : ∀ c ∈ V₀ ⊔ zpowers u, c * c = 1 := by
      intro c hc
      have hc' : c ∈ ((V₀ ⊔ zpowers u : Subgroup G) : Set G) := hc
      rw [hUcoe] at hc'
      obtain ⟨a, ha, w, hw, rfl⟩ := hc'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
      have h1 := hV₀2 a ha
      have hk : u ^ k * u ^ k = 1 := by
        rcases hu_zp k with h | h
        · rw [h, one_mul]
        · rw [h]; exact hu2
      calc a * u ^ k * (a * u ^ k) = (a * a) * (u ^ k * u ^ k) := by
            calc a * u ^ k * (a * u ^ k) = a * (u ^ k * a) * u ^ k := by group
              _ = a * (a * u ^ k) * u ^ k := by rw [← hzc a ha _ (mem_zpowers_iff.2 ⟨k, rfl⟩)]
              _ = (a * a) * (u ^ k * u ^ k) := by group
        _ = 1 := by rw [h1, hk, one_mul]
    have hcardU : Nat.card ↥(V₀ ⊔ zpowers u) = 2 * Nat.card ↥V₀ := by
      have h1 := P34.card_mul_inf V₀ (zpowers u)
      have hinf : V₀ ⊓ zpowers u = ⊥ := by
        refine eq_bot_iff.2 (fun w hw => ?_)
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw.2
        rcases hu_zp k with h | h
        · rw [h]; exact Subgroup.one_mem _
        · exfalso; apply hu; rw [← h]; exact hw.1
      have hset : Nat.card ↥((V₀ : Set G) * (zpowers u : Set G)) = Nat.card ↥(V₀ ⊔ zpowers u) := by
        rw [← hUcoe]; rfl
      rw [hset, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers,
        orderOf_eq_prime (by rw [sq]; exact hu2) hu1] at h1
      rw [h1]; ring
    have := hmax _ hUQ hUMg hUab hUsq
    rw [hcardU] at this
    have hpos : 0 < Nat.card ↥V₀ := Nat.card_pos
    omega
  obtain ⟨-, v₁, hv₁V, p₁, hp₁, hv₁⟩ := huV₀
  have hv₁1 : v₁ ≠ 1 := by
    intro h
    rw [h] at hv₁
    have := (eq_of_mul_eq_of_inf_bot hPQ hp₁ P.one_mem huQ Q.one_mem (by rw [← hv₁, mul_one])).2
    exact hu1 this
  intro q hq
  refine hcent v₁ hv₁V hv₁1 q ?_
  rw [hv₁]
  calc q * (p₁ * u) = (q * p₁) * u := by group
    _ = (p₁ * q) * u := by rw [(hcomm p₁ hp₁ q hq).symm]
    _ = p₁ * (q * u) := by group
    _ = p₁ * (u * q) := by rw [huc q hq]
    _ = p₁ * u * q := by group

end CFSG.GH74.GLS.C3.Layer1.Back
