module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.SolomonRed

open Subgroup

variable {K : Type*} [Group K]

theorem mem_zpowers_iff_of_mul_self_eq_one {z : K} (hz : z * z = 1) {c : K} :
    c ∈ zpowers z ↔ c = 1 ∨ c = z := by
  constructor
  · intro hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
      rw [hm, zpow_mul, h2, one_zpow]
    · right
      obtain ⟨m, hm⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
      rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  · rintro (h | h)
    · exact h ▸ one_mem _
    · exact h ▸ mem_zpowers z

theorem conj_conj_of_mul_self_eq_one {z : K} (hz : z * z = 1) (x : K) :
    z * (z * x * z⁻¹) * z⁻¹ = x := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  rw [hzi]
  calc z * (z * x * z) * z = (z * z) * x * (z * z) := by group
    _ = x := by rw [hz]; simp

theorem conj_eq_self_iff {z x : K} : z * x * z⁻¹ = x ↔ z * x = x * z := by
  constructor
  · intro h
    calc z * x = (z * x * z⁻¹) * z := by group
      _ = x * z := by rw [h]
  · intro h
    rw [h]
    group

theorem fixedPointFree_inverts [Finite K] (σ : K ≃* K) (hσ : ∀ x, σ (σ x) = x) {W : Subgroup K}
    (hW : ∀ w ∈ W, σ w ∈ W) (hfix : ∀ w ∈ W, σ w = w → w = 1) :
    ∀ w ∈ W, σ w = w⁻¹ := by
  let f : W → W := fun w => ⟨(w : K)⁻¹ * σ w, mul_mem (inv_mem w.2) (hW w w.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (a : K)⁻¹ * σ a = (b : K)⁻¹ * σ b := congrArg Subtype.val hab
    have h1' : σ (b : K) = (b : K) * (a : K)⁻¹ * σ (a : K) := by
      calc σ (b : K) = (b : K) * ((b : K)⁻¹ * σ (b : K)) := by group
        _ = (b : K) * ((a : K)⁻¹ * σ (a : K)) := by rw [← h1]
        _ = (b : K) * (a : K)⁻¹ * σ (a : K) := by group
    have h2 : σ ((b : K) * (a : K)⁻¹) = (b : K) * (a : K)⁻¹ := by
      rw [map_mul, map_inv, h1']
      group
    have h6 : (b : K) * (a : K)⁻¹ = 1 := hfix _ (mul_mem b.2 (inv_mem a.2)) h2
    exact Subtype.ext (mul_inv_eq_one.1 h6).symm
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  have hu' : (u : K)⁻¹ * σ u = w := congrArg Subtype.val hu
  rw [← hu', map_mul, map_inv, hσ, mul_inv_rev, inv_inv]

theorem fixedPointFree_commute [Finite K] (σ : K ≃* K) (hσ : ∀ x, σ (σ x) = x) {W : Subgroup K}
    (hW : ∀ w ∈ W, σ w ∈ W) (hfix : ∀ w ∈ W, σ w = w → w = 1) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  have hinv := fixedPointFree_inverts σ hσ hW hfix
  have h1 : σ (a * b) = (a * b)⁻¹ := hinv _ (mul_mem ha hb)
  rw [map_mul, hinv a ha, hinv b hb, mul_inv_rev] at h1
  have h4 := congrArg (·⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h4
  exact h4.symm

theorem fixedPointFree_commute_of_mul_self_eq_one [Finite K] {z : K} (hz : z * z = 1)
    {W : Subgroup K} (hW : ∀ w ∈ W, z * w * z⁻¹ ∈ W)
    (hfix : ∀ w ∈ W, z * w = w * z → w = 1) : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
  fixedPointFree_commute (MulAut.conj z) (fun x => by
    simpa [MulAut.conj_apply] using conj_conj_of_mul_self_eq_one hz x) hW
    (fun w hw h => hfix w hw (conj_eq_self_iff.1 h))

theorem inf_eq_bot_or_le_of_simple {B W : Subgroup K} (hB : IsSimpleGroup ↥B)
    (hnorm : ∀ b ∈ B, ∀ x ∈ W, b * x * b⁻¹ ∈ W) : B ⊓ W = ⊥ ∨ B ≤ W := by
  have hN : ((B ⊓ W).subgroupOf B).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, mem_inf] at hn ⊢
    exact ⟨(g * n * g⁻¹ : ↥B).2, hnorm g g.2 n hn.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((B ⊓ W).subgroupOf B) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : B) ∈ (B ⊓ W).subgroupOf B := hx
    rw [h, mem_bot] at this
    exact mem_bot.2 (congrArg Subtype.val this)
  · right
    intro b hb
    have : (⟨b, hb⟩ : B) ∈ (B ⊓ W).subgroupOf B := by rw [h]; trivial
    exact (mem_subgroupOf.1 this).2

theorem not_isPGroup_of_simple_nonabelian {p : ℕ} [Fact p.Prime] [Finite K] {B : Subgroup K}
    (hB : IsSimpleGroup ↥B) (hnab : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) : ¬ IsPGroup p ↥B := by
  intro hp
  have : Nontrivial ↥B := hB.toNontrivial
  have hcn := hp.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center ↥B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥B) with h | h
  · apply hc1
    have h' : (c : ↥B) ∈ (⊥ : Subgroup ↥B) := by rw [← h]; exact c.2
    exact Subtype.ext (mem_bot.1 h')
  · obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have hmem : (⟨a, ha⟩ : ↥B) ∈ Subgroup.center ↥B := by rw [h]; trivial
    exact hab (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hmem ⟨b, hb⟩).symm))

theorem eq_one_of_commute_of_simple {B : Subgroup K} (hB : IsSimpleGroup ↥B)
    (hnab : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) {x : K} (hx : x ∈ B)
    (hc : ∀ b ∈ B, b * x = x * b) : x = 1 := by
  have hmem : (⟨x, hx⟩ : ↥B) ∈ Subgroup.center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥B) with h | h
  · have h' : (⟨x, hx⟩ : ↥B) ∈ (⊥ : Subgroup ↥B) := by rw [← h]; exact hmem
    exact congrArg Subtype.val (mem_bot.1 h')
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have hmem' : (⟨a, ha⟩ : ↥B) ∈ Subgroup.center ↥B := by rw [h]; trivial
    exact hab (congrArg Subtype.val ((Subgroup.mem_center_iff.1 hmem' ⟨b, hb⟩).symm))

theorem eq_bot_of_isPerfect_of_commute {W : Subgroup K} (hW : ⁅W, W⁆ = W)
    (hc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) : W = ⊥ := by
  have h : ⁅W, W⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_bot, commutatorElement_def]
    have := hc a ha b hb
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [this]
      _ = 1 := by group
  rw [hW] at h
  exact le_bot_iff.1 h

theorem not_isPerfect_of_index_eq_two {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : N.index = 2) : ¬ Group.IsPerfect Y := by
  intro hP
  have hle : commutator Y ≤ N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
      Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff,
      inv_mem_iff]
    tauto
  rw [Group.isPerfect_def.1 hP, top_le_iff] at hle
  rw [hle, index_top] at hN
  exact absurd hN (by decide)

theorem exists_commute_not_mem_zpowers [Finite K] {X : Subgroup K} (hX : Group.IsPerfect X)
    {z : K} (hzX : z ∈ X) (hz : z * z = 1) (hz1 : z ≠ 1) :
    ∃ x ∈ X, x * z = z * x ∧ x ∉ zpowers z := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let z' : X := ⟨z, hzX⟩
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'2 : z' * z' = 1 := Subtype.ext hz
  have hord : orderOf z' = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz'2) hz'1
  have hpg : IsPGroup 2 (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hz'S : z' ∈ (S : Subgroup X) := hS (mem_zpowers z')
  have hnt : Nontrivial (S : Subgroup X) :=
    ⟨⟨⟨z', hz'S⟩, 1, fun h => hz'1 (congrArg Subtype.val h)⟩⟩
  have hcn := S.isPGroup'.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : Subgroup.center (S : Subgroup X))
  have hcz : ((c : S) : X) = z' := by
    have hcomm : ((c : S) : X) * z' = z' * ((c : S) : X) := by
      have := Subgroup.mem_center_iff.1 c.2 ⟨z', hz'S⟩
      exact congrArg Subtype.val this.symm
    have hmem := hcon ((c : S) : X) ((c : S) : X).2 (by
      have := congrArg Subtype.val hcomm
      simpa using this)
    rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 hmem with h | h
    · exfalso
      apply hc1
      have h1 : ((c : S) : X) = 1 := Subtype.ext h
      have h2 : (c : S) = 1 := Subtype.ext h1
      exact Subtype.ext h2
    · exact Subtype.ext h
  have hzcen : (⟨z', hz'S⟩ : S) ∈ Subgroup.center (S : Subgroup X) := by
    have : c.1 = ⟨z', hz'S⟩ := Subtype.ext hcz
    rw [← this]
    exact c.2
  have hSle : ∀ s : S, ((s : X) : K) ∈ zpowers z := by
    intro s
    have hcomm := Subgroup.mem_center_iff.1 hzcen s
    apply hcon _ (s : X).2
    have := congrArg (fun t : S => ((t : X) : K)) hcomm
    simpa using this
  have hSeq : (S : Subgroup X) = zpowers z' := by
    apply le_antisymm
    · intro s hs
      rcases (mem_zpowers_iff_of_mul_self_eq_one hz).1 (hSle ⟨s, hs⟩) with h | h
      · have : s = 1 := Subtype.ext h
        rw [this]; exact one_mem _
      · have : s = z' := Subtype.ext h
        rw [this]; exact mem_zpowers _
    · exact hS
  have hcard : Nat.card (S : Subgroup X) = 2 := by
    rw [hSeq, Nat.card_zpowers, hord]
  have hcyc : IsCyclic (S : Subgroup X) := isCyclic_of_prime_card hcard
  obtain ⟨N, hN, hcompl⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hcyc
  have hidx : N.index = 2 := by
    rw [hcompl.symm.index_eq_card, hcard]
  exact not_isPerfect_of_index_eq_two hidx hX

theorem simple_le_or_le_of_decomposition {B M P Q : Subgroup K} (hB : IsSimpleGroup ↥B)
    (hBnab : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) (hBM : B ≤ M) (hPM : P ≤ M) (hQM : Q ≤ M)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hM : ∀ m ∈ M, ∃ p ∈ P, ∃ q ∈ Q, m = p * q)
    (hBn : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ ∈ B) : B ≤ P ∨ B ≤ Q := by
  have hPnorm : ∀ m ∈ M, ∀ x ∈ P, m * x * m⁻¹ ∈ P := by
    intro m hm x hx
    obtain ⟨p, hp, q, hq, rfl⟩ := hM m hm
    have hqx : q * x * q⁻¹ = x := by
      have := hPQ x hx q hq
      calc q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [this]
        _ = x := by group
    have : p * q * x * (p * q)⁻¹ = p * x * p⁻¹ := by
      calc p * q * x * (p * q)⁻¹ = p * (q * x * q⁻¹) * p⁻¹ := by group
        _ = p * x * p⁻¹ := by rw [hqx]
    rw [this]
    exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  have hQnorm : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := by
    intro m hm y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := hM m hm
    have hpy : p * (q * y * q⁻¹) * p⁻¹ = q * y * q⁻¹ := by
      have := hPQ p hp (q * y * q⁻¹) (Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq))
      calc p * (q * y * q⁻¹) * p⁻¹ = ((q * y * q⁻¹) * p) * p⁻¹ := by rw [this]
        _ = q * y * q⁻¹ := by group
    have : p * q * y * (p * q)⁻¹ = q * y * q⁻¹ := by
      calc p * q * y * (p * q)⁻¹ = p * (q * y * q⁻¹) * p⁻¹ := by group
        _ = q * y * q⁻¹ := hpy
    rw [this]
    exact Q.mul_mem (Q.mul_mem hq hy) (Q.inv_mem hq)
  rcases inf_eq_bot_or_le_of_simple hB (fun b hb x hx => hPnorm b (hBM hb) x hx) with hP | hP
  · rcases inf_eq_bot_or_le_of_simple hB (fun b hb x hx => hQnorm b (hBM hb) x hx) with hQ | hQ
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hBnab
      apply hab
      have hcommP : ∀ c ∈ B, ∀ x ∈ P, c * x = x * c := by
        intro c hc x hx
        have h1 : c * x * c⁻¹ * x⁻¹ ∈ B ⊓ P := by
          refine ⟨?_, ?_⟩
          · have h2 : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
            rw [h2]
            exact B.mul_mem hc (hBn x (hPM hx) c⁻¹ (B.inv_mem hc))
          · exact P.mul_mem (hPnorm c (hBM hc) x hx) (P.inv_mem hx)
        rw [hP, mem_bot] at h1
        calc c * x = (c * x * c⁻¹ * x⁻¹) * x * c := by group
          _ = x * c := by rw [h1]; group
      have hcommQ : ∀ c ∈ B, ∀ y ∈ Q, c * y = y * c := by
        intro c hc y hy
        have h1 : c * y * c⁻¹ * y⁻¹ ∈ B ⊓ Q := by
          refine ⟨?_, ?_⟩
          · have h2 : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
            rw [h2]
            exact B.mul_mem hc (hBn y (hQM hy) c⁻¹ (B.inv_mem hc))
          · exact Q.mul_mem (hQnorm c (hBM hc) y hy) (Q.inv_mem hy)
        rw [hQ, mem_bot] at h1
        calc c * y = (c * y * c⁻¹ * y⁻¹) * y * c := by group
          _ = y * c := by rw [h1]; group
      obtain ⟨p, hp, q, hq, hb'⟩ := hM b (hBM hb)
      rw [hb']
      calc a * (p * q) = (a * p) * q := by group
        _ = (p * a) * q := by rw [hcommP a ha p hp]
        _ = p * (a * q) := by group
        _ = p * (q * a) := by rw [hcommQ a ha q hq]
        _ = p * q * a := by group
    · exact Or.inr hQ
  · exact Or.inl hP

end CFSG.EvenSporadicStandard.SolomonRed
