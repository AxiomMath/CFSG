module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

open Subgroup

namespace SL23Pair

variable {K : Type} [Group K] {A B : Subgroup K}

theorem symm (h : SL23Pair K A B) : SL23Pair K B A :=
  ⟨fun b hb a ha => (h.comm a ha b hb).symm, by rw [sup_comm]; exact h.top, h.isoB, h.isoA⟩

theorem card_cent_subtype {E : Type} [Group E] (e : E ≃* SL23) {g : E} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : Nat.card {c : E // c * g = g * c} = 6 := by
  have hs3 : (e g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have hs1 : e g ≠ 1 := fun h1 => hg1 (e.injective (by rw [h1, map_one]))
  have h6 := card_cent_of_pow_three hs3 hs1
  have h7 : Nat.card {t : SL23 // t * e g = e g * t} = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h6
  rw [← h7]
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun c => ?_)
  show c * g = g * c ↔ e c * e g = e g * e c
  rw [← map_mul, ← map_mul, e.injective.eq_iff]

variable [Finite K] (h : SL23Pair K A B)

include h

theorem eq_one_of_mem_inf {z : K} (hz : z ∈ A ⊓ B) (hz3 : z ^ 3 = 1) : z = 1 := by
  have hsq := h.inf_sq hz
  have h1 : z ^ 3 = z * (z * z) := pow_three z
  rw [hsq, mul_one, hz3] at h1
  exact h1.symm

theorem cent_large_of_mem_A {x : K} (hxA : x ∈ A) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    36 < Nat.card ↥(Subgroup.centralizer {x}) := by
  have hBle : B ≤ Subgroup.centralizer {x} := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm x hxA b hb).symm
  have hxC : x ∈ Subgroup.centralizer {x} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxB : x ∉ B := fun hxB => hx1 (h.eq_one_of_mem_inf ⟨hxA, hxB⟩ hx3)
  have hdvd : Nat.card ↥B ∣ Nat.card ↥(Subgroup.centralizer {x}) := Subgroup.card_dvd_of_le hBle
  have hlt : Nat.card ↥B < Nat.card ↥(Subgroup.centralizer {x}) := by
    by_contra hge
    have heq := Subgroup.eq_of_le_of_card_ge hBle (not_lt.mp hge)
    exact hxB (heq ▸ hxC)
  rw [h.card_B] at hdvd hlt
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem cent_gen_large (p : Fin 4 ⊕ Fin 4) : 36 < Nat.card ↥(Subgroup.centralizer {h.gen p}) := by
  rcases p with i | i
  · exact h.cent_large_of_mem_A (h.gen_mem_A i) (h.gen_pow_three _) (h.gen_ne_one _)
  · exact h.symm.cent_large_of_mem_A (h.gen_mem_B i) (h.gen_pow_three _) (h.gen_ne_one _)

theorem mul_comm_iff {a b c d : K} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ A) (hd : d ∈ B) :
    (c * d) * (a * b) = (a * b) * (c * d) ↔ (c * a) * (d * b) = (a * c) * (b * d) := by
  have e1 : (c * d) * (a * b) = (c * a) * (d * b) := by
    calc (c * d) * (a * b) = c * (d * a) * b := by group
      _ = c * (a * d) * b := by rw [h.comm a ha d hd]
      _ = (c * a) * (d * b) := by group
  have e2 : (a * b) * (c * d) = (a * c) * (b * d) := by
    calc (a * b) * (c * d) = a * (b * c) * d := by group
      _ = a * (c * b) * d := by rw [h.comm c hc b hb]
      _ = (a * c) * (b * d) := by group
  rw [e1, e2]

theorem centralizer_decomp {a b c d : K} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ A) (hd : d ∈ B)
    (ha3 : a ^ 3 = 1) (hcomm : (c * d) * (a * b) = (a * b) * (c * d)) :
    c * a = a * c ∧ d * b = b * d := by
  have h1 : (c * a) * (d * b) = (a * c) * (b * d) := (h.mul_comm_iff ha hb hc hd).mp hcomm
  obtain ⟨z, hz⟩ : ∃ z : K, z = (a * c)⁻¹ * (c * a) := ⟨_, rfl⟩
  have hzA : z ∈ A := by
    rw [hz]
    exact mul_mem (inv_mem (mul_mem ha hc)) (mul_mem hc ha)
  have hzB : z ∈ B := by
    have hzb : z = (b * d) * (d * b)⁻¹ := by
      calc z = (a * c)⁻¹ * ((c * a) * (d * b)) * (d * b)⁻¹ := by rw [hz]; group
        _ = (a * c)⁻¹ * ((a * c) * (b * d)) * (d * b)⁻¹ := by rw [h1]
        _ = (b * d) * (d * b)⁻¹ := by group
    rw [hzb]
    exact mul_mem (mul_mem hb hd) (inv_mem (mul_mem hd hb))
  have hzi : z ∈ A ⊓ B := ⟨hzA, hzB⟩
  have hcen : ∀ k : K, z * k = k * z := h.inf_central hzi
  have hca : c * a = a * c * z := by rw [hz]; group
  have h2 : c * a * c⁻¹ = a * z := by
    calc c * a * c⁻¹ = a * c * z * c⁻¹ := by rw [hca]
      _ = a * (c * z) * c⁻¹ := by group
      _ = a * (z * c) * c⁻¹ := by rw [← hcen c]
      _ = a * z := by group
  have h3 : (c * a * c⁻¹) ^ 3 = 1 := by
    rw [conj_pow, ha3]
    group
  rw [h2, Commute.mul_pow (hcen a).symm, ha3, one_mul] at h3
  have hz1 : z = 1 := h.eq_one_of_mem_inf hzi h3
  have hac : c * a = a * c := (inv_mul_eq_one.mp (hz.symm.trans hz1)).symm
  refine ⟨hac, mul_left_cancel (a := a * c) ?_⟩
  rw [hac] at h1
  exact h1

theorem cent_mixed_small {x : K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hmix : ∀ p, x ≠ h.gen p ∧ x ≠ (h.gen p)⁻¹) :
    Nat.card ↥(Subgroup.centralizer {x}) ≤ 36 := by
  obtain ⟨a, ha, b, hb, hx, ha3, hb3⟩ := h.exists_decomp_pow_three hx3
  have ha1 : a ≠ 1 := by
    intro ha1
    have hxB : x ∈ A ∨ x ∈ B := Or.inr (by rw [hx, ha1, one_mul]; exact hb)
    obtain ⟨p, hp | hp⟩ := h.exists_gen_of_pow_three hx3 hx1 hxB
    · exact (hmix p).1 hp
    · exact (hmix p).2 hp
  have hb1 : b ≠ 1 := by
    intro hb1
    have hxA : x ∈ A ∨ x ∈ B := Or.inl (by rw [hx, hb1, mul_one]; exact ha)
    obtain ⟨p, hp | hp⟩ := h.exists_gen_of_pow_three hx3 hx1 hxA
    · exact (hmix p).1 hp
    · exact (hmix p).2 hp
  have ha3' : (⟨a, ha⟩ : ↥A) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hb3' : (⟨b, hb⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have ha1' : (⟨a, ha⟩ : ↥A) ≠ 1 := fun h1 => ha1 (by simpa using congrArg Subtype.val h1)
  have hb1' : (⟨b, hb⟩ : ↥B) ≠ 1 := fun h1 => hb1 (by simpa using congrArg Subtype.val h1)
  have hcA := card_cent_subtype h.eA ha3' ha1'
  have hcB := card_cent_subtype h.eB hb3' hb1'
  have hmem : ∀ (c : ↥A) (d : ↥B), c * ⟨a, ha⟩ = ⟨a, ha⟩ * c → d * ⟨b, hb⟩ = ⟨b, hb⟩ * d →
      (c : K) * d ∈ Subgroup.centralizer {x} := by
    intro c d hc hd
    rw [Subgroup.mem_centralizer_singleton_iff, hx]
    exact (h.mul_comm_iff ha hb c.2 d.2).mpr
      (by rw [show (c : K) * a = a * c from congrArg Subtype.val hc,
        show (d : K) * b = b * d from congrArg Subtype.val hd])
  let f : {c : ↥A // c * ⟨a, ha⟩ = ⟨a, ha⟩ * c} × {d : ↥B // d * ⟨b, hb⟩ = ⟨b, hb⟩ * d} →
      ↥(Subgroup.centralizer {x}) := fun p => ⟨p.1.1 * p.2.1, hmem _ _ p.1.2 p.2.2⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨k, hk⟩
    obtain ⟨c, hc, d, hd, rfl⟩ := h.exists_mul k
    have hk' : (c * d) * (a * b) = (a * b) * (c * d) := by
      rw [← hx]
      exact Subgroup.mem_centralizer_singleton_iff.mp hk
    obtain ⟨h1, h2⟩ := h.centralizer_decomp ha hb hc hd ha3 hk'
    exact ⟨(⟨⟨c, hc⟩, Subtype.ext h1⟩, ⟨⟨d, hd⟩, Subtype.ext h2⟩), Subtype.ext rfl⟩
  calc Nat.card ↥(Subgroup.centralizer {x}) ≤ Nat.card
        ({c : ↥A // c * ⟨a, ha⟩ = ⟨a, ha⟩ * c} × {d : ↥B // d * ⟨b, hb⟩ = ⟨b, hb⟩ * d}) :=
      Nat.card_le_card_of_surjective f hsurj
    _ = 36 := by rw [Nat.card_prod, hcA, hcB]

theorem exists_image (α : MulAut K) (p : Fin 4 ⊕ Fin 4) :
    ∃ q, α (h.gen p) = h.gen q ∨ α (h.gen p) = (h.gen q)⁻¹ := by
  by_contra hcon
  push Not at hcon
  have h3 : (α (h.gen p)) ^ 3 = 1 := by rw [← map_pow, h.gen_pow_three, map_one]
  have h1 : α (h.gen p) ≠ 1 := fun h1 => h.gen_ne_one p (α.injective (by rw [h1, map_one]))
  have hle := h.cent_mixed_small h3 h1 hcon
  have hge := h.cent_gen_large p
  have hmem : ∀ k ∈ Subgroup.centralizer {h.gen p},
      α k ∈ Subgroup.centralizer {α (h.gen p)} := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg α (Subgroup.mem_centralizer_singleton_iff.mp hk)
  have hinj : Nat.card ↥(Subgroup.centralizer {h.gen p}) ≤
      Nat.card ↥(Subgroup.centralizer {α (h.gen p)}) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨α k.1, hmem k.1 k.2⟩) ?_
    intro k1 k2 hk
    exact Subtype.ext (α.injective (congrArg Subtype.val hk))
  omega

end SL23Pair

end CFSG.OddStandard.SmallF3.Omega.K5
