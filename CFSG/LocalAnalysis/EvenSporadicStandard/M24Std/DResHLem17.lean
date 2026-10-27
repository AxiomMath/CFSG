module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairTransport
public import Certificates.Certificate25760

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup CFSG.QuasithinUnique.Setup.X1

@[expose] def Lem17 {G : Type} [Group G] (L A B : Subgroup G) : Prop :=
  ∃ T : Subgroup G, Nat.card T = 9 ∧ (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ (∀ x ∈ T, x ^ 3 = 1) ∧
    (∀ x ∈ T, x ∈ egNL L A ∧ x ∈ normalizer (B : Set G)) ∧
    ∀ τ ∈ T, τ ≠ 1 → ∃ a ∈ A, τ * a * τ⁻¹ * a⁻¹ ∉ B

theorem lem17_of_pair {G : Type} [Group G] {L A B : Subgroup G}
    (h : PairType L A B) : Lem17 L A B := by
  obtain ⟨e, hA, hB⟩ := h.exists_listImage
  obtain ⟨hlen, hnd, h1, hmul, hcube, hnorm, hfaith⟩ := Certificates.certificate25760
  obtain ⟨T, hT⟩ := exists_listImage e h1 fun x hx y hy => (hmul x hx y hy).1
  refine ⟨T, (hT.card hnd).trans hlen, fun x hx y hy => ?_, fun x hx => ?_, fun x hx => ?_,
    fun τ hτ hτ1 => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hT.exists_eq hx
    obtain ⟨r, hr, rfl⟩ := hT.exists_eq hy
    rw [← map_mul, ← map_mul, (hmul q hq r hr).2]
  · obtain ⟨q, hq, rfl⟩ := hT.exists_eq hx
    rw [← map_pow, pow_three', hcube q hq, map_one]
  · obtain ⟨q, hq, rfl⟩ := hT.exists_eq hx
    exact ⟨hA.pinV_mem_egNL (hnorm q hq).1, hB.pinV_mem_normalizer (hnorm q hq).2⟩
  · obtain ⟨q, hq, rfl⟩ := hT.exists_eq hτ
    have hq1 : q ≠ 1 := fun hq1 => hτ1 (by rw [hq1, map_one])
    obtain ⟨a, ha, hna⟩ := hfaith q hq hq1
    refine ⟨pinV e a, (hA.pinV_mem_iff a).2 ha, fun hmem => hna ?_⟩
    rw [← hB.pinV_mem_iff]
    simpa only [map_mul, map_inv] using hmem

end CFSG.EvenSporadicStandard.M24Std.DResH
