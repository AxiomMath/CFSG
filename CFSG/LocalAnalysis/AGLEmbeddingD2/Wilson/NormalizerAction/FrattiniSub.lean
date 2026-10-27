module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.OrbitFrattini

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

variable {G : Type*} [Group G]

theorem normalizer_subgroupOf_eq {M P : Subgroup G} (hPM : P ≤ M) :
    normalizer ((P.subgroupOf M : Subgroup M) : Set M) = (normalizer (P : Set G)).subgroupOf M := by
  ext g
  rw [mem_subgroupOf, mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := (h ⟨x, hPM hx⟩).1 (by rwa [mem_subgroupOf])
      rwa [mem_subgroupOf] at this
    · have hxM : x ∈ M := by
        have := M.mul_mem (M.mul_mem (M.inv_mem g.2) (hPM hx)) g.2
        simpa [mul_assoc] using this
      have := (h ⟨x, hxM⟩).2 (by rwa [mem_subgroupOf])
      rwa [mem_subgroupOf] at this
  · intro h x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact h x

theorem card_inf_normalizer_mul_card {p : ℕ} [Fact p.Prime] [Finite G] (M K P : Subgroup G)
    (hKM : K ≤ M) (hKn : (K.subgroupOf M).Normal) (hPK : P ≤ K)
    (hcard : Nat.card P = p ^ (Nat.card K).factorization p) :
    Nat.card ↥(M ⊓ normalizer (P : Set G)) * Nat.card K =
      Nat.card M * Nat.card ↥(K ⊓ normalizer (P : Set G)) := by
  have hPM : P ≤ M := hPK.trans hKM
  have hKcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv
  have hle : P.subgroupOf M ≤ K.subgroupOf M := fun x hx => hPK hx
  let Pk : Subgroup (K.subgroupOf M) := (P.subgroupOf M).subgroupOf (K.subgroupOf M)
  have hPkcard : Nat.card Pk = p ^ (Nat.card (K.subgroupOf M)).factorization p := by
    have : Nat.card Pk = Nat.card (P.subgroupOf M) := Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    rw [this, hKcard, ← hcard]
    exact Nat.card_congr (subgroupOfEquivOfLe hPM).toEquiv
  let S : Sylow p (K.subgroupOf M) := Sylow.ofCard Pk hPkcard
  have hmap : ((S : Subgroup (K.subgroupOf M)).map (K.subgroupOf M).subtype : Subgroup M) =
      P.subgroupOf M := by
    show Pk.map (K.subgroupOf M).subtype = _
    exact map_subgroupOf_eq_of_le hle
  have h := Proving.card_normalizer_mul_card_eq S
  rw [hmap, hKcard, normalizer_subgroupOf_eq hPM] at h
  have e1 : Nat.card ((normalizer (P : Set G)).subgroupOf M) = Nat.card ↥(M ⊓ normalizer (P : Set G)) := by
    have : (normalizer (P : Set G)).subgroupOf M = (M ⊓ normalizer (P : Set G)).subgroupOf M := by
      ext x; simp [mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have e2 : Nat.card ((K.subgroupOf M) ⊓ (normalizer (P : Set G)).subgroupOf M : Subgroup M) =
      Nat.card ↥(K ⊓ normalizer (P : Set G)) := by
    have : (K.subgroupOf M) ⊓ (normalizer (P : Set G)).subgroupOf M =
        (K ⊓ normalizer (P : Set G)).subgroupOf M := by
      ext x; simp [mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hKM)).toEquiv
  rw [e1, e2] at h
  exact h

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
