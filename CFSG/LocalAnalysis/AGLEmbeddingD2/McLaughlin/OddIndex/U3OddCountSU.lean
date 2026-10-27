module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddLevi
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddCount

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LinearGroups

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

omit [Fact p.Prime] [CharP F p] in
include hF in
theorem two_le_prime_pow_of_card : 2 ≤ p ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : p ^ f ≤ 1 := by omega
  have h3 : (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h2 2
  omega

include hF in
theorem card_range_embSU :
    Nat.card (embSU (unitaryInvolution F p f)).range = p ^ f * ((p ^ f) ^ 2 - 1) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (embSU_injective _)).toEquiv, card_SU_two hF]

theorem comap_range_embSU_eq_rootsOfUnity [NeZero (p ^ f - 1)] :
    (embSU (unitaryInvolution F p f)).range.comap (tSU hF) = rootsOfUnity (p ^ f - 1) F := by
  ext μ
  rw [Subgroup.mem_comap, tSU_mem_range_embSU_iff hF μ, mem_rootsOfUnity]

theorem card_inf_range_embSU_range_tSU :
    Nat.card ((embSU (unitaryInvolution F p f)).range ⊓ (tSU hF).range : Subgroup _) =
      p ^ f - 1 := by
  have hq2 := two_le_prime_pow_of_card hF
  have : NeZero (p ^ f - 1) := ⟨by omega⟩
  have hmap : Subgroup.map (tSU hF) ((embSU (unitaryInvolution F p f)).range.comap (tSU hF)) =
      (tSU hF).range ⊓ (embSU (unitaryInvolution F p f)).range := Subgroup.map_comap_eq _ _
  rw [inf_comm, ← hmap, Subgroup.card_map_of_injective (tSU_injective hF),
    comap_range_embSU_eq_rootsOfUnity hF]
  apply card_rootsOfUnity_of_dvd
  rw [hF]
  refine ⟨p ^ f + 1, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  have h : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
  omega

theorem card_inf_centralizer_zSU (hp2 : p ≠ 2) (W : Subgroup (SU (unitaryInvolution F p f) 3))
    (hTW : (tSU hF).range ≤ W) :
    Nat.card (W ⊓ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) :
        Subgroup _) *
      Nat.card ((embSU (unitaryInvolution F p f)).range ⊓ (tSU hF).range : Subgroup _) =
    Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) *
      Nat.card (tSU hF).range := by
  have hC := centralizer_zSU hF hp2
  have hLC : (embSU (unitaryInvolution F p f)).range ≤ Subgroup.centralizer
      ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by rw [hC]; exact le_sup_left
  have hTC : (tSU hF).range ≤ Subgroup.centralizer
      ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by rw [hC]; exact le_sup_right
  have h := card_mul_inf_eq (W ⊓ (embSU (unitaryInvolution F p f)).range) (tSU hF).range
    (W ⊓ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)))
    (fun x hx => ⟨hx.1, hLC hx.2⟩) (fun x hx => ⟨hTW hx, hTC hx⟩) (by
      intro b hb
      have hb' : b * zSU hF = zSU hF * b := (hb.2 (zSU hF) rfl).symm
      obtain ⟨l, hl, t, ht, rfl⟩ := (mem_centralizer_zSU_iff hF hp2 b).1 hb'
      refine ⟨l, ⟨?_, hl⟩, t, ht, rfl⟩
      have : l = (l * t) * t⁻¹ := by group
      rw [this]
      exact W.mul_mem hb.1 (W.inv_mem (hTW ht)))
  have hinf : (W ⊓ (embSU (unitaryInvolution F p f)).range) ⊓ (tSU hF).range =
      (embSU (unitaryInvolution F p f)).range ⊓ (tSU hF).range := by
    ext x
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      exact ⟨⟨hTW h3, h2⟩, h3⟩
  rw [hinf] at h
  exact h

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
