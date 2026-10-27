module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MaxByFixedPoints

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_modEq_one {p : ℕ} [Fact p.Prime] {N W P : Subgroup G} (hNW : N ≤ W)
    (hPN : P ≤ N) (hP : IsPGroup p P)
    (hfix : ∀ g : G, (∀ s ∈ P, g⁻¹ * s * g ∈ N) → g ∈ N) :
    N.relIndex W ≡ 1 [MOD p] := by
  classical
  let N' : Subgroup W := N.subgroupOf W
  let P' : Subgroup W := P.subgroupOf W
  have hPW : P ≤ W := hPN.trans hNW
  have hP' : IsPGroup p P' := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    exact IsPGroup.of_card (n := k) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPW).toEquiv, hk])
  have hmod := hP'.card_modEq_card_fixedPoints (W ⧸ N')
  have hcard1 : Nat.card (MulAction.fixedPoints P' (W ⧸ N')) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    have key : ∀ z : MulAction.fixedPoints P' (W ⧸ N'),
        z.1 = (QuotientGroup.mk 1 : W ⧸ N') := by
      rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
      have hw : (w : G) ∈ N := by
        apply hfix
        intro s hs
        have hs' : s⁻¹ ∈ P := P.inv_mem hs
        have h1 : (⟨s⁻¹, hPW hs'⟩ : W) ∈ P' := hs'
        have h2 := hz ⟨⟨s⁻¹, hPW hs'⟩, h1⟩
        change ((⟨s⁻¹, hPW hs'⟩ : W) • (QuotientGroup.mk w : W ⧸ N')) = QuotientGroup.mk w at h2
        rw [show (⟨s⁻¹, hPW hs'⟩ : W) • (QuotientGroup.mk w : W ⧸ N') =
          QuotientGroup.mk (⟨s⁻¹, hPW hs'⟩ * w) from rfl, QuotientGroup.eq] at h2
        have := Subgroup.mem_subgroupOf.mp h2
        simpa [mul_assoc] using this
      show (QuotientGroup.mk w : W ⧸ N') = QuotientGroup.mk 1
      rw [QuotientGroup.eq, mul_one]
      exact Subgroup.mem_subgroupOf.mpr (N.inv_mem hw)
    refine ⟨⟨fun x y => Subtype.ext ((key x).trans (key y).symm)⟩,
      ⟨⟨QuotientGroup.mk 1, ?_⟩⟩⟩
    intro s
    show (s : W) • (QuotientGroup.mk 1 : W ⧸ N') = QuotientGroup.mk 1
    change (QuotientGroup.mk ((s : W) * 1) : W ⧸ N') = QuotientGroup.mk 1
    rw [QuotientGroup.eq]
    have hs : ((s : W) : G) ∈ P := s.2
    rw [mul_one, mul_one]
    exact Subgroup.mem_subgroupOf.mpr (N.inv_mem (hPN hs))
  have hN : Nat.card (W ⧸ N') = N.relIndex W := rfl
  rw [hcard1, hN] at hmod
  exact hmod

theorem eq_or_eq_top_of_fixed {N P₃ P₅ : Subgroup G} (hidx : N.index = 2926) (h3N : P₃ ≤ N)
    (h5N : P₅ ≤ N) (h3 : IsPGroup 3 P₃) (h5 : IsPGroup 5 P₅)
    (hfix3 : ∀ g : G, (∀ s ∈ P₃, g⁻¹ * s * g ∈ N) → g ∈ N)
    (hfix5 : ∀ g : G, (∀ s ∈ P₅, g⁻¹ * s * g ∈ N) → g ∈ N) {W : Subgroup G} (hNW : N ≤ W) :
    W = N ∨ W = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have m3 := relIndex_modEq_one hNW h3N h3 hfix3
  have m5 := relIndex_modEq_one hNW h5N h5 hfix5
  have hdvd : N.relIndex W ∣ 2926 := hidx ▸ Subgroup.relIndex_dvd_index_of_le hNW
  have hle : N.relIndex W ≤ 2926 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : N.relIndex W = 1 ∨ N.relIndex W = 2926 := by
    have hmem : N.relIndex W ∈ (Nat.divisors 2926) := by simp [hdvd]
    have h15 : N.relIndex W % 15 = 1 := by
      have a3 : N.relIndex W % 3 = 1 := m3
      have a5 : N.relIndex W % 5 = 1 := m5
      omega
    have : Nat.divisors 2926 = {1, 2, 7, 11, 14, 19, 22, 38, 77, 133, 154, 209, 266, 418, 1463, 2926} := by
      decide +kernel
    rw [this] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  rcases hcases with h | h
  · left
    exact le_antisymm ((Subgroup.relIndex_eq_one.mp h)) hNW
  · right
    have := Subgroup.relIndex_mul_index hNW
    rw [h, hidx] at this
    have hW : W.index = 1 := by omega
    exact Subgroup.index_eq_one.mp hW

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.MaxByFixedPoints
