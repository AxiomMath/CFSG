module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Syl

public section

namespace CFSG.ClassicalInvolution.Asc77.T7F2

variable {G : Type} [Group G]

theorem mul_mem_iff_of_relIndex_two {P N : Subgroup G} (h : P.relIndex N = 2) {x y : G}
    (hx : x ∈ N) (hy : y ∈ N) : x * y ∈ P ↔ (x ∈ P ↔ y ∈ P) := by
  have := Subgroup.mul_mem_iff_of_index_two (H := P.subgroupOf N) h (a := ⟨x, hx⟩)
    (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

structure BData (S N P P' : Subgroup G) (t a : G) : Prop where
  hNS : N ≤ S
  ht : t ∈ S
  htN : t ∉ N
  htt : t * t = 1
  hS : ∀ s ∈ S, s ∈ N ∨ t * s ∈ N
  hnorm : ∀ n ∈ N, t * n * t⁻¹ ∈ N
  hP : P ≤ N
  hP' : P' ≤ N
  hPi : P.relIndex N = 2
  hPi' : P'.relIndex N = 2
  hswap : ∀ n ∈ N, (t * n * t⁻¹ ∈ P ↔ n ∈ P') ∧ (t * n * t⁻¹ ∈ P' ↔ n ∈ P)
  haP : a ∈ P
  haP' : a ∉ P'

namespace BData

variable {S N P P' : Subgroup G} {t a : G} (d : BData S N P P' t a)

include d

@[expose] def D : Subgroup G where
  carrier := {n | n ∈ N ∧ (n ∈ P ↔ n ∈ P')}
  one_mem' := ⟨N.one_mem, iff_of_true P.one_mem P'.one_mem⟩
  mul_mem' := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨N.mul_mem hxN hyN, ?_⟩
    rw [mul_mem_iff_of_relIndex_two d.hPi hxN hyN, mul_mem_iff_of_relIndex_two d.hPi' hxN hyN]
    tauto
  inv_mem' := by
    rintro x ⟨hxN, hx⟩
    exact ⟨N.inv_mem hxN, by rw [inv_mem_iff, inv_mem_iff]; exact hx⟩

theorem mem_D {n : G} : n ∈ d.D ↔ n ∈ N ∧ (n ∈ P ↔ n ∈ P') := Iff.rfl

theorem D_le_N : d.D ≤ N := fun _ h => h.1

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right d.htt

theorem conj_D {n : G} (hn : n ∈ d.D) : t * n * t⁻¹ ∈ d.D := by
  obtain ⟨hnN, hn⟩ := hn
  refine ⟨d.hnorm n hnN, ?_⟩
  rw [(d.hswap n hnN).1, (d.hswap n hnN).2]
  exact hn.symm

@[expose] def B : Subgroup G := d.D ⊔ Subgroup.zpowers t

theorem t_mem_B : t ∈ d.B := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)

theorem D_le_B : d.D ≤ d.B := le_sup_left

theorem B_le_S : d.B ≤ S :=
  sup_le (d.D_le_N.trans d.hNS) (Subgroup.zpowers_le.mpr d.ht)

variable [Finite G]

theorem t_mem_normalizer : t ∈ Subgroup.normalizer (d.D : Set G) :=
  mem_normalizer_of_forall fun _ hn => d.conj_D hn

theorem mem_B_cases {b : G} (hb : b ∈ d.B) : b ∈ d.D ∨ ∃ n ∈ d.D, b = n * t := by
  obtain ⟨n, hn, j, rfl⟩ := exists_mul_zpow_of_mem_sup d.t_mem_normalizer hb
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact d.htt
  obtain ⟨q, r, hr, hj⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ j = 2 * q + r :=
    ⟨j / 2, j % 2, by omega, by omega⟩
  have hpow : t ^ j = t ^ r := by
    rw [hj, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with rfl | rfl
  · left; simpa [hpow] using hn
  · right; exact ⟨n, hn, by rw [hpow, zpow_one]⟩

theorem mem_D_of_mem_B_of_mem_N {b : G} (hb : b ∈ d.B) (hbN : b ∈ N) : b ∈ d.D := by
  rcases d.mem_B_cases hb with h | ⟨n, hn, rfl⟩
  · exact h
  · exfalso
    apply d.htN
    have := N.mul_mem (N.inv_mem (d.D_le_N hn)) hbN
    simpa using this

theorem a_not_mem_B : a ∉ d.B := by
  intro h
  have haN : a ∈ N := d.hP d.haP
  obtain ⟨-, h2⟩ := d.mem_D_of_mem_B_of_mem_N h haN
  exact d.haP' (h2.mp d.haP)

omit [Finite G] in
theorem mem_D_xor {n : G} (hn : n ∈ N) : Xor (n ∈ d.D) (n * a ∈ d.D) := by
  have haN : a ∈ N := d.hP d.haP
  have h1 := mul_mem_iff_of_relIndex_two d.hPi hn haN
  have h2 := mul_mem_iff_of_relIndex_two d.hPi' hn haN
  simp only [Xor, mem_D, hn, N.mul_mem hn haN, true_and, h1, h2, d.haP, d.haP', iff_true,
    iff_false]
  tauto

theorem B_cover {s : G} (hs : s ∈ S) : Xor (s ∈ d.B) (s * a ∈ d.B) := by
  have haN : a ∈ N := d.hP d.haP
  have hnotB := d.a_not_mem_B
  rcases d.hS s hs with hsN | hts
  · have hx := d.mem_D_xor hsN
    have e1 : s ∈ d.B ↔ s ∈ d.D :=
      ⟨fun h => d.mem_D_of_mem_B_of_mem_N h hsN, fun h => d.D_le_B h⟩
    have e2 : s * a ∈ d.B ↔ s * a ∈ d.D :=
      ⟨fun h => d.mem_D_of_mem_B_of_mem_N h (N.mul_mem hsN haN), fun h => d.D_le_B h⟩
    rw [e1, e2]
    exact hx
  ·
    have hsn : s = t * (t * s) := by rw [← mul_assoc, d.htt, one_mul]
    set n := t * s with hn
    have e1 : s ∈ d.B ↔ n ∈ d.D := by
      rw [hsn]
      constructor
      · intro h
        have : n ∈ d.B := by
          have := d.B.mul_mem (d.B.inv_mem d.t_mem_B) h
          simpa using this
        exact d.mem_D_of_mem_B_of_mem_N this hts
      · intro h
        exact d.B.mul_mem d.t_mem_B (d.D_le_B h)
    have e2 : s * a ∈ d.B ↔ n * a ∈ d.D := by
      have hsa : s * a = t * (n * a) := by rw [hsn]; group
      rw [hsa]
      constructor
      · intro h
        have : n * a ∈ d.B := by
          have := d.B.mul_mem (d.B.inv_mem d.t_mem_B) h
          simpa using this
        exact d.mem_D_of_mem_B_of_mem_N this (N.mul_mem hts haN)
      · intro h
        exact d.B.mul_mem d.t_mem_B (d.D_le_B h)
    rw [e1, e2]
    exact d.mem_D_xor hts

theorem relIndex_B : d.B.relIndex S = 2 := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  have haS : a ∈ S := d.hNS (d.hP d.haP)
  refine ⟨⟨a, haS⟩, fun y => ?_⟩
  obtain ⟨s, hs⟩ := y
  have := d.B_cover hs
  simpa [Xor, Subgroup.mem_subgroupOf] using this.symm

theorem mul_self_mem {b : G} (hb : b ∈ d.B) : b * b ∈ P ∧ b * b ∈ P' := by
  rcases d.mem_B_cases hb with ⟨hbN, hbPP⟩ | ⟨n, hn, rfl⟩
  · constructor
    · rw [mul_mem_iff_of_relIndex_two d.hPi hbN hbN]
    · rw [mul_mem_iff_of_relIndex_two d.hPi' hbN hbN]
  ·
    have hnN : n ∈ N := d.D_le_N hn
    have hcN : t * n * t⁻¹ ∈ N := d.hnorm n hnN
    have e : n * t * (n * t) = n * (t * n * t⁻¹) := by
      rw [d.t_inv]; group
    rw [e]
    have hcD := d.conj_D hn
    obtain ⟨-, hn2⟩ := hn
    obtain ⟨-, hc2⟩ := hcD
    constructor
    · rw [mul_mem_iff_of_relIndex_two d.hPi hnN hcN]
      rw [(d.hswap n hnN).1] at hc2 ⊢
      constructor <;> intro h <;> tauto
    · rw [mul_mem_iff_of_relIndex_two d.hPi' hnN hcN]
      rw [(d.hswap n hnN).2] at hc2 ⊢
      constructor <;> intro h <;> tauto

end BData

end CFSG.ClassicalInvolution.Asc77.T7F2
