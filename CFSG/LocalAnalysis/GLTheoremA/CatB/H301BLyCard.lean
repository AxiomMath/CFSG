module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyBound
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyZero

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem Config.fixed_unique {E : Subgroup (Perm X)} (c : Config E) {x y z : X}
    (hx : ∀ e ∈ E, e x = x) (hy : ∀ e ∈ E, e y = y) (hz : ∀ e ∈ E, e z = z) (hxy : x ≠ y)
    (hzy : z ≠ y) : z = x := by
  rcases c.eq_of_fixed hx with h1 | h1 <;> rcases c.eq_of_fixed hy with h2 | h2 <;>
    rcases c.eq_of_fixed hz with h3 | h3
  all_goals first
    | exact h3.trans h1.symm
    | exact absurd (h1.trans h2.symm) hxy
    | exact absurd (h3.trans h2.symm) hzy

theorem le_normalizer_inf_stabilizer {E T : Subgroup (Perm X)} (hET : E ≤ normalizer T) {x : X}
    (hx : ∀ e ∈ E, e x = x) :
    E ≤ normalizer (T ⊓ stabilizer (Perm X) x : Subgroup (Perm X)) := fun e he =>
  inf_normalizer_le_normalizer_inf
    ⟨hET he, Subgroup.le_normalizer (show e ∈ stabilizer (Perm X) x from hx e he)⟩

theorem card_orbit_le_four (hX : Fintype.card X = 11) {E U : Subgroup (Perm X)} (c : Config E)
    (hE : IsPGroup 3 E) (hU : IsPGroup 2 U) (hEU : E ≤ normalizer U) {x y : X}
    (hx : ∀ e ∈ E, e x = x) (hy : ∀ e ∈ E, e y = y) (hxy : x ≠ y)
    (hyS : y ∉ (orbit U x : Set X)) : Nat.card (orbit U x) ≤ 4 := by
  obtain ⟨k, hk⟩ := exists_card_orbit_eq hU x
  have hmod := card_modEq_fix hE (orbit U x : Set X)
    (fun f hf z hz => (mem_setStab.1 (mem_setStab_orbit hEU (mem_orbit_self x) hf (hx f hf)) z).2
      hz)
  have hone : Nat.card {z : X // z ∈ (orbit U x : Set X) ∧ ∀ f ∈ E, f z = z} = 1 := by
    have : Unique {z : X // z ∈ (orbit U x : Set X) ∧ ∀ f ∈ E, f z = z} :=
      { default := ⟨x, mem_orbit_self x, hx⟩
        uniq := fun ⟨z, hz, hf⟩ =>
          Subtype.ext (c.fixed_unique hx hy hf hxy fun h => hyS (h ▸ hz)) }
    exact Nat.card_unique
  have hXc : Nat.card X = 11 := by rw [Nat.card_eq_fintype_card]; exact hX
  have hlt : Nat.card (orbit U x : Set X) < 11 := by
    have := Finite.card_subtype_lt (p := fun z => z ∈ (orbit U x : Set X)) hyS
    rwa [hXc] at this
  rw [hone, hk] at hmod
  rw [hk] at hlt ⊢
  have hk3 : k < 4 := by
    by_contra hk4
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hk4)
    omega
  interval_cases k
  · norm_num
  · exact absurd hmod (by decide)
  · norm_num
  · exact absurd hmod (by decide)

theorem card_le_sixteen (hX : Fintype.card X = 11) {E T : Subgroup (Perm X)} (c : Config E)
    (hE : IsPGroup 3 E) (hT : IsPGroup 2 T) (hET : E ≤ normalizer T) : Nat.card T ≤ 16 := by
  let T1 : Subgroup (Perm X) := T ⊓ stabilizer (Perm X) c.p
  have hT1 : IsPGroup 2 T1 := hT.to_le inf_le_left
  have hE1 : E ≤ normalizer T1 := le_normalizer_inf_stabilizer hET c.fix_p
  have hT2 : IsPGroup 2 (T1 ⊓ stabilizer (Perm X) c.q : Subgroup (Perm X)) :=
    hT1.to_le inf_le_left
  have hE2 : E ≤ normalizer (T1 ⊓ stabilizer (Perm X) c.q : Subgroup (Perm X)) :=
    le_normalizer_inf_stabilizer hE1 c.fix_q
  have h3 : (T1 ⊓ stabilizer (Perm X) c.q : Subgroup (Perm X)) = ⊥ :=
    eq_bot_of_fix c hE hT2 hE2 (fun w hw => hw.1.2) (fun w hw => hw.2)
  have hc1 : Nat.card T = Nat.card (orbit T c.p) * Nat.card T1 := card_eq_orbit_mul T c.p
  have hc2 := card_eq_orbit_mul T1 c.q
  rw [h3, Subgroup.card_bot, mul_one] at hc2
  have hA : Nat.card (orbit T1 c.q) ≤ 4 := by
    refine card_orbit_le_four hX c hE hT1 hE1 c.fix_q c.fix_p c.p_ne_q.symm fun h => ?_
    obtain ⟨⟨w, hw⟩, hwq⟩ := mem_orbit_iff.1 h
    have hwp : w c.p = c.p := hw.2
    exact c.p_ne_q (w.injective ((show w c.q = c.p from hwq).trans hwp.symm)).symm
  have hB : Nat.card (orbit T c.p) ≤ 4 := by
    by_cases hq : c.q ∈ orbit T c.p
    · have hsub : (orbit T c.p : Set X) ⊆ {c.p, c.q} := fun z hz => by
        rcases orbit_subset_pair c hE hT hET hq z hz with h | h
        · exact Or.inl h
        · exact Or.inr h
      rw [Nat.card_coe_set_eq]
      exact ((Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_pair c.p_ne_q).le).trans
        (by norm_num)
    · exact card_orbit_le_four hX c hE hT hET c.fix_p c.fix_q c.p_ne_q hq
  calc Nat.card T = Nat.card (orbit T c.p) * Nat.card T1 := hc1
    _ = Nat.card (orbit T c.p) * Nat.card (orbit T1 c.q) := by rw [hc2]
    _ ≤ 4 * 4 := Nat.mul_le_mul hB hA
    _ = 16 := by norm_num

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
