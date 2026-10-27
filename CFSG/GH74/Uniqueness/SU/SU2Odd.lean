module

public import CFSG.GH74.Uniqueness.SU.SU2Struct

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

section Odd

theorem eq_of_swap_of_odd {G α : Type*} [Group G] [MulAction G α] [Finite G]
    (hodd : Odd (Nat.card G)) {g : G} {a b : α} (h1 : g • a = b) (h2 : g • b = a) : a = b := by
  have hord : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
  obtain ⟨m, hm⟩ := hord
  have hg : g = (g ^ 2) ^ (m + 1) := by
    have h : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
    calc g = g * g ^ (2 * m + 1) := by rw [h, mul_one]
      _ = g ^ (2 * (m + 1)) := by rw [← pow_succ']; ring_nf
      _ = (g ^ 2) ^ (m + 1) := by rw [pow_mul]
  have hga : g ^ 2 • a = a := by rw [pow_two, mul_smul, h1, h2]
  have hfix : ∀ n : ℕ, (g ^ 2) ^ n • a = a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hga]; exact ih
  calc a = (g ^ 2) ^ (m + 1) • a := (hfix _).symm
    _ = g • a := by rw [← hg]
    _ = b := h1

theorem ncard_orbit_mul_card_inf {X α : Type*} [Group X] [MulAction X α] (K : Subgroup X)
    (a : α) : (MulAction.orbit ↥K a).ncard * Nat.card ↥(K ⊓ MulAction.stabilizer X a) =
      Nat.card K := by
  rw [← MulAction.index_stabilizer]
  have : Nat.card ↥(MulAction.stabilizer ↥K a) = Nat.card ↥(K ⊓ MulAction.stabilizer X a) :=
    Nat.card_congr
      { toFun := fun n => ⟨n.1.1, n.1.2, n.2⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [← this]
  exact Subgroup.index_mul_card _

theorem card_stab_inf_le {X α : Type*} [Group X] [MulAction X α] [Finite X] (h : X) {a b c : α}
    (h1 : h • b = a) (h2 : h • a = c) :
    Nat.card ↥(MulAction.stabilizer X a ⊓ MulAction.stabilizer X b) ≤
      Nat.card ↥(MulAction.stabilizer X c ⊓ MulAction.stabilizer X a) := by
  have hle : (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b).map (MulAut.conj h).toMonoidHom ≤
      MulAction.stabilizer X c ⊓ MulAction.stabilizer X a := by
    rintro _ ⟨x, ⟨hxa, hxb⟩, rfl⟩
    have hxa' : x • a = a := MulAction.mem_stabilizer_iff.1 hxa
    have hxb' : x • b = b := MulAction.mem_stabilizer_iff.1 hxb
    have hc : h⁻¹ • c = a := by rw [inv_smul_eq_iff]; exact h2.symm
    have ha : h⁻¹ • a = b := by rw [inv_smul_eq_iff]; exact h1.symm
    refine ⟨MulAction.mem_stabilizer_iff.2 ?_, MulAction.mem_stabilizer_iff.2 ?_⟩
    · show (h * x * h⁻¹) • c = c
      rw [mul_smul, mul_smul, hc, hxa', h2]
    · show (h * x * h⁻¹) • a = a
      rw [mul_smul, mul_smul, ha, hxb', h1]
  have := Subgroup.card_le_of_le hle
  rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective] at this

namespace GOPair

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V] {Y : Subgroup X}

theorem ncard_omegaB_eq [Finite X] [Finite V] (hGO : GOPair V Y) {W : Subgroup V}
    (hW : W ∈ omegaB V Y) : (omegaB V Y).ncard = Nat.card Y := by
  rw [hGO.omegaB_eq_orbit hW, ← MulAction.index_stabilizer]
  have hbot : MulAction.stabilizer ↥Y W = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have := hGO.typeB_stab_trivial hW.1 hW.2.1 hW.2.2 y.2 (MulAction.mem_stabilizer_iff.1 hy)
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  rw [hbot, Subgroup.index_bot]

theorem card_fixSub_eq_two [Finite X] [Finite V] (hGO : GOPair V Y) (hodd : Odd (Nat.card X))
    {W₁ W₂ : Subgroup V} (hW₁ : W₁ ∈ omegaA V Y) (hW₂ : W₂ ∈ omegaB V Y) :
    Nat.card (fixSub V Y) = 2 := by
  set X₀ := MulAction.stabilizer X (fixSub V Y) with hX₀
  have hYX₀ : ∀ y ∈ Y, y ∈ X₀ := fun y hy =>
    MulAction.mem_stabilizer_iff.2 (smul_fixSub_of_mem hy)
  have hoA : omegaA V Y = MulAction.orbit ↥X₀ W₁ := by
    ext A
    constructor
    · intro hA
      obtain ⟨y, hy, rfl⟩ := hGO.typeA_conj hW₁.1 hW₁.2.2 hA.1 hA.2.2
      exact ⟨⟨y, hYX₀ y hy⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact hGO.smul_mem_omegaA (MulAction.mem_stabilizer_iff.1 hx) hW₁
  have hoB : omegaB V Y = MulAction.orbit ↥X₀ W₂ := by
    ext A
    constructor
    · intro hA
      obtain ⟨y, hy, rfl⟩ := hGO.typeB_conj hW₂.1 hW₂.2.1 hW₂.2.2 hA.1 hA.2.1 hA.2.2
      exact ⟨⟨y, hYX₀ y hy⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact hGO.smul_mem_omegaB (MulAction.mem_stabilizer_iff.1 hx) hW₂
  obtain ⟨h₂, hh₂⟩ := mem_omega_iff.1 hW₂.1
  have hgW₂ : h₂⁻¹ • W₂ = fixSub V Y := by rw [inv_smul_eq_iff]; exact hh₂.symm
  have hBΩ : h₂⁻¹ • fixSub V Y ∈ omega V Y := smul_mem_omega (fixSub_mem_omega Y) h₂⁻¹
  have hB0 : h₂⁻¹ • fixSub V Y ≠ fixSub V Y := by
    intro h
    apply hW₂.2.1
    have : h₂⁻¹ • W₂ = h₂⁻¹ • fixSub V Y := by rw [hgW₂]; exact h.symm
    exact MulAction.injective h₂⁻¹ this
  rw [omega_eq] at hBΩ
  simp only [Set.mem_insert_iff, Set.mem_union] at hBΩ
  rcases hBΩ with hB | hB | hB
  · exact absurd hB hB0
  ·
    obtain ⟨y, hy, hyB⟩ := hGO.typeA_conj hW₁.1 hW₁.2.2 hB.1 hB.2.2
    have hs1 : (y⁻¹ * h₂⁻¹) • W₂ = fixSub V Y := by
      rw [mul_smul, hgW₂, inv_smul_eq_iff]; exact (smul_fixSub_of_mem hy).symm
    have hs2 : (y⁻¹ * h₂⁻¹) • fixSub V Y = W₁ := by rw [mul_smul, hyB, inv_smul_smul]
    have hc1 := card_stab_inf_le (y⁻¹ * h₂⁻¹) hs1 hs2
    have hs1' : (y⁻¹ * h₂⁻¹)⁻¹ • W₁ = fixSub V Y := by rw [inv_smul_eq_iff]; exact hs2.symm
    have hs2' : (y⁻¹ * h₂⁻¹)⁻¹ • fixSub V Y = W₂ := by rw [inv_smul_eq_iff]; exact hs1.symm
    have hc2 := card_stab_inf_le (y⁻¹ * h₂⁻¹)⁻¹ hs1' hs2'
    have hcard : Nat.card ↥(MulAction.stabilizer X (fixSub V Y) ⊓ MulAction.stabilizer X W₂) =
        Nat.card ↥(MulAction.stabilizer X (fixSub V Y) ⊓ MulAction.stabilizer X W₁) := by
      rw [inf_comm (MulAction.stabilizer X W₁)] at hc1
      refine le_antisymm hc1 ?_
      rw [inf_comm (MulAction.stabilizer X W₂)] at hc2
      exact hc2
    have hA := ncard_orbit_mul_card_inf X₀ W₁
    have hB' := ncard_orbit_mul_card_inf X₀ W₂
    rw [← hoA] at hA
    rw [← hoB] at hB'
    have hposA : 0 < Nat.card ↥(X₀ ⊓ MulAction.stabilizer X W₁) := Nat.card_pos
    have hAB : (omegaA V Y).ncard = (omegaB V Y).ncard := by
      have : (omegaA V Y).ncard * Nat.card ↥(X₀ ⊓ MulAction.stabilizer X W₁) =
          (omegaB V Y).ncard * Nat.card ↥(X₀ ⊓ MulAction.stabilizer X W₁) := by
        rw [hA, ← hcard, hB']
      exact Nat.eq_of_mul_eq_mul_right hposA this
    rw [hGO.ncard_omegaB_eq hW₂, hGO.omegaA_eq_orbit hW₁, ← MulAction.index_stabilizer] at hAB
    have hYc := Subgroup.index_mul_card (MulAction.stabilizer ↥Y W₁)
    rw [hAB] at hYc
    have hYpos : 0 < Nat.card Y := Nat.card_pos
    have hstab1 : Nat.card ↥(MulAction.stabilizer ↥Y W₁) = 1 := by
      have : Nat.card Y * Nat.card ↥(MulAction.stabilizer ↥Y W₁) = Nat.card Y * 1 := by
        rw [hYc, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hYpos this
    have hbot : MulAction.stabilizer ↥Y W₁ = ⊥ := (Subgroup.eq_bot_iff_card _).2 hstab1
    obtain ⟨w₀, hw₀, hw₀1⟩ := exists_ne_one_of_ne_bot (hGO.omega_ne_bot hW₁.1)
    have hsub : (W₁ : Set V) ⊆ {1, w₀} := by
      intro w hw
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · right
        obtain ⟨y', hy', hy'W, hy'w⟩ := hGO.typeA_trans hW₁.1 hW₁.2.2 hw₀ hw hw₀1 hw1
        have : (⟨y', hy'⟩ : Y) ∈ MulAction.stabilizer ↥Y W₁ := hy'W
        rw [hbot, Subgroup.mem_bot] at this
        have hy1 : y' = 1 := congrArg Subtype.val this
        rw [hy1, one_smul] at hy'w
        exact hy'w.symm
    have hle2 : Nat.card W₁ ≤ 2 := by
      have h1 := Nat.card_mono (Set.toFinite ({1, w₀} : Set V)) hsub
      have h2 : Nat.card ↥({1, w₀} : Set V) = 2 := by
        rw [Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hw₀1)]
      rw [h2] at h1
      exact h1
    have hge2 : 2 ≤ Nat.card W₁ := by
      have := (Subgroup.one_lt_card_iff_ne_bot W₁).2 (hGO.omega_ne_bot hW₁.1)
      omega
    rw [← card_eq_of_mem_omega hW₁.1]
    omega
  ·
    obtain ⟨y, hy, hyB⟩ := hGO.typeB_conj hW₂.1 hW₂.2.1 hW₂.2.2 hB.1 hB.2.1 hB.2.2
    exfalso
    have hs1 : (y⁻¹ * h₂⁻¹) • W₂ = fixSub V Y := by
      rw [mul_smul, hgW₂, inv_smul_eq_iff]; exact (smul_fixSub_of_mem hy).symm
    have hs2 : (y⁻¹ * h₂⁻¹) • fixSub V Y = W₂ := by rw [mul_smul, hyB, inv_smul_smul]
    exact hW₂.2.1 (eq_of_swap_of_odd hodd hs1 hs2)

end GOPair

end Odd

end CFSG.GH74.Uniqueness.SU.SU2
