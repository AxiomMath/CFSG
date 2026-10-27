module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

variable {W V N : Type} [Group W] [Finite W] [Group V] [Finite V] [Group N] [Finite N]

theorem asl_section (act : N →* MulAut W) (vact : N →* MulAut V) (π : W →* V)
    (hπ : Function.Surjective π) (hπact : ∀ (n : N) (w : W), π (act n w) = vact n (π w))
    (hW : ∀ w : W, w ^ 2 = 1) (hV8 : Nat.card V = 8)
    (hU : ∀ n : N, ∀ u ∈ π.ker, act n u = u)
    (htrans : ∀ a b a' b' : V, a ≠ 1 → b ≠ 1 → a ≠ b → a' ≠ 1 → b' ≠ 1 → a' ≠ b' →
      ∃ n : N, vact n a = a' ∧ vact n b = b')
    (S : Subgroup N) (hSN : Nat.card N = 21 * Nat.card S) {w₀ : W}
    (hw₀ : ∀ x ∈ S, act x w₀ = w₀) (hw₀1 : π w₀ ≠ 1) :
    ∃ s : V → W, s 1 = 1 ∧ (∀ v, π (s v) = v) ∧
      ∀ (n : N) (v : V), v ≠ 1 → s (vact n v) = act n (s v) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  have hWcomm : ∀ a b : W, a * b = b * a := by
    intro a b
    have ha : a = a⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hW a)
    have hb : b = b⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hW b)
    have hab : a * b = (a * b)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hW (a * b))
    rw [hab, mul_inv_rev, ← ha, ← hb]
  letI : MulAction N W := MulAction.compHom W act
  letI : MulAction N V := MulAction.compHom V vact
  have hsurj_orbit : ∀ v : V, v ≠ 1 → ∃ n : N, vact n (π w₀) = v := by
    intro v hv
    have hcardV : Fintype.card V = 8 := by
      rw [← Nat.card_eq_fintype_card]; exact hV8
    have hex : ∃ b : V, b ≠ 1 ∧ b ≠ π w₀ ∧ b ≠ v := by
      have hlt : ({1, π w₀, v} : Finset V).card < (Finset.univ : Finset V).card := by
        have h3 : ({1, π w₀, v} : Finset V).card ≤ 3 := Finset.card_le_three
        rw [Finset.card_univ, hcardV]
        omega
      obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
      exact ⟨b, hb.1, hb.2.1, hb.2.2⟩
    obtain ⟨b, hb1, hb2, hb3⟩ := hex
    obtain ⟨n, hn, -⟩ :=
      htrans (π w₀) b v b hw₀1 hb1 (Ne.symm hb2) hv hb1 (Ne.symm hb3)
    exact ⟨n, hn⟩
  have horbit : MulAction.orbit N (π w₀) = {v : V | v ≠ 1} := by
    ext v
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      change vact n (π w₀) ≠ 1
      intro h
      exact hw₀1 ((vact n).injective (h.trans (map_one (vact n)).symm))
    · intro hv
      exact hsurj_orbit v hv
  have hncard : ({v : V | v ≠ 1} : Set V).ncard = 7 := by
    have hset : ({v : V | v ≠ 1} : Set V) = Set.univ \ ({1} : Set V) := by
      ext v; simp
    rw [hset, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : V)), Set.ncard_univ,
      hV8]
  have hidxV : (MulAction.stabilizer N (π w₀)).index = 7 := by
    rw [MulAction.index_stabilizer, horbit]
    exact hncard
  have hstabWV : (MulAction.stabilizer N w₀) ≤ (MulAction.stabilizer N (π w₀)) := by
    intro n hn
    change vact n (π w₀) = π w₀
    change act n w₀ = w₀ at hn
    rw [← hπact n w₀, hn]
  let c : MulAction.stabilizer N (π w₀) →* W :=
    { toFun := fun n => act n.1 w₀ * w₀⁻¹
      map_one' := by simp
      map_mul' := by
        intro n m
        have hcm : act m.1 w₀ * w₀⁻¹ ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hπact]
          have hm : vact m.1 (π w₀) = π w₀ := m.2
          rw [hm, mul_inv_cancel]
        have hfix : act n.1 (act m.1 w₀ * w₀⁻¹) = act m.1 w₀ * w₀⁻¹ :=
          hU n.1 _ hcm
        have hmw : act m.1 w₀ = (act m.1 w₀ * w₀⁻¹) * w₀ := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
        calc act (n.1 * m.1) w₀ * w₀⁻¹
            = act n.1 (act m.1 w₀) * w₀⁻¹ := by
                rw [map_mul act n.1 m.1, MulAut.mul_apply]
          _ = act n.1 ((act m.1 w₀ * w₀⁻¹) * w₀) * w₀⁻¹ := by
                conv_lhs => rw [hmw]
          _ = (act n.1 (act m.1 w₀ * w₀⁻¹)) * (act n.1 w₀) * w₀⁻¹ := by
                rw [map_mul (act n.1) (act m.1 w₀ * w₀⁻¹) w₀]
          _ = (act m.1 w₀ * w₀⁻¹) * act n.1 w₀ * w₀⁻¹ := by rw [hfix]
          _ = (act n.1 w₀ * w₀⁻¹) * (act m.1 w₀ * w₀⁻¹) := by
                conv_lhs => rw [mul_assoc]
                exact hWcomm (act m.1 w₀ * w₀⁻¹) (act n.1 w₀ * w₀⁻¹) }
  have hker : c.ker = (MulAction.stabilizer N w₀).subgroupOf
      (MulAction.stabilizer N (π w₀)) := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change act n.1 w₀ * w₀⁻¹ = 1 ↔ act n.1 w₀ = w₀
    rw [mul_eq_one_iff_eq_inv]
    simp
  have hr : (MulAction.stabilizer N w₀).relIndex (MulAction.stabilizer N (π w₀))
      = Nat.card c.range := by
    change ((MulAction.stabilizer N w₀).subgroupOf
      (MulAction.stabilizer N (π w₀))).index = Nat.card c.range
    rw [← hker, Subgroup.index_ker]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW2 : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  obtain ⟨j, hj⟩ : ∃ j, Nat.card c.range = 2 ^ j :=
    (IsPGroup.iff_card (p := 2) (G := c.range)).mp (hW2.to_subgroup c.range)
  have hSidx : S.index = 21 := by
    have h := Subgroup.card_mul_index (H := S)
    rw [hSN] at h
    exact Nat.eq_of_mul_eq_mul_left (Finite.card_pos (α := S)) (by rw [h, mul_comm])
  have hle : S ≤ MulAction.stabilizer N w₀ := by
    intro x hx
    change act x w₀ = w₀
    exact hw₀ x hx
  have hdiv : (MulAction.stabilizer N w₀).index ∣ 21 := by
    rw [← hSidx]
    exact Subgroup.index_dvd_of_le hle
  have htower : (MulAction.stabilizer N w₀).index
      = 7 * (MulAction.stabilizer N w₀).relIndex (MulAction.stabilizer N (π w₀)) := by
    rw [← Subgroup.relIndex_mul_index hstabWV, hidxV, mul_comm]
  have hindex : (MulAction.stabilizer N w₀).index = 7 * 2 ^ j := by
    rw [htower, hr, hj]
  have h2j : 2 ^ j ∣ 3 := by
    have h21 : 7 * 2 ^ j ∣ 21 := by
      rw [← hindex]
      exact hdiv
    have h21' : (7 : ℕ) * 2 ^ j ∣ 7 * 3 := by
      rw [show (7 : ℕ) * 3 = 21 by rfl]
      exact h21
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < (7 : ℕ))).mp h21'
  have hj0 : j = 0 := by
    have hjle : 2 ^ j ≤ 3 := Nat.le_of_dvd (by decide : 0 < (3 : ℕ)) h2j
    have hjle1 : j ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_not_le h)
      have h4 : 4 ≤ 2 ^ j := by
        calc (4 : ℕ) = 2 ^ 2 := by rfl
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) h2
      omega
    have hj_cases : j = 0 ∨ j = 1 := by omega
    rcases hj_cases with hj0' | hj1'
    · exact hj0'
    · exfalso
      rw [hj1'] at h2j
      exact absurd h2j (by decide)
  have hr1 : (MulAction.stabilizer N w₀).relIndex (MulAction.stabilizer N (π w₀)) = 1 := by
    rw [hr, hj, hj0]
    rfl
  have hstab_eq : (MulAction.stabilizer N w₀) = MulAction.stabilizer N (π w₀) := by
    refine le_antisymm hstabWV ?_
    exact Subgroup.relIndex_eq_one.mp hr1
  have hwell : ∀ n m : N, vact n (π w₀) = vact m (π w₀) → act n w₀ = act m w₀ := by
    intro n m h
    have hmn : m⁻¹ * n ∈ MulAction.stabilizer N (π w₀) := by
      change vact (m⁻¹ * n) (π w₀) = π w₀
      rw [map_mul vact m⁻¹ n]
      change vact m⁻¹ (vact n (π w₀)) = π w₀
      rw [h, ← MulAut.mul_apply, ← map_mul vact m⁻¹ m, inv_mul_cancel, map_one]
      rfl
    have hmn' : m⁻¹ * n ∈ MulAction.stabilizer N w₀ := hstab_eq.symm ▸ hmn
    have hfix : act (m⁻¹ * n) w₀ = w₀ := hmn'
    calc act n w₀ = act (m * (m⁻¹ * n)) w₀ := by rw [mul_inv_cancel_left]
      _ = act m (act (m⁻¹ * n) w₀) := by rw [map_mul]; rfl
      _ = act m w₀ := by rw [hfix]
  let s : V → W := fun v =>
    if hv : v = 1 then 1 else act (Classical.choose (hsurj_orbit v hv)) w₀
  have sec_eq : ∀ (v : V) (hv : v ≠ 1) (n : N), vact n (π w₀) = v → s v = act n w₀ := by
    intro v hv n hn
    have hch := Classical.choose_spec (hsurj_orbit v hv)
    dsimp only [s]
    rw [dif_neg hv]
    exact (hwell n (Classical.choose (hsurj_orbit v hv)) (by rw [hn, hch])).symm
  refine ⟨s, ?_, ?_, ?_⟩
  · dsimp only [s]; simp
  · intro v
    by_cases hv : v = 1
    · subst hv
      dsimp only [s]; simp
    · dsimp only [s]
      rw [dif_neg hv]
      exact (hπact (Classical.choose (hsurj_orbit v hv)) w₀).trans
        (Classical.choose_spec (hsurj_orbit v hv))
  · intro n v hv
    have hne : vact n v ≠ 1 := by
      intro h
      apply hv
      have h1 : vact n⁻¹ (vact n v) = v := by
        rw [← MulAut.mul_apply, ← map_mul vact n⁻¹ n, inv_mul_cancel, map_one]
        rfl
      rw [h, map_one] at h1
      exact h1.symm
    have hkey : vact (n * Classical.choose (hsurj_orbit v hv)) (π w₀) = vact n v := by
      rw [map_mul]
      change vact n (vact (Classical.choose (hsurj_orbit v hv)) (π w₀)) = vact n v
      rw [Classical.choose_spec (hsurj_orbit v hv)]
    have hsv : s v = act (Classical.choose (hsurj_orbit v hv)) w₀ := by
      dsimp only [s]; rw [dif_neg hv]
    rw [sec_eq (vact n v) hne (n * Classical.choose (hsurj_orbit v hv)) hkey, hsv, map_mul]
    rfl

end CFSG.OddStandard.HigherRank.YamadaG23
