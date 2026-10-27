module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.ThreeCycle

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_support_eq_three_of_le {b : Perm α} (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hle : b.support.card ≤ 3) : b.support.card = 3 := by
  have h2 := Perm.two_le_card_support_of_ne_one hb1
  rcases (by omega : b.support.card = 2 ∨ b.support.card = 3) with h | h
  · exfalso
    obtain ⟨x, y, hxy, rfl⟩ := Perm.card_support_eq_two.1 h
    apply hb1
    have hs : swap x y * swap x y = 1 := swap_mul_self x y
    calc swap x y = swap x y ^ 3 * (swap x y * swap x y)⁻¹ := by group
      _ = 1 := by rw [hb3, hs]; group
  · exact h

theorem support_subset_of_fix {b : Perm α} {S : Finset α} (h : ∀ x ∉ S, b x = x) :
    b.support ⊆ S := by
  intro x hx
  by_contra hxS
  exact (Perm.mem_support.1 hx) (h x hxS)

theorem three_mul_le_three_pow (j : ℕ) : 3 * j ≤ 3 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    have : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem exists_card_support_eq_three :
    ∀ (m : ℕ) (B : Subgroup (Perm α)) (S : Finset α), 1 ≤ m → (∀ b ∈ B, b ^ 3 = 1) →
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → (∀ b ∈ B, ∀ x ∉ S, b x = x) → S.card ≤ 3 * m →
      3 ^ m ≤ Nat.card B → ∃ b ∈ B, b.support.card = 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro B S hm hB3 hBc hfix hS hcard
  classical
  have hnt : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : B = ⊥ := eq_bot_iff.2 fun b hb => Subgroup.mem_bot.2 (h b hb)
    rw [hbot, Subgroup.card_bot] at hcard
    have : 3 ≤ 3 ^ m := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨b, hbB, hb1⟩ := hnt
  by_cases hm1 : m = 1
  · subst hm1
    refine ⟨b, hbB, card_support_eq_three_of_le hb1 (hB3 b hbB) ?_⟩
    exact (Finset.card_le_card (support_subset_of_fix (hfix b hbB))).trans (by simpa using hS)
  have hm2 : 2 ≤ m := by omega
  obtain ⟨x, hx⟩ : ∃ x, b x ≠ x := by
    by_contra h
    push Not at h
    exact hb1 (Perm.ext h)
  have hxS : x ∈ S := by
    by_contra h
    exact hx (hfix b hbB x h)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB3 g g.2)⟩
  set O := MulAction.orbit B x with hO
  set Bx := MulAction.stabilizer B x with hBx
  have horb : Nat.card O * Nat.card Bx = Nat.card B := by
    rw [hO, hBx, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group B x
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hOdvd : Nat.card O ∣ 3 ^ n := by rw [← hn, ← horb]; exact Dvd.intro _ rfl
  obtain ⟨j, hj, hOj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hOdvd
  have hOS : ∀ y ∈ O, y ∈ S := by
    rintro y ⟨g, rfl⟩
    show (g : Perm α) x ∈ S
    by_contra h
    have e := hfix _ (B.inv_mem g.2) _ h
    rw [show ((g : Perm α)⁻¹) ((g : Perm α) x) = x from (g : Perm α).symm_apply_apply x] at e
    rw [← e] at h
    exact h hxS
  have hbx : (⟨b, hbB⟩ : B) • x ∈ O := MulAction.mem_orbit x _
  have hj1 : 1 ≤ j := by
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero] at hOj
    have hxO : x ∈ O := MulAction.mem_orbit_self x
    have : (⟨b, hbB⟩ : B) • x = x := by
      have := (Set.ncard_eq_one.1 (by rw [← Nat.card_coe_set_eq]; exact hOj))
      obtain ⟨z, hz⟩ := this
      have h1 : (⟨b, hbB⟩ : B) • x ∈ ({z} : Set α) := hz ▸ hbx
      have h2 : x ∈ ({z} : Set α) := hz ▸ hxO
      rw [Set.mem_singleton_iff] at h1 h2
      rw [h1, h2]
    exact hx this
  set OF : Finset α := S.filter (fun y => y ∈ O) with hOF
  have hOFc : OF.card = 3 ^ j := by
    have e : OF = O.toFinset := by
      ext y
      simp only [hOF, Finset.mem_filter, Set.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hOS y h, h⟩⟩
    rw [e, Set.toFinset_card, ← Nat.card_eq_fintype_card, hOj]
  have hjm : j < m := by
    by_contra h
    have hle : OF.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    have : 3 ^ m ≤ 3 * m := by
      calc 3 ^ m ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = OF.card := hOFc.symm
        _ ≤ 3 * m := hle.trans hS
    have h3 : 3 * m < 3 ^ m := by
      have := three_mul_le_three_pow (m - 1)
      have e : 3 ^ m = 3 * 3 ^ (m - 1) := by
        rw [← pow_succ']; congr 1; omega
      have : 1 ≤ 3 ^ (m - 2) := Nat.one_le_pow _ _ (by norm_num)
      have e2 : 3 ^ (m - 1) = 3 * 3 ^ (m - 2) := by
        rw [← pow_succ']; congr 1; omega
      have := three_mul_le_three_pow (m - 2)
      omega
    omega
  set B1 : Subgroup (Perm α) := Bx.map B.subtype with hB1
  have hB1le : B1 ≤ B := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hB1fixO : ∀ s ∈ B1, ∀ y ∈ O, s y = y := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨g, rfl⟩
    have hsx : (s : Perm α) x = x := hs
    show (s : Perm α) ((g : Perm α) x) = (g : Perm α) x
    rw [← Perm.mul_apply, hBc _ s.2 _ g.2, Perm.mul_apply, hsx]
  have hcardB1 : Nat.card B1 = Nat.card Bx :=
    Subgroup.card_map_of_injective B.subtype_injective
  refine (ih (m - j) (by omega) B1 (S \ OF) (by omega) (fun s hs => hB3 s (hB1le hs))
    (fun a ha c hc => hBc a (hB1le ha) c (hB1le hc)) ?_ ?_ ?_).imp
    fun c hc => ⟨hB1le hc.1, hc.2⟩
  · intro s hs y hy
    rw [Finset.mem_sdiff, not_and_or, not_not] at hy
    rcases hy with hy | hy
    · exact hfix s (hB1le hs) y hy
    · exact hB1fixO s hs y (Finset.mem_filter.1 hy).2
  · rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hOFc]
    have := three_mul_le_three_pow j
    omega
  · rw [hcardB1]
    have h1 : Nat.card B = 3 ^ j * Nat.card Bx := by rw [← horb, hOj]
    have h2 : 3 ^ m = 3 ^ j * 3 ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [h2, h1] at hcard
    exact Nat.le_of_mul_le_mul_left hcard (by positivity)

end CFSG.LocalAnalysis.GLTheoremA.ThreeCycle
