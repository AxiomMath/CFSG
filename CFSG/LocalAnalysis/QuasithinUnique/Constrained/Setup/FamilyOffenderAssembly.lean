module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module

section Assembly

variable {G : Type*} [Group G] [Finite G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E]

omit [Finite G] in
theorem finrank_range_sub1_le_of_offender (ρ : G →* (E ≃ₗ[ZMod 2] E)) {B : Subgroup G}
    {F : Submodule (ZMod 2) E} (hF : ∀ a ∈ B, ∀ x ∈ F, ρ a x = x) {a : G} (ha : a ∈ B) {n : ℕ}
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) F ≤ n) :
    finrank (ZMod 2) (LinearMap.range (sub1 (ρ a))) ≤ n := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (sub1 (ρ a))
  have h2 : finrank (ZMod 2) F ≤ finrank (ZMod 2) (LinearMap.ker (sub1 (ρ a))) := by
    refine Submodule.finrank_mono fun x hx => ?_
    rw [LinearMap.mem_ker, sub1_apply, hF a ha x hx, sub_self]
  omega

theorem no_offender_of_ranks (ρ : G →* (E ≃ₗ[ZMod 2] E)) (L B : Subgroup G) (hB1 : B ≠ ⊥)
    (F : Submodule (ZMod 2) E) (hF : ∀ a ∈ B, ∀ x ∈ F, ρ a x = x)
    (hin : ∀ t ∈ B, t ∈ L → t ≠ 1 → 4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ t))))
    (hcard : ∀ T : Subgroup G, T ≤ B → T ≤ L → Nat.card T ≤ 4)
    (hout : ∀ a ∈ B, a ∉ L → 2 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ a))))
    (hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ L → a' ∉ L → a * a' ∈ L)
    (hoff : finrank (ZMod 2) E - finrank (ZMod 2) F ≤ Nat.log 2 (Nat.card B)) : False := by
  classical
  obtain ⟨t, htB, ht1⟩ : ∃ t ∈ B, t ≠ 1 := by
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    exact ⟨t, t.2, fun h => ht (Subtype.ext h)⟩
  have hlog : ∀ n : ℕ, Nat.card B ≤ n → Nat.log 2 (Nat.card B) ≤ Nat.log 2 n :=
    fun n hn => Nat.log_mono_right hn
  by_cases hBL : ∀ a ∈ B, a ∈ L
  ·
    have hc : Nat.card B ≤ 4 := hcard B le_rfl hBL
    have h1 := hlog 4 hc
    have h2 : Nat.log 2 4 = 2 := by decide
    have h3 := finrank_range_sub1_le_of_offender ρ hF htB (hoff.trans (h1.trans h2.le))
    have h4 := hin t htB (hBL t htB) ht1
    omega
  · push Not at hBL
    obtain ⟨a₀, ha₀B, ha₀L⟩ := hBL
    set T : Subgroup G := B ⊓ L with hT
    have hTB : T ≤ B := inf_le_left
    have hTL : T ≤ L := inf_le_right
    have hT4 : Nat.card T ≤ 4 := hcard T hTB hTL
    have hBT : Nat.card B ≤ 2 * Nat.card T := by
      let f : B → T ⊕ T := fun x =>
        if hx : (x : G) ∈ L then Sum.inl ⟨x, x.2, hx⟩
        else Sum.inr ⟨a₀ * x, B.mul_mem ha₀B x.2, hidx a₀ ha₀B x x.2 ha₀L hx⟩
      have hf : Function.Injective f := by
        intro x y hxy
        by_cases hx : (x : G) ∈ L <;> by_cases hy : (y : G) ∈ L
        · simp only [f, hx, hy, dite_true, Sum.inl.injEq] at hxy
          exact Subtype.ext (congrArg (fun z : T => (z : G)) hxy)
        · simp [f, hx, hy] at hxy
        · simp [f, hx, hy] at hxy
        · simp only [f, hx, hy, dite_false, Sum.inr.injEq] at hxy
          exact Subtype.ext (mul_left_cancel (congrArg (fun z : T => (z : G)) hxy))
      have := Nat.card_le_card_of_injective f hf
      rwa [Nat.card_sum, ← two_mul] at this
    by_cases hTbot : ∀ x ∈ T, x = 1
    ·
      have hT1 : Nat.card T ≤ 1 := by
        have : T = ⊥ := (Subgroup.eq_bot_iff_forall T).2 hTbot
        rw [this, Subgroup.card_bot]
      have hc : Nat.card B ≤ 2 := by omega
      have h1 := hlog 2 hc
      have h2 : Nat.log 2 2 = 1 := by decide
      have h3 := finrank_range_sub1_le_of_offender ρ hF ha₀B (hoff.trans (h1.trans h2.le))
      have h4 := hout a₀ ha₀B ha₀L
      omega
    · push Not at hTbot
      obtain ⟨u, huT, hu1⟩ := hTbot
      have hc : Nat.card B ≤ 8 := by omega
      have h1 := hlog 8 hc
      have h2 : Nat.log 2 8 = 3 := by decide
      have h3 := finrank_range_sub1_le_of_offender ρ hF (hTB huT) (hoff.trans (h1.trans h2.le))
      have h4 := hin u (hTB huT) (hTL huT) hu1
      omega

end Assembly

end CFSG.QuasithinUnique.Setup.Family
