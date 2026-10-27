module

public import CFSG.GH74.Conclusion

public section

namespace CFSG.GH74.Filter

open Subgroup Blueprint Assembly.LowTwoRank

@[expose] def S_alt_small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 5 ≤ n → n ≤ 7 →
    Nonempty (G ≃* alternatingGroup (Fin n)) → Open.twoRank G ≤ 2

@[expose] def S_alt_large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), 12 ≤ n →
    Nonempty (G ≃* alternatingGroup (Fin n)) → ¬ Gen4 G

@[expose] def S_iso_L4_two : Prop :=
  ∀ (G : Type) [Group G], StatedClassicalModel G .PSL 4 2 1 →
    Nonempty (G ≃* alternatingGroup (Fin 8))

@[expose] def S_iso_U4_two : Prop :=
  ∀ (G : Type) [Group G], StatedClassicalModel G .PSU 4 2 1 → StatedClassicalModel G .PSp 2 3 1

@[expose] def S_PSL_two_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .PSL 2 p f → Open.twoRank G ≤ 2

@[expose] def S_PSL_three_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .PSL 3 p f → Open.twoRank G ≤ 2

@[expose] def S_PSL_two_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSL 2 2 2 → Open.twoRank G ≤ 2

@[expose] def S_PSL_three_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSL 3 2 1 → Open.twoRank G ≤ 2

@[expose] def S_PSL_even_unipotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ), StatedClassicalModel G .PSL n 2 f →
    5 ≤ f * (n / 2) * ((n + 1) / 2) → ¬ Gen4 G

@[expose] def S_PSL_four_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → p ^ f % 8 = 1 →
    StatedClassicalModel G .PSL 4 p f → ¬ Gen4 G

@[expose] def S_PSL_five_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → p ^ f % 4 = 1 →
    StatedClassicalModel G .PSL 5 p f → ¬ Gen4 G

@[expose] def S_PSL_six_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .PSL 6 p f → ¬ Gen4 G

@[expose] def S_PSL_ge_seven_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 → 7 ≤ n →
    StatedClassicalModel G .PSL n p f → ¬ Gen4 G

@[expose] def S_PSU_three_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .PSU 3 p f → Open.twoRank G ≤ 2

@[expose] def S_PSU_three_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSU 3 2 2 → Open.twoRank G ≤ 2

@[expose] def S_PSU_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ), StatedClassicalModel G .PSU n 2 f →
    3 ≤ f * (n - 2) → ¬ Gen4 G

@[expose] def S_PSU_four_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → p ^ f % 8 = 7 →
    StatedClassicalModel G .PSU 4 p f → ¬ Gen4 G

@[expose] def S_PSU_five_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 → p ^ f % 4 = 3 →
    StatedClassicalModel G .PSU 5 p f → ¬ Gen4 G

@[expose] def S_PSU_six_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .PSU 6 p f → ¬ Gen4 G

@[expose] def S_PSU_ge_seven_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 → 7 ≤ n →
    StatedClassicalModel G .PSU n p f → ¬ Gen4 G

@[expose] def S_PSp_even_unipotent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ), StatedClassicalModel G .PSp n 2 f →
    5 ≤ f * (n + 1) → ¬ Gen4 G

@[expose] def S_PSp_three_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .PSp 3 2 1 → ¬ Gen4 G

@[expose] def S_PSp_odd_ge_three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 → 3 ≤ n →
    StatedClassicalModel G .PSp n p f → ¬ Gen4 G

@[expose] def S_POmegaOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 → 3 ≤ n →
    StatedClassicalModel G .POmegaOdd n p f → ¬ Gen4 G

@[expose] def S_POmegaPlus_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .POmegaPlus n p f → ¬ Gen4 G

@[expose] def S_POmegaMinus_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n p f : ℕ), p ≠ 2 →
    StatedClassicalModel G .POmegaMinus n p f → ¬ Gen4 G

@[expose] def S_POmegaPlus_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ), StatedClassicalModel G .POmegaPlus n 2 f →
    ¬ Gen4 G

@[expose] def S_POmegaMinus_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ), StatedClassicalModel G .POmegaMinus n 2 f →
    ¬ Gen4 G

@[expose] def S_G2_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ChevalleyExceptionalModel G .G2 2 f → ¬ Gen4 G

@[expose] def S_F4_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ChevalleyExceptionalModel G .F4 2 f → ¬ Gen4 G

@[expose] def S_E6_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ChevalleyExceptionalModel G .E6 2 f → ¬ Gen4 G

@[expose] def S_E7_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ChevalleyExceptionalModel G .E7 2 f → ¬ Gen4 G

@[expose] def S_E8_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ChevalleyExceptionalModel G .E8 2 f → ¬ Gen4 G

@[expose] def S_2E6_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ),
    ChevalleyExceptionalModel G .twistedE6 2 f → ¬ Gen4 G

@[expose] def S_3D4_even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ),
    ChevalleyExceptionalModel G .trialityD4 2 f → ¬ Gen4 G

@[expose] def S_F4_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    ChevalleyExceptionalModel G .F4 p f → ¬ Gen4 G

@[expose] def S_E6_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    ChevalleyExceptionalModel G .E6 p f → ¬ Gen4 G

@[expose] def S_E7_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    ChevalleyExceptionalModel G .E7 p f → ¬ Gen4 G

@[expose] def S_E8_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    ChevalleyExceptionalModel G .E8 p f → ¬ Gen4 G

@[expose] def S_2E6_odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), p ≠ 2 →
    ChevalleyExceptionalModel G .twistedE6 p f → ¬ Gen4 G

@[expose] def S_suzuki_large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p f : ℕ), 5 ≤ f → SuzukiModel G p f → ¬ Gen4 G

@[expose] def S_twistedF4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ), ReeTitsModel G .twistedF4 2 f → ¬ Gen4 G

@[expose] def S_Tits : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ReeTitsModel G .Tits 2 1 → ¬ Gen4 G

@[expose] def S_M11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], NativeSporadic.IsSporadic G .M11 → Open.twoRank G ≤ 2

@[expose] def sporadicOut : Finset TauCeti.SporadicName :=
  {.M24, .J4, .HS, .He, .Ru, .Suz, .ONan, .Co1, .Co2, .Co3, .Fi22, .Fi23, .Fi24Prime, .HN, .Th,
    .B, .M}

@[expose] def S_sporadic (s : TauCeti.SporadicName) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (∃ a b : G, a * b ≠ b * a) →
    NativeSporadic.IsSporadic G s → ¬ Gen4 G


section Conclusion

variable {G : Type} [Group G]

theorem conclusion_G2 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .G2 0 p f) : GH74Conclusion G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inl h⟩

theorem conclusion_D4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .trialityD4 0 p f) : GH74Conclusion G :=
  Or.inl ⟨p, f, hp, hp2, hf, Or.inr h⟩

theorem conclusion_PSp {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : LieModel G .PSp 2 p f) : GH74Conclusion G :=
  Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h⟩)

theorem conclusion_Ree {f : ℕ} (h : LieModel G .twistedG2 0 3 f) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inl ⟨f, h⟩))

theorem conclusion_PSL4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 8 ≠ 1) (h : LieModel G .PSL 4 p f) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, h⟩)))

theorem conclusion_PSU4 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : p ^ f % 8 ≠ 7) (h : LieModel G .PSU 4 p f) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, hq, h⟩))))

theorem conclusion_PSL5 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 4 = 3) (h : LieModel G .PSL 5 p f) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, h⟩)))))

theorem conclusion_PSU5 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hq : p ^ f % 4 = 1) (h : LieModel G .PSU 5 p f) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hf, hq, h⟩))))))

theorem conclusion_L2_8 (h : LieModel G .PSL 2 2 3) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))))))

theorem conclusion_L2_16 (h : LieModel G .PSL 2 2 4) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl h)))))))))

theorem conclusion_L3_4 (h : LieModel G .PSL 3 2 2) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (Or.inr (Or.inr (Or.inl h))))))))))

theorem conclusion_Sz8 (h : LieModel G .twistedB2 0 2 3) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (Or.inr (Or.inr (Or.inr h))))))))))

theorem conclusion_alt {n : ℕ} (h8 : 8 ≤ n) (h11 : n ≤ 11)
    (h : Nonempty (G ≃* alternatingGroup (Fin n))) : GH74Conclusion G :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, h8, h11, h⟩))))))))

theorem conclusion_sporadic {s : TauCeti.SporadicName}
    (hs : s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .McL ∨ s = .Ly)
    (h : NativeSporadic.IsSporadic G s) : GH74Conclusion G := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))))
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

theorem lieModel_of_classical {t : StatedLieTag} {n p f : ℕ} (ht : t ∈ classicalTags)
    (h : StatedClassicalModel G t n p f) : LieModel G t n p f :=
  Or.inl ⟨ht, h⟩

theorem lieModel_of_chevalley {t : StatedLieTag} {p f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel G t p f) : LieModel G t 0 p f :=
  Or.inr (Or.inl ⟨rfl, ht, h⟩)

theorem lieModel_of_reeTits {t : StatedLieTag} {p f : ℕ} (ht : t ∈ reeTitsTags)
    (h : ReeTitsModel G t p f) : LieModel G t 0 p f :=
  Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩))

theorem lieModel_of_suzuki {p f : ℕ} (h : SuzukiModel G p f) : LieModel G .twistedB2 0 p f :=
  Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))

end Conclusion

theorem odd_pow_mod_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p ^ f % 2 = 1 := by
  have h : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  rw [Nat.pow_mod, h]
  simp

theorem unip_PSL_bound {n f : ℕ} (hn : 6 ≤ n) (hf : 1 ≤ f) : 5 ≤ f * (n / 2) * ((n + 1) / 2) := by
  have h1 : 3 ≤ n / 2 := by omega
  have h2 : 3 ≤ (n + 1) / 2 := by omega
  calc 5 ≤ 1 * 3 * 3 := by norm_num
    _ ≤ f * (n / 2) * ((n + 1) / 2) := Nat.mul_le_mul (Nat.mul_le_mul hf h1) h2

section Cases

variable {G : Type} [Group G] [Finite G]

theorem excl_rank (hrk : 3 ≤ Open.twoRank G) (h : Open.twoRank G ≤ 2) : GH74Conclusion G :=
  absurd h (by omega)

omit [Finite G] in
theorem excl_gen (hgen : Gen4 G) (h : ¬ Gen4 G) : GH74Conclusion G :=
  absurd hgen h

theorem filter_alt (h_small : S_alt_small) (h_large : S_alt_large) (n : ℕ) (hn : 5 ≤ n)
    (he : Nonempty (G ≃* alternatingGroup (Fin n))) (hrk : 3 ≤ Open.twoRank G) (hgen : Gen4 G) :
    GH74Conclusion G := by
  by_cases h7 : n ≤ 7
  · exact excl_rank hrk (h_small G n hn h7 he)
  · by_cases h12 : 12 ≤ n
    · exact excl_gen hgen (h_large G n h12 he)
    · exact conclusion_alt (by omega) (by omega) he

theorem filter_PSL (h_two_odd : S_PSL_two_odd) (h_three_odd : S_PSL_three_odd)
    (h_two_four : S_PSL_two_four) (h_three_two : S_PSL_three_two)
    (h_unip : S_PSL_even_unipotent) (h_iso : S_iso_L4_two) (h_four : S_PSL_four_odd)
    (h_five : S_PSL_five_odd) (h_six : S_PSL_six_odd) (h_ge7 : S_PSL_ge_seven_odd)
    (n p f : ℕ) (hm : StatedClassicalModel G .PSL n p f) (hrk : 3 ≤ Open.twoRank G)
    (hgen : Gen4 G) : GH74Conclusion G := by
  obtain ⟨hp, hf, hn2, h22, -⟩ := hm.1
  have hL : ∀ {n p f : ℕ}, StatedClassicalModel G .PSL n p f → LieModel G .PSL n p f :=
    fun h => lieModel_of_classical (by decide) h
  by_cases hp2 : p = 2
  · subst hp2
    obtain rfl | rfl | rfl | rfl | hn6 : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    · have hf2 : 2 ≤ f := by
        by_contra h
        obtain rfl : f = 1 := by omega
        exact h22 (by norm_num)
      obtain rfl | rfl | rfl | hf5 : f = 2 ∨ f = 3 ∨ f = 4 ∨ 5 ≤ f := by omega
      · exact excl_rank hrk (h_two_four G hm)
      · exact conclusion_L2_8 (hL hm)
      · exact conclusion_L2_16 (hL hm)
      · exact excl_gen hgen (h_unip G 2 f hm (by simp; omega))
    · obtain rfl | rfl | hf3 : f = 1 ∨ f = 2 ∨ 3 ≤ f := by omega
      · exact excl_rank hrk (h_three_two G hm)
      · exact conclusion_L3_4 (hL hm)
      · exact excl_gen hgen (h_unip G 3 f hm (by simp; omega))
    · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
      · exact conclusion_alt (by norm_num) (by norm_num) (h_iso G hm)
      · exact excl_gen hgen (h_unip G 4 f hm (by simp; omega))
    · exact excl_gen hgen (h_unip G 5 f hm (by simp; omega))
    · exact excl_gen hgen (h_unip G n f hm (unip_PSL_bound hn6 hf))
  · obtain rfl | rfl | rfl | rfl | hn6 : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    · exact excl_rank hrk (h_two_odd G p f hp2 hm)
    · exact excl_rank hrk (h_three_odd G p f hp2 hm)
    · by_cases hq : p ^ f % 8 = 1
      · exact excl_gen hgen (h_four G p f hp2 hq hm)
      · exact conclusion_PSL4 hp hp2 hf hq (hL hm)
    · have := odd_pow_mod_two (f := f) hp hp2
      by_cases hq : p ^ f % 4 = 1
      · exact excl_gen hgen (h_five G p f hp2 hq hm)
      · exact conclusion_PSL5 hp hf (by omega) (hL hm)
    · by_cases h6 : n = 6
      · subst h6
        exact excl_gen hgen (h_six G p f hp2 hm)
      · exact excl_gen hgen (h_ge7 G n p f hp2 (by omega) hm)

theorem filter_PSU (h_three_odd : S_PSU_three_odd) (h_three_four : S_PSU_three_four)
    (h_even : S_PSU_even) (h_iso : S_iso_U4_two) (h_four : S_PSU_four_odd)
    (h_five : S_PSU_five_odd) (h_six : S_PSU_six_odd) (h_ge7 : S_PSU_ge_seven_odd)
    (n p f : ℕ) (hm : StatedClassicalModel G .PSU n p f) (hrk : 3 ≤ Open.twoRank G)
    (hgen : Gen4 G) : GH74Conclusion G := by
  obtain ⟨hp, hf, hn3, h32⟩ := hm.1
  have hL : ∀ {n p f : ℕ}, StatedClassicalModel G .PSU n p f → LieModel G .PSU n p f :=
    fun h => lieModel_of_classical (by decide) h
  by_cases hp2 : p = 2
  · subst hp2
    obtain rfl | rfl | hn5 : n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
    · have hf2 : 2 ≤ f := by
        by_contra h
        obtain rfl : f = 1 := by omega
        exact h32 (by norm_num)
      obtain rfl | hf3 : f = 2 ∨ 3 ≤ f := by omega
      · exact excl_rank hrk (h_three_four G hm)
      · exact excl_gen hgen (h_even G 3 f hm (by simp; omega))
    · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
      · exact conclusion_PSp Nat.prime_three (by norm_num) le_rfl
          (lieModel_of_classical (by decide) (h_iso G hm))
      · exact excl_gen hgen (h_even G 4 f hm (by omega))
    · exact excl_gen hgen (h_even G n f hm (le_trans (by norm_num) (Nat.mul_le_mul hf (show 3 ≤ n - 2 by omega))))
  · obtain rfl | rfl | rfl | hn6 : n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
    · exact excl_rank hrk (h_three_odd G p f hp2 hm)
    · have := odd_pow_mod_two (f := f) hp hp2
      by_cases hq : p ^ f % 8 = 7
      · exact excl_gen hgen (h_four G p f hp2 hq hm)
      · exact conclusion_PSU4 hp hp2 hf hq (hL hm)
    · have := odd_pow_mod_two (f := f) hp hp2
      by_cases hq : p ^ f % 4 = 3
      · exact excl_gen hgen (h_five G p f hp2 hq hm)
      · exact conclusion_PSU5 hp hf (by omega) (hL hm)
    · by_cases h6 : n = 6
      · subst h6
        exact excl_gen hgen (h_six G p f hp2 hm)
      · exact excl_gen hgen (h_ge7 G n p f hp2 (by omega) hm)

theorem filter_PSp (h_unip : S_PSp_even_unipotent) (h_three_two : S_PSp_three_two)
    (h_odd : S_PSp_odd_ge_three) (n p f : ℕ) (hm : StatedClassicalModel G .PSp n p f)
    (hgen : Gen4 G) : GH74Conclusion G := by
  obtain ⟨hp, hf, hn2, h22⟩ := hm.1
  by_cases hp2 : p = 2
  · subst hp2
    obtain rfl | rfl | hn4 : n = 2 ∨ n = 3 ∨ 4 ≤ n := by omega
    · have hf2 : 2 ≤ f := by
        by_contra h
        obtain rfl : f = 1 := by omega
        exact h22 (by norm_num)
      exact excl_gen hgen (h_unip G 2 f hm (by omega))
    · obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
      · exact excl_gen hgen (h_three_two G hm)
      · exact excl_gen hgen (h_unip G 3 f hm (by omega))
    · exact excl_gen hgen (h_unip G n f hm (by nlinarith))
  · by_cases hn2' : n = 2
    · subst hn2'
      exact conclusion_PSp hp hp2 hf (lieModel_of_classical (by decide) hm)
    · exact excl_gen hgen (h_odd G n p f hp2 (by omega) hm)

theorem filter_orthogonal (h_odd : S_POmegaOdd) (h_plus_odd : S_POmegaPlus_odd)
    (h_minus_odd : S_POmegaMinus_odd) (h_plus_even : S_POmegaPlus_even)
    (h_minus_even : S_POmegaMinus_even) (t : StatedLieTag) (n p f : ℕ)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hm : StatedClassicalModel G t n p f) (hgen : Gen4 G) : GH74Conclusion G := by
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, -, hn3, hp2⟩ := hm.1
    exact excl_gen hgen (h_odd G n p f hp2 hn3 hm)
  · by_cases hp2 : p = 2
    · subst hp2
      exact excl_gen hgen (h_plus_even G n f hm)
    · exact excl_gen hgen (h_plus_odd G n p f hp2 hm)
  · by_cases hp2 : p = 2
    · subst hp2
      exact excl_gen hgen (h_minus_even G n f hm)
    · exact excl_gen hgen (h_minus_odd G n p f hp2 hm)

theorem filter_chevalley (h_G2e : S_G2_even) (h_F4e : S_F4_even) (h_E6e : S_E6_even)
    (h_E7e : S_E7_even) (h_E8e : S_E8_even) (h_2E6e : S_2E6_even) (h_3D4e : S_3D4_even)
    (h_F4o : S_F4_odd) (h_E6o : S_E6_odd) (h_E7o : S_E7_odd) (h_E8o : S_E8_odd)
    (h_2E6o : S_2E6_odd) (t : StatedLieTag) (ht : t ∈ chevalleyExceptionalTags) (p f : ℕ)
    (hm : ChevalleyExceptionalModel G t p f) (hgen : Gen4 G) : GH74Conclusion G := by
  have hadm := hm.1
  obtain ⟨hp, hf, -⟩ := hadm
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  by_cases hp2 : p = 2
  · subst hp2
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact excl_gen hgen (h_G2e G f hm)
    · exact excl_gen hgen (h_F4e G f hm)
    · exact excl_gen hgen (h_E6e G f hm)
    · exact excl_gen hgen (h_E7e G f hm)
    · exact excl_gen hgen (h_E8e G f hm)
    · exact excl_gen hgen (h_2E6e G f hm)
    · exact excl_gen hgen (h_3D4e G f hm)
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact conclusion_G2 hp hp2 hf (lieModel_of_chevalley (by decide) hm)
    · exact excl_gen hgen (h_F4o G p f hp2 hm)
    · exact excl_gen hgen (h_E6o G p f hp2 hm)
    · exact excl_gen hgen (h_E7o G p f hp2 hm)
    · exact excl_gen hgen (h_E8o G p f hp2 hm)
    · exact excl_gen hgen (h_2E6o G p f hp2 hm)
    · exact conclusion_D4 hp hp2 hf (lieModel_of_chevalley (by decide) hm)

theorem filter_reeTits (h_F4 : S_twistedF4) (h_Tits : S_Tits) (t : StatedLieTag)
    (ht : t ∈ reeTitsTags) (p f : ℕ) (hm : ReeTitsModel G t p f) (hgen : Gen4 G) :
    GH74Conclusion G := by
  have hadm := hm.1
  simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · obtain ⟨-, -, -, hp3, -, -⟩ := hadm
    subst hp3
    exact conclusion_Ree (lieModel_of_reeTits (by decide) hm)
  · obtain ⟨-, -, -, hp2, -, -⟩ := hadm
    subst hp2
    exact excl_gen hgen (h_F4 G f hm)
  · obtain ⟨-, -, -, hp2, hf1⟩ := hadm
    subst hp2 hf1
    exact excl_gen hgen (h_Tits G hm)

theorem filter_suzuki (h_large : S_suzuki_large) (p f : ℕ) (hm : SuzukiModel G p f)
    (hgen : Gen4 G) : GH74Conclusion G := by
  have hm' := hm
  obtain ⟨hp2, a, ha, K, -, -, hfa, -⟩ := hm'
  subst hp2
  by_cases ha1 : a = 1
  · subst ha1
    obtain rfl : f = 3 := by omega
    exact conclusion_Sz8 (lieModel_of_suzuki hm)
  · exact excl_gen hgen (h_large G 2 f (by omega) hm)

theorem filter_sporadic (h_M11 : S_M11) (h_spor : ∀ s ∈ sporadicOut, S_sporadic s)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (s : TauCeti.SporadicName)
    (he : NativeSporadic.IsSporadic G s) (hrk : 3 ≤ Open.twoRank G) (hgen : Gen4 G) :
    GH74Conclusion G := by
  have out : ∀ s ∈ sporadicOut, NativeSporadic.IsSporadic G s → GH74Conclusion G :=
    fun s hs he => excl_gen hgen (h_spor s hs G hnonab he)
  cases s
  · exact excl_rank hrk (h_M11 G he)
  · exact conclusion_sporadic (by simp) he
  · exact conclusion_sporadic (by simp) he
  · exact conclusion_sporadic (by simp) he
  · exact out _ (by decide) he
  · exact conclusion_sporadic (by simp) he
  · exact conclusion_sporadic (by simp) he
  · exact conclusion_sporadic (by simp) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact conclusion_sporadic (by simp) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact conclusion_sporadic (by simp) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he
  · exact out _ (by decide) he

end Cases


theorem filter_of_families
    (h_alt_small : S_alt_small) (h_alt_large : S_alt_large)
    (h_iso_L4 : S_iso_L4_two) (h_iso_U4 : S_iso_U4_two)
    (h_PSL_two_odd : S_PSL_two_odd) (h_PSL_three_odd : S_PSL_three_odd)
    (h_PSL_two_four : S_PSL_two_four) (h_PSL_three_two : S_PSL_three_two)
    (h_PSL_even_unip : S_PSL_even_unipotent) (h_PSL_four_odd : S_PSL_four_odd)
    (h_PSL_five_odd : S_PSL_five_odd) (h_PSL_six_odd : S_PSL_six_odd)
    (h_PSL_ge_seven_odd : S_PSL_ge_seven_odd)
    (h_PSU_three_odd : S_PSU_three_odd) (h_PSU_three_four : S_PSU_three_four)
    (h_PSU_even : S_PSU_even) (h_PSU_four_odd : S_PSU_four_odd)
    (h_PSU_five_odd : S_PSU_five_odd) (h_PSU_six_odd : S_PSU_six_odd)
    (h_PSU_ge_seven_odd : S_PSU_ge_seven_odd)
    (h_PSp_even_unip : S_PSp_even_unipotent) (h_PSp_three_two : S_PSp_three_two)
    (h_PSp_odd : S_PSp_odd_ge_three)
    (h_POmegaOdd : S_POmegaOdd) (h_POmegaPlus_odd : S_POmegaPlus_odd)
    (h_POmegaMinus_odd : S_POmegaMinus_odd) (h_POmegaPlus_even : S_POmegaPlus_even)
    (h_POmegaMinus_even : S_POmegaMinus_even)
    (h_G2e : S_G2_even) (h_F4e : S_F4_even) (h_E6e : S_E6_even) (h_E7e : S_E7_even)
    (h_E8e : S_E8_even) (h_2E6e : S_2E6_even) (h_3D4e : S_3D4_even)
    (h_F4o : S_F4_odd) (h_E6o : S_E6_odd) (h_E7o : S_E7_odd) (h_E8o : S_E8_odd)
    (h_2E6o : S_2E6_odd)
    (h_suzuki : S_suzuki_large) (h_twistedF4 : S_twistedF4) (h_Tits : S_Tits)
    (h_M11 : S_M11) (h_sporadic : ∀ s ∈ sporadicOut, S_sporadic s) :
    ∀ (G : Type) [Group G] [Finite G], Catalog G → (∃ a b : G, a * b ≠ b * a) →
      3 ≤ Open.twoRank G → Gen4 G → GH74Conclusion G := by
  intro G _ _ hcat hnonab hrk hgen
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, he⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, he⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact filter_alt h_alt_small h_alt_large n hn he hrk hgen
  · have hcl := Milestones.statedClassicalModel_tag_mem G t n p f hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcl
    rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact filter_PSL h_PSL_two_odd h_PSL_three_odd h_PSL_two_four h_PSL_three_two
        h_PSL_even_unip h_iso_L4 h_PSL_four_odd h_PSL_five_odd h_PSL_six_odd h_PSL_ge_seven_odd
        n p f hm hrk hgen
    · exact filter_PSU h_PSU_three_odd h_PSU_three_four h_PSU_even h_iso_U4 h_PSU_four_odd
        h_PSU_five_odd h_PSU_six_odd h_PSU_ge_seven_odd n p f hm hrk hgen
    · exact filter_PSp h_PSp_even_unip h_PSp_three_two h_PSp_odd n p f hm hgen
    · exact filter_orthogonal h_POmegaOdd h_POmegaPlus_odd h_POmegaMinus_odd h_POmegaPlus_even
        h_POmegaMinus_even _ n p f (Or.inl rfl) hm hgen
    · exact filter_orthogonal h_POmegaOdd h_POmegaPlus_odd h_POmegaMinus_odd h_POmegaPlus_even
        h_POmegaMinus_even _ n p f (Or.inr (Or.inl rfl)) hm hgen
    · exact filter_orthogonal h_POmegaOdd h_POmegaPlus_odd h_POmegaMinus_odd h_POmegaPlus_even
        h_POmegaMinus_even _ n p f (Or.inr (Or.inr rfl)) hm hgen
  · rcases hex with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact filter_chevalley h_G2e h_F4e h_E6e h_E7e h_E8e h_2E6e h_3D4e h_F4o h_E6o h_E7o h_E8o
        h_2E6o t ht p f hm hgen
    · exact filter_reeTits h_twistedF4 h_Tits t ht p f hm hgen
    · exact filter_suzuki h_suzuki p f hm hgen
  · exact filter_sporadic h_M11 h_sporadic hnonab s he hrk hgen

end CFSG.GH74.Filter
