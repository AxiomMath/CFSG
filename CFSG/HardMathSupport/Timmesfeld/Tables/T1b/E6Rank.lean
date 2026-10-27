module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Split

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def IsE6Params (t : StatedLieTag) (r f : ℕ) : Prop :=
  (t = .E6 ∧ 3 ∣ r ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ r ^ f + 1)

@[expose] def E6RankUpper : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (t : StatedLieTag) (n r f : ℕ),
    CFSG.Blueprint.LieModel S t n r f → IsE6Params t r f →
      CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 6 ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut S)) ≤ 7

@[expose] def E6RankLower : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    ∀ (t : StatedLieTag) (n r f : ℕ),
      CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f → IsE6Params t r f →
        (3 ∣ Nat.card (Subgroup.center L) → 6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) ∧
        ((t = .E6 → 9 ∣ r ^ f - 1) → (t = .twistedE6 → 9 ∣ r ^ f + 1) →
          6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)))

theorem nine_dvd_pow_three_sub_one {x : ℕ} (h : 3 ∣ x ^ 3 - 1) (hx : 1 ≤ x) : 9 ∣ x ^ 3 - 1 := by
  have h1 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have h2 : x ^ 3 % 9 = (x % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  have h3 : x ^ 3 % 3 = 1 := by omega
  have h4 : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases hx9 : x % 9 <;> omega

theorem nine_dvd_pow_three_add_one {x : ℕ} (h : 3 ∣ x ^ 3 + 1) : 9 ∣ x ^ 3 + 1 := by
  have h2 : x ^ 3 % 9 = (x % 9) ^ 3 % 9 := Nat.pow_mod _ _ _
  have h3 : x ^ 3 % 3 = 2 := by omega
  have h4 : x % 9 < 9 := Nat.mod_lt _ (by norm_num)
  interval_cases hx9 : x % 9 <;> omega

theorem nine_dvd_of_three_dvd_exponent {r f : ℕ} (hf : 3 ∣ f)
    (h : 3 ∣ r ^ f - 1) : 9 ∣ r ^ f - 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp
    · simp [zero_pow hf0.ne']
  obtain ⟨g, rfl⟩ := hf
  rw [mul_comm, pow_mul] at h ⊢
  exact nine_dvd_pow_three_sub_one h (Nat.one_le_pow _ _ hr)

theorem nine_dvd_of_three_dvd_exponent' {r f : ℕ} (hf : 3 ∣ f) (h : 3 ∣ r ^ f + 1) :
    9 ∣ r ^ f + 1 := by
  obtain ⟨g, rfl⟩ := hf
  rw [mul_comm, pow_mul] at h ⊢
  exact nine_dvd_pow_three_add_one h

theorem t1bLieHardAt_E6_of_rank (hU : E6RankUpper) (hL : E6RankLower) : T1bLieHardAt .E6 := by
  intro L _ _ hLC hq hK p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  simp only [OutEasy, not_or, not_not, ne_eq] at hE
  obtain ⟨rfl, h1, h2⟩ := hE
  have hpar : IsE6Params .E6 r f := Or.inl ⟨rfl, h1⟩
  have h9 : 9 ∣ r ^ f - 1 := nine_dvd_of_three_dvd_exponent h2 h1
  obtain ⟨hS6, hA7⟩ := hU _ .E6 n r f hm hpar
  obtain ⟨hZ, hlow⟩ := hL L hq .E6 n r f hm hpar
  have hmono := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp
  by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center L)
  · have := hZ hZ3
    omega
  · have h6 := hlow (fun _ => h9) (fun h => by cases h)
    have := pRank_centerQuotient_le_of_not_dvd hp hZ3
    omega

theorem t1bLieHardAt_twistedE6_of_rank (hU : E6RankUpper) (hL : E6RankLower) :
    T1bLieHardAt .twistedE6 := by
  intro L _ _ hLC hq hK p hp hp2 hcond ⟨n, r, f, hm, hE⟩
  simp only [OutEasy, not_or, not_not, ne_eq] at hE
  obtain ⟨rfl, h1, h2⟩ := hE
  have hpar : IsE6Params .twistedE6 r f := Or.inr ⟨rfl, h1⟩
  have h9 : 9 ∣ r ^ f + 1 := nine_dvd_of_three_dvd_exponent' h2 h1
  obtain ⟨hS6, hA7⟩ := hU _ .twistedE6 n r f hm hpar
  obtain ⟨hZ, hlow⟩ := hL L hq .twistedE6 n r f hm hpar
  have hmono := pRank_mulAut_le_mulAut_centerQuotient hq.1 hp
  by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center L)
  · have := hZ hZ3
    omega
  · have h6 := hlow (fun h => by cases h) (fun _ => h9)
    have := pRank_centerQuotient_le_of_not_dvd hp hZ3
    omega

theorem lieCoverRankHighE6_of_rank (hU : E6RankUpper) (hL : E6RankLower) :
    LieCoverRankHighE6 := by
  intro L _ _ hq hLC p hp hp2 hdvd h3 ⟨hp3, t, n, r, f, ht, hm⟩
  subst hp3
  have hpar : IsE6Params t r f := ht
  have h6 := (hL L hq t n r f hm hpar).1 hdvd
  have hS := (hU _ t n r f hm hpar).1
  omega

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
