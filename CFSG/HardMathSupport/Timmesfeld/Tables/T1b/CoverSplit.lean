module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨hQ.1⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  refine ⟨hp, hQ.2, ?_⟩
  have h := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using h

theorem case_of_dvd_table {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : StatedLieTag} {n r f : ℕ}
    (h : p ∣ (genericOrders t n r f).1 * (genericOrders t n r f).2 *
      ((exceptionalOrders t n r f).1 * (exceptionalOrders t n r f).2)) :
    (t = .PSL ∧ p ∣ Nat.gcd n (r ^ f - 1)) ∨ (t = .PSU ∧ p ∣ Nat.gcd n (r ^ f + 1)) ∨
      ((t = .E6 ∧ p = 3 ∧ 3 ∣ r ^ f - 1) ∨ (t = .twistedE6 ∧ p = 3 ∧ 3 ∣ r ^ f + 1)) ∨
      (p = 3 ∧ ((t = .PSL ∧ n = 2 ∧ r = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ r = 3 ∧ f = 1) ∨
        (t = .G2 ∧ n = 0 ∧ r = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ r = 3 ∧ f = 1))) := by
  have hno : ∀ a : ℕ, a ∣ 4 → p ∣ a → False := fun a ha hpa => by
    have h4 : p ∣ 2 ^ 2 := by simpa using hpa.trans ha
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have hsnd := Multiplier.genericOrders_snd_le t n r f
  have hex := Multiplier.exceptionalOrders_le t n r f
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1
    · cases t <;> simp only [genericOrders] at h1
      case PSL => exact Or.inl ⟨rfl, h1⟩
      case PSU => exact Or.inr (Or.inl ⟨rfl, h1⟩)
      case E6 =>
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (h1.trans (Nat.gcd_dvd_left _ _))
        have hd := h1.trans (Nat.gcd_dvd_right _ _)
        rw [hp3] at hd
        exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, hp3, hd⟩)))
      case twistedE6 =>
        have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (h1.trans (Nat.gcd_dvd_left _ _))
        have hd := h1.trans (Nat.gcd_dvd_right _ _)
        rw [hp3] at hd
        exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, hp3, hd⟩)))
      case PSp => exact (hno _ ((Nat.gcd_dvd_left _ _).trans (by norm_num)) h1).elim
      case POmegaOdd => exact (hno _ (by norm_num) h1).elim
      case POmegaPlus =>
        split_ifs at h1
        · exact (hno _ (by norm_num) h1).elim
        · exact (hno _ (by norm_num) h1).elim
        · exact (hno _ (Nat.gcd_dvd_left _ _) h1).elim
      case POmegaMinus => exact (hno _ (Nat.gcd_dvd_left _ _) h1).elim
      case E7 => exact (hno _ ((Nat.gcd_dvd_left _ _).trans (by norm_num)) h1).elim
      all_goals exact (hno _ (by norm_num) h1).elim
    · exfalso
      have := Nat.le_of_dvd hsnd.1 h1
      have := hp.two_le
      omega
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h1 | h1 <;>
    · revert h1
      unfold exceptionalOrders
      split
      all_goals intro h1
      all_goals simp only at h1
      all_goals first
        | (exfalso; refine hno _ ?_ h1; norm_num; done)
        | (have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
           first
             | exact Or.inr (Or.inr (Or.inr ⟨h3, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩))
             | exact Or.inr (Or.inr (Or.inr ⟨h3, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩))
             | exact Or.inr (Or.inr (Or.inr ⟨h3, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))⟩))
             | exact Or.inr (Or.inr (Or.inr ⟨h3, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))⟩)))

@[expose] def LieCoverRankHighLin : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → LieCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      (∃ n r f : ℕ,
        (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSL n r f ∧
          p ∣ Nat.gcd n (r ^ f - 1)) ∨
        (CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU n r f ∧
          p ∣ Nat.gcd n (r ^ f + 1))) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def LieCoverRankHighE6 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → LieCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      (p = 3 ∧ ∃ (t : StatedLieTag) (n r f : ℕ),
        ((t = .E6 ∧ 3 ∣ r ^ f - 1) ∨ (t = .twistedE6 ∧ 3 ∣ r ^ f + 1)) ∧
        CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L)

@[expose] def LieCoverRankHighExc3 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → LieCentralQuotient L →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center L) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      (p = 3 ∧ ∃ (t : StatedLieTag) (n r f : ℕ),
        ((t = .PSL ∧ n = 2 ∧ r = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ r = 3 ∧ f = 1) ∨
          (t = .G2 ∧ n = 0 ∧ r = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ r = 3 ∧ f = 1)) ∧
        CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f) →
      CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank p (⊤ : Subgroup L)

theorem lieCoverRankHigh_of_parts
    (hGA : CFSG.Open.GriessAllModelsStatement) (hLin : LieCoverRankHighLin)
    (hE6 : LieCoverRankHighE6) (hExc3 : LieCoverRankHighExc3) : LieCoverRankHigh := by
  intro L _ _ hq hLC p hp hp2 hdvd h3
  obtain ⟨idx, ⟨e⟩⟩ := hLC
  obtain ⟨t, n, r, f, hm⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.exists_lieModel idx
  have hLC : LieCentralQuotient L := ⟨idx, ⟨e⟩⟩
  have hmB : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) t n r f :=
    blueprintLieModel_of_models (models_lieModel_of_mulEquiv e.symm hm)
  have htab := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.center_dvd_table hGA (K := L)
    (isQuasisimple_of_open' hq) e hm
  have hpt := hdvd.trans htab
  rcases case_of_dvd_table hp hp2 hpt with ⟨rfl, hg⟩ | ⟨rfl, hg⟩ |
    ⟨⟨rfl, rfl, hd⟩ | ⟨rfl, rfl, hd⟩⟩ | ⟨rfl, hx⟩
  · exact hLin L hq hLC p hp hp2 hdvd h3 ⟨n, r, f, Or.inl ⟨hmB, hg⟩⟩
  · exact hLin L hq hLC p hp hp2 hdvd h3 ⟨n, r, f, Or.inr ⟨hmB, hg⟩⟩
  · exact hE6 L hq hLC 3 hp hp2 hdvd h3 ⟨rfl, .E6, n, r, f, Or.inl ⟨rfl, hd⟩, hmB⟩
  · exact hE6 L hq hLC 3 hp hp2 hdvd h3
      ⟨rfl, .twistedE6, n, r, f, Or.inr ⟨rfl, hd⟩, hmB⟩
  · exact hExc3 L hq hLC 3 hp hp2 hdvd h3 ⟨rfl, t, n, r, f, hx, hmB⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
