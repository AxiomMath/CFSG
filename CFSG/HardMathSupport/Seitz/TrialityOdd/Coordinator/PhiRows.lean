module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBPhi3

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration

theorem prime_ne_of_dvd_phi {ℓ f r : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hr : r.Prime) {ε : ℤ}
    (hd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) : r ≠ ℓ := by
  rintro rfl
  have hrQ : (r : ℤ) ∣ ((r ^ f : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact dvd_pow_self _ (by omega)
  have h2 : (r : ℤ) ∣ ((r ^ f : ℕ) : ℤ) ^ 2 + ε * ((r ^ f : ℕ) : ℤ) := by
    rw [show ((r ^ f : ℕ) : ℤ) ^ 2 + ε * ((r ^ f : ℕ) : ℤ) =
      ((r ^ f : ℕ) : ℤ) * (((r ^ f : ℕ) : ℤ) + ε) by ring]
    exact dvd_mul_of_dvd_left hrQ _
  have h1 : (r : ℤ) ∣ 1 := by
    have := dvd_sub hd h2
    rwa [add_sub_cancel_left] at this
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hr.one_lt.ne' (by exact_mod_cast this)

@[expose] def PhiPlaneGenAt (ε : ℤ) (r : ℕ) : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    r.Prime → r ≠ ℓ → (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1 →
    ∀ E : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      CFSG.IsElementaryAbelian r E → Nat.card E = r ^ 2 →
      Subgroup.closure {k : graphFixedRootGroup TwistTag.D4 K σ.toRingHom |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

theorem trialityOddPhi36_of_rows (h3 : ∀ r, 5 ≤ r → PhiPlaneGenAt 1 r)
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : Inner.TrialityOddPhi36 := by
  intro q hq K _ _ _ hnab hiso p hp hp5 _ hP E hE hcard hinner
  left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, σ, hX, hσ, -, ⟨e⟩⟩ := Inner.exists_trialityD4_model_of_isoLie hiso
  have hqc : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hX' : Nat.card X = (q.p ^ q.exponent) ^ 3 := by rw [hX, hqc]
  have hσ' : ∀ c, σ c = c ^ (q.p ^ q.exponent) := fun c => by rw [hσ, hqc]
  have hle : q.card ≤ q.card ^ 2 := Nat.le_self_pow (by norm_num) _
  have hd : ∃ ε : ℤ, (p : ℤ) ∣ ((q.p ^ q.exponent : ℕ) : ℤ) ^ 2 +
      ε * ((q.p ^ q.exponent : ℕ) : ℤ) + 1 ∧ PhiPlaneGenAt ε p := by
    rcases hP with h | h
    · refine ⟨1, ?_, h3 p hp5⟩
      rw [← hqc, one_mul]
      exact_mod_cast h
    · refine ⟨-1, ?_, h6 p hp5⟩
      have := Int.natCast_dvd_natCast.mpr h
      rw [← hqc]
      rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at this
      convert this using 1
      ring
  obtain ⟨ε, hdvd, hgen⟩ := hd
  have hpℓ : p ≠ q.p := prime_ne_of_dvd_phi q.prime_p q.exponent_pos hp hdvd
  refine CFSG.RankThree.PartOne.CTP.closure_fixUnion_eq_top_of_inner_equiv hnab e (p := p) ?_ E
    hcard hinner
  intro E₁ hE₁ hcard₁
  exact hgen q.p q.exponent q.prime_p hq q.exponent_pos X hX' σ hσ' hp hpℓ hdvd E₁ hE₁ hcard₁

theorem seitzExcAnisotropicTrialityOdd_of_rows
    (h3 : ∀ r, 5 ≤ r → PhiPlaneGenAt 1 r)
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : SeitzExcAnisotropicTrialityOdd :=
  Inner.seitzExcAnisotropicTrialityOdd_of_phi36 (trialityOddPhi36_of_rows h3 h6)

@[expose] def LongTorusClosingOdd : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 2 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 3 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      Inner.LongTorusClosing σ.toRingHom

theorem phiPlaneGenAt_one_of_closing
    (hClose : LongTorusClosingOdd) {r : ℕ} (hr3 : r ≠ 3) :
    PhiPlaneGenAt 1 r := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ hr _ hrd E hE hEcard
  have hrd' : r ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1 := by
    have h : (r : ℤ) ∣ (((ℓ ^ f) ^ 2 + ℓ ^ f + 1 : ℕ) : ℤ) := by
      push_cast
      simpa using hrd
    exact Int.natCast_dvd_natCast.1 h
  exact Inner.phi3_cenGen_top hℓ hℓ2 hf hK σ hσ (hClose ℓ f hℓ hℓ2 hf K hK σ hσ) hr hr3 hrd' E hE
    hEcard

theorem seitzExcAnisotropicTrialityOdd_of_closing
    (hClose : LongTorusClosingOdd)
    (h6 : ∀ r, 5 ≤ r → PhiPlaneGenAt (-1) r) : SeitzExcAnisotropicTrialityOdd :=
  seitzExcAnisotropicTrialityOdd_of_rows
    (fun _ hr5 => phiPlaneGenAt_one_of_closing hClose (by omega)) h6

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
