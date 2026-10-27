module

public import CFSG.HardMathSupport.Solomon.Coordinator.L5Lift
public import CFSG.HardMathSupport.Solomon.Proving.TorusStar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus CFSG.HardMathSupport.Solomon.Proving

section Star

variable {K : Type*} [Field K] {n r : ℕ}

theorem det_starX (ζ : Kˣ) {c : Fin n} {d : Fin r → Fin n} (hcd : ∀ k, c ≠ d k) (k : Fin r) :
    ((starX ζ c d k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [starX, diagHom_apply, det_diagGL, Finset.prod_eq_mul c (d k) (hcd k)]
  · rw [tvec_apply_i ζ (hcd k), tvec_apply_j]
    simp
  · intro m _ hm
    rw [tvec_apply_of_ne ζ (fun h => hm.1 h) (fun h => hm.2 h)]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem det_starSw {c : Fin n} {d : Fin r → Fin n} (hcd : ∀ k, c ≠ d k) (k : Fin r) :
    ((starSw c d k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 :=
  det_sgnSwap (hcd k)

theorem comp_swap_eq_of_eq {α : Type*} {v : Fin n → α} {a b : Fin n} (h : v a = v b) :
    v ∘ Equiv.swap a b = v := by
  funext m
  simp only [Function.comp_apply]
  by_cases hma : m = a
  · subst hma
    rw [Equiv.swap_apply_left, h]
  · by_cases hmb : m = b
    · subst hmb
      rw [Equiv.swap_apply_right, h]
    · rw [Equiv.swap_apply_of_ne_of_ne hma hmb]

theorem ne_scalar_of_entry {g : GL (Fin n) K} {a b : Fin n} (hab : a ≠ b)
    (hg : (g : Matrix (Fin n) (Fin n) K) a b ≠ 0) (c : Kˣ) :
    g ≠ GeneralLinearGroup.scalar (Fin n) c := by
  intro h
  rw [h] at hg
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hab] at hg

end Star

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem mem_range_toGL_of_det {n : ℕ} {g : GL (Fin n) F}
    (hg : (g : Matrix (Fin n) (Fin n) F).det = 1) :
    g ∈ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) F →* GL (Fin n) F).range := by
  rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
  exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, hg]; rfl)

omit [Finite F] in
theorem proj_ker_scalar {n : ℕ} (g : SpecialLinearGroup (Fin n) F) (hg : proj n F g = 1) :
    ∃ c : Fˣ, SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) c := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg)
  exact ⟨c, Units.ext hc⟩

omit [Finite F] in
theorem commute_of_toGL {n : ℕ} {s t : SpecialLinearGroup (Fin n) F}
    (h : Commute (SpecialLinearGroup.toGL s) (SpecialLinearGroup.toGL t)) : Commute s t :=
  SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul]; exact h.eq)

theorem hasCentTorus_projectiveSL {n r : ℕ} [NeZero r] {Lb : Type*} [Group Lb] [Finite Lb]
    {Γ : Lb →* projectiveSL n F} (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb))) {p : ℕ}
    [Fact p.Prime] {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ p) (c z : Fin n) (d : Fin r → Fin n)
    (hd : Function.Injective d) (hcd : ∀ k, c ≠ d k) (hzc : z ≠ c) (hzd : ∀ k, z ≠ d k)
    (t : SpecialLinearGroup (Fin n) F)
    (ht1 : ∀ a : Fˣ, SpecialLinearGroup.toGL t ≠ GeneralLinearGroup.scalar (Fin n) a)
    {e : ℕ} (ht2 : t ^ 2 ^ e = 1)
    (htX : ∀ k, Commute (SpecialLinearGroup.toGL t) (starX ζ c d k))
    (htS : ∀ k, Commute (SpecialLinearGroup.toGL t) (starSw c d k)) :
    HasCentTorus p r Lb := by
  obtain ⟨D, hcard, hX, hS⟩ := exists_torusData_star hζ SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective (proj n F) proj_ker_scalar c z d hd hcd hzc hzd
    (fun k => mem_range_toGL_of_det (det_starX ζ hcd k))
    (fun k => mem_range_toGL_of_det (det_starSw hcd k))
  refine hasCentTorus_of_torusData Fact.out hΓ hker hodd D hcard (T := proj n F t) ?_
    ⟨e, by rw [← map_pow, ht2, map_one]⟩ ?_ ?_
  · intro h
    obtain ⟨a, ha⟩ := proj_ker_scalar t h
    exact ht1 a ha
  · intro k
    obtain ⟨x, hx, hxk⟩ := hX k
    rw [hxk]
    have h1 := htX k
    rw [← hx] at h1
    exact (commute_of_toGL h1).map (proj n F)
  · intro k
    obtain ⟨s, hs, hsk⟩ := hS k
    rw [hsk]
    have h1 := htS k
    rw [← hs] at h1
    exact (commute_of_toGL h1).map (proj n F)

section Five

variable {Lb : Type*} [Group Lb] [Finite Lb] {Γ : Lb →* projectiveSL 5 F}

theorem exists_primitiveRoot_five_of_dvd (h5 : 5 ∣ Nat.card F - 1) :
    ∃ ζ : Fˣ, IsPrimitiveRoot ζ 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hdvd : 5 ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 5 hdvd
  exact ⟨ζ, hζ ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem hasCentTorus_two_projectiveSL_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ Nat.card F - 1) : HasCentTorus 5 2 Lb := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five_of_dvd h5
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (mem_range_toGL_of_det (F := F) (det_sgnSwap (K := F) h01))
  refine hasCentTorus_projectiveSL hΓ hker hodd hζ 2 0 ![3, 4] (by decide) (by decide) (by decide)
    (by decide) t (fun a => ht ▸ ne_scalar_of_entry h01 (sgnSwap_apply_ne 0 1) a) (e := 2) ?_ ?_ ?_
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, ht, map_one]
    exact sgnSwap_pow_four 0 1
  · intro k
    rw [ht, starX]
    refine commute_sgnSwap_diag (tvec_comp_swap_disj ζ ?_ ?_ ?_ ?_) <;> fin_cases k <;> decide
  · intro k
    rw [ht, starSw]
    exact commute_sgnSwap_sgnSwap (by fin_cases k <;> decide)

@[expose] def negFourVec : Fin 5 → Fˣ := ![-1, -1, -1, -1, 1]

theorem hasCentTorus_three_projectiveSL_five (hΓ : Function.Surjective Γ)
    (hker : Γ.ker = Subgroup.center Lb) (hodd : Odd (Nat.card (Subgroup.center Lb)))
    (h5 : 5 ∣ Nat.card F - 1) (h2 : ringChar F ≠ 2) : HasCentTorus 5 3 Lb := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five_of_dvd h5
  have hneg : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
  have hdet : ((diagHom (negFourVec (F := F)) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).det = 1 := by
    rw [diagHom_apply, det_diagGL]
    simp [negFourVec, Fin.prod_univ_five]
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1 (mem_range_toGL_of_det hdet)
  refine hasCentTorus_projectiveSL hΓ hker hodd hζ 0 4 ![1, 2, 3] (by decide) (by decide)
    (by decide) (by decide) t ?_ (e := 1) ?_ ?_ ?_
  · intro a h
    rw [ht] at h
    have h0 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) 0 0) h
    have h4 := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) 4 4) h
    simp [diagHom_apply, coe_diagGL, negFourVec, GeneralLinearGroup.coe_scalar] at h0 h4
    exact hneg (h0.trans h4.symm)
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, ht, map_one, pow_one, ← map_pow]
    have : negFourVec (F := F) ^ 2 = 1 := by
      funext i
      fin_cases i <;> simp [negFourVec]
    rw [this, map_one]
  · intro k
    rw [ht]
    exact (Commute.all _ _).map diagHom
  · intro k
    rw [ht, starSw]
    refine (commute_sgnSwap_diag (comp_swap_eq_of_eq ?_)).symm
    fin_cases k <;> simp [negFourVec]

end Five

end CFSG.HardMathSupport.Solomon.Coordinator
