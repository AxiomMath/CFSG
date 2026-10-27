module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fieldActor_one fieldActor_mul
  ringEquiv_cube_apply_eq)
open CFSG.Blueprint.Chevalley (TwistTag)


theorem sfm4_cube_eq_one {p f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ^ 3 = 1 := by
  refine RingEquiv.ext fun c => ?_
  simpa [pow_succ] using ringEquiv_cube_apply_eq hK hσ c

theorem sfm4_frob_ne_one {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (p ^ f)) : σ ≠ 1 := by
  intro h1
  have hroot : ∀ c : K, c ^ (p ^ f) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) h1
    simpa [hσ] using this
  classical
  haveI := Fintype.ofFinite K
  have hQ : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
  have hdeg : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).natDegree = p ^ f :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K hQ
  have hne : (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset K).val ⊆
      (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial K).roots := by
    intro c _
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hroot c, sub_self]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg, Finset.card_univ, ← Nat.card_eq_fintype_card, hK] at hle
  generalize p ^ f = x at hle hQ
  have h2 : 2 ≤ x := hQ
  nlinarith [Nat.mul_le_mul_left x h2, Nat.mul_le_mul_left (x * x) h2]

theorem sfm4_fieldActor_pow {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) (n : ℕ) :
    fieldActor (t := TwistTag.D4) σ (δ ^ n) = fieldActor (t := TwistTag.D4) σ δ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, fieldActor_one]
  | succ n ih =>
    rw [pow_succ δ n, fieldActor_mul, ih, pow_succ (fieldActor (t := TwistTag.D4) σ δ) n]

theorem sfm4_cube_roots_cyclic {G : Type} [Group G] [Finite G] [IsCyclic G] {σ x : G}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hx : x ^ 3 = 1) : x = 1 ∨ x = σ ∨ x = σ ^ 2 := by
  classical
  haveI := Fintype.ofFinite G
  have hσ2 : σ ^ 2 ≠ 1 := by
    intro h
    apply hσ1
    have h4 : σ ^ 4 = σ := by rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hσ3, one_mul]
    have h4' : σ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow]
    exact h4.symm.trans h4'
  have hss : σ ≠ σ ^ 2 := by
    intro h
    apply hσ1
    have h' : σ * σ = σ * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel h'
  have hne : (1 : G) ≠ σ := fun h => hσ1 h.symm
  have hne' : (1 : G) ≠ σ ^ 2 := fun h => hσ2 h.symm
  have hcard : ({1, σ, σ ^ 2} : Finset G).card = 3 :=
    Finset.card_eq_three.2 ⟨1, σ, σ ^ 2, hne, hne', hss, rfl⟩
  have hle : (Finset.univ.filter fun a : G => a ^ 3 = 1).card ≤ 3 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hsub : ({1, σ, σ ^ 2} : Finset G) ⊆ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 3
    · exact hσ3
    · rw [← pow_mul, mul_comm, pow_mul, hσ3, one_pow]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have hxS : x ∈ Finset.univ.filter fun a : G => a ^ 3 = 1 := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx⟩
  rw [← heq] at hxS
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hxS

theorem sfm4_fixSubgroup_sq {X : Type} [Group X] (α : MulAut X) (h : α ^ 3 = 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (α ^ 2) =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
  ext x
  have h3 : ∀ y, α (α (α y)) = y := fun y => by
    have := congrArg (fun γ : MulAut X => γ y) h
    simpa [pow_succ, MulAut.mul_apply] using this
  show (α ^ 2) x = x ↔ α x = x
  rw [sq, MulAut.mul_apply]
  constructor
  · intro h2
    have := congrArg α h2
    rw [h3 x] at this
    exact this.symm
  · intro h1
    rw [h1, h1]

theorem sfm4_normal_form {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (∀ α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) ∧
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      ∀ (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ → Θ α = δ) ∧
    IsCyclic (K ≃+* K) := by
  obtain ⟨-, hu, ⟨Θ, hΘ, -⟩, hcyc, -⟩ :=
    CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hf K hK σ hσ
  exact ⟨fun α => by
      obtain ⟨⟨g, δ⟩, h⟩ := (hu α).exists
      exact ⟨g, δ, h⟩, ⟨Θ, hΘ⟩, hcyc⟩

theorem sfm4_twist {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ3 : β ^ 3 = 1)
    (hβi : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
      (δ = σ ∨ δ = σ ^ 2) ∧ MulAut.conj g * β = fieldActor (t := TwistTag.D4) σ δ := by
  obtain ⟨hdec, ⟨Θ, hΘ⟩, hcyc⟩ := sfm4_normal_form hf K hK σ hσ
  haveI := hcyc
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) (fun a b h => RingEquiv.ext fun x => congrFun h x)
  obtain ⟨g₀, δ₀, hβ⟩ := hdec β
  have h3 : δ₀ ^ 3 = 1 := by
    rw [← hΘ β g₀ δ₀ hβ, ← map_pow, hβ3, map_one]
  have hδ1 : δ₀ ≠ 1 := by
    intro h
    apply hβi
    exact MonoidHom.mem_range.2 ⟨g₀, by rw [hβ, h, fieldActor_one, mul_one]⟩
  rcases sfm4_cube_roots_cyclic (sfm4_cube_eq_one hK hσ) (sfm4_frob_ne_one Nat.prime_two hf hK hσ) h3 with
    h | h | h
  · exact absurd h hδ1
  · exact ⟨g₀⁻¹, δ₀, Or.inl h, by rw [hβ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩
  · exact ⟨g₀⁻¹, δ₀, Or.inr h, by rw [hβ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩

theorem sfm4_card_fix {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {δ : K ≃+* K} (hδ : δ = σ ∨ δ = σ ^ 2) :
    Nat.card ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
      (fieldActor (t := TwistTag.D4) σ δ)) =
      (2 ^ f) ^ 6 * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1)) := by
  have hc := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.card_fixSubgroup_fieldActor
    Nat.prime_two hf hK σ hσ
  rcases hδ with rfl | rfl
  · rw [hc]
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, mul_assoc]
  · have h3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
      rw [← sfm4_fieldActor_pow, sfm4_cube_eq_one hK hσ, fieldActor_one]
    rw [sfm4_fieldActor_pow σ σ 2, sfm4_fixSubgroup_sq _ h3, hc]
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, mul_assoc]

theorem sfm4_factorization_two {n : ℕ} (hn : 1 ≤ n) :
    ((2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1))).factorization 2 = 6 * n := by
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h2a : 2 ∣ (2 ^ n) ^ 6 := dvd_trans h2n (dvd_pow_self _ (by norm_num))
  have h2b : 2 ∣ (2 ^ n) ^ 2 := dvd_trans h2n (dvd_pow_self _ (by norm_num))
  have ha1 : 0 < (2 ^ n) ^ 6 := by positivity
  have hb1 : 0 < (2 ^ n) ^ 2 := by positivity
  have hodd1 : Odd ((2 ^ n) ^ 6 - 1) := Nat.odd_iff.2 (by omega)
  have hodd2 : Odd ((2 ^ n) ^ 2 - 1) := Nat.odd_iff.2 (by omega)
  have hodd : Odd (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) := hodd1.mul hodd2
  have hne : ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) ≠ 0 := hodd.pos.ne'
  have hnd : ¬ 2 ∣ ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := by
    intro h
    have := Nat.odd_iff.1 hodd
    omega
  rw [Nat.factorization_mul (by positivity) hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [mul_comm]

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
