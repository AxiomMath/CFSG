module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LinearGroups

variable {K : Type*} [Field K]

theorem card_pow_eq_self_of_card_eq_sq [Fintype K] [DecidableEq K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Fintype.card K = q ^ 2) : Fintype.card {c : K // c ^ q = c} = q := by
  have hunits : Fintype.card Kˣ = (q + 1) * (q - 1) := by
    rw [Fintype.card_units, hK]
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = (q + 1) * (q - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hunits]
  have hoh : orderOf (g ^ (q + 1)) = q - 1 := by
    rw [orderOf_pow_of_dvd (by omega) (hog ▸ dvd_mul_right _ _), hog,
      Nat.mul_div_cancel_left _ (by omega)]
  set S : Finset Kˣ := Finset.univ.filter fun a => a ^ (q - 1) = 1 with hS
  have hSle : S.card ≤ q - 1 := IsCyclic.card_pow_eq_one_le (by omega)
  have hSge : q - 1 ≤ S.card := by
    have hsub : (Finset.range (q - 1)).image (fun i => (g ^ (q + 1)) ^ i) ⊆ S := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, ← hoh, pow_orderOf_eq_one, one_pow]
    calc q - 1 = ((Finset.range (q - 1)).image (fun i => (g ^ (q + 1)) ^ i)).card := by
          rw [Finset.card_image_of_injOn, Finset.card_range]
          intro i hi j hj hij
          have := pow_injOn_Iio_orderOf (x := g ^ (q + 1))
          rw [hoh] at this
          exact this (by simpa using hi) (by simpa using hj) hij
      _ ≤ S.card := Finset.card_le_card hsub
  have hfilter : Finset.univ.filter (fun c : K => c ^ q = c) =
      insert 0 (S.map ⟨Units.val, Units.val_injective⟩) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_map,
      Function.Embedding.coeFn_mk, hS]
    constructor
    · intro hc
      by_cases h0 : c = 0
      · exact Or.inl h0
      · refine Or.inr ⟨Units.mk0 c h0, ?_, rfl⟩
        apply Units.ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        have h1 : c ^ (q - 1) * c = 1 * c := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hc, one_mul]
        exact mul_right_cancel₀ h0 h1
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact zero_pow (by omega)
      · have h1 : (u : K) ^ (q - 1) = 1 := by
          rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
        calc (u : K) ^ q = (u : K) ^ (q - 1) * u := by
              rw [← pow_succ, Nat.sub_add_cancel (by omega)]
          _ = u := by rw [h1, one_mul]
  rw [Fintype.card_subtype, hfilter, Finset.card_insert_of_notMem, Finset.card_map]
  · omega
  · simp only [Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
    exact fun u _ => u.ne_zero

theorem finite_field_quadratic_frobenius {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ σ : K ≃+* K, (∀ c, σ c = c ^ p ^ f) ∧ σ ≠ 1 ∧ σ ^ 2 = 1 ∧
      ∃ F : Subfield K, (∀ c, c ∈ F ↔ c ^ p ^ f = c) ∧ Nat.card F = p ^ f := by
  classical
  have hq2 : 2 ≤ p ^ f :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = (p ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have : Fact p.Prime := ⟨hp⟩
  let φ : K →+* K := iterateFrobenius K p f
  have hφ : ∀ c, φ c = c ^ p ^ f := fun c => iterateFrobenius_def p f c
  let σ : K ≃+* K := RingEquiv.ofBijective φ (Finite.injective_iff_bijective.mp φ.injective)
  have hσ : ∀ c, σ c = c ^ p ^ f := hφ
  have hfix : ∀ c : K, c ∈ (σ : K →+* K).eqLocusField (RingHom.id K) ↔ c ^ p ^ f = c := by
    intro c
    rw [RingHom.mem_eqLocusField]
    exact iff_of_eq (congrArg (· = c) (hσ c))
  have hcount := card_pow_eq_self_of_card_eq_sq hq2 hcard
  refine ⟨σ, hσ, ?_, ?_, (σ : K →+* K).eqLocusField (RingHom.id K), hfix, ?_⟩
  · intro h1
    have hall : ∀ c : K, c ^ p ^ f = c := fun c => by
      rw [← hσ, h1]
      rfl
    rw [Fintype.card_subtype, Finset.filter_true_of_mem (fun c _ => hall c), Finset.card_univ,
      hcard] at hcount
    nlinarith
  · ext c
    rw [pow_two, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← pow_two, ← hcard, FiniteField.pow_card]
    rfl
  · rw [← hcount, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight hfix)

end CFSG.LinearGroups
