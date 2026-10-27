module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoSpine

public section

open scoped MatrixGroups

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TauCeti CFSG.Open

@[expose] def HasTwoCovers (G : Type*) [Group G] (p : ℕ) (Pl : Subgroup G → Prop) : Prop :=
  ∃ (H₁ H₂ : Type) (_ : Group H₁) (_ : Group H₂) (_ : Finite H₁) (_ : Finite H₂)
    (ψ₁ : H₁ →* G) (ψ₂ : H₂ →* G) (P : Subgroup G),
    ¬ p ∣ Nat.card ψ₁.ker ∧ ¬ p ∣ Nat.card ψ₂.ker ∧
    (∀ F : Subgroup H₁, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₁ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤) ∧
    (∀ F : Subgroup H₂, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₂ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤) ∧
    (∀ M : Subgroup G, ψ₁.range ≤ M → ψ₂.range ≤ M → M = ⊤) ∧
    P ≤ ψ₁.range ∧ P ≤ ψ₂.range ∧
    ∀ E₀ : Subgroup G, (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 → Pl E₀ →
      ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P

theorem closure_centralizers_eq_top_of_hasTwoCovers {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {Pl : Subgroup G → Prop} (h : HasTwoCovers G p Pl) (E₀ : Subgroup G)
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2) (hPl : Pl E₀) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  obtain ⟨H₁, H₂, _, _, _, _, ψ₁, ψ₂, P, hk₁, hk₂, h₁, h₂, hc, hP₁, hP₂, hS⟩ := h
  exact closure_centralizers_eq_top_of_two_covers ψ₁ ψ₂ hk₁ hk₂ h₁ h₂ hc P hP₁ hP₂ E₀ hE₀p hE₀c
    (hS E₀ hE₀p hE₀c hPl)

theorem hasTwoCovers_of_frame {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) {k : ℕ}
    (ρ : Fin k → SL(2, K) →* G) (hρi : ∀ i, Function.Injective (ρ i))
    (hρc : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y))
    (A : Subgroup G) (hAc : ∀ a ∈ A, ∀ (i : Fin k) (y : SL(2, K)), Commute a (ρ i y))
    (hord : (Nat.card G).factorization p ≤
      k * (Nat.card K + 1).factorization p + (Nat.card A).factorization p)
    (H₁ H₂ : Type) [Group H₁] [Group H₂] [Finite H₁] [Finite H₂] (ψ₁ : H₁ →* G)
    (ψ₂ : H₂ →* G) (hk₁ : ¬ p ∣ Nat.card ψ₁.ker) (hk₂ : ¬ p ∣ Nat.card ψ₂.ker)
    (h₁ : ∀ F : Subgroup H₁, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₁ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (h₂ : ∀ F : Subgroup H₂, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₂ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (hclose : ∀ M : Subgroup G, ψ₁.range ≤ M → ψ₂.range ≤ M → M = ⊤)
    (hF₁ : (⨆ i, (ρ i).range) ⊔ A ≤ ψ₁.range) (hF₂ : (⨆ i, (ρ i).range) ⊔ A ≤ ψ₂.range)
    (Pl : Subgroup G → Prop) : HasTwoCovers G p Pl :=
  ⟨H₁, H₂, inferInstance, inferInstance, inferInstance, inferInstance, ψ₁, ψ₂,
    (⨆ i, (ρ i).range) ⊔ A, hk₁, hk₂, h₁, h₂, hclose, hF₁, hF₂,
    fun E₀ hE₀p _ _ => exists_conj_le_frame_torus ρ hρi hρc A hAc hp5 hpq hord E₀ hE₀p⟩

section Native


@[expose] def TwE6TwoNative (R : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
    Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → R p → p ∣ ℓ ^ f + 1 →
      ∀ E₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        ¬ NormalizesRGroup ℓ E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem seitzExcHighTwE6Two_of_native_for {R : ℕ → Prop} (h : TwE6TwoNative R) :
    SeitzExcHighForAt IsTwistedE6Index fun d p =>
      R p ∧ ClassRange LieTypeIndex.twistedE6 (fun _ => True) 2 d p := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hR, hp5, q, hdq, -, hord⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : p ∣ q.p ^ q.exponent + 1 := by
    rw [← PrimePower.card_def]
    exact dvd_add_one_of_orderOf_eq_two hp hord
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  refine planeGen_of_native_closure_cond (r := q.p) e hZ
    (fun E₀ hE₀p hE₀c hN => h K σ q.p q.exponent q.prime_p q.exponent_pos hK hσ p hp5 hR hpq E₀
      hE₀p hE₀c hN) hE hcard hin ?_
  simpa [TauCeti.LieTypeIndex.characteristic_twistedE6, NormalizesRSubgroup] using hn

theorem twE6TwoNative_of_covers {R : ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ℓ f : ℕ), ℓ.Prime → 1 ≤ f →
      Nat.card K = (ℓ ^ f) ^ 2 → (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → R p → p ∣ ℓ ^ f + 1 →
        HasTwoCovers (twistedE6RootGroup K σ) p fun E₀ => ¬ NormalizesRGroup ℓ E₀) :
    TwE6TwoNative R := by
  intro K _ _ σ ℓ f hℓ hf hK hσ p _ hp5 hR hpq E₀ hE₀p hE₀c hN
  exact closure_centralizers_eq_top_of_hasTwoCovers (h K σ ℓ f hℓ hf hK hσ p hp5 hR hpq) E₀ hE₀p
    hE₀c hN

@[expose] def SeitzExcHighTwE6TwoGeSeven : Prop :=
  SeitzExcHighForAt IsTwistedE6Index fun d p =>
    7 ≤ p ∧ ClassRange LieTypeIndex.twistedE6 (fun _ => True) 2 d p

@[expose] def SeitzExcHighTwE6TwoFive : Prop :=
  SeitzExcHighForAt IsTwistedE6Index fun d p =>
    p = 5 ∧ ClassRange LieTypeIndex.twistedE6 (fun _ => True) 2 d p

theorem seitzExcHighTwE6Two_of_ge_seven_of_five (h7 : SeitzExcHighTwE6TwoGeSeven)
    (h5 : SeitzExcHighTwE6TwoFive) : SeitzExcHighTwE6Two :=
  SeitzExcHighForAt.union (fun d p hp _ hQ => by
    have hQ' := hQ
    obtain ⟨h5', -⟩ := hQ'
    rcases Nat.lt_or_ge p 7 with h | h
    · refine Or.inr ⟨?_, hQ⟩
      have h56 : p = 5 ∨ p = 6 := by omega
      rcases h56 with h' | h'
      · exact h'
      · exact absurd (h' ▸ hp) (by norm_num)
    · exact Or.inl ⟨h, hQ⟩) h7 h5

end Native

end CFSG.LieType.SeitzGeneration.ExcHigh
