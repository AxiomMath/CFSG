module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesTwist
public import CFSG.CharacterTheory.Wreathed.UniqueLocalBlockSectionColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.FlatCentralFourier

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

@[expose] def IsTwistedCentralSectionRows (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (B : basis.index) (a : G)
    (m : ℕ) (C : ℕ → Subgroup G) (lam Φ : G → ℂ) (ε : ℤ)
    (v : basis.index → ℕ → Fin 2 → ℂ) : Prop :=
  ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
    ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) →
      (basis.representation χ).character (a ^ k * r) =
        lam r * (v χ k 0 + v χ k 1 * (1 + ε * Φ r))

omit [Fintype G] in
theorem exists_combination_of_mem_oddRestrictionLattice {E : Type} [Group E] [Fintype E]
    (localBasis : FiniteIrreducibleCharacterBasis E) (labels : Finset localBasis.index)
    {φ : E → ℂ} (h : oddRestriction φ ∈ oddRestrictionLattice localBasis labels) :
    ∃ c : localBasis.index → ℂ, ∀ y : E, Odd (orderOf y) →
      φ y = ∑ θ ∈ labels, c θ * (localBasis.representation θ).character y := by
  suffices hgen : ∀ ψ ∈ oddRestrictionLattice localBasis labels, ∃ c : localBasis.index → ℂ,
      ∀ y : OddElements E, ψ y = ∑ θ ∈ labels, c θ * (localBasis.representation θ).character y.1
    by
    obtain ⟨c, hc⟩ := hgen _ h
    exact ⟨c, fun y hy => hc ⟨y, hy⟩⟩
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨θ, hθ, rfl⟩ := hx
    refine ⟨fun θ' => if θ' = θ then 1 else 0, fun y => ?_⟩
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' _ θ, ite_eq_left (Finset.mem_coe.mp hθ)]
    rfl
  | zero => exact ⟨0, fun y => by simp⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hx'
    refine ⟨c + c', fun y => ?_⟩
    rw [Pi.add_apply, hc y, hc' y, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Pi.add_apply, add_mul]
  | smul k x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨fun θ => (k : ℂ) * c θ, fun y => ?_⟩
    rw [Pi.smul_apply, hc y, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun θ _ => ?_
    ring

theorem twisted_section_rows (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) {u : G} {r : ℕ}
    (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r) (hgroup : IsPGroup 2 (Subgroup.zpowers u))
    (lamG ΦG : G → ℂ) (ε : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hlocal : ∀ (lb : FiniteIrreducibleCharacterBasis
        (Subgroup.centralizer (Subgroup.zpowers u : Set G))) (ℓ : lb.index),
      (∀ c, (lb.representation ℓ).character c = lamG c) →
      brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hgroup
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb ℓ =
        centralCharacterResidueHom basis ideal B ∧
      ∀ θ, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers u) hgroup
          (Subgroup.centralizer (Subgroup.zpowers u : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) lb θ =
        centralCharacterResidueHom basis ideal B →
        θ ∈ coefficientBlock lb (localizedComplexIntegerRing ideal) ℓ)
    (C : Subgroup G) (hC : C = Subgroup.centralizer (Subgroup.zpowers u : Set G))
    (localBasis : FiniteIrreducibleCharacterBasis C) (ℓ : localBasis.index)
    (hℓ : ∀ c, (localBasis.representation ℓ).character c = lamG c)
    (hdata : TwistedRegularIntegralBasisData localBasis ideal ℓ (fun c => lamG c)
      (fun c => ΦG c) ε M)
    (hlam0 : ∀ c ∈ C, lamG c ≠ 0)
    (hindep : ∀ α β : ℂ, (∀ y ∈ C, Odd (orderOf y) → α + β * (1 + ε * ΦG y) = 0) →
      α = 0 ∧ β = 0)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 ^ r)) :
    ∃ v : basis.index → Fin 2 → ℂ,
      (∀ χ t, v χ t ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ y ∈ C, Odd (orderOf y) →
          (basis.representation χ).character (u * y) =
            lamG y * (v χ 0 + v χ 1 * (1 + ε * ΦG y))) ∧
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        ∀ w : Fin 2 → ℂ, (∀ y ∈ C, Odd (orderOf y) →
          (basis.representation χ).character (u * y) =
            lamG y * (w 0 + w 1 * (1 + ε * ΦG y))) → w = v χ) ∧
      (∀ s t, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        conj (v χ s) * v χ t = M s t) ∧
      ∀ g : G, (∀ a c : G, a * c = g → Commute a c → (∃ e : ℕ, orderOf a = 2 ^ e) →
          Odd (orderOf c) → ¬ IsConj a u) →
        ∀ s, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
          v χ s * conj ((basis.representation χ).character g) = 0 := by
  subst hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd_iff : ∀ n : ℕ, ¬ 2 ∣ n ↔ Odd n := fun n => by
    rw [Nat.odd_iff, Nat.two_dvd_ne_zero]
  obtain ⟨hbrauer, hunique⟩ := hlocal localBasis ℓ hℓ
  let b : Fin 2 → Subgroup.centralizer (Subgroup.zpowers u : Set G) → ℂ :=
    ![fun c => lamG c, (fun c : Subgroup.centralizer (Subgroup.zpowers u : Set G) => lamG c) *
      (1 + (ε : ℂ) • fun c : Subgroup.centralizer (Subgroup.zpowers u : Set G) => ΦG c)]
  have hb0 : ∀ y, b 0 y = lamG y := fun y => rfl
  have hb1 : ∀ y, b 1 y = lamG y * (1 + ε * ΦG y) := fun y => rfl
  have hbmem : ∀ j, ∃ c : localBasis.index → ℂ, ∀ y, ¬ 2 ∣ orderOf y →
      b j y = ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ,
        c θ * (localBasis.representation θ).character y := by
    intro j
    have hmem : oddRestriction (b j) ∈ oddRestrictionLattice localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ) := by
      rw [← hdata.span]
      fin_cases j
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    obtain ⟨c, hc⟩ := exists_combination_of_mem_oddRestrictionLattice localBasis _ hmem
    exact ⟨c, fun y hy => hc y ((hodd_iff _).mp hy)⟩
  have hbindep : ∀ c : Fin 2 → ℂ, (∀ y, ¬ 2 ∣ orderOf y → ∑ j, c j * b j y = 0) → c = 0 := by
    intro c hc
    obtain ⟨h0, h1⟩ := hindep (c 0) (c 1) (fun y hy hyodd => by
      have h := hc ⟨y, hy⟩ ((hodd_iff _).mpr (by rwa [Subgroup.orderOf_mk]))
      rw [Fin.sum_univ_two, hb0, hb1] at h
      have h' : lamG y * (c 0 + c 1 * (1 + ε * ΦG y)) = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h').resolve_left (hlam0 y hy))
    funext j
    fin_cases j
    · exact h0
    · exact h1
  obtain ⟨D, hD⟩ := hdata.rows
  have hgram := hdata.gram D hD
  let d : localBasis.index → Fin 2 → ℤ := fun θ j =>
    if hθ : θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ
    then D ⟨θ, hθ⟩ j else 0
  have hd : ∀ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ,
      ∀ y, ¬ 2 ∣ orderOf y →
        (localBasis.representation θ).character y = ∑ j, (d θ j : ℂ) * b j y := by
    intro θ hθ y hy
    have h := congrFun (hD ⟨θ, hθ⟩) ⟨y, (hodd_iff _).mp hy⟩
    simp only [oddRestriction, Pi.add_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
      Pi.one_apply, smul_eq_mul, Pi.intCast_apply] at h
    rw [Fin.sum_univ_two, hb0, hb1]
    simp only [d, dite_eq_left hθ]
    rw [h]
  have hdgram : ∀ j k, ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) ℓ,
      d θ j * d θ k = M j k := by
    intro j k
    have h := congrFun (congrFun hgram j) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.transpose_apply] at h
    rw [← h, ← Finset.sum_coe_sort (coefficientBlock localBasis
      (localizedComplexIntegerRing ideal) ℓ)]
    refine Finset.sum_congr rfl fun θ _ => ?_
    simp only [d, dite_eq_left θ.2]
  obtain ⟨U, -, -, -, -, -, hUint, hrow, huniq, hUgram, hvanish⟩ :=
    unique_local_block_primary_section_integral_columns basis ideal 2 hr hu hgroup localBasis B
      ℓ hbrauer hunique hζ 2 (by norm_num) b hbmem hbindep d hd
  refine ⟨U, hUint, fun χ hχ y hy hyodd => ?_, fun χ hχ w hw => ?_, fun s t => ?_,
    fun g hg s => ?_⟩
  · have h := hrow χ hχ ⟨y, hy⟩ ((hodd_iff _).mpr (by rwa [Subgroup.orderOf_mk]))
    rw [Fin.sum_univ_two, hb0, hb1] at h
    rw [show u * y = u * ((⟨y, hy⟩ : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G)
      from rfl, h]
    ring
  · apply huniq χ hχ w
    intro y hy
    have hy' : Odd (orderOf (y : G)) := by
      rw [Subgroup.orderOf_coe]
      exact (hodd_iff _).mp hy
    rw [Fin.sum_univ_two, hb0, hb1, hw y y.2 hy']
    ring
  · rw [hUgram s t]
    push_cast
    rw [← hdgram s t]
    push_cast
    rfl
  · exact hvanish g (fun a c hac hcomm ha hc => hg a c hac hcomm ha ((hodd_iff _).mp hc)) s

end CFSG.Wreathed.FlatCentralFourier
