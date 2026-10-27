module

public import CFSG.ClassicalInvolution.Q3.Chart
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Frame

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups

variable {G : Type} [Group G]

structure WeakInSigma3 (E K : Subgroup G) : Prop where
  member : ∃ z, IsClassicalMember3 K z ∧ z ∈ E
  normalizes : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K
  index_two : (axisSub E K).relIndex E = 2
  chart : ∃ φ : ↥K →* SL(2, ZMod 3), IsChart3 K φ ∧
    (∀ e ∈ E, (∀ k k' : ↥K, (k' : G) = e * k * e⁻¹ → φ k' = φ k) → e ∈ axisSub E K)

namespace WeakInSigma3

variable {E K : Subgroup G}

theorem exists_split (hK : WeakInSigma3 E K) :
    ∃ a ∈ E, a ∉ axisSub E K ∧ ∀ x ∈ E, x ∈ axisSub E K ∨ x * a ∈ axisSub E K := by
  obtain ⟨a, ha, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hK.index_two
  have hna : a ∉ axisSub E K := by
    intro hmem
    have h1 : (1 : G) ∈ axisSub E K := (axisSub E K).one_mem
    have := hxor 1 E.one_mem
    simp [Xor, hmem, h1] at this
  refine ⟨a, ha, hna, fun x hx => ?_⟩
  rcases hxor x hx with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inr h1
  · exact Or.inl h1

theorem exists_mem_not_mem_axis (hK : WeakInSigma3 E K) : ∃ a ∈ E, a ∉ axisSub E K := by
  obtain ⟨a, ha, hna, -⟩ := hK.exists_split
  exact ⟨a, ha, hna⟩

theorem conj (hK : WeakInSigma3 E K) {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    WeakInSigma3 E (conjSub n K) := by
  have hnE : ∀ x, n⁻¹ * x * n ∈ E ↔ x ∈ E := fun x => mem_conj_iff_of_mem_normalizer hn x
  have hnE' : ∀ x, n * x * n⁻¹ ∈ E ↔ x ∈ E := fun x => (Subgroup.mem_normalizer_iff.mp hn x).symm
  let ε : ↥K ≃* ↥(conjSub n K) :=
    Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  have hε : ∀ k : ↥K, ((ε k : ↥(conjSub n K)) : G) = n * k * n⁻¹ := fun k =>
    Subgroup.coe_equivMapOfInjective_apply K (MulAut.conj n).toMonoidHom
      (MulAut.conj n).injective k
  have hεs : ∀ k₁ : ↥(conjSub n K), ((ε.symm k₁ : ↥K) : G) = n⁻¹ * k₁ * n := by
    intro k₁
    have h := hε (ε.symm k₁)
    rw [MulEquiv.apply_symm_apply] at h
    calc ((ε.symm k₁ : ↥K) : G) = n⁻¹ * (n * ↑(ε.symm k₁) * n⁻¹) * n := by group
      _ = n⁻¹ * k₁ * n := by rw [← h]
  have hO : (classicalInvolutionOddCore ↥K).map ε.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub n K) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant ε
  obtain ⟨z, hz, hzE⟩ := hK.member
  obtain ⟨φ, hφ, hker⟩ := hK.chart
  refine ⟨⟨n * z * n⁻¹, hz.conj n, (hnE' z).mpr hzE⟩, ?_, ?_, ?_⟩
  · intro e he k₁ hk₁
    rw [mem_conjSub_iff] at hk₁ ⊢
    have he' : n⁻¹ * e * n ∈ E := (hnE e).mpr he
    have := hK.normalizes _ he' _ hk₁
    have e1 : n⁻¹ * (e * k₁ * e⁻¹) * n = (n⁻¹ * e * n) * (n⁻¹ * k₁ * n) * (n⁻¹ * e * n)⁻¹ := by
      group
    rw [e1]
    exact this
  · have h2 := relIndex_conjSub n (axisSub E K) E
    rw [conjSub_eq_of_mem_normalizer hn] at h2
    rw [axisSub_conjSub hn, h2]
    exact hK.index_two
  · refine ⟨φ.comp ε.symm.toMonoidHom, ⟨hφ.surjective.comp ε.symm.surjective, ?_⟩, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφ.ker_eq, ← hO,
        Subgroup.mem_map_equiv]
      rfl
    · intro e he htriv
      have he' : n⁻¹ * e * n ∈ E := (hnE e).mpr he
      have hax : n⁻¹ * e * n ∈ axisSub E K := by
        refine hker _ he' fun k k' hkk' => ?_
        have := htriv (ε k) (ε k') (by
          rw [hε, hε, hkk']
          group)
        simpa using this
      rw [axisSub_conjSub hn, mem_conjSub_iff]
      exact hax

end WeakInSigma3

@[expose] def weakSigmaSet3 (Ω : Set (Subgroup G)) (E : Subgroup G) : Set (Subgroup G) :=
  {K | K ∈ Ω ∧ WeakInSigma3 E K}

structure WeakPreFrame3 (Ω : Set (Subgroup G)) (E : Subgroup G) (S : Set (Subgroup G)) : Prop where
  inv : ConjInvariant Ω
  elem : ∀ x ∈ E, x * x = 1
  eq_sigma : S = weakSigmaSet3 Ω E
  gen : Subgroup.closure (wzSet S) = E
  card : 8 ≤ Nat.card E

structure WeakToralFrame3 (Ω : Set (Subgroup G)) (E : Subgroup G) (S : Set (Subgroup G)) : Prop
    extends WeakPreFrame3 Ω E S where
  sym : WeakPairingSymmetric E S
  conn : WeakPairingConnected E S

namespace WeakPreFrame3

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}
  (Fr : WeakPreFrame3 Ω E S)

include Fr

theorem subset : S ⊆ Ω := by
  rw [Fr.eq_sigma]
  exact fun _ h => h.1

theorem mem_iff {K : Subgroup G} : K ∈ S ↔ K ∈ Ω ∧ WeakInSigma3 E K := by
  rw [Fr.eq_sigma]
  exact Iff.rfl

theorem weakInSigma {K : Subgroup G} (hK : K ∈ S) : WeakInSigma3 E K :=
  (Fr.mem_iff.mp hK).2

theorem conj_mem {n : G} (hn : n ∈ Subgroup.normalizer (E : Set G)) {K : Subgroup G}
    (hK : K ∈ S) : conjSub n K ∈ S :=
  Fr.mem_iff.mpr ⟨Fr.inv n K (Fr.subset hK), (Fr.weakInSigma hK).conj hn⟩

theorem exists_member {K : Subgroup G} (hK : K ∈ S) : ∃ z, IsClassicalMember3 K z ∧ z ∈ E :=
  (Fr.weakInSigma hK).member

theorem exists_central {K : Subgroup G} (hK : K ∈ S) :
    ∃ z, IsCentralInvolution K z ∧ z ∈ E := by
  obtain ⟨z, hz, hzE⟩ := Fr.exists_member hK
  exact ⟨z, hz.isCentralInvolution, hzE⟩

theorem eq_of_central [Finite G] {K : Subgroup G} (hK : K ∈ S) {z z' : G}
    (hz : IsCentralInvolution K z) (hz' : IsCentralInvolution K z') : z = z' := by
  obtain ⟨φ, hφ, -⟩ := (Fr.weakInSigma hK).chart
  exact hφ.eq_of_central hz hz'

theorem mem_of_central [Finite G] {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsCentralInvolution K z) : z ∈ E := by
  obtain ⟨z₀, hz₀, hz₀E⟩ := Fr.exists_central hK
  rw [Fr.eq_of_central hK hz hz₀]
  exact hz₀E

theorem comm {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  comm_of_sq_eq_one Fr.elem hx hy

theorem mem_axisSub_of_central [Finite G] {K : Subgroup G} (hK : K ∈ S) {z : G}
    (hz : IsCentralInvolution K z) : z ∈ axisSub E K :=
  mem_axisSub_iff.mpr ⟨Fr.mem_of_central hK hz, fun k hk => (hz.central k hk).symm⟩

theorem exists_ne [Finite G] : ∃ K ∈ S, ∃ L ∈ S, K ≠ L := by
  by_contra hne
  push Not at hne
  rcases S.eq_empty_or_nonempty with hS | ⟨K₀, hK₀⟩
  · have h1 : E = ⊥ := by
      rw [← Fr.gen, hS]
      simp [wzSet]
    have := Fr.card
    rw [h1, Subgroup.card_bot] at this
    omega
  · obtain ⟨z₀, hz₀, -⟩ := Fr.exists_central hK₀
    have h1 : E ≤ Subgroup.zpowers z₀ := by
      rw [← Fr.gen, Subgroup.closure_le]
      rintro z ⟨K, hK, hz⟩
      have hKK : K = K₀ := hne K hK K₀ hK₀
      subst hKK
      rw [SetLike.mem_coe, Fr.eq_of_central hK hz hz₀]
      exact Subgroup.mem_zpowers z₀
    have h2 : Nat.card E ≤ 2 := by
      have hfin : IsOfFinOrder z₀ :=
        isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, by rw [pow_two]; exact hz₀.sq⟩
      have := hfin.finite_zpowers
      have h3 : Nat.card (Subgroup.zpowers z₀) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by norm_num)
          (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz₀.sq))
      exact (Subgroup.card_le_of_le h1).trans h3
    have := Fr.card
    omega

end WeakPreFrame3

end CFSG.ClassicalInvolution.Q3
