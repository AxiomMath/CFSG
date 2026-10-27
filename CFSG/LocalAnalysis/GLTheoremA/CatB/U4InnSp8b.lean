module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8a
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.PartOne.TCP.SurvPrimary
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

open CFSG.Open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Facts

variable {s : StatedSp 4 (ZMod 2)}

theorem squarefree_minpoly_spEnd (hs3 : s ^ 3 = 1) :
    Squarefree (minpoly (ZMod 2) (spEnd s)) :=
  (altPrimaryData_spLin (p := 3) (by decide) hs3).squarefree

theorem eq_one_of_trivial_on_primary (hs3 : s ^ 3 = 1) {g : StatedSp 4 (ZMod 2)}
    (hg : ∀ k ∈ primaryFactors (spEnd s), ∀ v ∈ primaryComponent (spEnd s) k, spEnd g v = v) :
    g = 1 := by
  have h := ext_primaryComponent (squarefree_minpoly_spEnd hs3) (f := spEnd g)
    (g := LinearMap.id) (fun a ha v hv => hg a ha v hv)
  apply spLin_injective
  apply Units.ext
  rw [map_one, Units.val_one]
  exact h

theorem reciprocal_eq_self (hs3 : s ^ 3 = 1) {h : (ZMod 2)[X]}
    (hh : h ∈ primaryFactors (spEnd s)) : CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h = h := by
  by_cases h1 : h = X - 1
  · rw [h1]; exact reciprocalPolynomial_X_sub_one
  · have hord : orderOf (Nat.card (ZMod 2) : ZMod 3) = 2 := by
      rw [Nat.card_zmod]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by decide) (by decide)
    exact CFSG.RankThree.PartOne.TCP.reciprocalPolynomial_eq_of_mem Nat.prime_three
      (spEnd_pow hs3) hord hh h1

theorem reciprocalTransversal_empty (hs3 : s ^ 3 = 1) :
    IsReciprocalTransversal (spEnd s) ∅ := by
  refine ⟨fun h hh => absurd hh (Finset.notMem_empty h), fun h hh hne => ?_,
    fun h hh => absurd hh (Finset.notMem_empty h)⟩
  exact absurd (reciprocal_eq_self hs3 hh).symm hne

theorem spSupported_X_sub_one_eq_bot (hs3 : s ^ 3 = 1)
    (h1 : (X - 1 : (ZMod 2)[X]) ∉ primaryFactors (spEnd s)) :
    spSupported s {(X - 1 : (ZMod 2)[X])} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' := (mem_spSupported.1 hg).2
  refine eq_one_of_trivial_on_primary hs3 (fun k hk v hv => hg' k hk ?_ v hv)
  intro hkm
  rw [Set.mem_singleton_iff] at hkm
  exact h1 (hkm ▸ hk)

theorem spSupported_le_centralizer (O : Set (ZMod 2)[X]) :
    spSupported s O ≤ Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) :=
  fun _ hg => Subgroup.mem_centralizer_singleton_iff.2 (mem_spSupported.1 hg).1

theorem centralizer_eq_sup (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) =
      spSupported s {(X - 1 : (ZMod 2)[X])} ⊔ spSupported s {q2} := by
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have blocks := sp8_blocks s hord
  refine le_antisymm ?_ (sup_le (spSupported_le_centralizer _) (spSupported_le_centralizer _))
  rw [← blocks.directProduct.2.2]
  refine iSup_le fun O => ?_
  obtain ⟨h, hh, hO⟩ := O.2
  have hself := reciprocal_eq_self hs3 hh
  rcases mem_primaryFactors_pow_three (spEnd_pow hs3) hh with rfl | rfl
  · have : (O : Set (ZMod 2)[X]) = {X - 1} := by
      rw [← hO]; simp only [hself, Set.pair_eq_singleton]
    rw [this]; exact le_sup_left
  · have : (O : Set (ZMod 2)[X]) = {q2} := by
      rw [← hO]; simp only [hself, Set.pair_eq_singleton]
    rw [this]; exact le_sup_right

theorem inf_supported_eq_bot (hs3 : s ^ 3 = 1) :
    spSupported s {(X - 1 : (ZMod 2)[X])} ⊓ spSupported s {q2} = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨h0, h1⟩ := Subgroup.mem_inf.1 hg
  refine eq_one_of_trivial_on_primary hs3 (fun k hk v hv => ?_)
  by_cases hk1 : k = X - 1
  · refine (mem_spSupported.1 h1).2 k hk ?_ v hv
    rw [Set.mem_singleton_iff, hk1]
    exact q2_ne_X_sub_one.symm
  · exact (mem_spSupported.1 h0).2 k hk (by rwa [Set.mem_singleton_iff]) v hv

theorem commute_supported (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (h1 : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd s)) (hq : q2 ∈ primaryFactors (spEnd s)) :
    ∀ a ∈ spSupported s {(X - 1 : (ZMod 2)[X])}, ∀ b ∈ spSupported s {q2}, a * b = b * a := by
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have blocks := sp8_blocks s hord
  intro a ha b hb
  have hrec := reciprocal_eq_self hs3 h1
  have hrec2 := reciprocal_eq_self hs3 hq
  have hO1 : ({X - 1, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial (X - 1)} :
      Set (ZMod 2)[X]) ∈ reciprocalOrbits (spEnd s) := ⟨X - 1, h1, rfl⟩
  have hO2 : ({q2, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial q2} :
      Set (ZMod 2)[X]) ∈ reciprocalOrbits (spEnd s) := ⟨q2, hq, rfl⟩
  rw [hrec, Set.pair_eq_singleton] at hO1
  rw [hrec2, Set.pair_eq_singleton] at hO2
  have hne : ({X - 1} : Set (ZMod 2)[X]) ≠ {q2} := by
    intro h
    exact q2_ne_X_sub_one (Set.singleton_eq_singleton_iff.1 h).symm
  exact (blocks.directProduct.1 _ hO1 _ hO2 hne a ha b hb).eq

theorem primaryMultiplicity_q2_eq_zero (hq : q2 ∉ primaryFactors (spEnd s)) :
    primaryMultiplicity (spEnd s) q2 = 0 := by
  have hbot := primaryComponent_eq_bot_of_not_mem (y := spEnd s) q2_irreducible monic_q2 hq
  haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
  haveI : Subsingleton ↥(primaryComponent (spEnd s) q2) := by rw [hbot]; infer_instance
  exact Module.finrank_zero_of_subsingleton

open CFSG.RankThree.PartOne.KCOrthogonal in
theorem dimension_count (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ s₀ : ℕ, Module.finrank (ZMod 2) ↥(primaryComponent (spEnd s) (X - 1)) = 2 * s₀ ∧
      4 = s₀ + primaryMultiplicity (spEnd s) q2 := by
  classical
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have blocks := sp8_blocks s hord
  obtain ⟨s₀, hs₀, -, hrk⟩ := blocks.rank
  refine ⟨s₀, hs₀, ?_⟩
  have h4 := hrk ∅ (reciprocalTransversal_empty hs3)
  rw [Finset.sum_empty, add_zero] at h4
  refine h4.trans ?_
  congr 1
  rw [Finset.sum_filter]
  by_cases hq : q2 ∈ primaryFactors (spEnd s)
  · rw [Finset.sum_eq_single q2]
    · rw [if_pos ⟨reciprocal_eq_self hs3 hq, q2_ne_X_sub_one⟩, natDegree_q2]
      simp
    · intro h hh hne
      rw [if_neg]
      rintro ⟨-, hne1⟩
      rcases mem_primaryFactors_pow_three (spEnd_pow hs3) hh with h' | h'
      · exact hne1 h'
      · exact hne h'
    · intro hq'
      exact absurd hq hq'
  · rw [Finset.sum_eq_zero, primaryMultiplicity_q2_eq_zero hq]
    intro h hh
    rw [if_neg]
    rintro ⟨-, hne1⟩
    rcases mem_primaryFactors_pow_three (spEnd_pow hs3) hh with h' | h'
    · exact hne1 h'
    · exact hq (h' ▸ hh)

theorem q2_mem_primaryFactors (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    q2 ∈ primaryFactors (spEnd s) := by
  by_contra hq
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have blocks := sp8_blocks s hord
  obtain ⟨s₀, hs₀, hs4⟩ := dimension_count hs3 hs1
  rw [primaryMultiplicity_q2_eq_zero hq, add_zero] at hs4
  subst hs4
  have htop : primaryComponent (spEnd s) (X - 1) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hs₀]
    simp [Module.finrank_fintype_fun_eq_card]
  apply hs1
  apply spLin_injective
  apply Units.ext
  rw [map_one, Units.val_one]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ primaryComponent (spEnd s) (X - 1) := htop ▸ Submodule.mem_top
  rw [blocks.fixed_eq] at hv
  exact sub_eq_zero.mp (by simpa using LinearMap.mem_ker.mp hv)

structure Sp8Class (s : StatedSp 4 (ZMod 2)) (s₀ m : ℕ) (A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))) :
    Prop where
  sum_eq : s₀ + m = 4
  one_le : 1 ≤ m
  centralizer_eq : Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))) = A₀ ⊔ A₁
  commute : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a
  disjoint : A₀ ⊓ A₁ = ⊥
  fixed : (s₀ = 0 ∧ A₀ = ⊥) ∨ (1 ≤ s₀ ∧ Nonempty (↥A₀ ≃* StatedSp s₀ (ZMod 2)))
  unitary : ∃ (E : Type) (_ : Field E) (hE : UnitaryFieldData 2 1 E) (W : Type) (_ : AddCommGroup W)
      (_ : Module E W) (_ : FiniteDimensional E W) (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧ Module.finrank E W = m ∧ Nonempty (↥A₁ ≃* sesqUnitaryGroup Hf)

theorem exists_class_spSupported (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ s₀ : ℕ, Sp8Class s s₀ (primaryMultiplicity (spEnd s) q2)
      (spSupported s {(X - 1 : (ZMod 2)[X])}) (spSupported s {q2}) := by
  classical
  have hord : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have blocks := sp8_blocks s hord
  have hsq := squarefree_minpoly_spEnd hs3
  have hq := q2_mem_primaryFactors hs3 hs1
  haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
  obtain ⟨s₀, hs₀, hs4⟩ := dimension_count hs3 hs1
  refine ⟨s₀, ⟨hs4.symm, ?_, centralizer_eq_sup hs3 hs1, ?_, inf_supported_eq_bot hs3, ?_, ?_⟩⟩
  ·
    have h1 : 1 ≤ finrank (ZMod 2) (primaryComponent (spEnd s) q2) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq hq)
    have h2 := finrank_primaryComponent (x := spEnd s) (a := q2)
    rcases Nat.eq_zero_or_pos (primaryMultiplicity (spEnd s) q2) with h0 | h0
    · have h0' : finrank (AdjoinRoot q2) ↥(primaryComponent (spEnd s) q2) = 0 := h0
      rw [h0', mul_zero] at h2
      omega
    · exact h0
  ·
    by_cases h1 : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd s)
    · exact commute_supported hs3 hs1 h1 hq
    · intro a ha b _
      rw [spSupported_X_sub_one_eq_bot hs3 h1, Subgroup.mem_bot] at ha
      rw [ha, one_mul, mul_one]
  ·
    by_cases h1 : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd s)
    · right
      obtain ⟨φ, -⟩ := blocks.fixedFactor h1
      have hB : ((spForm 4 (ZMod 2)).restrict (primaryComponent (spEnd s) (X - 1))).IsAlt :=
        fun c => spForm_isAlt (c : Fin 4 ⊕ Fin 4 → ZMod 2)
      obtain ⟨s', hs', ⟨e⟩⟩ := CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp
        hB blocks.fixed_nondegenerate
      have h1' : 1 ≤ finrank (ZMod 2) (primaryComponent (spEnd s) (X - 1)) :=
        Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq h1)
      have hss : s' = s₀ := by omega
      subst hss
      exact ⟨by omega, ⟨φ.trans e⟩⟩
    · left
      have hbot := primaryComponent_eq_bot_of_not_mem (y := spEnd s) irreducible_X_sub_one
        monic_X_sub_one h1
      have hfr : finrank (ZMod 2) ↥(primaryComponent (spEnd s) (X - 1)) = 0 := by
        rw [hbot]; exact finrank_bot _ _
      exact ⟨by omega, spSupported_X_sub_one_eq_bot hs3 h1⟩
  ·
    obtain ⟨d, hd, -, σ, -, -, -, -, -, hE, -, Hf, hsymm, hsep, -, -, φ, -⟩ :=
      (blocks.selfDual ⟨q2, hq⟩ q2_ne_X_sub_one (reciprocal_eq_self hs3 hq)).exists_half
    have hd1 : d = 1 := by
      have := natDegree_q2
      simp only at hd
      omega
    subst hd1
    exact ⟨_, _, hE, _, _, _, inferInstance, Hf, hsymm, hsep, rfl, ⟨φ⟩⟩

theorem exists_class (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ (s₀ m : ℕ) (A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))), Sp8Class s s₀ m A₀ A₁ :=
  let ⟨s₀, h⟩ := exists_class_spSupported hs3 hs1
  ⟨s₀, _, _, _, h⟩

end Facts

end CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8
end
