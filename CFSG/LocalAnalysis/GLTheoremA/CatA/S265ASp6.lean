module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8a
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.RankThree.PartOne.TCP.SurvPrimary
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 (q2 natDegree_q2 monic_q2 q2_irreducible
  q2_ne_X_sub_one mem_primaryFactors_pow_three)

structure Sp6Class (s : StatedSp 3 (ZMod 2)) (s₀ m : ℕ)
    (A₀ A₁ : Subgroup (StatedSp 3 (ZMod 2))) : Prop where
  sum_eq : s₀ + m = 3
  one_le : 1 ≤ m
  centralizer_eq : Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2))) = A₀ ⊔ A₁
  commute : ∀ a ∈ A₀, ∀ b ∈ A₁, a * b = b * a
  disjoint : A₀ ⊓ A₁ = ⊥
  fixed : (s₀ = 0 ∧ A₀ = ⊥) ∨ (1 ≤ s₀ ∧ Nonempty (↥A₀ ≃* StatedSp s₀ (ZMod 2)))
  unitary : ∃ (E : Type) (_ : Field E) (hE : UnitaryFieldData 2 1 E) (W : Type)
      (_ : AddCommGroup W) (_ : Module E W) (_ : FiniteDimensional E W)
      (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E), Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        Module.finrank E W = m ∧ Nonempty (↥A₁ ≃* sesqUnitaryGroup Hf)
  finrank_fixed : Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd s - 1)) = 2 * s₀

variable {s : StatedSp 3 (ZMod 2)}

private theorem sp6_blocks (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    SpPrimaryBlocks 2 1 3 s (proj 3 (ZMod 2) s) := by
  have hs : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hinj : Function.Injective (proj 3 (ZMod 2)) := by
    rw [← MonoidHom.ker_eq_bot_iff, SymplecticHigher.ker_proj, ← Subgroup.card_eq_one,
      card_spScalars_eq_gcd (ZMod 2) (r := 3) (by norm_num)]
    simp [Nat.card_zmod]
  exact (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two le_rfl
    (by simp [Nat.card_zmod]) Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    (proj 3 (ZMod 2) s) (by rw [orderOf_injective _ hinj s, hs])).2 s rfl hs

private theorem squarefree_minpoly (hs3 : s ^ 3 = 1) :
    Squarefree (minpoly (ZMod 2) (spEnd s)) :=
  (altPrimaryData_spLin (p := 3) (by decide) hs3).squarefree

private theorem eq_one_of_trivial_on_primary (hs3 : s ^ 3 = 1) {g : StatedSp 3 (ZMod 2)}
    (hg : ∀ k ∈ primaryFactors (spEnd s), ∀ v ∈ primaryComponent (spEnd s) k, spEnd g v = v) :
    g = 1 := by
  apply spLin_injective; apply Units.ext; rw [map_one, Units.val_one]
  exact ext_primaryComponent (squarefree_minpoly hs3) (f := spEnd g) (g := LinearMap.id)
    (fun a ha v hv => hg a ha v hv)

private theorem reciprocal_eq_self (hs3 : s ^ 3 = 1) {h : (ZMod 2)[X]}
    (hh : h ∈ primaryFactors (spEnd s)) :
    CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial h = h := by
  by_cases h1 : h = X - 1
  · rw [h1]; exact reciprocalPolynomial_X_sub_one
  · have hord : orderOf (Nat.card (ZMod 2) : ZMod 3) = 2 := by
      rw [Nat.card_zmod]; exact orderOf_eq_prime (by decide) (by decide)
    exact CFSG.RankThree.PartOne.TCP.reciprocalPolynomial_eq_of_mem Nat.prime_three
      (spEnd_pow hs3) hord hh h1

private theorem reciprocalTransversal_empty (hs3 : s ^ 3 = 1) :
    IsReciprocalTransversal (spEnd s) ∅ := by
  refine ⟨fun h hh => absurd hh (Finset.notMem_empty h), fun h hh hne => ?_,
    fun h hh => absurd hh (Finset.notMem_empty h)⟩
  exact absurd (reciprocal_eq_self hs3 hh).symm hne

private theorem spSupported_X_sub_one_eq_bot (hs3 : s ^ 3 = 1)
    (h1 : (X - 1 : (ZMod 2)[X]) ∉ primaryFactors (spEnd s)) :
    spSupported s {(X - 1 : (ZMod 2)[X])} = ⊥ :=
  eq_bot_iff.2 fun _ hg => Subgroup.mem_bot.2 <| eq_one_of_trivial_on_primary hs3
    fun k hk v hv => (mem_spSupported.1 hg).2 k hk
      (fun hkm => h1 (Set.mem_singleton_iff.1 hkm ▸ hk)) v hv

private theorem centralizer_eq_sup (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set (StatedSp 3 (ZMod 2))) =
      spSupported s {(X - 1 : (ZMod 2)[X])} ⊔ spSupported s {q2} := by
  have hle (O : Set (ZMod 2)[X]) : spSupported s O ≤ Subgroup.centralizer {s} :=
    fun _ hg => Subgroup.mem_centralizer_singleton_iff.2 (mem_spSupported.1 hg).1
  refine le_antisymm ?_ (sup_le (hle _) (hle _))
  rw [← (sp6_blocks hs3 hs1).directProduct.2.2]
  refine iSup_le fun O => ?_
  obtain ⟨h, hh, hO⟩ := O.2
  have hself := reciprocal_eq_self hs3 hh
  have hO' : (O : Set (ZMod 2)[X]) = {h} := by rw [← hO]; simp only [hself, Set.pair_eq_singleton]
  rw [hO']
  rcases mem_primaryFactors_pow_three (spEnd_pow hs3) hh with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

private theorem inf_supported_eq_bot (hs3 : s ^ 3 = 1) :
    spSupported s {(X - 1 : (ZMod 2)[X])} ⊓ spSupported s {q2} = ⊥ := by
  refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 <|
    eq_one_of_trivial_on_primary hs3 fun k hk v hv => ?_
  obtain ⟨h0, h1⟩ := Subgroup.mem_inf.1 hg
  by_cases hk1 : k = X - 1
  · refine (mem_spSupported.1 h1).2 k hk ?_ v hv
    rw [Set.mem_singleton_iff, hk1]
    exact q2_ne_X_sub_one.symm
  · exact (mem_spSupported.1 h0).2 k hk (by rwa [Set.mem_singleton_iff]) v hv

private theorem commute_supported (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1)
    (h1 : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd s))
    (hq : q2 ∈ primaryFactors (spEnd s)) :
    ∀ a ∈ spSupported s {(X - 1 : (ZMod 2)[X])}, ∀ b ∈ spSupported s {q2}, a * b = b * a := by
  intro a ha b hb
  have hO1 : ({X - 1, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial (X - 1)} :
      Set (ZMod 2)[X]) ∈ reciprocalOrbits (spEnd s) := ⟨X - 1, h1, rfl⟩
  have hO2 : ({q2, CFSG.RankThree.PartOne.KCOrthogonal.reciprocalPolynomial q2} :
      Set (ZMod 2)[X]) ∈ reciprocalOrbits (spEnd s) := ⟨q2, hq, rfl⟩
  rw [reciprocal_eq_self hs3 h1, Set.pair_eq_singleton] at hO1
  rw [reciprocal_eq_self hs3 hq, Set.pair_eq_singleton] at hO2
  have hne : ({X - 1} : Set (ZMod 2)[X]) ≠ {q2} := fun h =>
    q2_ne_X_sub_one (Set.singleton_eq_singleton_iff.1 h).symm
  exact ((sp6_blocks hs3 hs1).directProduct.1 _ hO1 _ hO2 hne a ha b hb).eq

private theorem primaryMultiplicity_q2_eq_zero (hq : q2 ∉ primaryFactors (spEnd s)) :
    primaryMultiplicity (spEnd s) q2 = 0 := by
  have hbot := primaryComponent_eq_bot_of_not_mem (y := spEnd s) q2_irreducible monic_q2 hq
  haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
  haveI : Subsingleton ↥(primaryComponent (spEnd s) q2) := by rw [hbot]; infer_instance
  exact Module.finrank_zero_of_subsingleton

open CFSG.RankThree.PartOne.KCOrthogonal in
private theorem dimension_count (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ s₀ : ℕ, Module.finrank (ZMod 2) ↥(primaryComponent (spEnd s) (X - 1)) = 2 * s₀ ∧
      3 = s₀ + primaryMultiplicity (spEnd s) q2 := by
  classical
  obtain ⟨s₀, hs₀, -, hrk⟩ := (sp6_blocks hs3 hs1).rank
  refine ⟨s₀, hs₀, ?_⟩
  have h3 := hrk ∅ (reciprocalTransversal_empty hs3)
  rw [Finset.sum_empty, add_zero] at h3
  refine h3.trans (congrArg (s₀ + ·) ?_)
  rw [Finset.sum_filter, Finset.sum_eq_single q2]
  · by_cases hq : q2 ∈ primaryFactors (spEnd s)
    · rw [if_pos ⟨reciprocal_eq_self hs3 hq, q2_ne_X_sub_one⟩, natDegree_q2]
      simp
    · rw [primaryMultiplicity_q2_eq_zero hq]
      simp
  · intro h hh hne
    rw [if_neg]
    rintro ⟨-, hne1⟩
    rcases mem_primaryFactors_pow_three (spEnd_pow hs3) hh with h' | h'
    · exact hne1 h'
    · exact hne h'
  · intro hq
    rw [primaryMultiplicity_q2_eq_zero hq]
    simp

private theorem q2_mem_primaryFactors (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    q2 ∈ primaryFactors (spEnd s) := by
  by_contra hq
  obtain ⟨s₀, hs₀, hsum⟩ := dimension_count hs3 hs1
  rw [primaryMultiplicity_q2_eq_zero hq, add_zero] at hsum
  subst hsum
  have htop : primaryComponent (spEnd s) (X - 1) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hs₀]; simp [Module.finrank_fintype_fun_eq_card])
  apply hs1; apply spLin_injective; apply Units.ext; rw [map_one, Units.val_one]
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ primaryComponent (spEnd s) (X - 1) := htop ▸ Submodule.mem_top
  rw [(sp6_blocks hs3 hs1).fixed_eq] at hv
  exact sub_eq_zero.mp (by simpa using LinearMap.mem_ker.mp hv)

theorem exists_sp6Class_spSupported (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ s₀ : ℕ, Sp6Class s s₀ (primaryMultiplicity (spEnd s) q2)
      (spSupported s {(X - 1 : (ZMod 2)[X])}) (spSupported s {q2}) := by
  classical
  have blocks := sp6_blocks hs3 hs1
  have hsq := squarefree_minpoly hs3
  have hq := q2_mem_primaryFactors hs3 hs1
  haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
  obtain ⟨s₀, hs₀, hsum⟩ := dimension_count hs3 hs1
  refine ⟨s₀, ⟨hsum.symm, ?_, centralizer_eq_sup hs3 hs1, ?_, inf_supported_eq_bot hs3, ?_, ?_,
    by rw [← blocks.fixed_eq]; exact hs₀⟩⟩
  ·
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 : 1 ≤ finrank (ZMod 2) (primaryComponent (spEnd s) q2) :=
      Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq hq)
    have h0' : finrank (AdjoinRoot q2) ↥(primaryComponent (spEnd s) q2) = 0 := h0
    have h2 := finrank_primaryComponent (x := spEnd s) (a := q2)
    rw [h0', mul_zero] at h2
    omega
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
      have hB : ((spForm 3 (ZMod 2)).restrict (primaryComponent (spEnd s) (X - 1))).IsAlt :=
        fun c => spForm_isAlt (c : Fin 3 ⊕ Fin 3 → ZMod 2)
      obtain ⟨s', hs', ⟨e⟩⟩ :=
        CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB
          blocks.fixed_nondegenerate
      have h1' : 1 ≤ finrank (ZMod 2) (primaryComponent (spEnd s) (X - 1)) :=
        Submodule.one_le_finrank_iff.mpr (primaryComponent_ne_bot hsq h1)
      obtain rfl : s' = s₀ := by omega
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
    obtain rfl : d = 1 := by
      have := natDegree_q2
      simp only at hd
      omega
    exact ⟨_, _, hE, _, _, _, inferInstance, Hf, hsymm, hsep, rfl, ⟨φ⟩⟩

theorem exists_sp6Class (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ (s₀ m : ℕ) (A₀ A₁ : Subgroup (StatedSp 3 (ZMod 2))), Sp6Class s s₀ m A₀ A₁ :=
  let ⟨s₀, h⟩ := exists_sp6Class_spSupported hs3 hs1
  ⟨s₀, _, _, _, h⟩

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
