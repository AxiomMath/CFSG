module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OrtHBlocks
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks
  (isSolvable_orthogonalGroup_of_smallFixedException)
open scoped commutatorElement

theorem t6orth_factorOK_of_solvable (q : ℕ) {G : Type} [Group G] {F : Subgroup G}
    (hF : Group.IsSolvable ↥F) : t6orth_FactorOK q F :=
  ⟨0, fun i => i.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, Or.inl hF,
    fun j => j.elim0⟩

section Small

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem t6orth_commute_orthDerived_of_finrank_le_two {R : QuadraticForm K W}
    (hR : R.polarBilin.Nondegenerate) (hW : finrank K W ≤ 2) {g g' : W ≃ₗ[K] W}
    (hg : g ∈ orthDerived R) (hg' : g' ∈ orthDerived R) : g * g' = g' * g := by
  have h1 := dicksonHom_eq_one_of_mem_orthDerived hR hg
  have h1' := dicksonHom_eq_one_of_mem_orthDerived hR hg'
  by_cases h2 : finrank K W = 2
  · exact commute_of_dicksonHom_eq_one hR h2 (orthDerived_le_orthogonalGroup hg)
      (orthDerived_le_orthogonalGroup hg') h1 h1'
  · have hle : finrank K W ≤ 1 := by omega
    have e1 : g = 1 := eq_one_of_dicksonHom_eq_one_of_finrank_le_one hR hle h1
    rw [e1, one_mul, mul_one]

theorem t6orth_isSolvable_orthogonalGroup_of_finrank_le_two {R : QuadraticForm K W}
    (hR : R.polarBilin.Nondegenerate) (hW : finrank K W ≤ 2) :
    Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup R with hO
  have h : t6orth_dsub O 2 = ⊥ := by
    rw [eq_bot_iff]
    show ⁅⁅O, O⁆, ⁅O, O⁆⁆ ≤ ⊥
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact t6orth_commute_orthDerived_of_finrank_le_two hR hW ha hb
  refine ⟨⟨2, ?_⟩⟩
  have h' : (derivedSeries ↥O 2).map O.subtype = ⊥ := by
    rw [t6orth_map_subtype_derivedSeries]
    exact h
  exact Subgroup.map_injective O.subtype_injective (h'.trans (Subgroup.map_bot _).symm)

end Small

theorem t6orth_mem_commutator_of_isPGroup_two {G : Type*} [Group G]
    (hP : IsPGroup 2 (G ⧸ commutator G)) {g : G} (hg : Odd (orderOf g)) : g ∈ commutator G := by
  have h1 : orderOf (QuotientGroup.mk g : G ⧸ commutator G) ∣ orderOf g :=
    orderOf_map_dvd (QuotientGroup.mk' (commutator G)) g
  obtain ⟨k, hk⟩ := hP (QuotientGroup.mk g : G ⧸ commutator G)
  have h2 : orderOf (QuotientGroup.mk g : G ⧸ commutator G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hg)
  have h3 : orderOf (QuotientGroup.mk g : G ⧸ commutator G) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact (QuotientGroup.eq_one_iff g).1 (orderOf_eq_one_iff.1 h3)

section Odd

variable {K : Type} [Field K] [Finite K] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem t6orth_odd_mem_orthDerived (R : QuadraticForm K W) (hR : R.polarBilin.Nondegenerate)
    (h3 : 3 ≤ finrank K W) (hns : ¬ SmallFixedException R) {g : W ≃ₗ[K] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (ho : Odd (orderOf g)) :
    g ∈ orthDerived R := by
  classical
  set O := TauCeti.QuadraticMap.orthogonalGroup R with hO
  have hcomm : ∀ y : ↥O, y ∈ commutator ↥O → (y : W ≃ₗ[K] W) ∈ orthDerived R := fun y hy => by
    rw [orthDerived, ← Subgroup.map_subtype_commutator]
    exact ⟨y, hy, rfl⟩
  by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0
  · obtain ⟨-, -, -, -, -, -, hodd, -⟩ :=
      CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hR hT
    exact hodd g hg ho
  by_cases h2 : ringChar K = 2
  ·
    haveI : CharP K 2 := ringChar.of_eq h2
    obtain ⟨⟨n, hn⟩, -, hnf, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms R hR
    by_cases hS : ∃ U : Submodule K W, finrank K U = n ∧ ∀ u ∈ U, R u = 0
    ·
      obtain ⟨U, hUn, hUQ⟩ := hS
      have hn2 : n = 2 := by
        by_contra hne
        exact hT (exists_threeSingular_of_le R hUQ (by omega))
      subst hn2
      have hcase : (Odd (Nat.card K) ∧ (finrank K W = 3 ∨ finrank K W = 4 ∨ finrank K W = 5)) ∨
          (Odd (Nat.card K) ∧ finrank K W = 6 ∧
            ¬ ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) ∨
          (finrank K W = 4 ∧ ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) :=
        Or.inr (Or.inr ⟨by omega, U, hUn, hUQ⟩)
      obtain ⟨-, hcov, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage R hR hcase
      obtain ⟨-, hP, -, -⟩ := hcov hns
      exact hcomm ⟨g, hg⟩ (t6orth_mem_commutator_of_isPGroup_two hP
        (by rw [Subgroup.orderOf_mk]; exact ho))
    · have hts : ∀ U : Submodule K W, finrank K U = n → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hS ⟨U, hU, hcon⟩
      rcases hnf n (by omega) hn with ⟨b, hb⟩ | ⟨β, γ, -, -, b, hb⟩
      · exfalso
        refine hS ⟨Submodule.span K (Set.range fun i : Fin n => b (Sum.inl i)), ?_, ?_⟩
        · exact (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans
            (by simp)
        · intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0
      · have hU : ∀ u ∈ Submodule.span K (Set.range fun i : Fin (n - 1) => b (Sum.inl i)),
            R u = 0 := by
          intro u hu
          obtain ⟨x, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
          simpa using hb x 0 0 0
        have hdU : finrank K (Submodule.span K (Set.range fun i : Fin (n - 1) =>
            b (Sum.inl i))) = n - 1 :=
          (finrank_span_eq_card (b.linearIndependent.comp _ Sum.inl_injective)).trans (by simp)
        have hn23 : n = 2 ∨ n = 3 := by
          by_contra hne
          exact hT (exists_threeSingular_of_le R hU (by omega))
        have hd46 : finrank K W = 4 ∨ finrank K W = 6 := by omega
        obtain ⟨-, -, -, -, hodd, -⟩ :=
          CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction R hR hd46
            (fun U hU => hts U (by omega))
        exact hodd g hg ho
  ·
    obtain ⟨hEA, -, -, -⟩ := odd_orthogonal_abelianization_order_bound h2 hR
    have hsq : ∀ y : ↥O, y ^ 2 ∈ commutator ↥O := by
      intro y
      obtain ⟨c, hc⟩ := hEA.exponent_dvd_p
      have h1 : (Abelianization.of y) ^ 2 = 1 := by
        rw [hc, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
      have hker : y ^ 2 ∈ (Abelianization.of : ↥O →* Abelianization ↥O).ker := by
        rw [MonoidHom.mem_ker, map_pow]
        exact h1
      rwa [Abelianization.ker_of] at hker
    obtain ⟨k, hk⟩ := ho
    have h1 : (⟨g, hg⟩ : ↥O) = ((⟨g, hg⟩ : ↥O) ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf (⟨g, hg⟩ : ↥O) + 1 by
        rw [Subgroup.orderOf_mk]; omega, pow_succ, pow_orderOf_eq_one, one_mul]
    have h2' : (⟨g, hg⟩ : ↥O) ∈ commutator ↥O := by
      rw [h1]
      exact Subgroup.pow_mem _ (hsq _) _
    exact hcomm ⟨g, hg⟩ h2'

end Odd

section Fixed

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem t6orth_mem_commutator_fixed (hx : OddOrderIsometry Q p x)
    (h3 : 3 ≤ finrank K (fixedSpace x))
    (hns : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype))
    {b : V ≃ₗ[K] V} (hb : b ∈ supportedBlock Q x (X - 1)) (hb3 : b ^ 3 = 1) :
    b ∈ ⁅supportedBlock Q x (X - 1), supportedBlock Q x (X - 1)⁆ := by
  rw [← hx.supportedFixedDerived_eq]
  refine mem_supportedFixedDerived.mpr ⟨hb, ?_⟩
  set φ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) :=
    fixedBlockEquiv hx ⟨b, hb⟩ with hφ
  have hφ3 : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨b, hb⟩ : ↥(supportedBlock Q x (X - 1))) ^ 3 = 1 := Subtype.ext hb3
    rw [this, map_one]
  have hodd : Odd (orderOf (φ : fixedSpace x ≃ₗ[K] fixedSpace x)) := by
    rw [Subgroup.orderOf_coe]
    have hd : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  exact t6orth_odd_mem_orthDerived (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate h3 hns φ.2 hodd

theorem t6orth_factorOK_fixed (hx : OddOrderIsometry Q p x) (q : ℕ) :
    t6orth_FactorOK q (supportedBlock Q x (X - 1)) := by
  classical
  set F := supportedBlock Q x (X - 1) with hF
  set R := Q.comp (fixedSpace x).subtype with hR
  have hRn := hx.polarBilin_fixed_nondegenerate
  have e := fixedBlockEquiv hx
  by_cases hd : finrank K (fixedSpace x) ≤ 2
  · refine t6orth_factorOK_of_solvable q ?_
    haveI := t6orth_isSolvable_orthogonalGroup_of_finrank_le_two hRn hd
    exact Group.isSolvable_of_isSolvable_injective (f := (fixedBlockEquiv hx).toMonoidHom)
      (fixedBlockEquiv hx).injective
  have hd3 : 3 ≤ finrank K (fixedSpace x) := by omega
  by_cases hS : SmallFixedException R
  · refine t6orth_factorOK_of_solvable q ?_
    haveI := isSolvable_orthogonalGroup_of_smallFixedException R hRn hd3 hS
    exact Group.isSolvable_of_isSolvable_injective (f := (fixedBlockEquiv hx).toMonoidHom)
      (fixedBlockEquiv hx).injective
  · have hcov := (orthogonal_regular_space_coverage R hRn hd3).2 hS
    obtain ⟨n, Fs, -, -, hsup, hFs, hcomm, -⟩ := hx.exists_supported_factors hcov
    have hSFD := hx.supportedFixedDerived_eq
    have hcomm' : ∀ j j', j ≠ j' → ∀ u ∈ Fs j, ∀ v ∈ Fs j', Commute u v :=
      fun j j' hjj' u hu v hv => hcomm j j' hjj' u hu v hv
    refine ⟨n, Fs, fun j => (hFs j).1, fun j => ?_, fun j => ?_, Or.inr ?_, ?_⟩
    · rw [← hSFD]
      exact (hFs j).2.1
    · have := (hFs j).2.2
      rw [hSFD] at this
      exact this
    · rw [← hSFD, ← hsup]
    · intro j _ b hb hb3
      have hbd : b ∈ ⁅F, F⁆ := t6orth_mem_commutator_fixed hx hd3 hS hb hb3
      have hbj : b ∈ ⨆ i, Fs i := by
        rw [hsup, hSFD]
        exact hbd
      obtain ⟨bi, hbi, w, hw, rfl⟩ := exists_decomp_of_commuting_iSup Fs hcomm' j hbj
      refine ⟨bi, hbi, fun m hm => ?_⟩
      have hwm : w * m = m * w := hw m hm
      calc bi * w * m * (bi * w)⁻¹ = bi * (w * m * w⁻¹) * bi⁻¹ := by group
        _ = bi * m * bi⁻¹ := by rw [hwm]; group

end Fixed

end CFSG.HardMathSupport.Dickson.Sec6.I1431
