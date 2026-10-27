module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcData
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcUni
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Two

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

namespace Up34Exc

section Counting

variable {τ : Tag}

theorem ncard_eq_two_mul_ncard_posRoots {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hfin : Ψ.Finite) : Ψ.ncard = 2 * (posRoots Ψ).ncard := by
  classical
  have hu : Ψ = posRoots Ψ ∪ negRoots Ψ := by
    ext α
    constructor
    · intro hα
      exact (mem_posRoots_or_mem_negRoots hΨ hα).elim Or.inl Or.inr
    · rintro (h | h)
      · exact h.1
      · exact ((mem_negRoots_iff hΨ).1 h).1
  have hdisj : Disjoint (posRoots Ψ) (negRoots Ψ) :=
    Set.disjoint_left.2 fun α h1 h2 => not_mem_negRoots_of_mem_posRoots h1 h2
  have himg : negRoots Ψ = (fun α : Fin τ.rank → ℤ => -α) '' posRoots Ψ := by
    ext α
    constructor
    · intro h
      exact ⟨-α, h, by simp⟩
    · rintro ⟨β, hβ, rfl⟩
      change -(-β) ∈ posRoots Ψ
      rw [neg_neg]
      exact hβ
  have hfp : (posRoots Ψ).Finite := hfin.subset fun α hα => hα.1
  have hfn : (negRoots Ψ).Finite := by rw [himg]; exact hfp.image _
  conv_lhs => rw [hu]
  rw [Set.ncard_union_eq hdisj hfp hfn, himg, Set.ncard_image_of_injective _ neg_injective]
  ring

end Counting

section Branches

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem finite_rationalComponent (S : LangSetup τ L p₀) (a : Fin τ.rank → Lˣ)
    (i : KernelComponent (rootCharHom a)) :
    Finite ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  haveI := S.finite
  have h1 : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ S.D.model :=
    (Subgroup.commutator_le_self _).trans ((inf_le_right : _ ≤ S.Γ).trans
      (Subgroup.commutator_le_self _))
  exact Finite.of_injective (Subgroup.inclusion h1) (Subgroup.inclusion_injective h1)

theorem innerData_range_eq (D : InnerData S a i)
    (hperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) :
    D.f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
  le_antisymm (D.hf3 (Subgroup.isPerfect_iff.1 hperf)) D.hf1

theorem exists_surjective_central_of_perfect (D : InnerData S a i)
    (hperf : Group.IsPerfect ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) :
    ∃ g : ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) →*
        ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      Function.Surjective g ∧ g.ker ≤ Subgroup.center ↥(componentRootSpan (fixSubfield D.σ)
        (rootCharHom a) i) := by
  have hrange := innerData_range_eq D hperf
  refine ⟨D.f.codRestrict _ (fun c => hrange ▸ ⟨c, rfl⟩), fun r => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := D.hf1 r.2
    exact ⟨c, Subtype.ext hc⟩
  · rw [MonoidHom.ker_codRestrict]
    exact D.hf2

theorem inner_a1_false (D : InnerData S a i)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      δ = α ∨ δ = -α)
    (hL34 : IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_rationalComponent S a i
  by_cases hQ : 4 ≤ Nat.card (fixSubfield D.σ)
  · have hQ' : 4 ≤ 2 ^ (D.e * D.s) := D.hKcard ▸ hQ
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ (Nat.mul_pos D.he D.hs0) hQ'
    have hperf := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
      (χ := rootCharHom a) ht i
    obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
    exact rankOne_not_isLThreeFour (rootCharHom a) i hrank (fixSubfield D.σ) g hg hgk hL34
  · have hK2 : Nat.card (fixSubfield D.σ) = 2 := by
      have hes : D.e * D.s = 1 := by
        by_contra h
        have h2 : 2 ≤ D.e * D.s := by
          have := Nat.mul_pos D.he D.hs0
          omega
        have : 4 ≤ 2 ^ (D.e * D.s) :=
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (D.e * D.s) := Nat.pow_le_pow_right (by norm_num) h2
        rw [D.hKcard] at hQ
        omega
      rw [D.hKcard, hes]
      norm_num
    have hC6 := card_componentRootSpan_rankOne_le_six (rootCharHom a) i hrank
      (fixSubfield D.σ) hK2
    haveI : Finite ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) := inferInstance
    haveI : Finite ↥D.f.range := Finite.of_surjective D.f.rangeRestrict D.f.rangeRestrict_surjective
    have h1 : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥D.f.range :=
      Subgroup.card_le_of_le D.hf1
    have h2 : Nat.card ↥D.f.range ≤
        Nat.card ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd D.f)
    have h3 := card_eq_of_isLThreeFour hL34
    have h4 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≤
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega

theorem eq_zero_or_one_of_card_two' {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (c : F) : c = 0 ∨ c = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype F := Fintype.ofFinite F
  have h3 : ({0, 1, c} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hcon.2.symm
    · simp [hcon.1.symm, zero_ne_one]
  have := Finset.card_le_univ ({0, 1, c} : Finset F)
  rw [h3, ← Nat.card_eq_fintype_card, hF] at this
  omega

theorem exists_pair_of_two_lt_ncard {Ψ : Set (Fin τ.rank → ℤ)} (hne : Ψ.Nonempty)
    (h : 2 < Ψ.ncard) : ∃ α ∈ Ψ, ∃ δ ∈ Ψ, δ ≠ α ∧ δ ≠ -α := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨α, hα⟩ := hne
  have hsub : Ψ ⊆ {α, -α} := fun δ hδ => by
    by_cases h1 : δ = α
    · exact Or.inl h1
    · exact Or.inr (hcon α hα δ hδ h1)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    simp
  omega

theorem isPerfect_componentRootSpan_of_big (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (D : InnerData S a i) (hbig : 14 ≤ (componentRoots (rootCharHom a) i).ncard) :
    Group.IsPerfect ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (componentRoots (rootCharHom a) i).Nonempty := by
    obtain ⟨b, hb⟩ := Quotient.exists_rep i
    exact ⟨b.1, b.2, hb⟩
  have hpair := exists_pair_of_two_lt_ncard hne (by omega)
  by_cases hQ : 4 ≤ Nat.card (fixSubfield D.σ)
  · have hQ' : 4 ≤ 2 ^ (D.e * D.s) := D.hKcard ▸ hQ
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ (Nat.mul_pos D.he D.hs0) hQ'
    exact isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
      (χ := rootCharHom a) ht i
  · rcases hτ with rfl | h | h | h
    ·
      have hK2 : Nat.card (fixSubfield D.σ) = 2 := by
        have hes : D.e * D.s = 1 := by
          by_contra h
          have h2 : 2 ≤ D.e * D.s := by
            have := Nat.mul_pos D.he D.hs0
            omega
          have : 4 ≤ 2 ^ (D.e * D.s) :=
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ (D.e * D.s) := Nat.pow_le_pow_right (by norm_num) h2
          rw [D.hKcard] at hQ
          omega
        rw [D.hKcard, hes]
        norm_num
      have hK2' : ∀ x : fixSubfield D.σ, x = 0 ∨ x = 1 := eq_zero_or_one_of_card_two' hK2
      refine isPerfect_componentRootSpan_F4_two hK2' i ?_
      by_contra hno
      push Not at hno
      obtain ⟨s, l, -, -, -, hΨ⟩ := eq_b2Block_of_noA2 i hpair hno
      have h8 : (componentRoots (rootCharHom a) i).ncard ≤ 8 := by
        have hset : componentRoots (rootCharHom a) i = (↑([s, -s, l, -l, s + l, -(s + l),
            2 • s + l, -(2 • s + l)] : List (Fin Tag.F4.rank → ℤ)).toFinset :
            Set (Fin Tag.F4.rank → ℤ)) := by
          rw [hΨ]
          ext x
          simp
        rw [hset, Set.ncard_coe_finset]
        exact (List.toFinset_card_le _).trans (by simp)
      omega
    · exact isPerfect_componentRootSpan_simplyLaced (Or.inr (Or.inl h)) i hpair
    · exact isPerfect_componentRootSpan_simplyLaced (Or.inr (Or.inr (Or.inl h))) i hpair
    · exact isPerfect_componentRootSpan_simplyLaced (Or.inr (Or.inr (Or.inr h))) i hpair

theorem inner_big_false (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (D : InnerData S a i)
    (hbig : 14 ≤ (componentRoots (rootCharHom a) i).ncard)
    (hL34 : IsLThreeFour (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_rationalComponent S a i
  have hperf := isPerfect_componentRootSpan_of_big hτ D hbig
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have h2N := ncard_eq_two_mul_ncard_posRoots hΨ hfin
  have hN : 7 ≤ (posRoots (componentRoots (rootCharHom a) i)).ncard := by omega
  have hK2 : 2 ≤ Nat.card (fixSubfield D.σ) := Finite.one_lt_card
  have hbig' : 64 < Nat.card (fixSubfield D.σ) ^
      (posRoots (componentRoots (rootCharHom a) i)).ncard :=
    calc 64 < 2 ^ 7 := by norm_num
      _ ≤ 2 ^ (posRoots (componentRoots (rootCharHom a) i)).ncard :=
        Nat.pow_le_pow_right (by norm_num) hN
      _ ≤ _ := Nat.pow_le_pow_left hK2 _
  exact unipotent_not_isLThreeFour uniEmbed_holds (rootCharHom a) i (fixSubfield D.σ) g hg hgk
    hperf hL34 hbig'

end Branches

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
