module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase
public import CFSG.ClassicalInvolution.Asc77.AscIH8Rest
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHRed

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.LocalBalance (commute_of_isComponent_of_ne)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Components

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem thm5IH_isComponent_comp (hΩ : ConjInvariant Ω) (D : OmegaLie p f Ω) (i : Fin D.card) :
    CFSG.IsComponent (D.comp i) := by
  refine ⟨?_, ?_⟩
  · have hopen := ModelFacts.isQuasisimple_modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out
      (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i)
    have hq := @CFSG.ComponentClassification.Quasisimple.central_quotient _ _ hopen
      (D.hom i).ker (MonoidHom.normal_ker (D.hom i)) (D.ker_le_center i)
    have hrange : CFSG.Open.IsQuasisimple (D.hom i).range :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (QuotientGroup.quotientKerEquivRange (D.hom i)).symm hq
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hrange
  · have hY : (omegaGen Ω).Normal := omegaGen_normal hΩ
    refine Subgroup.IsSubnormal.step (D.comp i) (omegaGen Ω) (D.comp_le_omegaGen i)
      hY.isSubnormal ?_
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using D.mem_comp_conj g.2 hx

end Components

theorem thm5IH_of_base (hbase : T5Base p f) : Ih8Thm5 p f := by
  intro n hn hp2 hq G _ _ hlt Ω hΩ hO K hK J hJ z hz A hA hAKJ hzA
  have hne : Ω.Nonempty := ⟨K, hK⟩
  obtain ⟨D⟩ := exists_omegaLie hn hΩ hne hO hlt
  have hex : ExactMembers Ω := D.exactMembers hp2 hq hΩ
  have hΩ' : HypOmega p f Ω := hΩ.toExact hex
  have hKJ : Commutes K J := AscE186.commutes_of_mem_omegaNbr hp2 hq hΩ' hK hJ
  have hO' : CFSG.pPrimeCore 2 G = ⊥ := by
    rw [← CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact hO
  have hA4 : Nat.card A = 4 := by simpa using hA.1
  have hA2 : ∀ a ∈ A, a * a = 1 := hA.2
  have hAY : A ≤ omegaGen Ω := hAKJ.trans (sup_le (le_omegaGen hK) (le_omegaGen hJ.1))
  have hcompC : ∀ i, CFSG.IsComponent (D.comp i) := fun i =>
    thm5IH_isComponent_comp hΩ.conjInvariant D i
  refine thm5IH_alphaOf_eq_bot_of_components hO' hA2 hA4 ?_
  intro L hL
  by_cases hcase : ∃ i, L = D.comp i
  · obtain ⟨i, rfl⟩ := hcase
    have hAN : A ≤ Subgroup.normalizer ((D.comp i : Subgroup G) : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact D.mem_comp_conj (hAY ha) hx
      · intro hx
        have := D.mem_comp_conj (inv_mem (hAY ha)) hx
        simpa [mul_assoc] using this
    refine ⟨hAN, fun hf => ?_⟩
    have hzL : ¬ ∀ x ∈ D.comp i, z * x = x * z := hf z hzA hz.ne_one
    obtain ⟨i₁, R, hR, hKR⟩ := D.fundamental K hK
    have hi₁ : i₁ = i := by
      by_contra hne'
      apply hzL
      have hKc : K ≤ D.comp i₁ := by
        rw [hKR]
        exact Subgroup.map_le_range _ _
      intro x hx
      exact D.comp_commute hne' z (hKc hz.mem) x hx
    subst hi₁
    obtain ⟨zK, hzK⟩ := hΩ.classical K hK
    obtain ⟨e⟩ := hzK.nonempty_equiv_sl2 (hex K hK)
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hq
    have hodd : Odd (Nat.card (GaloisField p f)) := by
      rw [GaloisField.card p f hf0]
      exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
    have hZ := thm5IH_center_of_exact hodd hz e
    obtain ⟨j, R', hR', hJR'⟩ := D.fundamental J hJ.1
    have hjj : j = i₁ := by
      by_contra hne'
      have hJc : J ≤ D.comp j := by
        rw [hJR']
        exact Subgroup.map_le_range _ _
      obtain ⟨a, haA, ha1, hac⟩ := thm5IH_exists_centralizing hKJ hz hZ hA2 hA4 hAKJ hzA hAN
        (fun j' hj' x hx => D.comp_commute hne' j' (hJc hj') x hx)
      exact hf a haA ha1 (fun x hx => hac x hx)
    subst hjj
    obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ.1
    obtain ⟨e'⟩ := hzJ.nonempty_equiv_sl2 (hex J hJ.1)
    have hKR' : K = R.map (D.hom j) := hKR
    refine hbase hp2 hq (D.tag j) (D.rank j) (D.exp j) (D.isFundTag j) (D.admissible j)
      (D.exp_eq j) G (D.hom j) (D.ker_le_center j) R hR R' hR' ?_ ?_ ?_ ?_ z ?_ A hA ?_ hzA hf
    · rw [← hKR]
      exact ⟨e⟩
    · rw [← hJR']
      exact ⟨e'⟩
    · rw [← hKR, ← hJR']
      exact fun h => hJ.2.1 h.symm
    · rw [← hKR, ← hJR']
      exact hKJ
    · rw [← hKR]
      exact hz
    · rw [← hKR, ← hJR']
      exact hAKJ
  · push Not at hcase
    have hcen : ∀ a ∈ A, ∀ x ∈ L, a * x = x * a := by
      intro a ha x hx
      have hle : omegaGen Ω ≤ Subgroup.centralizer (L : Set G) := by
        rw [← D.iSup_comp]
        refine iSup_le fun i => ?_
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        exact commute_of_isComponent_of_ne hL (hcompC i) (hcase i) w hw y hy
      exact (Subgroup.mem_centralizer_iff.mp (hle (hAY ha)) x hx).symm
    refine ⟨?_, fun hf => absurd (hcen z hzA) (hf z hzA hz.ne_one)⟩
    intro a ha
    exact CFSG.ClassicalInvolution.Balance.LocalBalance.mem_normalizer_of_conjSub_eq
      (Lemma52Proof.conjSub_eq_of_centralizes (hcen a ha))

end CFSG.ClassicalInvolution.Asc77
