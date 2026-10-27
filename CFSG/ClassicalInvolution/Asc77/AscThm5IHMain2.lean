module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHMain
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSplit
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance.LocalBalance (commute_of_isComponent_of_ne)
open scoped commutatorElement MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem thm5IH_of_base_shapes
    (htwin : ∀ (t : Assembly.LowTwoRank.StatedLieTag) (k e : ℕ),
      (TwinShape t k ∨ t = .G2 ∨ t = .trialityD4) → T5BaseAt p f t k e id)
    (hnt : ∀ (t : Assembly.LowTwoRank.StatedLieTag) (k e : ℕ), T5BaseAt p f t k e Not) :
    Ih8Thm5 p f := by
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
    have heK : Nonempty (↥(R.map (D.hom j)) ≃* SL(2, GaloisField p f)) := by
      rw [← hKR]
      exact ⟨e⟩
    have heJ : Nonempty (↥(R'.map (D.hom j)) ≃* SL(2, GaloisField p f)) := by
      rw [← hJR']
      exact ⟨e'⟩
    have hne' : R.map (D.hom j) ≠ R'.map (D.hom j) := by
      rw [← hKR, ← hJR']
      exact fun h => hJ.2.1 h.symm
    have hcomm' : Commutes (R.map (D.hom j)) (R'.map (D.hom j)) := by
      rw [← hKR, ← hJR']
      exact hKJ
    have hz' : IsUniqueInvolution (R.map (D.hom j)) z := by
      rw [← hKR]
      exact hz
    have hAKJ' : A ≤ R.map (D.hom j) ⊔ R'.map (D.hom j) := by
      rw [← hKR, ← hJR']
      exact hAKJ
    have hfin : ∀ P : Prop → Prop, T5BaseAt p f (D.tag j) (D.rank j) (D.exp j) P →
        P (z ∈ R'.map (D.hom j)) → alphaOf (inducedImage (D.hom j).range A) = ⊥ := fun P hb hP =>
      hb hp2 hq (D.isFundTag j) (D.admissible j) (D.exp_eq j) G (D.hom j) (D.ker_le_center j) R hR
        R' hR' heK heJ hne' hcomm' z hz' hP A hA hAKJ' hzA hf
    by_cases hzJ' : z ∈ R'.map (D.hom j)
    · refine hfin id (htwin _ _ _ ?_) hzJ'
      by_cases hG2 : D.tag j = .G2
      · exact Or.inr (Or.inl hG2)
      by_cases hD4 : D.tag j = .trialityD4
      · exact Or.inr (Or.inr hD4)
      have hzK' : IsUniqueInvolution (R'.map (D.hom j)) z := by
        refine ⟨hzJ', hz.ne_one, hz.sq, fun w hw hw2 => ?_⟩
        by_cases hw1 : w = 1
        · exact Or.inl hw1
        · right
          have hwJ : w ∈ J := by
            rw [hJR']
            exact hw
          have hzJ'' : z ∈ J := by
            rw [hJR']
            exact hzJ'
          have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
          have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
          rw [eq_sl2Inv_of_orderOf_eq_two hodd e' hwJ hwo,
            eq_sl2Inv_of_orderOf_eq_two hodd e' hzJ'' hzo]
      refine Or.inl (twinShape_of_twin hp2 hq hΩ' D j hG2 hD4 hR hR' ?_ ?_ hz' hzK' hne').1
      · rw [← hKR]
        exact hK
      · rw [← hJR']
        exact hJ.1
    · exact hfin Not (hnt _ _ _) hzJ'
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
