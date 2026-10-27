module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem cl24_orderOf_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {σ : MulAut S}
    {P : Subgroup S} (hP : HypA2.ProperFixedComp σ P) : orderOf σ = 2 := by
  have hpow : σ ^ 2 = 1 := by
    ext x
    simpa [pow_two] using hP.1 x
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hFtop : fixedSubgroup (1 : MulAut S) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rfl
    haveI : IsSimpleGroup (fixedSubgroup (1 : MulAut S)) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    have hcomp : IsComponent (P.subgroupOf (fixedSubgroup (1 : MulAut S))) := hP.2.2.2
    have htop : P.subgroupOf (fixedSubgroup (1 : MulAut S)) = ⊤ := by
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hcomp.2 with h' | h'
      · exfalso
        have hnt : Nontrivial (P.subgroupOf (fixedSubgroup (1 : MulAut S))) :=
          CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
        rw [h'] at hnt
        exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt
      · exact h'
    apply hP.2.2.1
    rw [eq_top_iff]
    intro x _
    have hmem : (⟨x, hFtop ▸ mem_top x⟩ : fixedSubgroup (1 : MulAut S)) ∈
        P.subgroupOf (fixedSubgroup (1 : MulAut S)) := htop ▸ mem_top _
    exact hmem
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hpow hσ1

theorem cl24_card_psl_two_two_three {G : Type} [Group G] (h : LieModel G .PSL 2 2 3) :
    Nat.card G = 504 := by
  rw [GH74.card_of_lieModel_PSL (G := G) (n := 2) (p := 2) (f := 3) (by norm_num) h]
  decide

theorem cl24_not_lieModel_three_of_card_dvd (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : Nat.card X ∣ 504) {τ : StatedLieTag} {n d : ℕ} (h : LieModel X τ n 3 d) : False := by
  have hadm := h.admissible
  have h27 : ¬ 3 ^ (2 + 1) ∣ Nat.card X := fun hd => by
    have := hd.trans hX
    norm_num at this
  obtain ⟨hb, hmul⟩ := CatLeaf.lie_bounds hO hadm h h27
  have hd1 : 1 ≤ d := hadm.2.1
  rcases CatLeaf.lie_casework hadm (by omega) with
    ⟨hτ, hn2, hn5, -, hd10⟩ | ⟨hτ, hn2, hn3, -, hd10⟩ | ⟨hτ, hn0, -, hd5⟩
  · rcases hτ with rfl | rfl
    · simp only [lieSylowExponent] at hb
      have hn : n = 2 := by
        interval_cases n <;> omega
      subst hn
      have hd : d ≤ 2 := by omega
      interval_cases d
      · exact absurd (by norm_num) hadm.2.2.2.2
      · simp only [lieOrderNumerator, lieOrderDivisor] at hmul
        norm_num [Finset.Icc_self] at hmul
        have : Nat.card X = 360 := by omega
        rw [this] at hX
        norm_num at hX
    · simp only [lieSylowExponent] at hb
      have hn3 : 3 ≤ n := hadm.2.2.1
      interval_cases n <;> omega
  · rcases hτ with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      · interval_cases n <;> omega
  · cases τ <;> simp only [lieSylowExponent] at hb <;> first
      | (exfalso; simp at hτ; done)
      | omega
      | exact absurd hadm.2.2.2.1 (by norm_num)

theorem a2l_cl2_of_tracked (hO : LieOrderFormulasInput)
    (hS : ∀ (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ),
      LieModel G t n p f → IsSimpleGroup G)
    (hT : ∀ τ, Cl24TrackedFamily τ) (hU : Cl24FieldUnique3) : HypA2.ClosureFieldExp := by
  intro S _ _ σ P hP τ n c hτ τ' n' d hτ'
  haveI : IsSimpleGroup S := hS S τ n 3 c hτ
  have hσ2 : orderOf σ = 2 := cl24_orderOf_two hP
  let e := Subgroup.subgroupOfEquivOfLe hP.2.1
  rcases hT τ S n c hτ.admissible hτ σ hσ2 (P.subgroupOf (fixedSubgroup σ)) hP.2.2.2 with
    ⟨τ'', n'', f', hrel, -, hLie⟩ | ⟨-, -, hK⟩
  · have hLie' : LieModel (P ⧸ center P) τ'' n'' 3 f' :=
      LieModel.of_mulEquiv (Sol78.centerQuotCongr e) hLie
    have hdf : f' = d := hU _ τ'' τ' n'' n' f' d hLie' hτ'
    subst hdf
    exact hrel
  · exfalso
    have hK504 := cl24_card_psl_two_two_three hK
    have hτ'K : LieModel (P.subgroupOf (fixedSubgroup σ) ⧸
        center (P.subgroupOf (fixedSubgroup σ))) τ' n' 3 d :=
      LieModel.of_mulEquiv (Sol78.centerQuotCongr e).symm hτ'
    exact cl24_not_lieModel_three_of_card_dvd hO
      (hK504 ▸ Subgroup.card_quotient_dvd_card _) hτ'K

end CFSG.OddStandard.SmallF3.HypA2Leaves
