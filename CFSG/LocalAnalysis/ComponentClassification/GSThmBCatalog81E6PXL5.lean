module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXLI
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXLG
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXT

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211X

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedLayer P211

variable {Q : ℕ → Prop}

theorem pow_mod_four_of_even {p f : ℕ} (hp : Odd p) (hf : Even f) : p ^ f % 4 = 1 := by
  obtain ⟨g, rfl⟩ := hf
  obtain ⟨k, rfl⟩ := hp
  rw [← two_mul, pow_mul, show (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 by ring]
  induction g with
  | zero => simp
  | succ g ih => rw [pow_succ, Nat.mul_mod, ih]; omega

theorem compOrd_psl5 {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL 5 p f) (hm : Blueprint.LieModel J .PSL 5 p f)
    (hq4 : p ^ f % 4 = 3) (hQ1 : Q (Open.ordA 1 (p ^ f))) (hQ2 : Q (Open.ordA 2 (p ^ f)))
    (hQ3 : Q (Open.ordA 3 (p ^ f))) (hQS : Q (Open.ordBC 2 (p ^ f))) {α : MulAut J}
    (hα : orderOf α = 2) : CompOrd Q (fixedSubgroup α) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hm
  have hf : 1 ≤ f := hadm.2.1
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact hpodd.pow
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hβ2 : MulAut.congr e α ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have key : ∀ γ : MulAut (ProjectiveSpecialLinearGroup (Fin 5) K), MulAut.congr e α = γ →
      CompOrd Q (fixedSubgroup γ) → CompOrd Q (fixedSubgroup α) := by
    intro γ hγ h
    exact CompOrd.of_mulEquiv ((CatLeafProof.fixedSubgroupCongrEquiv e α).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))) h
  have hQr : ∀ r, 2 ≤ r → r < 5 → Q (Open.ordA (r - 1) (Nat.card K)) := by
    intro r hr2 hr5
    rw [hK]
    interval_cases r
    · exact hQ1
    · exact hQ2
    · exact hQ3
  have hsemi : ∀ (A : GL (Fin 5) K) (σ : K ≃+* K),
      MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction 5 K A σ →
      CompOrd Q (fixedSubgroup α) := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact key _ hAσ (compOrd_inner_psl hKodd (by norm_num) (by decide) hQr A (hAσ ▸ hβ))
    · exfalso
      obtain ⟨heven, -⟩ := CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy 5 K
        p f hp hpodd hf hK (by norm_num) (Or.inl (by norm_num)) A σ hσ (hAσ ▸ hβ2)
      rw [pow_mod_four_of_even hpodd heven] at hq4
      exact absurd hq4 (by norm_num)
  obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := K) (n := 5) (by norm_num)
  obtain ⟨A, σ, ε, hε, hAσε⟩ :=
    hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv 5 K).symm (MulAut.congr e α))
  have hβ' : MulAut.congr e α = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv 5 K)
      (LocalAnalysis.ComponentInitial.LinearFlag.conjAut 5 K A *
        LocalAnalysis.ComponentInitial.LinearFlag.fieldAut 5 K σ *
          LocalAnalysis.ComponentInitial.LinearFlag.dualAut 5 K ^ ε) := by
    rw [← hAσε]
    ext x
    simp
  interval_cases ε
  · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
    exact hsemi A σ hβ'
  · rw [pow_one] at hβ'
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
      exact key _ hβ' (compOrd_graph_psl hp hp2 hK A (hβ' ▸ hβ) hQS)
    · exfalso
      rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
      have : Fact p.Prime := ⟨hp⟩
      have hne1 : CatalogueBGraphField.graphFieldAction 5 K A σ ≠ 1 := fun h => by
        rw [hβ', h, orderOf_one] at hβ
        exact absurd hβ (by decide)
      obtain ⟨heven, -⟩ :=
        CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native 5 K p f
          hpodd hf hK (by norm_num) A σ hσ hne1 (hβ' ▸ hβ2)
      rw [pow_mod_four_of_even hpodd heven] at hq4
      exact absurd hq4 (by norm_num)

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem exists_equiv_projectiveSL5 {G : Type} [Group G] {p f : ℕ}
    (h : Blueprint.LieModel G .PSL 5 p f) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nonempty (G ≃* projectiveSL 5 k) := by
  obtain ⟨-, k, _, _, -, ⟨e⟩⟩ := GH74.statedClassicalModel_of_lieModel (by norm_num) h
  exact ⟨k, inferInstance, inferInstance, ⟨e.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 5 k).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 5 k).symm))⟩⟩

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem derivedSeries_three_le_projectiveSL5 {k : Type*} [Field k] [Finite k] :
    derivedSeries (MulAut (projectiveSL 5 k)) 3 ≤
      (MulAut.conj : projectiveSL 5 k →* MulAut (projectiveSL 5 k)).range := by
  have hR := (automorphism_generation (K := k) (n := 5) (by norm_num)).1
  have h := (standard_outer_quotients (K := k) (n := 5)).2.2.2.2.2.2.2.2.2
  rw [hR] at h
  simpa only [derivedSeries_succ, derivedSeries_zero] using h

theorem p211For_L5 :
    P211For fun G _ => ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
      Blueprint.LieModel G .PSL 5 p f := by
  intro X _ _ hsimp hC ⟨p', f', hp', hf', hq4, hLie⟩ p f hp hp2 hf a J D _ _ _ _ hJt _ hDJ
    hDsyl hbound b K hb hb1 hKC hK hKt
  exfalso
  have hp2' : p' ≠ 2 := by
    rintro rfl
    obtain ⟨g, rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod] at hq4
    have : 2 ^ g % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : 2 ^ g % 4 <;> omega
  obtain ⟨k, _, _, ⟨eL⟩⟩ := exists_equiv_projectiveSL5 hLie
  have hKF : K ≤ generalizedFitting X := le_fstar_of_perfect hC eL
    derivedSeries_three_le_projectiveSL5 (commutator_eq_of_isPComp hKC hK)
  obtain ⟨-, hKv, hFv⟩ := p211_two_adic hp hp2 hf hJt hDJ hDsyl hbound hKt
  have hq'odd : Odd (p' ^ f') := ⟨p' ^ f' / 2, by omega⟩
  have hq'3 : 3 ≤ p' ^ f' := by omega
  have hF : padicValNat 2 (Nat.card (generalizedFitting X)) =
      2 * padicValNat 2 ((p' ^ f') ^ 2 - 1) + 3 := by
    rw [GH74.card_of_lieModel_PSL (by norm_num) hLie]
    exact v2_ordA_four hq4
  have hstated := GH74.statedClassicalModel_of_lieModel (by norm_num) hLie
  have hQS := CatLeaf.fixedTwoComponentsQuasisimple_psl hp2' (by norm_num : 3 ≤ 5) hstated
  obtain ⟨β, hβ, L, hL, hLv⟩ := exists_fixed_component hC hQS hb hb1 hKC hK hKF
    (center_socle_eq_bot hp hp2 hf hKt)
  have h1 := v2_ordA_one hq'odd hq'3
  have h2 := v2_ordA_two hq4
  have h3 := v2_ordA_three hq4
  have h4 := v2_ordBC hq'odd hq'3
  have hcls := compOrd_psl5 (Q := fun v => ∀ m', padicValNat 2 ((p' ^ f') ^ 2 - 1) + 1 ≤ m' →
      padicValNat 2 v ≠ 2 * m') hp' hp2' hstated.1 hLie hq4
    (fun m' hm' => by omega) (fun m' hm' => by omega) (fun m' hm' => by omega)
    (fun m' hm' => by omega) hβ
  exact hcls L hL (padicValNat 2 ((p ^ f) ^ 2 - 1)) (by omega) (by rw [hLv, hKv])

end P211X

end CFSG.ComponentClassification.GSThmB
