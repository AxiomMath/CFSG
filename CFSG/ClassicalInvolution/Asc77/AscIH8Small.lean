module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.RootSystem CFSG.LieType.Universal


section Generic

variable {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {k : ℕ}

theorem ih8_exists_commuting_of_orthogonal_longest (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t k p e)
    {γ δ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ}
    (hγ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ)
    (hδ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D δ)
    (horth : form (modelUniv t k p e Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S := by
  obtain ⟨_, _, _, hext⟩ := ModelFacts.hasBruhatDatum t k p e Fact.out (ih8_isFundTag_mf hfund) hadm
  have hc := commutes_fund_of_orthogonal_of_longest (modelUniv t k p e Fact.out).D hext hγ.1 hδ.1
    hγ.2 horth
  have hR : ((modelUniv t k p e Fact.out).D.rootGroup γ ⊔
      (modelUniv t k p e Fact.out).D.rootGroup (-γ)) ∈ ModelFund p t k e :=
    ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩
  have hS : ((modelUniv t k p e Fact.out).D.rootGroup δ ⊔
      (modelUniv t k p e Fact.out).D.rootGroup (-δ)) ∈ ModelFund p t k e :=
    ⟨1, δ, Or.inl hδ, (conjSub_one _).symm⟩
  refine ⟨_, hR, _, hS, fun h => ?_, hc⟩
  have hR' := hR
  rw [h] at hR'
  exact not_commutes_self_modelFund hp2 hfund hq hadm hR' (h ▸ hc)

theorem ih8_exists_commuting_of_orth_nodes (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t k p e)
    {i j : Fin (modelUniv t k p e Fact.out).D.rank} (hi : ModelFacts.IsLongNode t k i.val)
    (hj : ModelFacts.IsLongNode t k j.val) (hji : (modelUniv t k p e Fact.out).D.cartan j i = 0) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S := by
  refine ih8_exists_commuting_of_orthogonal_longest hp2 hq hfund hadm (γ := Pi.single i 1)
    (δ := Pi.single j 1)
    (ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm i hi)
    (ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm j hj) ?_
  have := form_toRat_single_eq_zero (modelUniv t k p e Fact.out).D j (Pi.single i 1)
    (by rw [coroot_single, hji])
  exact this

theorem ih8_exists_commuting_of_double_bond (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t k p e)
    {i j : Fin (modelUniv t k p e Fact.out).D.rank}
    (hAij : (modelUniv t k p e Fact.out).D.cartan i j = -2)
    (hAji : (modelUniv t k p e Fact.out).D.cartan j i = -1)
    (hj : ModelFacts.IsLongNode t k j.val) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, R ≠ S ∧ Commutes R S := by
  have hjl := ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm j hj
  have hA := (modelUniv t k p e Fact.out).D.isFiniteType
  set w := ((coxeterMatrix hA).toCoxeterSystem.simple i) with hw
  have hδ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D
      (weylAction hA w (Pi.single j 1)) := ModelFacts.IsLongest.map_weylAction hjl w
  have hδeq : weylAction hA w (Pi.single j 1) = Pi.single j 1 + 2 • Pi.single i 1 := by
    rw [hw, weylAction_simple, reflection_apply_coroot, coroot_single, hAij]
    module
  refine ih8_exists_commuting_of_orthogonal_longest hp2 hq hfund hadm hjl hδ ?_
  have hc0 : coroot (modelUniv t k p e Fact.out).D.cartan j
      (weylAction hA w (Pi.single j 1)) = 0 := by
    rw [hδeq, map_add, map_nsmul, coroot_single, coroot_single, hAji, hA.apply_self]
    norm_num
  have := form_toRat_single_eq_zero (modelUniv t k p e Fact.out).D j _ hc0
  rw [form_comm]
  exact this

end Generic

section Cases

variable {p e : ℕ} [Fact p.Prime]

theorem ih8_smallEdge_psl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSL 4 p e) :
    ∃ R ∈ ModelFund p .PSL 4 e, ∃ S ∈ ModelFund p .PSL 4 e, R ≠ S ∧ Commutes R S :=
  ih8_exists_commuting_of_orth_nodes hp2 hq trivial hadm (i := (0 : Fin 3)) (j := (2 : Fin 3))
    trivial trivial (by show (CartanMatrix.A 3 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0; decide)

theorem ih8_smallEdge_d4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p e) :
    ∃ R ∈ ModelFund p .POmegaPlus 4 e, ∃ S ∈ ModelFund p .POmegaPlus 4 e, R ≠ S ∧
      Commutes R S := by
  refine ih8_exists_commuting_of_orth_nodes hp2 hq trivial hadm (i := (0 : Fin 4))
    (j := (2 : Fin 4)) trivial trivial ?_
  show Spin.cartanD 4 2 0 = 0
  decide

theorem ih8_smallEdge_sp4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSp 2 p e) :
    ∃ R ∈ ModelFund p .PSp 2 e, ∃ S ∈ ModelFund p .PSp 2 e, R ≠ S ∧ Commutes R S :=
  ih8_exists_commuting_of_double_bond hp2 hq trivial hadm (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by show Symplectic.cartanC 2 0 1 = -2; decide) (by show Symplectic.cartanC 2 1 0 = -1; decide)
    (by show 1 + 1 = 2; rfl)

theorem ih8_smallEdge_b3 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    ∃ R ∈ ModelFund p .POmegaOdd 3 e, ∃ S ∈ ModelFund p .POmegaOdd 3 e, R ≠ S ∧
      Commutes R S :=
  ih8_exists_commuting_of_double_bond hp2 hq trivial hadm (i := (2 : Fin 3)) (j := (1 : Fin 3))
    (by show Spin.cartanB 3 2 1 = -2; decide) (by show Spin.cartanB 3 1 2 = -1; decide)
    (by show 1 + 1 < 3; decide)

theorem ih8_cartan_congr {Y X : LieUniversal} (h : Y = X) (i j : Fin Y.D.rank)
    (i' j' : Fin X.D.rank) (hi : i.val = i'.val) (hj : j.val = j'.val) :
    Y.D.cartan i j = X.D.cartan i' j' := by
  subst h
  rw [Fin.ext hi, Fin.ext hj]

theorem ih8_smallEdge_su4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (hadm : StatedLieAdmissible .PSU 4 p e) :
    ∃ R ∈ ModelFund p .PSU 4 e, ∃ S ∈ ModelFund p .PSU 4 e, R ≠ S ∧ Commutes R S := by
  have hf : 1 ≤ e := hadm.2.1
  have hM : modelUniv .PSU 4 p e Fact.out =
      ⟨_, Unitary.rootDatum (card_galoisField_two_mul p e hf) 4⟩ := by
    simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]
  have hr : (modelUniv .PSU 4 p e Fact.out).D.rank = 2 := congrArg (fun Z => Z.D.rank) hM
  refine ih8_exists_commuting_of_double_bond hp2 hq trivial hadm (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) ?_ ?_ ?_
  · have h0 : 0 < 4 / 2 := by decide
    have h1 : 1 < 4 / 2 := by decide
    rw [ih8_cartan_congr hM _ _ (⟨0, h0⟩ : Fin (4 / 2)) ⟨1, h1⟩ rfl rfl]
    show Unitary.cartan 4 0 1 = -2
    decide
  · have h0 : 0 < 4 / 2 := by decide
    have h1 : 1 < 4 / 2 := by decide
    rw [ih8_cartan_congr hM _ _ (⟨1, h1⟩ : Fin (4 / 2)) ⟨0, h0⟩ rfl rfl]
    show Unitary.cartan 4 1 0 = -1
    decide
  · show Even 4 ∧ 1 + 1 = 4 / 2
    decide

theorem ih8_smallEdge_dminus4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    ∃ R ∈ ModelFund p .POmegaMinus 4 e, ∃ S ∈ ModelFund p .POmegaMinus 4 e, R ≠ S ∧
      Commutes R S :=
  ih8_exists_commuting_of_double_bond hp2 hq trivial hadm (i := (2 : Fin 3)) (j := (1 : Fin 3))
    (by show Spin.cartanB 3 2 1 = -2; decide) (by show Spin.cartanB 3 1 2 = -1; decide)
    (by show 1 + 2 < 4; decide)

theorem ih8SmallEdge (p : ℕ) [Fact p.Prime] : Ih8SmallEdge p := by
  intro t k e hadm hp2 hq h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ih8_smallEdge_psl4 hp2 hq hadm
  · exact ih8_smallEdge_su4 hp2 hq hadm
  · exact ih8_smallEdge_sp4 hp2 hq hadm
  · exact ih8_smallEdge_b3 hp2 hq hadm
  · exact ih8_smallEdge_d4 hp2 hq hadm
  · exact ih8_smallEdge_dminus4 hp2 hq hadm

end Cases

end CFSG.ClassicalInvolution.Asc77
