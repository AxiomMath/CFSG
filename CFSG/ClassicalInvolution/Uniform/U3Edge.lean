module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD.Exotic

section Generic

variable {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {k : ℕ}

theorem exists_commuting_of_orthogonal_longest (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e)
    {γ δ : Fin (modelUniv t k p e Fact.out).D.rank → ℤ}
    (hγ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D γ)
    (hδ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D δ)
    (horth : form (modelUniv t k p e Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, Commutes R S := by
  obtain ⟨_, _, _, hext⟩ := ModelFacts.hasBruhatDatum t k p e Fact.out (ih8_isFundTag_mf hfund) hadm
  have hc := commutes_fund_of_orthogonal_of_longest (modelUniv t k p e Fact.out).D hext hγ.1 hδ.1
    hγ.2 horth
  exact ⟨_, ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩, _, ⟨1, δ, Or.inl hδ, (conjSub_one _).symm⟩, hc⟩

theorem exists_commuting_of_orth_nodes (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) {i j : Fin (modelUniv t k p e Fact.out).D.rank}
    (hi : ModelFacts.IsLongNode t k i.val) (hj : ModelFacts.IsLongNode t k j.val)
    (hji : (modelUniv t k p e Fact.out).D.cartan j i = 0) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, Commutes R S := by
  refine exists_commuting_of_orthogonal_longest hfund hadm (γ := Pi.single i 1)
    (δ := Pi.single j 1)
    (ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm i hi)
    (ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm j hj) ?_
  have := form_toRat_single_eq_zero (modelUniv t k p e Fact.out).D j (Pi.single i 1)
    (by rw [coroot_single, hji])
  exact this

theorem exists_commuting_of_double_bond (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) {i j : Fin (modelUniv t k p e Fact.out).D.rank}
    (hAij : (modelUniv t k p e Fact.out).D.cartan i j = -2)
    (hAji : (modelUniv t k p e Fact.out).D.cartan j i = -1)
    (hj : ModelFacts.IsLongNode t k j.val) :
    ∃ R ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, Commutes R S := by
  have hjl := ModelFacts.isLongestRoot_single t k p e Fact.out (ih8_isFundTag_mf hfund) hadm j hj
  have hA := (modelUniv t k p e Fact.out).D.isFiniteType
  set w := ((coxeterMatrix hA).toCoxeterSystem.simple i) with hw
  have hδ : ModelFacts.IsLongestRoot (modelUniv t k p e Fact.out).D
      (weylAction hA w (Pi.single j 1)) := ModelFacts.IsLongest.map_weylAction hjl w
  have hδeq : weylAction hA w (Pi.single j 1) = Pi.single j 1 + 2 • Pi.single i 1 := by
    rw [hw, weylAction_simple, reflection_apply_coroot, coroot_single, hAij]
    module
  refine exists_commuting_of_orthogonal_longest hfund hadm hjl hδ ?_
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

theorem cartan_congr {Y X : LieUniversal} (h : Y = X) (i j : Fin Y.D.rank)
    (i' j' : Fin X.D.rank) (hi : i.val = i'.val) (hj : j.val = j'.val) :
    Y.D.cartan i j = X.D.cartan i' j' := by
  subst h
  rw [Fin.ext hi, Fin.ext hj]

theorem exists_commuting_small_psl4 (hadm : StatedLieAdmissible .PSL 4 p e) :
    ∃ R ∈ ModelFund p .PSL 4 e, ∃ S ∈ ModelFund p .PSL 4 e, Commutes R S :=
  exists_commuting_of_orth_nodes trivial hadm (i := (0 : Fin 3)) (j := (2 : Fin 3))
    trivial trivial (by show (CartanMatrix.A 3 : Matrix (Fin 3) (Fin 3) ℤ) 2 0 = 0; decide)

theorem exists_commuting_small_d4 (hadm : StatedLieAdmissible .POmegaPlus 4 p e) :
    ∃ R ∈ ModelFund p .POmegaPlus 4 e, ∃ S ∈ ModelFund p .POmegaPlus 4 e, Commutes R S := by
  refine exists_commuting_of_orth_nodes trivial hadm (i := (0 : Fin 4)) (j := (2 : Fin 4))
    trivial trivial ?_
  show Spin.cartanD 4 2 0 = 0
  decide

theorem exists_commuting_small_sp4 (hadm : StatedLieAdmissible .PSp 2 p e) :
    ∃ R ∈ ModelFund p .PSp 2 e, ∃ S ∈ ModelFund p .PSp 2 e, Commutes R S :=
  exists_commuting_of_double_bond trivial hadm (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by show Symplectic.cartanC 2 0 1 = -2; decide) (by show Symplectic.cartanC 2 1 0 = -1; decide)
    (by show 1 + 1 = 2; rfl)

theorem exists_commuting_small_b3 (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    ∃ R ∈ ModelFund p .POmegaOdd 3 e, ∃ S ∈ ModelFund p .POmegaOdd 3 e, Commutes R S :=
  exists_commuting_of_double_bond trivial hadm (i := (2 : Fin 3)) (j := (1 : Fin 3))
    (by show Spin.cartanB 3 2 1 = -2; decide) (by show Spin.cartanB 3 1 2 = -1; decide)
    (by show 1 + 1 < 3; decide)

theorem exists_commuting_small_su4 (hadm : StatedLieAdmissible .PSU 4 p e) :
    ∃ R ∈ ModelFund p .PSU 4 e, ∃ S ∈ ModelFund p .PSU 4 e, Commutes R S := by
  have hf : 1 ≤ e := hadm.2.1
  have hM : modelUniv .PSU 4 p e Fact.out =
      ⟨_, Unitary.rootDatum (card_galoisField_two_mul p e hf) 4⟩ := by
    simp only [modelUniv, lieUniversal, hf, ↓reduceDIte]
  have hr : (modelUniv .PSU 4 p e Fact.out).D.rank = 2 := congrArg (fun Z => Z.D.rank) hM
  refine exists_commuting_of_double_bond trivial hadm (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) ?_ ?_ ?_
  · have h0 : 0 < 4 / 2 := by decide
    have h1 : 1 < 4 / 2 := by decide
    rw [cartan_congr hM _ _ (⟨0, h0⟩ : Fin (4 / 2)) ⟨1, h1⟩ rfl rfl]
    show Unitary.cartan 4 0 1 = -2
    decide
  · have h0 : 0 < 4 / 2 := by decide
    have h1 : 1 < 4 / 2 := by decide
    rw [cartan_congr hM _ _ (⟨1, h1⟩ : Fin (4 / 2)) ⟨0, h0⟩ rfl rfl]
    show Unitary.cartan 4 1 0 = -1
    decide
  · show Even 4 ∧ 1 + 1 = 4 / 2
    decide

theorem exists_commuting_small_dminus4 (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    ∃ R ∈ ModelFund p .POmegaMinus 4 e, ∃ S ∈ ModelFund p .POmegaMinus 4 e, Commutes R S :=
  exists_commuting_of_double_bond trivial hadm (i := (2 : Fin 3)) (j := (1 : Fin 3))
    (by show Spin.cartanB 3 2 1 = -2; decide) (by show Spin.cartanB 3 1 2 = -1; decide)
    (by show 1 + 2 < 4; decide)

end Cases

section Main

variable {p e : ℕ} [Fact p.Prime] {t : StatedLieTag} {k : ℕ}

theorem tag_casesU (hp2 : p ≠ 2) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    CommFamilyConnected (ModelFund p t k e) ∨ SmallModel t k := by
  by_cases hg : ConnGeneric t k
  · exact Or.inl (commFamilyConnected_of_generic hp2 hadm hg)
  by_cases hs : ConnShort t k
  · exact Or.inl (commFamilyConnected_of_short hp2 hadm hs)
  by_cases hx : ConnExotic t k
  · rcases hx with ⟨rfl, rfl⟩ | rfl
    · exact Or.inl (commFamilyConnected_psu_five hp2 hadm)
    · obtain rfl : k = 0 := hadm.2.2
      exact Or.inl (commFamilyConnected_twistedE6 hp2 hadm)
  exact Or.inr (small_model_cases hfund hadm hG2 hD4 hg hs hx)

theorem exists_commuting_fund (hp2 : p ≠ 2) (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hA1 : ¬ (t = .PSL ∧ k = 2)) (h3 : ¬ ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)))
    {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ ModelFund p t k e) :
    ∃ R' ∈ ModelFund p t k e, ∃ S ∈ ModelFund p t k e, Commutes R' S := by
  rcases tag_casesU hp2 hfund hadm hG2 hD4 with hconn | hsmall
  · obtain ⟨S, hS, hSR, -⟩ := Exotic.exists_fund_not_commuting hfund hadm hA1 hR
    rcases (hconn R hR S hS).cases_head with h | ⟨c, ⟨-, hc, hRc⟩, -⟩
    · exact absurd h.symm hSR
    · exact ⟨R, hR, c, hc, hRc⟩
  · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hk2 : 2 ≤ k := hadm.2.2.1
      have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl | rfl
      · exact (hA1 ⟨rfl, rfl⟩).elim
      · exact (h3 (Or.inl ⟨rfl, rfl⟩)).elim
      · exact exists_commuting_small_psl4 hadm
    · have hk3 : 3 ≤ k := hadm.2.2.1
      have : k = 3 ∨ k = 4 := by omega
      rcases this with rfl | rfl
      · exact (h3 (Or.inr ⟨rfl, rfl⟩)).elim
      · exact exists_commuting_small_su4 hadm
    · exact exists_commuting_small_sp4 hadm
    · exact exists_commuting_small_b3 hadm
    · exact exists_commuting_small_d4 hadm
    · exact exists_commuting_small_dminus4 hadm

end Main

end CFSG.ClassicalInvolution.Uniform
