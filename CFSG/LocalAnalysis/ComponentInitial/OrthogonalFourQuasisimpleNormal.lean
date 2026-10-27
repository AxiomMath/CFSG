module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthO2Ns
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.Open CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
  CFSG.ClassicalGroups.Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem card_centerQuotient_of_splitFour (hodd : Odd (Nat.card K)) (hK3 : Nat.card K ≠ 3)
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h4 : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ s ∈ S, R s = 0)
    {M : Subgroup ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))}
    (hMq : CFSG.IsQuasisimple ↥M) (hMn : M.Normal) :
    Nat.card (↥M ⧸ Subgroup.center ↥M) * 2 = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hK2' : Nat.card K ≠ 2 := by
    intro h2
    rw [h2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK2 : ringChar K ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  obtain ⟨ψ, e, hψ, he, hsup, hqL, hqR, hnL, hnR, hcomm, hperf, hsq⟩ :=
    orthogonal_split_four_derived hK2' hK3 R hR h4 hS
  obtain ⟨eL⟩ := CFSG.ComponentClassification.Burgoyne.C.nonempty_equiv_determinantLeftFactor
    (K := K)
  obtain ⟨eR⟩ := CFSG.ComponentClassification.Burgoyne.C.nonempty_equiv_determinantRightFactor
    (K := K)
  set M' : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    M.map (Subgroup.subtype (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))) with hM'
  have hM'move : ↥M ≃* ↥M' :=
    Subgroup.equivMapOfInjective M _ Subtype.val_injective
  have hM'sub : M'.subgroupOf
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) = M := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hx)
      rwa [Subtype.ext hyx] at hy
    · intro hx
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hx)
  have hM'le : M' ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hM']
    exact Subgroup.map_subtype_le M
  have hM'n : (M'.subgroupOf
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).Normal := by
    rw [hM'sub]
    exact hMn
  have hM'q : CFSG.IsQuasisimple ↥M' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv hM'move hMq
  set Lf := (determinantLeftFactor K).map e.symm.toMonoidHom with hLf
  set Rf := (determinantRightFactor K).map e.symm.toMonoidHom with hRf
  have hLfC : Lf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hLf, hsup]
    exact le_sup_left
  have hRfC : Rf ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
    rw [hRf, hsup]
    exact le_sup_right
  have hF : ∀ i : Fin 2, IsComponentOf (![Lf, Rf] i)
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    intro i
    fin_cases i
    · exact ⟨hLfC, IsSubnormal.step hLfC hnL (IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hqL⟩
    · exact ⟨hRfC, IsSubnormal.step hRfC hnR (IsSubnormal.refl _),
        CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hqR⟩
  have hperf' : ∀ P : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup R),
      P ≤ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R) → commutator ↥P = ⊤ →
      P ≤ ⨆ i, ![Lf, Rf] i := by
    intro P hP _
    refine hP.trans (hsup.le.trans (sup_le ?_ ?_))
    · exact le_iSup (fun i => ![Lf, Rf] i) 0
    · exact le_iSup (fun i => ![Lf, Rf] i) 1
  have hMc : IsComponentOf M' (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
    ⟨hM'le, IsSubnormal.step hM'le hM'n (IsSubnormal.refl _),
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.open_isQuasisimple hM'q⟩
  obtain ⟨i, hi⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors _ hF hperf' hMc
  have hcardM : Nat.card (↥M ⧸ Subgroup.center ↥M) =
      Nat.card (↥M' ⧸ Subgroup.center ↥M') :=
    Nat.card_congr (QuotientGroup.congr _ _ hM'move (Subgroup.map_center_eq hM'move)).toEquiv
  rw [hcardM]
  fin_cases i
  · rw [hi]
    have h1 : ↥((determinantLeftFactor K).map e.symm.toMonoidHom) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K :=
      ((Subgroup.equivMapOfInjective (determinantLeftFactor K) e.symm.toMonoidHom
        e.symm.injective).symm).trans eL
    rw [Nat.mul_comm]
    exact CFSG.ComponentClassification.ExcSelector.two_mul_card_centralQuotient_of_equiv_sl2
      hK2 h1
  · rw [hi]
    have h1 : ↥((determinantRightFactor K).map e.symm.toMonoidHom) ≃*
        Matrix.SpecialLinearGroup (Fin 2) K :=
      ((Subgroup.equivMapOfInjective (determinantRightFactor K) e.symm.toMonoidHom
        e.symm.injective).symm).trans eR
    rw [Nat.mul_comm]
    exact CFSG.ComponentClassification.ExcSelector.two_mul_card_centralQuotient_of_equiv_sl2
      hK2 h1

theorem card_centerQuotient_of_nonsplitFour (hodd : Odd (Nat.card K))
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (h4 : Module.finrank K W = 4)
    (hno : ¬ ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ s ∈ S, R s = 0)
    {M : Subgroup ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))}
    (hMq : CFSG.IsQuasisimple ↥M) (hMn : M.Normal) :
    Nat.card (↥M ⧸ Subgroup.center ↥M) * 2 =
      Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1) := by
  obtain ⟨δ, hns, _, _, e, _, _, hcomm, hq, -⟩ :=
    orthogonal_nonsplit_four_derived hodd R hR h4 hno
  haveI : Fact (¬ IsSquare (δ : K)) := ⟨hns⟩
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hMtop : M = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hMn with h | h
    · exact h
    · exfalso
      have hcommM : ∀ a b : ↥M, a * b = b * a := by
        intro a b
        exact Subtype.ext ((Subgroup.mem_center_iff.1 (h a.2) b.1).symm)
      haveI : Group.IsSolvable ↥M := isSolvable_of_comm hcommM
      haveI : Group.IsPerfect ↥M := hMq.1
      haveI : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hMq
      exact (Group.IsPerfect.not_isSolvable ↥M) inferInstance
  have hMeq : ↥M ≃* ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    rw [hMtop]
    exact Subgroup.topEquiv
  haveI hsimple : IsSimpleGroup ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    haveI : IsSimpleGroup ↥(specialImage (δ : K) h2) :=
      CFSG.ComponentClassification.GSThmB.X10Orth.isSimpleGroup_specialImage (δ := (δ : K)) h2
    have h1 : ↥(specialImage (δ : K) h2) ≃*
        ↥((specialImage (δ : K) h2).map e.symm.toMonoidHom) :=
      Subgroup.equivMapOfInjective _ e.symm.toMonoidHom e.symm.injective
    rw [hcomm]
    exact h1.symm.isSimpleGroup
  have hZbot : Subgroup.center ↥(commutator
      ↥(TauCeti.QuadraticMap.orthogonalGroup R)) = ⊥ := by
    haveI : Group.IsPerfect ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := hq.1
    refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).2
    simpa only [isMulCommutative_iff, not_forall] using
      Group.IsPerfect.not_isMulCommutative ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))
  have hcardΩ : Nat.card ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) * 2 =
      Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1) := by
    have hc := CFSG.ComponentClassification.GSThmB.X10Orth.card_specialImage
      (δ := (δ : K)) h2
    rw [CFSG.ComponentClassification.GSThmB.X10Orth.card_extension (δ := (δ : K))] at hc
    rw [hcomm, Subgroup.card_map_of_injective (K := specialImage (δ : K) h2)
      (f := e.symm.toMonoidHom) e.symm.injective]
    exact hc
  have hcard : Nat.card (↥M ⧸ Subgroup.center ↥M) =
      Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ⧸
        Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))) :=
    Nat.card_congr (QuotientGroup.congr _ _ hMeq (Subgroup.map_center_eq hMeq)).toEquiv
  rw [hcard]
  have hquot : Nat.card (↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ⧸
      Subgroup.center ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))) =
      Nat.card ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) := by
    rw [hZbot]
    exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rw [hquot, hcardΩ]

theorem false_of_splitFour_card_three (hR : (QuadraticMap.polarBilin R).Nondegenerate)
    (h4 : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ s ∈ S, R s = 0)
    (h3 : Nat.card K = 3)
    {M : Subgroup ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))}
    (hMq : CFSG.IsQuasisimple ↥M) :
    False := by
  have hdiv := (orthogonal_low_dimensional_fixed_derived_component_coverage R hR
    (Or.inr (Or.inr ⟨h4, hS⟩))).1 (Or.inr ⟨⟨h4, hS⟩, Or.inr h3⟩)
  haveI : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
    CFSG.ComponentClassification.Burgoyne.C.isSolvable_of_prime_dvd_two_three hdiv.1
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subtype (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R))).comp
        M.subtype)
      ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _))
  haveI : Group.IsPerfect ↥M := hMq.1
  haveI : Nontrivial ↥M := CFSG.LocalCores.isQuasisimple_nontrivial hMq
  exact (Group.IsPerfect.not_isSolvable ↥M) inferInstance

end CFSG.LocalAnalysis.ComponentInitial

end
