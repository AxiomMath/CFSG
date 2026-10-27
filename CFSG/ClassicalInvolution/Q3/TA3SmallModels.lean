module

public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete
public import CFSG.GH74.KGroups.M11
public import CFSG.GH74.KGroups.U33
public import CFSG.GH74.KGroups.L33
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.TL3S8Mu
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.GH74.KGroups (AutModel)

@[expose] def SmallL3Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 3 ∧
    Assembly.LowTwoRank.StatedClassicalModel F .PSL 3 p f

@[expose] def SmallU3Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 3 ∧
    Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 p f

@[expose] def SmallPSp4Ne3 (F : Type) [Group F] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f ≠ 3 ∧ LieModel F .PSp 2 p f

theorem eq_three_of_pow_eq_three {p f : ℕ} (h : p ^ f = 3) : p = 3 ∧ f = 1 :=
  (Nat.Prime.pow_eq_iff Nat.prime_three).mp h

theorem l33_QA_closure : GH74.KGroups.L33.QA.originalSubgroup =
    Subgroup.closure {GH74.KGroups.L33.PA, GH74.KGroups.L33.PB, GH74.KGroups.L33.sg0} := by
  rw [GH74.KGroups.L33.QA, Sporadic.Schreier.certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem u33_QA_closure : GH74.KGroups.U33.QA.originalSubgroup =
    Subgroup.closure {GH74.KGroups.U33.pa, GH74.KGroups.U33.pb, GH74.KGroups.U33.sg0} := by
  rw [GH74.KGroups.U33.QA, Sporadic.Schreier.certificate_originalSubgroup]
  congr 1
  ext g
  simp


theorem smallSimpleLeaf_of_models {G : Type} [Group G] {P A : Subgroup G}
    {Pr : ∀ (F : Type) [Group F], Prop}
    (hmodel : ∀ (F : Type) [Group F], Pr F → ∃ M : AutModel F G, M.P = P ∧ M.A = A)
    (hPA : P ≤ A) (hC : ConcreteLeaf G P A) : SmallSimpleLeaf Pr := by
  intro Y _ _ _ hA hnab hG hF R S t hd hc hE2
  obtain ⟨M, rfl, rfl⟩ := hmodel _ hF
  exact smallSimpleLeaf_of_concrete M hPA hC Y hA hnab hG ⟨MulEquiv.refl _⟩ R S t hd hc hE2

theorem SmallSimpleLeaf.of_split {P Q₃ Q : ∀ (F : Type) [Group F], Prop}
    (hsplit : ∀ (F : Type) [Group F], P F → Q₃ F ∨ Q F) (h₃ : SmallSimpleLeaf Q₃)
    (h : SmallSimpleLeaf Q) : SmallSimpleLeaf P :=
  SmallSimpleLeaf.mono hsplit (SmallSimpleLeaf.of_or h₃ h)

theorem SmallSimpleLeaf.l3_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSL 3 3 1)
    (h : SmallSimpleLeaf SmallL3Ne3) : SmallSimpleLeaf SmallL3 := by
  refine SmallSimpleLeaf.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem SmallSimpleLeaf.u3_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSU 3 3 1)
    (h : SmallSimpleLeaf SmallU3Ne3) : SmallSimpleLeaf SmallU3 := by
  refine SmallSimpleLeaf.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl (Or.inl ⟨by decide, hm⟩)
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem SmallSimpleLeaf.psp4_of_split (h₃ : SmallSimpleLeaf fun F _ => LieModel F .PSp 2 3 1)
    (h : SmallSimpleLeaf SmallPSp4Ne3) : SmallSimpleLeaf SmallPSp4 := by
  refine SmallSimpleLeaf.of_split (fun F _ hF => ?_) h₃ h
  obtain ⟨p, f, hp, hp2, hf, hm⟩ := hF
  by_cases h3 : p ^ f = 3
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_eq_three h3
    exact Or.inl hm
  · exact Or.inr ⟨p, f, hp, hp2, hf, h3, hm⟩

theorem smallSimpleLeaf_m11
    (hC : ConcreteLeaf (Equiv.Perm (Fin 11)) GH74.KGroups.M11.Q.originalSubgroup
      GH74.KGroups.M11.Q.originalSubgroup) : SmallSimpleLeaf SmallM11 :=
  smallSimpleLeaf_of_models (fun _ _ h => GH74.KGroups.M11.autModel h) le_rfl hC

theorem smallSimpleLeaf_l33
    (hC : ConcreteLeaf (Equiv.Perm (Fin 26)) GH74.KGroups.L33.QP.originalSubgroup
      GH74.KGroups.L33.QA.originalSubgroup) :
    SmallSimpleLeaf fun F _ => LieModel F .PSL 3 3 1 := by
  refine smallSimpleLeaf_of_models (fun _ _ h => ?_) ?_ hC
  · obtain ⟨e⟩ := GH74.KGroups.L33.equiv_of_lieModel h
    exact GH74.KGroups.L33.autModel e
  · rw [GH74.KGroups.L33.QP_closure, l33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

theorem smallSimpleLeaf_u33
    (hC : ConcreteLeaf (Equiv.Perm (Fin 28)) GH74.KGroups.U33.QP.originalSubgroup
      GH74.KGroups.U33.QA.originalSubgroup) :
    SmallSimpleLeaf fun F _ => LieModel F .PSU 3 3 1 := by
  refine smallSimpleLeaf_of_models (fun _ _ h => ?_) ?_ hC
  · obtain ⟨e⟩ := GH74.KGroups.U33.equiv_of_lieModel h
    exact GH74.KGroups.U33.autModel e
  · rw [GH74.KGroups.U33.QP_closure, u33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

theorem smallSimpleLeaf_psp43
    (hC : ConcreteLeaf (Equiv.Perm (Fin 45))
      ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup
      ComponentClassification.CatFactsSmall.PSp43.QA45.originalSubgroup) :
    SmallSimpleLeaf fun F _ => LieModel F .PSp 2 3 1 := by
  refine smallSimpleLeaf_of_models (fun _ _ h => ?_) ?_ hC
  · obtain ⟨e⟩ := ComponentClassification.CatFactsSmall.PSp43.equiv_of_lieModel h
    exact ComponentClassification.CatFactsSmall.PSp43.exists_model e
  · rw [ComponentClassification.CatFactsSmall.PSp43.QP45_closure,
      ComponentClassification.CatFactsSmall.PSp43.QA45_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)

end CFSG.ClassicalInvolution.Q3.TA3
