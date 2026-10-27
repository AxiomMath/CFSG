module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4F2Config
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldCentral
public import CFSG.LieType.Steinberg.TwistedD4.Perfect
public import CFSG.LieType.Steinberg.TwistedD4.Local
public import CFSG.LieType.Steinberg.CentralExt.TrialityTorus
public import CFSG.LieType.SeitzGeneration.ExcParabolicTw
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCaseB
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.KE.OddE6NoninnerOuter
public import CFSG.RankThree.PartOne.RF4.Basic
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open scoped commutatorElement
open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4

section TwBase


variable {K : Type} [Field K]

theorem d4Twist_one_eq_twistC (σ : K ≃+* K) (g : adjointGroup Tag.D4 K) :
    d4Twist 1 σ g = twistC TwistTag.D4 K σ.toRingHom g := by
  refine Subtype.ext ?_
  have h1 := coe_twistedEntrywiseAut TwistTag.D4 (1 : ℤ) σ g
  have h2 := coe_twistC TwistTag.D4 K σ.toRingHom g
  rw [zpow_one] at h1
  change ((twistedEntrywiseAut TwistTag.D4 1 σ g : adjointGroup TwistTag.D4.tag K) :
    ModGL TwistTag.D4.tag K) = ((twistC TwistTag.D4 K σ.toRingHom g :
    adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K)
  rw [h1, h2]
  apply Units.ext
  rw [coe_twistHom]
  simp only [Units.val_mul]
  rfl

theorem mem_fixedSubgroup_d4Twist_iff (σ : K ≃+* K) (g : adjointGroup Tag.D4 K) :
    g ∈ fixedSubgroup (d4Twist 1 σ) ↔ twistC TwistTag.D4 K σ.toRingHom g = g := by
  rw [mem_fixedSubgroup]
  constructor
  · intro h
    rw [← d4Twist_one_eq_twistC]
    exact h
  · intro h
    rw [d4Twist_one_eq_twistC]
    exact h

theorem xPar_mem_fixedSubgroup_d4Twist {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) (hfix : rho γ = γ) {c : K}
    (hc : σ c = c) : xPar (rootOperatorFamily Tag.D4) γ c ∈ fixedSubgroup (d4Twist 1 σ) := by
  have h1 := xPar_mem_of_fixed (σ := σ.toRingHom) (fun c => hσ3 c) hγ hfix hc
  have h2 := twistedRootSubgroupD4_le_twistFixed (K := K) σ.toRingHom (proj γ) h1
  exact (mem_fixedSubgroup_d4Twist_iff σ _).2 ((mem_twistFixed _ _ _).1 h2)

theorem nd_ne (a b : ℕ) (ha : a < 4) (hb : b < 4) (hab : a ≠ b) :
    (⟨a, ha⟩ : Fin Tag.D4.rank) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)

theorem commute_outer_xPar {a b : Fin Tag.D4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2) (hab : a ≠ b)
    (c d : K) :
    Commute (xPar (rootOperatorFamily Tag.D4) (Pi.single a 1) c)
      (xPar (rootOperatorFamily Tag.D4) (Pi.single b 1) d) := by
  have h := commute_xPar_outer (K := K) ha hb hab (s := 1) (s' := 1) (Or.inl rfl) (Or.inl rfl) c d
  rw [one_smul, one_smul] at h
  exact h

theorem commute_outer_neg_xPar {a b : Fin Tag.D4.rank} (ha : a ≠ nd 2) (hb : b ≠ nd 2)
    (hab : a ≠ b) (c d : K) :
    Commute (xPar (rootOperatorFamily Tag.D4) (-Pi.single a 1) c)
      (xPar (rootOperatorFamily Tag.D4) (-Pi.single b 1) d) := by
  have h := commute_xPar_outer (K := K) ha hb hab (s := -1) (s' := -1) (Or.inr rfl) (Or.inr rfl) c d
  rw [neg_smul, one_smul, neg_smul, one_smul] at h
  exact h

theorem triple_pos_mem {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (s : K) :
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (σ (σ s)) ∈
        fixedSubgroup (d4Twist 1 σ) := by
  refine (mem_fixedSubgroup_d4Twist_iff σ _).2 ?_
  erw [map_mul, map_mul]
  erw [twistC_xPar_single σ.toRingHom, twistC_xPar_single σ.toRingHom,
    twistC_xPar_single σ.toRingHom]
  rw [rhoPerm_zero, rhoPerm_one, rhoPerm_three]
  simp only [show ∀ c : K, σ.toRingHom c = σ c from fun _ => rfl]
  rw [hσ3]
  have hc := (commute_outer_xPar (K := K) (a := nd 0) (b := nd 1)
    (nd_ne 0 2 (by decide) (by decide) (by decide))
    (nd_ne 1 2 (by decide) (by decide) (by decide))
    (nd_ne 0 1 (by decide) (by decide) (by decide)) s (σ s)).mul_right
      (commute_outer_xPar (K := K) (a := nd 0) (b := nd 3)
        (nd_ne 0 2 (by decide) (by decide) (by decide))
        (nd_ne 3 2 (by decide) (by decide) (by decide))
        (nd_ne 0 3 (by decide) (by decide) (by decide)) s (σ (σ s)))
  exact (hc.eq.symm).trans (mul_assoc _ _ _).symm

theorem triple_neg_mem {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (s : K) :
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (σ (σ s)) ∈
        fixedSubgroup (d4Twist 1 σ) := by
  refine (mem_fixedSubgroup_d4Twist_iff σ _).2 ?_
  erw [map_mul, map_mul]
  erw [twistC_xPar_neg_single σ.toRingHom, twistC_xPar_neg_single σ.toRingHom,
    twistC_xPar_neg_single σ.toRingHom]
  rw [rhoPerm_zero, rhoPerm_one, rhoPerm_three]
  simp only [show ∀ c : K, σ.toRingHom c = σ c from fun _ => rfl]
  rw [hσ3]
  have hc := (commute_outer_neg_xPar (K := K) (a := nd 0) (b := nd 1)
    (nd_ne 0 2 (by decide) (by decide) (by decide))
    (nd_ne 1 2 (by decide) (by decide) (by decide))
    (nd_ne 0 1 (by decide) (by decide) (by decide)) s (σ s)).mul_right
      (commute_outer_neg_xPar (K := K) (a := nd 0) (b := nd 3)
        (nd_ne 0 2 (by decide) (by decide) (by decide))
        (nd_ne 3 2 (by decide) (by decide) (by decide))
        (nd_ne 0 3 (by decide) (by decide) (by decide)) s (σ (σ s)))
  exact (hc.eq.symm).trans (mul_assoc _ _ _).symm

theorem rho_e2 : rho (Pi.single (nd 2) 1) = Pi.single (nd 2) 1 := by decide

theorem rho_neg_e2 : rho (-Pi.single (nd 2) 1) = -Pi.single (nd 2) 1 := by decide

theorem xPar_e2_mem_fixed {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) {c : K}
    (hc : σ c = c) :
    xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ fixedSubgroup (d4Twist 1 σ) :=
  xPar_mem_fixedSubgroup_d4Twist hσ3 (isRoot_single Tag.D4 (nd 2)) rho_e2 hc

theorem xPar_neg_e2_mem_fixed {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) {c : K}
    (hc : σ c = c) :
    xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ fixedSubgroup (d4Twist 1 σ) :=
  xPar_mem_fixedSubgroup_d4Twist hσ3 (isRoot_neg_single Tag.D4 (nd 2)) rho_neg_e2 hc

theorem d4Root_22_eq : d4Root 22 = d4F2Theta := by
  funext i
  fin_cases i <;> rfl

theorem isMaxHeightRoot_d4Root_22 : IsMaxHeightRoot Tag.D4 (d4Root 22) := by
  rw [d4Root_22_eq]
  exact d4F2_theta_isMax

theorem isRoot_d4Root_21 : IsRoot Tag.D4 (d4Root 21) := isRoot_d4Root (by decide)

theorem xPar_theta_mem_fixed {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) {c : K}
    (hc : σ c = c) :
    xPar (rootOperatorFamily Tag.D4) (d4Root 22) c ∈ fixedSubgroup (d4Twist 1 σ) :=
  xPar_mem_fixedSubgroup_d4Twist hσ3 isMaxHeightRoot_d4Root_22.1 rho_d4Root_22 hc

theorem xPar_negBeta_mem_fixed {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c) {c : K}
    (hc : σ c = c) :
    xPar (rootOperatorFamily Tag.D4) (d4Root 21) c ∈ fixedSubgroup (d4Twist 1 σ) :=
  xPar_mem_fixedSubgroup_d4Twist hσ3 isRoot_d4Root_21 rho_d4Root_21 hc

theorem commutator_theta_negBeta (s t : K) :
    ⁅xPar (rootOperatorFamily Tag.D4) (d4Root 22) s,
      xPar (rootOperatorFamily Tag.D4) (d4Root 21) t⁆ =
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) (s * t) :=
  commutator_xPar_d4Root s t

theorem torus_conj_outer_pos (t : Kˣ) {j : Fin Tag.D4.rank}
    (hj : j = nd 0 ∨ j = nd 1 ∨ j = nd 3) (c : K) :
    torusElement Tag.D4 K (nd 2) t * xPar (rootOperatorFamily Tag.D4) (Pi.single j 1) c *
      (torusElement Tag.D4 K (nd 2) t)⁻¹ =
      xPar (rootOperatorFamily Tag.D4) (Pi.single j 1) ((t : K)⁻¹ * c) := by
  have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.torusElement_conj_xPar (K := K)
    (nd 2) t (isRoot_single Tag.D4 j) c
  have hpr : CFSG.LieType.Steinberg.CentralExt.TrialityClosed.pr (nd 2) (Pi.single j 1) = -1 := by
    rcases hj with rfl | rfl | rfl <;> decide
  erw [hpr, zpow_neg_one, Units.val_inv_eq_inv_val] at h
  exact h

theorem torus_conj_outer_neg (t : Kˣ) {j : Fin Tag.D4.rank}
    (hj : j = nd 0 ∨ j = nd 1 ∨ j = nd 3) (c : K) :
    torusElement Tag.D4 K (nd 2) t * xPar (rootOperatorFamily Tag.D4) (-Pi.single j 1) c *
      (torusElement Tag.D4 K (nd 2) t)⁻¹ =
      xPar (rootOperatorFamily Tag.D4) (-Pi.single j 1) ((t : K) * c) := by
  have h := CFSG.LieType.Steinberg.CentralExt.TrialityClosed.torusElement_conj_xPar (K := K)
    (nd 2) t (isRoot_neg_single Tag.D4 j) c
  have hpr : CFSG.LieType.Steinberg.CentralExt.TrialityClosed.pr (nd 2) (-Pi.single j 1) = 1 := by
    rcases hj with rfl | rfl | rfl <;> decide
  erw [hpr, zpow_one] at h
  exact h

theorem torusElement_e2_mem {S : Subgroup (adjointGroup Tag.D4 K)}
    (hE : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ S) (t : Kˣ) :
    torusElement Tag.D4 K (nd 2) t ∈ S := by
  erw [torusElement_eq (K := K) (nd 2) t]
  refine S.mul_mem ?_ (S.inv_mem ?_)
  · unfold CFSG.LieType.Steinberg.weylElement
    exact S.mul_mem (S.mul_mem (hE _).1 (hE _).2) (hE _).1
  · unfold CFSG.LieType.Steinberg.weylElement
    exact S.mul_mem (S.mul_mem (hE _).1 (hE _).2) (hE _).1

end TwBase

end CFSG.LieType.SeitzGeneration.ExcWideThree
