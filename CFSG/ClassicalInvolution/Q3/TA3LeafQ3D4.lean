module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Good
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5G2D4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Cent

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem TightDatum.commute_A_of_sl2 (hD : TightDatum R S t) {N : Subgroup Y} {F₁ F₂ : Type}
    [Field F₁] [Finite F₁] [Field F₂] (hodd : Odd (Nat.card F₁)) (h4 : 4 ≤ Nat.card F₁)
    {h3 : (3 : F₂) = 0} (P : CentShape Y (N ⊓ Subgroup.centralizer ({t} : Set Y)) t F₁ F₂ h3) :
    ∀ m ∈ R, m ∈ N → ∀ a ∈ P.A, m * a = a * m := by
  have hAC : P.A ≤ Subgroup.centralizer ({t} : Set Y) := fun a ha =>
    (Subgroup.mem_inf.mp (P.le_A ha)).2
  have : Group.IsPerfect ↥P.A := by
    have hS : Group.IsPerfect SL(2, F₁) := sl2_isPerfect h4
    refine ⟨?_⟩
    have h := congrArg (Subgroup.map P.eA.symm.toMonoidHom) hS.commutator_eq_top
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ P.eA.symm.surjective] at h
    rw [commutator_def]
    exact h
  have hM₀ : P.A ⊓ oddCoreImg R = ⊥ := by
    refine noOddNormal_of_equiv_sl2 hodd h4 P.eA _ inf_le_left ⟨fun n hn g => ?_⟩
      ((odd_natCard_oddCoreImg R).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnA, hnO⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨?_, datum_conj_mem_oddCoreImg hD (hAC g.2) hnO⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hnA) (Subgroup.inv_mem _ g.2)
  intro m hm hmN a ha
  have hc : ⁅a, m⁆ ∈ P.A ⊓ oddCoreImg R := by
    refine Subgroup.mem_inf.mpr ⟨?_, datum_commutator_mem hD hAC a ha m hm⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem ha ?_
    rw [← mul_assoc]
    exact P.normal_A m (Subgroup.mem_inf.mpr ⟨hmN, hD.cent hm⟩) _ (inv_mem ha)
  rw [hM₀, Subgroup.mem_bot] at hc
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm

theorem good_d43 [IsSimpleGroup ↥(genFittingFStar Y)]
    (hnab : ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a)
    (hm : LieModel ↥(genFittingFStar Y) .trialityD4 0 3 1) (hD : TightDatum R S t) :
    GoodThreeElement R t := by
  have := genFittingFStar_normal Y
  obtain ⟨htN, s, hsR, hsN, hs4⟩ := TightDatum.exists_cyclic4_of_outTwoCyclic hD
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) (outTwoCyclic_trialityD4 (by decide)
      (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)))
  have ht : orderOf (⟨t, htN⟩ : genFittingFStar Y) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hD.order
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, hz⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 Nat.prime_three (by decide) hm _ ht
  have hF₂ : Nat.card F₂ = 3 := by rw [hc₂, pow_one]
  have hF₁ : Nat.card F₁ = 27 := by rw [hc₁]; norm_num
  have h3 : (3 : F₂) = 0 := LieType.HighestRoot.three_eq_zero hF₂
  have hzt : ((Sh.z : genFittingFStar Y) : Y) = t := by rw [hz]
  exact TightDatum.good_of_centShape hD hsR hsN hs4 hF₂
    (Q3Sh.toCentShape htN Sh hzt h3 (two_ne_zero_of_three h3))
    (TightDatum.commute_A_of_sl2 hD (by rw [hF₁]; decide) (by rw [hF₁]; norm_num) _)

theorem smallSimpleLeaf_d43 : SmallSimpleLeaf fun F _ => LieModel F .trialityD4 0 3 1 := by
  intro Y _ _ _ _ hnab _ hm R S t hD _ _
  exact Or.inr (good_d43 hnab hm hD)

end CFSG.ClassicalInvolution.Q3.TA3
