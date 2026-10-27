module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222ExcCenter
public import CFSG.LieType.Multipliers.U42
public import CFSG.RankThree.SubgroupLists.SymplecticInvolutions
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.RankThree.PerfectCover.HopfCentralCoversLift
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherProjective
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Large
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalReduce
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.GH74.Exceptional
open CFSG.LocalAnalysis.ComponentInitial

theorem nonempty_mulEquiv_statedSp_of_lieModel
    {H : Type} [Group H] [Finite H] (hH : Group.IsPerfect H)
    (hZ : Nat.card (center H) = 2) (hL : CFSG.Blueprint.LieModel (H ⧸ center H) .PSU 4 2 1) :
    Nonempty (StatedSp 2 (ZMod 3) ≃* H) := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 hL
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hL
  set Z := (StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3)).subgroupOf (StatedSp 2 (ZMod 3)) with hZdef
  let p₀ : StatedSp 2 (ZMod 3) →* H ⧸ center H := e.symm.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hp₀ : Function.Surjective p₀ := e.symm.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker₀ : p₀.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e.symm (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e.symm e.symm.injective, QuotientGroup.eq_one_iff]
  have hk₀ : p₀.ker ≤ center (StatedSp 2 (ZMod 3)) :=
    hker₀ ▸ SymplecticHigher.spScalars_le_center
  have hcardZ : Nat.card p₀.ker = 2 := by
    have h1 : Nat.card PSp43 * Nat.card Z = 51840 := by
      rw [← card_statedSp_two_three]
      exact (Subgroup.card_eq_card_quotient_mul_card_subgroup Z).symm
    rw [CFSG.LieType.Multipliers.U42.card_PSp43] at h1
    rw [hker₀]
    omega
  have hS₀ : Group.IsPerfect (StatedSp 2 (ZMod 3)) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 (ZMod 3)
      (Or.inr (Or.inl ⟨Nat.card_zmod 3, le_rfl⟩))
  let p : H →* H ⧸ center H := QuotientGroup.mk' (center H)
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective _
  have hker : p.ker = center H := QuotientGroup.ker_mk' _
  have h2 : IsPGroup 2 p.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hM : Nat.card (hopfMultiplier (H ⧸ center H)) = Nat.card p₀.ker * 1 := by
    rw [mul_one, hcardZ, ← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv,
      Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  obtain ⟨α, hα, -⟩ := exists_lift_of_odd_index hS₀ hH p₀ hp₀ hk₀ p hp hker.le h2 1 odd_one hM
  have hc₀ : Nat.card (StatedSp 2 (ZMod 3)) = Nat.card H := by
    rw [card_statedSp_two_three, Subgroup.card_eq_card_quotient_mul_card_subgroup (center H), hZ,
      Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U42.card_PSp43]
  exact ⟨MulEquiv.ofBijective α (hα.bijective_of_nat_card_le hc₀.le)⟩

theorem exc213_PSU_four :
    Exc213 .PSU 4 := by
  intro H _ _ hq heven hL P hP
  have hperf : Group.IsPerfect H := Group.isPerfect_def.2 hq.1
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ hL
  have hZ2 : Nat.card (center H) = 2 := by
    have : Group.IsPerfect H := hperf
    let q : H →* H ⧸ center H := QuotientGroup.mk' (center H)
    have hq' : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hker : q.ker = center H := QuotientGroup.ker_mk' _
    have hmap := map_hopfMultiplier_hopfLift q hq' hker.le
    have hdvd : Nat.card (center H) ∣ 2 := by
      have h := Subgroup.card_map_dvd (H := hopfMultiplier (H ⧸ center H))
        (hopfLift q hq' hker.le)
      rw [hmap, hker, ← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h
      exact h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · rw [h] at heven
      exact absurd heven (by decide)
    · exact h
  obtain ⟨α⟩ := nonempty_mulEquiv_statedSp_of_lieModel hperf hZ2 hL
  have hcen : ∀ x : StatedSp 2 (ZMod 3), x ∈ center (StatedSp 2 (ZMod 3)) → α x ∈ center H := by
    intro x hx
    rw [mem_center_iff] at hx ⊢
    intro g
    obtain ⟨g', rfl⟩ := α.surjective g
    rw [← map_mul, ← map_mul, hx g']
  have hneg : ∀ x : StatedSp 2 (ZMod 3), (x : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 →
      x ∈ center (StatedSp 2 (ZMod 3)) := by
    intro x hx
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_neg_one, neg_one_mul]
  have hnc : ∀ y ∈ P, y ≠ 1 → y ∉ center H := fun y hy hy1 hyc =>
    hy1 (hP.eq_one_of_mem_center y hy hyc)
  obtain ⟨u, hu, v, hv, hu1, hv1, hvu, huv⟩ := hP.exists_pair
  obtain ⟨a, rfl⟩ := α.surjective u
  obtain ⟨b, rfl⟩ := α.surjective v
  have ha2 : a * a = 1 := α.injective (by rw [map_mul, ← sq, hP.sq_eq_one _ hu, map_one])
  have hb2 : b * b = 1 := α.injective (by rw [map_mul, ← sq, hP.sq_eq_one _ hv, map_one])
  have hab : a * b = b * a := α.injective (by rw [map_mul, map_mul, huv])
  have hA2 : (a : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * a = 1 := by
    rw [← Subgroup.coe_mul, ha2, Subgroup.coe_one]
  have hB2 : (b : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * b = 1 := by
    rw [← Subgroup.coe_mul, hb2, Subgroup.coe_one]
  have hAB : (a : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) * b = b * a := by
    rw [← Subgroup.coe_mul, hab, Subgroup.coe_mul]
  have hA1 : (a : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ 1 := fun h =>
    hu1 (by rw [show a = 1 from Subtype.ext h, map_one])
  have hAm : (a : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ -1 := fun h => hnc _ hu hu1 (hcen a (hneg a h))
  rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution (by decide : (2 : ZMod 3) ≠ 0)
      a.2 b.2 hA2 hB2 hAB hA1 hAm with h | h | h | h
  · exact hv1 (by rw [show b = 1 from Subtype.ext h, map_one])
  · exact hnc _ hv hv1 (hcen b (hneg b h))
  · exact hvu (by rw [show b = a from Subtype.ext h])
  · have hab1 : ((a * b : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 := by
      rw [Subgroup.coe_mul, h, mul_neg, hA2]
    have hc := hcen _ (hneg _ hab1)
    rw [map_mul] at hc
    have h1 : α a * α b = 1 := hP.eq_one_of_mem_center _ (mul_mem hu hv) hc
    have hui : (α a)⁻¹ = α a :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hP.sq_eq_one _ hu)
    exact hvu (by rw [← hui]; exact eq_inv_of_mul_eq_one_right h1)

end CFSG.ComponentClassification.RankTwoClassical
