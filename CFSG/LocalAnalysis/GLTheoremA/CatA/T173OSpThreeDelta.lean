module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourLin
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinII
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.TailTrivialThree
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType CFSG.RankThree.PartOne.KCUnitary
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

private theorem exists_selfDual_data [Fact (Irreducible (SpFin.h3 F))]
    (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ (hE : UnitaryFieldData 2 1 (AdjoinRoot (SpFin.h3 F)))
      (Hf : primaryComponent (spEnd d) (SpFin.h3 F) →ₛₗ[hE.bar]
        primaryComponent (spEnd d) (SpFin.h3 F) →ₗ[AdjoinRoot (SpFin.h3 F)]
        AdjoinRoot (SpFin.h3 F)),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        ∃ φ : spSupported d {(SpFin.h3 F)} ≃* sesqUnitaryGroup Hf,
          ∀ (g : spSupported d {(SpFin.h3 F)}) (v : Fin ℓ ⊕ Fin ℓ → F)
            (hv : v ∈ primaryComponent (spEnd d) (SpFin.h3 F)),
            KCUnitary.blockApply (↑(φ g)) v hv = spEnd (↑g) v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hℓ1 : 1 ≤ ℓ := by
    by_contra h
    have h0 : ℓ = 0 := by omega
    subst h0
    exact hd1 (Subsingleton.elim d 1)
  have hblocks := SpFour.blocks_of_order_three hF hℓ1 hd3 hd1
  let g : primaryFactors (spEnd d) := ⟨SpFin.h3 F, SpFin.h3_mem_primaryFactors hF hd3 hd1⟩
  have hg : (g : F[X]) = SpFin.h3 F := rfl
  have hne : (g : F[X]) ≠ X - 1 := by
    rw [hg]
    exact SpFin.h3_ne_X_sub_one
  have hrec : KCOrthogonal.reciprocalPolynomial (g : F[X]) = (g : F[X]) := by
    rw [hg]
    exact SpFin.h3_reciprocal
  have hS : SpSelfDualBlock 2 1 3 d g := hblocks.selfDual g hne hrec
  obtain ⟨m, hdeg, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, ⟨e₀, -⟩, φ, hφ⟩ :=
    hS.exists_half
  have hm : m = 1 := by
    have h2 : (g : F[X]).natDegree = 2 := by
      rw [hg]
      exact SpFin.h3_natDegree
    rw [h2] at hdeg
    omega
  subst hm
  exact ⟨hE, Hf, hHf, hHfl, φ, hφ⟩

private theorem four_le_finrank_unitary [Fact (Irreducible (SpFin.h3 F))]
    (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆)
    {hE : UnitaryFieldData 2 1 (AdjoinRoot (SpFin.h3 F))}
    {Hf : primaryComponent (spEnd d) (SpFin.h3 F) →ₛₗ[hE.bar]
      primaryComponent (spEnd d) (SpFin.h3 F) →ₗ[AdjoinRoot (SpFin.h3 F)]
      AdjoinRoot (SpFin.h3 F)}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (φ : spSupported d {(SpFin.h3 F)} ≃* sesqUnitaryGroup Hf) :
    4 ≤ Module.finrank (AdjoinRoot (SpFin.h3 F))
      (primaryComponent (spEnd d) (SpFin.h3 F)) := by
  have hsp : spSupported d ({X ^ 2 + X + 1} : Set F[X]) =
      spSupported d {(SpFin.h3 F)} := rfl
  have hQh : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d {(SpFin.h3 F)}, spSupported d {(SpFin.h3 F)}⁆ := by
    rw [hsp] at hQ
    exact hQ
  by_contra hlt
  have hlt' : Module.finrank (AdjoinRoot (SpFin.h3 F))
      (primaryComponent (spEnd d) (SpFin.h3 F)) ≤ 3 := by omega
  haveI : Group.IsSolvable ↥(sesqUnitaryGroup Hf) :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.isSolvable_sesqUnitaryGroup_of_finrank_le_three
      hE hHf hHfl hlt'
  haveI : Group.IsSolvable ↥(spSupported d {(SpFin.h3 F)}) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  exact
    CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab.not_isSolvable_of_isQuasisimple
    hQh
    (Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (Subgroup.commutator_le_self _))
      (Subgroup.inclusion_injective _))

private theorem exists_unitary_data [Fact (Irreducible (SpFin.h3 F))]
    (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆) :
    ∃ (hE : UnitaryFieldData 2 1 (AdjoinRoot (SpFin.h3 F)))
      (Hf : primaryComponent (spEnd d) (SpFin.h3 F) →ₛₗ[hE.bar]
        primaryComponent (spEnd d) (SpFin.h3 F) →ₗ[AdjoinRoot (SpFin.h3 F)]
        AdjoinRoot (SpFin.h3 F)),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧
        4 ≤ Module.finrank (AdjoinRoot (SpFin.h3 F))
          (primaryComponent (spEnd d) (SpFin.h3 F)) ∧
        ∃ φ : spSupported d {(SpFin.h3 F)} ≃* sesqUnitaryGroup Hf,
          ∀ (g : spSupported d {(SpFin.h3 F)}) (v : Fin ℓ ⊕ Fin ℓ → F)
            (hv : v ∈ primaryComponent (spEnd d) (SpFin.h3 F)),
            KCUnitary.blockApply (↑(φ g)) v hv = spEnd (↑g) v := by
  obtain ⟨hE, Hf, hHf, hHfl, φ, hφ⟩ := exists_selfDual_data hF hd3 hd1
  exact ⟨hE, Hf, hHf, hHfl, four_le_finrank_unitary hF hd3 hd1 hQ hHf hHfl φ, φ, hφ⟩

private theorem unitaryDet_apply_eq_one_of_sq_eq_one [Fact (Irreducible (SpFin.h3 F))]
    {d : ↥(StatedSp ℓ F)}
    {hE : UnitaryFieldData 2 1 (AdjoinRoot (SpFin.h3 F))}
    {Hf : primaryComponent (spEnd d) (SpFin.h3 F) →ₛₗ[hE.bar]
      primaryComponent (spEnd d) (SpFin.h3 F) →ₗ[AdjoinRoot (SpFin.h3 F)]
      AdjoinRoot (SpFin.h3 F)}
    (e : ↥(spSupported d {(SpFin.h3 F)}) →* sesqUnitaryGroup Hf)
    {t : ↥(StatedSp ℓ F)} (ht : t ∈ spSupported d {(SpFin.h3 F)}) (ht2 : t ^ 2 = 1) :
    CFSG.LinearGroups.unitaryDet Hf (e ⟨t, ht⟩) = 1 := by
  haveI : CharP (AdjoinRoot (SpFin.h3 F)) 2 := hE.charP
  have hpow : e ⟨t, ht⟩ ^ 2 = 1 := by
    rw [← map_pow e]
    have hx2 : (⟨t, ht⟩ : ↥(spSupported d {(SpFin.h3 F)})) ^ 2 = 1 := Subtype.ext ht2
    rw [hx2, map_one]
  have hdet2 : (CFSG.LinearGroups.unitaryDet Hf (e ⟨t, ht⟩)) ^ 2 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hdetval : ((CFSG.LinearGroups.unitaryDet Hf (e ⟨t, ht⟩) :
      (AdjoinRoot (SpFin.h3 F))ˣ) : AdjoinRoot (SpFin.h3 F)) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hdet2, Units.val_one]
  rcases sq_eq_one_iff.mp hdetval with h1 | h1
  · exact Units.ext h1
  · exact Units.ext (h1.trans (CharTwo.neg_eq 1))

private theorem mem_commutator_of_det_eq_one [Fact (Irreducible (SpFin.h3 F))]
    {d : ↥(StatedSp ℓ F)}
    {hE : UnitaryFieldData 2 1 (AdjoinRoot (SpFin.h3 F))}
    {Hf : primaryComponent (spEnd d) (SpFin.h3 F) →ₛₗ[hE.bar]
      primaryComponent (spEnd d) (SpFin.h3 F) →ₗ[AdjoinRoot (SpFin.h3 F)]
      AdjoinRoot (SpFin.h3 F)}
    (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    (h4 : 4 ≤ Module.finrank (AdjoinRoot (SpFin.h3 F))
      (primaryComponent (spEnd d) (SpFin.h3 F)))
    (e : ↥(spSupported d {(SpFin.h3 F)}) →* sesqUnitaryGroup Hf)
    (he_inj : Function.Injective e) (he_surj : Function.Surjective e)
    {y : ↥(StatedSp ℓ F)} (hy : y ∈ spSupported d {(SpFin.h3 F)})
    (hdet : CFSG.LinearGroups.unitaryDet Hf (e ⟨y, hy⟩) = 1) :
    y ∈ ⁅spSupported d {(SpFin.h3 F)}, spSupported d {(SpFin.h3 F)}⁆ := by
  let U : Subgroup (blockGL (spEnd d) (SpFin.h3 F)) := sesqUnitaryGroup Hf
  let SU : Subgroup (blockGL (spEnd d) (SpFin.h3 F)) := sesqSpecialUnitaryGroup Hf
  let eG : ↥(spSupported d {(SpFin.h3 F)}) →* blockGL (spEnd d) (SpFin.h3 F) := U.subtype.comp e
  have hqSU : CFSG.IsQuasisimple ↥SU := by
    refine CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hE hHf hHfl (by omega) ⟨?_, ?_⟩
    · omega
    · omega
  have hSUperf : ⁅SU, SU⁆ = SU := Subgroup.isPerfect_iff.mp hqSU.1
  have hSU_le : SU ≤ ⁅U, U⁆ := by
    rw [← hSUperf]
    exact Subgroup.commutator_mono inf_le_left inf_le_left
  have hmapC : (commutator ↥(spSupported d {(SpFin.h3 F)})).map e = commutator ↥U := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective e he_surj]
  have hySU : eG ⟨y, hy⟩ ∈ SU := by
    change U.subtype (e ⟨y, hy⟩) ∈ SU
    rw [mem_sesqSpecialUnitaryGroup]
    refine ⟨(e ⟨y, hy⟩).2, ?_⟩
    have := congrArg Units.val hdet
    simpa [CFSG.LinearGroups.unitaryDet_apply] using this
  have hyamb : eG ⟨y, hy⟩ ∈ ⁅U, U⁆ := hSU_le hySU
  have hycommU : e ⟨y, hy⟩ ∈ commutator ↥U := by
    rw [← Subgroup.map_subtype_commutator U] at hyamb
    exact (Subgroup.mem_map_iff_mem (f := U.subtype) U.subtype_injective).mp hyamb
  have hyC : (⟨y, hy⟩ : ↥(spSupported d {(SpFin.h3 F)})) ∈
      commutator ↥(spSupported d {(SpFin.h3 F)}) := by
    rw [← Subgroup.mem_map_iff_mem (f := e) he_inj, hmapC]
    exact hycommU
  rw [← Subgroup.map_subtype_commutator (spSupported d {(SpFin.h3 F)}), Subgroup.mem_map]
  exact ⟨⟨y, hy⟩, hyC, rfl⟩

private theorem exists_mul_pow_eq_one_of_card_three {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 3) {u v : H} (hv : v ≠ 1) : ∃ i : ℕ, i < 3 ∧ u * v ^ i = 1 := by
  have hv3 : v ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := H) (x := v)
    rwa [hH] at h
  have hvord : orderOf v = 3 := orderOf_eq_prime hv3 hv
  have htop : Subgroup.zpowers v = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, hvord, hH]
  have hu : u ∈ Subgroup.zpowers v := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, hj3, hj⟩ : ∃ j : ℕ, j < 3 ∧ u = v ^ j := by
    refine ⟨(z % 3).toNat, ?_, ?_⟩
    · have := Int.emod_lt_of_pos z (show (0 : ℤ) < 3 by norm_num)
      omega
    · rw [← hz, ← zpow_natCast]
      rw [show ((z % 3).toNat : ℤ) = z % (3 : ℤ) from
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      exact zpow_eq_zpow_emod' z hv3
  interval_cases j
  · exact ⟨0, by norm_num, by rw [hj]; simp⟩
  · exact ⟨2, by norm_num, by rw [hj, ← pow_add]; norm_num; exact hv3⟩
  · exact ⟨1, by norm_num, by rw [hj, ← pow_add]; norm_num; exact hv3⟩

theorem eight_le_finrank_unitary (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆) :
    8 ≤ Module.finrank F
      ↥(primaryComponent (spEnd d) (X ^ 2 + X + 1 : F[X])) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  haveI : Fact (Irreducible (SpFin.h3 F)) := ⟨SpFin.h3_irreducible hF⟩
  obtain ⟨hE, Hf, -, -, h4, -, -⟩ := exists_unitary_data hF hd3 hd1 hQ
  have hfin := finrank_primaryComponent (spEnd d) (SpFin.h3 F)
  rw [SpFin.h3_natDegree] at hfin
  change 8 ≤ Module.finrank F ↥(primaryComponent (spEnd d) (SpFin.h3 F))
  rw [hfin]
  omega

theorem mem_commutator_of_sq_eq_one (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆)
    {t : ↥(StatedSp ℓ F)}
    (ht : t ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X])) (ht2 : t ^ 2 = 1) :
    t ∈ ⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
      spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  haveI : Fact (Irreducible (SpFin.h3 F)) := ⟨SpFin.h3_irreducible hF⟩
  obtain ⟨hE, Hf, hHf, hHfl, h4, φ, -⟩ := exists_unitary_data hF hd3 hd1 hQ
  have ht' : t ∈ spSupported d {(SpFin.h3 F)} := ht
  exact mem_commutator_of_det_eq_one hHf hHfl h4 φ.toMonoidHom φ.injective φ.surjective ht'
    (unitaryDet_apply_eq_one_of_sq_eq_one φ.toMonoidHom ht' ht2)

theorem exists_mul_pow_mem_commutator (hF : Nat.card F = 2) {d : ↥(StatedSp ℓ F)}
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hQ : CFSG.Open.IsQuasisimple
      ↥⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆)
    {x a : ↥(StatedSp ℓ F)}
    (hx : x ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X]))
    (hxK : x ∉ ⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
      spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆)
    (ha : a ∈ spSupported d ({X ^ 2 + X + 1} : Set F[X])) :
    ∃ i : ℕ, i < 3 ∧ a * x ^ i ∈
      ⁅spSupported d ({X ^ 2 + X + 1} : Set F[X]),
        spSupported d ({X ^ 2 + X + 1} : Set F[X])⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  haveI : Fact (Irreducible (SpFin.h3 F)) := ⟨SpFin.h3_irreducible hF⟩
  obtain ⟨hE, Hf, hHf, hHfl, h4, φ, -⟩ := exists_unitary_data hF hd3 hd1 hQ
  have hx' : x ∈ spSupported d {(SpFin.h3 F)} := hx
  have ha' : a ∈ spSupported d {(SpFin.h3 F)} := ha
  have hxK' : x ∉ ⁅spSupported d {(SpFin.h3 F)}, spSupported d {(SpFin.h3 F)}⁆ := hxK
  have hxdet1 : CFSG.LinearGroups.unitaryDet Hf (φ.toMonoidHom ⟨x, hx'⟩) ≠ 1 := by
    intro h1
    exact hxK' (mem_commutator_of_det_eq_one hHf hHfl h4 φ.toMonoidHom φ.injective
      φ.surjective hx' h1)
  haveI : CharP (AdjoinRoot (SpFin.h3 F)) 2 := hE.charP
  have hEcard : Nat.card (AdjoinRoot (SpFin.h3 F)) = 4 := SpFin.card_adjoinRoot_h3 hF
  have hunits : Nat.card (AdjoinRoot (SpFin.h3 F))ˣ = 3 := by
    rw [Nat.card_units, hEcard]
  obtain ⟨i, hi3, hi⟩ := exists_mul_pow_eq_one_of_card_three (H := (AdjoinRoot (SpFin.h3 F))ˣ)
    hunits (u := CFSG.LinearGroups.unitaryDet Hf (φ.toMonoidHom ⟨a, ha'⟩))
    (v := CFSG.LinearGroups.unitaryDet Hf (φ.toMonoidHom ⟨x, hx'⟩)) hxdet1
  refine ⟨i, hi3, ?_⟩
  have haxi : a * x ^ i ∈ spSupported d {(SpFin.h3 F)} :=
    (spSupported d {(SpFin.h3 F)}).mul_mem ha' ((spSupported d {(SpFin.h3 F)}).pow_mem hx' i)
  have heq : (⟨a * x ^ i, haxi⟩ : ↥(spSupported d {(SpFin.h3 F)})) =
      ⟨a, ha'⟩ * ⟨x, hx'⟩ ^ i := Subtype.ext rfl
  have hdet : CFSG.LinearGroups.unitaryDet Hf (φ.toMonoidHom ⟨a * x ^ i, haxi⟩) = 1 := by
    rw [heq, map_mul φ.toMonoidHom, map_pow φ.toMonoidHom,
      map_mul (CFSG.LinearGroups.unitaryDet Hf), map_pow (CFSG.LinearGroups.unitaryDet Hf), hi]
  exact mem_commutator_of_det_eq_one hHf hHfl h4 φ.toMonoidHom φ.injective φ.surjective
    haxi hdet

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
