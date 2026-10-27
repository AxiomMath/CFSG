module

public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSL

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Linear

variable {F : Type} [Field F] {n : ℕ} {D : Matrix (Fin n) (Fin n) F}

theorem mem_sup_longRootGroup_of_det_eq_one (h2 : (2 : F) ≠ 0) (hD : D * D = 1)
    {x : SL(n, F)} (hxD : (x : Matrix (Fin n) (Fin n) F) * D = D * x)
    (hdet : (partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F)).det = 1) :
    x ∈ longRootGroup D ⊔ longRootGroup (-D) := by
  have hsum := minusProj_add_plusProj (D := D) h2
  have hef := minusProj_mul_plusProj hD
  have hfe := plusProj_mul_minusProj hD
  have hprod := eq_mul_partOn_of_commute h2 hD hxD
  have hdetp : (partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F)).det = 1 := by
    have := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hdet, one_mul] at this
    rw [this]
    exact x.2
  let xmS : SL(n, F) := ⟨partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F), hdet⟩
  let xpS : SL(n, F) := ⟨partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F), hdetp⟩
  have hDe : D = plusProj D - minusProj D := eq_plusProj_sub_minusProj h2
  have h1D : (1 : Matrix (Fin n) (Fin n) F) + D = (2 : F) • plusProj D := by
    unfold plusProj
    rw [smul_smul, mul_inv_cancel₀ h2, one_smul]
  have h1D' : (1 : Matrix (Fin n) (Fin n) F) + -D = (2 : F) • minusProj D := by
    unfold minusProj
    rw [smul_smul, mul_inv_cancel₀ h2, one_smul, sub_eq_add_neg]
  have hxm : xmS ∈ longRootGroup D := by
    refine ⟨?_, ?_⟩
    · show partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F) * D = D *
        partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F)
      have e1 := partOn_mul_sub hsum hef hfe (x : Matrix (Fin n) (Fin n) F)
      have e2 := sub_mul_partOn hsum hef hfe (x : Matrix (Fin n) (Fin n) F)
      rw [← hDe] at e1 e2
      rw [e1, e2]
    · show partOn (minusProj D) (plusProj D) (x : Matrix (Fin n) (Fin n) F) * (1 + D) = 1 + D
      rw [h1D, Matrix.mul_smul, partOn_mul_right hef hfe hsum]
  have hxp : xpS ∈ longRootGroup (-D) := by
    refine ⟨?_, ?_⟩
    · show partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F) * (-D) = (-D) *
        partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F)
      have hsum' : plusProj D + minusProj D = 1 := (add_comm _ _).trans hsum
      have e1 := partOn_mul_sub hsum' hfe hef (x : Matrix (Fin n) (Fin n) F)
      have e2 := sub_mul_partOn hsum' hfe hef (x : Matrix (Fin n) (Fin n) F)
      have hDe' : -D = minusProj D - plusProj D := by
        calc -D = -(plusProj D - minusProj D) := by rw [← hDe]
          _ = minusProj D - plusProj D := neg_sub _ _
      rw [← hDe'] at e1 e2
      rw [e1, e2]
    · show partOn (plusProj D) (minusProj D) (x : Matrix (Fin n) (Fin n) F) * (1 + -D) = 1 + -D
      rw [h1D', Matrix.mul_smul, partOn_mul_right hfe hef ((add_comm _ _).trans hsum)]
  have hx' : x = xmS * xpS := Subtype.ext hprod.symm
  rw [hx']
  exact Subgroup.mul_mem_sup hxm hxp

theorem longRootGroup_inf_neg_eq_bot (h2 : (2 : F) ≠ 0) :
    longRootGroup D ⊓ longRootGroup (-D) = ⊥ := by
  refine eq_bot_iff.mpr fun x ⟨⟨_, hx1⟩, ⟨_, hx2⟩⟩ => ?_
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hsum : (x : Matrix (Fin n) (Fin n) F) * ((2 : F) • 1) = (2 : F) • 1 := by
    have : (2 : F) • (1 : Matrix (Fin n) (Fin n) F) = (1 + D) + (1 + -D) := by
      rw [two_smul]
      abel
    rw [this, Matrix.mul_add, hx1, hx2]
  rw [Matrix.mul_smul, Matrix.mul_one] at hsum
  exact smul_right_injective _ h2 hsum

end Linear

section Member

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem eq_one_of_pow_three_eq_one_of_natCard_three (hF : Nat.card F = 3) {d : F}
    (hd : d ^ 3 = 1) : d = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.pow_card d
  rwa [Fintype.card_eq_nat_card, hF, hd, eq_comm] at h1

end Member

section Main

variable {n : ℕ}

private theorem natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem isLongRootSL2_of_isClassicalMember3 (hn : 2 ≤ n)
    {L : Subgroup SL(n, GaloisField 3 1)} {z : SL(n, GaloisField 3 1)}
    (h : IsClassicalMember3 L z) (hO : classicalInvolutionOddCore L = ⊥) :
    IsLongRootSL2 hn L z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 3 1 with hFdef
  have hF3 : Nat.card F = 3 := natCard_galoisField_three
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF3]; decide)
  obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hO
  let e : SL(2, ZMod 3) ≃* L := eL.symm
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  set D : Matrix (Fin n) (Fin n) F := (z : Matrix (Fin n) (Fin n) F) with hDdef
  have hD : D * D = 1 := by
    rw [hDdef, ← Matrix.SpecialLinearGroup.coe_mul, hzz, Matrix.SpecialLinearGroup.coe_one]
  have hD' : (-D) * (-D) = 1 := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, hD]
  have hLC : ∀ x ∈ L, (x : Matrix (Fin n) (Fin n) F) * D = D * x := fun x hx => by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
    have h2' := congrArg Subtype.val h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2'
    exact h2'
  have hsum := minusProj_add_plusProj (D := D) h2
  have hef := minusProj_mul_plusProj hD
  have hfe := plusProj_mul_minusProj hD
  have hcube : ∀ y : SL(n, F), y ∈ L → y ^ 3 = 1 → y ∈ longRootGroup D ⊔ longRootGroup (-D) := by
    intro y hyL hy3
    have hyD := hLC y hyL
    refine mem_sup_longRootGroup_of_det_eq_one h2 hD hyD ?_
    set M : Matrix (Fin n) (Fin n) F := (y : Matrix (Fin n) (Fin n) F) with hM
    have hMe := commute_minusProj hyD
    have hMf := commute_plusProj hyD
    have hMMe : (M * M) * minusProj D = minusProj D * (M * M) := by
      rw [Matrix.mul_assoc, hMe, ← Matrix.mul_assoc, hMe, Matrix.mul_assoc]
    have hMMf : (M * M) * plusProj D = plusProj D * (M * M) := by
      rw [Matrix.mul_assoc, hMf, ← Matrix.mul_assoc, hMf, Matrix.mul_assoc]
    have hM3 : M * (M * M) = 1 := by
      rw [← pow_three, hM, ← Matrix.SpecialLinearGroup.coe_pow, hy3,
        Matrix.SpecialLinearGroup.coe_one]
    have h1 := partOn_mul hsum hef hfe hMe hMe hMf
    have h2' := partOn_mul hsum hef hfe hMe hMMe hMMf
    rw [hM3, partOn_one hsum hef, h1] at h2'
    have hd := congrArg Matrix.det h2'
    rw [Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
    exact eq_one_of_pow_three_eq_one_of_natCard_three hF3 (by rw [pow_three]; exact hd.symm)
  have hLsup : L ≤ longRootGroup D ⊔ longRootGroup (-D) := by
    intro x hx
    obtain ⟨g, hg⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨a, b, c, ha, hb, hc, rfl⟩ := sl2Three_exists_cubes g
    have hcub : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 →
        ((e y : L) : SL(n, F)) ∈ longRootGroup D ⊔ longRootGroup (-D) := fun y hy =>
      hcube _ (e y).2 (by rw [← Subgroup.coe_pow, ← map_pow, hy, map_one]; rfl)
    have hx' : x = ((e a : L) : SL(n, F)) * (e b : L) * (e c : L) := by
      have := congrArg Subtype.val hg
      rw [map_mul, map_mul] at this
      exact this.symm
    rw [hx']
    exact mul_mem (mul_mem (hcub a ha) (hcub b hb)) (hcub c hc)
  have hcomm : ∀ x ∈ longRootGroup D, ∀ y ∈ longRootGroup (-D), x * y = y * x :=
    fun x hx y hy => commute_longRootGroup_neg h2 hD hx hy
  have hinf : longRootGroup D ⊓ longRootGroup (-D) = ⊥ := longRootGroup_inf_neg_eq_bot h2
  have hAC : longRootGroup D ≤ Subgroup.centralizer ({z} : Set SL(n, F)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hx.1
  have hBC : longRootGroup (-D) ≤ Subgroup.centralizer ({z} : Set SL(n, F)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have := hx.1
    rw [Matrix.mul_neg, Matrix.neg_mul] at this
    exact neg_injective this
  have hsub : IsSubnormal L (longRootGroup D ⊔ longRootGroup (-D)) := by
    have := isSubnormal_inf h.subnormal (longRootGroup D ⊔ longRootGroup (-D))
    rwa [inf_eq_left.mpr hLsup, inf_eq_right.mpr (sup_le hAC hBC)] at this
  have hzA : z ∈ longRootGroup D := by
    refine ⟨rfl, ?_⟩
    show D * (1 + D) = 1 + D
    rw [Matrix.mul_add, Matrix.mul_one, hD, add_comm]
  obtain ⟨a, ha, P, hP, hAm⟩ := exists_longRootGroup_data h2 (by omega) hD
  obtain ⟨b, hb, P', hP', hAp⟩ := exists_longRootGroup_data h2 (by omega) hD'
  obtain ⟨eA⟩ := nonempty_mulEquiv_longRootGroup ha hAm
  obtain ⟨eB⟩ := nonempty_mulEquiv_longRootGroup hb hAp
  obtain ⟨e3⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF3
  have hB : Subsingleton (longRootGroup (-D)) ∨
      (CFSG.Open.IsQuasisimple (longRootGroup (-D)) ∧
        IsPGroup 2 (Subgroup.center (longRootGroup (-D)))) ∨
      Nonempty (SL(2, ZMod 3) ≃* longRootGroup (-D)) := by
    rcases Nat.lt_or_ge b 3 with hb3 | hb3
    · rcases Nat.lt_or_ge b 2 with hb2 | hb2
      · left
        have : Subsingleton SL(b, F) := subsingleton_sl_of_le_one (by omega)
        exact eB.surjective.subsingleton
      · right
        right
        obtain rfl : b = 2 := by omega
        exact ⟨e3.symm.trans eB⟩
    · right
      left
      obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
      have hq : CFSG.Open.IsQuasisimple SL(m + 1, F) :=
        open_isQuasisimple (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega))
      refine ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv eB.symm hq, ?_⟩
      exact (CenterExp.of_mulEquiv eB.symm
        (centerExp_specialLinear m 1 F (by rw [hF3]; norm_num))).isPGroup
  have hLA : L ≤ longRootGroup D :=
    le_of_isSubnormal_of_commute hcomm hinf e hLsup hsub hB h.mem h.ne_one hzA
  have hLA' : IsSubnormal L (longRootGroup D) := by
    have := isSubnormal_inf h.subnormal (longRootGroup D)
    rwa [inf_eq_left.mpr hLA, inf_eq_right.mpr hAC] at this
  have ha2 : a = 2 := by
    by_contra hne
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · have : Subsingleton SL(a, F) := subsingleton_sl_of_le_one (by omega)
      have hs : Subsingleton (longRootGroup D) := eA.surjective.subsingleton
      exact h.ne_one (congrArg Subtype.val (Subsingleton.elim (⟨z, hzA⟩ : longRootGroup D) 1))
    · obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
      have hq : CFSG.Open.IsQuasisimple SL(m + 1, F) :=
        open_isQuasisimple (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F (by omega))
      exact not_isQuasisimple_of_member3 e hLA hLA'
        (CFSG.ComponentClassification.Components.quasisimple_of_equiv eA.symm hq)
  subst ha2
  have hcard : Nat.card (longRootGroup D) ≤ 24 := by
    rw [← Nat.card_congr eA.toEquiv, Nat.card_congr e3.toEquiv, natCard_sl2Three]
  have hLeq : L = longRootGroup D := eq_of_le_of_natCard_le e hLA hcard
  refine ⟨P, ?_, ?_⟩
  · rw [hLeq]
    exact hAm
  · have hdiag : negBlock F n 0 =
        Matrix.diagonal (fun j : Fin n => if j.val < 2 then (-1 : F) else 1) := by
      rw [negBlock_eq_diagonal]
      congr 1
      funext j
      simp
    have hPP : (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
        1 := coe_mul_coe_inv P
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, hdiag,
      ← hP, Matrix.mul_assoc, hPP, Matrix.mul_one]

theorem classicalMembersFundamental3Tag_PSL : ClassicalMembersFundamental3Tag .PSL := by
  intro n hp hFT hadm L z hL hO
  have hn : 2 ≤ n := hadm.2.2.1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact RouteD.longRootSet_subset_fundamentalSubgroups_psl hn
    ⟨z, isLongRootSL2_of_isClassicalMember3 hn hL hO⟩

end Main

end CFSG.ClassicalInvolution.Q3
