module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.ANineSylowInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.InnerCoverAltBlock

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup CFSG.LocalAnalysis.ComponentInitial

private theorem cycleType_eq_two_two {σ : Perm (Fin 9)} (h : σ ^ 2 = 1)
    (hs : σ.support.card = 2 * 2) : σ.cycleType = {2, 2} := by
  rw [← multiset_replicate_two_two, cycleType_eq_replicate_iff_of_sq_eq_one h]
  exact hs

theorem cycleType_aNineSylowGenA : (aNineSylowGenA : Perm (Fin 9)).cycleType = {2, 2} :=
  cycleType_eq_two_two (by decide) (by decide)

theorem cycleType_aNineSylowGenB : (aNineSylowGenB : Perm (Fin 9)).cycleType = {2, 2} :=
  cycleType_eq_two_two (by decide) (by decide)

theorem cycleType_aNineSylowGenC : (aNineSylowGenC : Perm (Fin 9)).cycleType = {2, 2} :=
  cycleType_eq_two_two (by decide) (by decide)

theorem cycleType_aNineSylowGenA_mul_genB :
    ((aNineSylowGenA : Perm (Fin 9)) * (aNineSylowGenB : Perm (Fin 9))).cycleType = {2, 2} :=
  cycleType_eq_two_two (by decide) (by decide)

theorem cycleType_aNineSylowGenA_mul_genC :
    ((aNineSylowGenA : Perm (Fin 9)) * (aNineSylowGenC : Perm (Fin 9))).cycleType =
      {2, 2, 2, 2} := by
  rw [← multiset_replicate_four_two, cycleType_eq_replicate_iff_of_sq_eq_one (by decide)]
  decide

theorem isConj_aNineSylowGenB {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {2, 2}) : IsConj aNineSylowGenB g :=
  isConj_of_commute_of_sign_eq_neg_one
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_aNineSylowGenB.trans hg.symm))
    (Perm.sign_swap (show (0 : Fin 9) ≠ 2 by decide))
    (show swap (0 : Fin 9) 2 * (aNineSylowGenB : Perm (Fin 9)) =
      (aNineSylowGenB : Perm (Fin 9)) * swap 0 2 by decide)

theorem isConj_aNineSylowGenA_mul_genC {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    IsConj (aNineSylowGenA * aNineSylowGenC) g :=
  isConj_of_commute_of_sign_eq_neg_one
    (Perm.isConj_iff_cycleType_eq.mpr (cycleType_aNineSylowGenA_mul_genC.trans hg.symm))
    (Perm.sign_swap (show (0 : Fin 9) ≠ 1 by decide))
    (show swap (0 : Fin 9) 1 * ((aNineSylowGenA : Perm (Fin 9)) *
        (aNineSylowGenC : Perm (Fin 9))) =
      (aNineSylowGenA : Perm (Fin 9)) * (aNineSylowGenC : Perm (Fin 9)) * swap 0 1 by decide)

theorem ne_one_of_cycleType_eq {g : alternatingGroup (Fin 9)} {m : Multiset ℕ}
    (hg : (g : Perm (Fin 9)).cycleType = m) (hm : m ≠ 0) : g ≠ 1 := by
  rintro rfl
  rw [OneMemClass.coe_one, Perm.cycleType_one] at hg
  exact hm hg.symm

private def cycleL : alternatingGroup (Fin 9) :=
  ⟨swap 4 5 * swap 4 6, Perm.mem_alternatingGroup.mpr (by decide)⟩

private def cycleR : alternatingGroup (Fin 9) :=
  ⟨swap 4 6 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

private theorem commute_of_coe {σ τ : alternatingGroup (Fin 9)}
    (h : (σ : Perm (Fin 9)) * (τ : Perm (Fin 9)) = (τ : Perm (Fin 9)) * σ) : Commute σ τ :=
  Subtype.ext h

private theorem cycleL_pow_three : cycleL ^ 3 = 1 :=
  Subtype.ext (show (swap 4 5 * swap 4 6 : Perm (Fin 9)) ^ 3 = 1 by decide)

private theorem cycleR_pow_three : cycleR ^ 3 = 1 :=
  Subtype.ext (show (swap 4 6 * swap 6 7 : Perm (Fin 9)) ^ 3 = 1 by decide)

private theorem cycleL_mul_cycleR : cycleL * cycleR = aNineSylowGenC :=
  Subtype.ext (show (swap 4 5 * swap 4 6) * (swap 4 6 * swap 6 7) =
    (swap 4 5 * swap 6 7 : Perm (Fin 9)) by decide)

private theorem commute_cycles {g : alternatingGroup (Fin 9)}
    (hg : g = aNineSylowGenA ∨ g = aNineSylowGenB) : Commute g cycleL ∧ Commute g cycleR := by
  rcases hg with rfl | rfl
  · exact ⟨commute_of_coe (by decide), commute_of_coe (by decide)⟩
  · exact ⟨commute_of_coe (by decide), commute_of_coe (by decide)⟩

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J) (e : J ⧸ center J ≃* alternatingGroup (Fin 9))
include hJ

theorem isPGroup_ker_proj : IsPGroup 2 (proj e).ker := by
  rw [ker_proj]
  exact hJ.isPGroup_center

theorem existsUnique_lift_pow_three {g : alternatingGroup (Fin 9)} (hg : g ^ 3 = 1) :
    ∃! x : J, proj e x = g ∧ x ^ 3 = 1 := by
  obtain ⟨y, rfl⟩ := proj_surjective e g
  obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one (ker_proj e).le (hJ.isPGroup_ker_proj e) hg
  exact ⟨x, ⟨hx, hx3⟩, fun x' hx' => eq_of_pow_three_eq_one_of_map_eq (ker_proj e).le
    (hJ.isPGroup_ker_proj e) hx'.2 hx3 (hx'.1.trans hx.symm)⟩

theorem existsUnique_lift_of_isThreeCycle {g : alternatingGroup (Fin 9)}
    (hg : (g : Perm (Fin 9)).IsThreeCycle) : ∃! x : J, proj e x = g ∧ orderOf x = 3 := by
  have hg3 : g ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, OneMemClass.coe_one, ← hg.orderOf, pow_orderOf_eq_one])
  obtain ⟨x, ⟨hx, hx3⟩, hu⟩ := hJ.existsUnique_lift_pow_three e hg3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨x, ⟨hx, orderOf_eq_prime hx3 ?_⟩, fun x' hx' => hu x' ⟨hx'.1, ?_⟩⟩
  · rintro rfl
    rw [map_one] at hx
    exact hg.ne_one (by rw [← hx, OneMemClass.coe_one])
  · rw [← hx'.2]
    exact pow_orderOf_eq_one x'

theorem commute_of_pow_three_eq_one {u x : J} (hx : x ^ 3 = 1)
    (h : Commute (proj e u) (proj e x)) : Commute u x := by
  have hkc : u * x * u⁻¹ * x⁻¹ ∈ center J := (proj_eq_one_iff e).mp (by
    simp only [map_mul, map_inv, h.eq, mul_inv_cancel_right, mul_inv_cancel])
  have hkx : Commute (u * x * u⁻¹ * x⁻¹) x := (Subgroup.mem_center_iff.mp hkc x).symm
  have hk3 : (u * x * u⁻¹ * x⁻¹) ^ 3 = 1 := by
    have h3 : (u * x * u⁻¹) ^ 3 = 1 := by rw [conj_pow, hx, mul_one, mul_inv_cancel]
    rwa [show u * x * u⁻¹ = (u * x * u⁻¹ * x⁻¹) * x by group, hkx.mul_pow, hx, mul_one] at h3
  have hk1 : u * x * u⁻¹ * x⁻¹ = 1 := by
    calc u * x * u⁻¹ * x⁻¹
        = (u * x * u⁻¹ * x⁻¹) ^ 3 * ((u * x * u⁻¹ * x⁻¹) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hk3, hJ.sq_eq_one_of_mem_center hkc, inv_one, one_mul]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk1
  exact hk1

private theorem exists_lift_genB_sq : ∃ y : J, proj e y = aNineSylowGenB ∧ y ^ 2 = zbar J := by
  have : Finite J := hJ.finite
  have : Group.IsPerfect J := hJ.perfect
  have hne : (proj e).ker ≠ ⊥ := by
    rw [ker_proj, Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨zbar J, hJ.zbar_mem_center⟩, fun h => hJ.zbar_ne_one (congrArg Subtype.val h)⟩
  obtain ⟨x, z, hx, -, hz, hz1, -, hxz⟩ := CFSG.QuasithinUnique.Ch1.alt_cover_structure (m := 7)
    (by norm_num) (proj e) (proj_surjective e) (ker_proj e).le (hJ.isPGroup_ker_proj e) hne
  refine ⟨x 0 * x 1, ?_, ?_⟩
  · rw [map_mul, hx, hx]
    apply Subtype.ext
    rw [coe_altThreeCycle_mul (by decide)]
    decide
  · rw [hxz 0 1 (by decide)]
    exact hJ.eq_zbar_of_mem_center hz hz1

theorem sq_eq_zbar_of_cycleType_two_two {x : J}
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2}) :
    x ^ 2 = zbar J := by
  obtain ⟨y, hy, hy2⟩ := hJ.exists_lift_genB_sq e
  rw [← hy2]
  refine hJ.sq_eq_of_isConj e ?_ (by rw [hy2]; exact hJ.zbar_mem_center)
  rw [hy]
  exact (isConj_aNineSylowGenB hx).symm

theorem orderOf_eq_four_of_cycleType_two_two {x : J}
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2}) :
    orderOf x = 4 := by
  have h2 := hJ.sq_eq_zbar_of_cycleType_two_two e hx
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := x)
    (by rw [pow_one, h2]; exact hJ.zbar_ne_one)
    (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, h2, hJ.zbar_sq])
  rw [h]
  norm_num

theorem commute_of_proj_eq_genC {u w : J}
    (hu : proj e u = aNineSylowGenA ∨ proj e u = aNineSylowGenB)
    (hw : proj e w = aNineSylowGenC) : Commute u w := by
  obtain ⟨x₁, hx₁, hx₁3⟩ := (hJ.existsUnique_lift_pow_three e cycleL_pow_three).exists
  obtain ⟨x₂, hx₂, hx₂3⟩ := (hJ.existsUnique_lift_pow_three e cycleR_pow_three).exists
  obtain ⟨hc₁, hc₂⟩ := commute_cycles hu
  have hk : (x₁ * x₂)⁻¹ * w ∈ center J :=
    (proj_eq_proj_iff e).mp (by rw [map_mul, hx₁, hx₂, cycleL_mul_cycleR, hw])
  rw [← mul_inv_cancel_left (x₁ * x₂) w]
  refine ((hJ.commute_of_pow_three_eq_one e hx₁3 ?_).mul_right
    (hJ.commute_of_pow_three_eq_one e hx₂3 ?_)).mul_right (Subgroup.mem_center_iff.mp hk u)
  · rw [hx₁]
    exact hc₁
  · rw [hx₂]
    exact hc₂

private theorem exists_lift_genAC_sq :
    ∃ x : J, proj e x = aNineSylowGenA * aNineSylowGenC ∧ x ^ 2 = 1 := by
  obtain ⟨a, ha⟩ := proj_surjective e aNineSylowGenA
  obtain ⟨w, hw⟩ := proj_surjective e aNineSylowGenC
  refine ⟨a * w, by rw [map_mul, ha, hw], ?_⟩
  rw [(hJ.commute_of_proj_eq_genC e (Or.inl ha) hw).mul_pow,
    hJ.sq_eq_zbar_of_cycleType_two_two e (by rw [ha]; exact cycleType_aNineSylowGenA),
    hJ.sq_eq_zbar_of_cycleType_two_two e (by rw [hw]; exact cycleType_aNineSylowGenC),
    hJ.zbar_mul_zbar]

theorem sq_eq_one_of_cycleType_two_two_two_two {x : J}
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    x ^ 2 = 1 := by
  obtain ⟨y, hy, hy2⟩ := hJ.exists_lift_genAC_sq e
  rw [hJ.sq_eq_of_isConj e (v := y) (by rw [hy]; exact (isConj_aNineSylowGenA_mul_genC hx).symm)
    (by rw [hy2]; exact (center J).one_mem), hy2]

theorem orderOf_eq_two_of_cycleType_two_two_two_two {x : J}
    (hx : ((proj e x : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    orderOf x = 2 ∧ x ∉ center J := by
  have hne := ne_one_of_cycleType_eq hx (by decide)
  refine ⟨orderOf_eq_prime (hJ.sq_eq_one_of_cycleType_two_two_two_two e hx) ?_,
    fun h => hne ((proj_eq_one_iff e).mpr h)⟩
  rintro rfl
  exact hne (map_one _)

theorem conj_eq_mul_zbar_of_genB_of_genA {u x : J} (hu : proj e u = aNineSylowGenB)
    (hx : proj e x = aNineSylowGenA) : u * x * u⁻¹ = x * zbar J := by
  have hx2 : x * x = zbar J := by
    rw [← sq]
    exact hJ.sq_eq_zbar_of_cycleType_two_two e (by rw [hx]; exact cycleType_aNineSylowGenA)
  have hu2 : u * u = zbar J := by
    rw [← sq]
    exact hJ.sq_eq_zbar_of_cycleType_two_two e (by rw [hu]; exact cycleType_aNineSylowGenB)
  have hxu2 : x * u * (x * u) = zbar J := by
    rw [← sq]
    exact hJ.sq_eq_zbar_of_cycleType_two_two e (by
      rw [map_mul, hx, hu, Subgroup.coe_mul]
      exact cycleType_aNineSylowGenA_mul_genB)
  have hxinv : x⁻¹ = x * zbar J :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hx2, hJ.zbar_mul_zbar])
  have huinv : u⁻¹ = u * zbar J :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hu2, hJ.zbar_mul_zbar])
  calc u * x * u⁻¹ = x⁻¹ * (x * u * (x * u)) * zbar J := by rw [huinv]; group
    _ = x⁻¹ := by rw [hxu2, mul_assoc, hJ.zbar_mul_zbar, mul_one]
    _ = x * zbar J := hxinv

theorem conj_eq_mul_zbar_of_genB_of_genAC {u x : J} (hu : proj e u = aNineSylowGenB)
    (hx : proj e x = aNineSylowGenA * aNineSylowGenC) : u * x * u⁻¹ = x * zbar J := by
  obtain ⟨a, ha⟩ := proj_surjective e aNineSylowGenA
  have hw : proj e (a⁻¹ * x) = aNineSylowGenC := by
    rw [map_mul, map_inv, ha, hx, inv_mul_cancel_left]
  have hcomm := hJ.commute_of_proj_eq_genC e (Or.inr hu) hw
  calc u * x * u⁻¹ = u * a * u⁻¹ * (u * (a⁻¹ * x) * u⁻¹) := by group
    _ = a * zbar J * (a⁻¹ * x) := by
      rw [hJ.conj_eq_mul_zbar_of_genB_of_genA e hu ha, hcomm.eq, mul_inv_cancel_right]
    _ = a * ((a⁻¹ * x) * zbar J) := by rw [mul_assoc, (hJ.commute_zbar (a⁻¹ * x)).eq]
    _ = x * zbar J := by group

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
