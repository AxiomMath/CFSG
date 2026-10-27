module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Lift
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinSpAut
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem T1_mul_self : T1 K * T1 K = 1 :=
  sp_ext (by rw [Subgroup.coe_mul, Units.val_mul, coe_T1, blk_mul]; simp [blk_one_one])

omit [Finite K] in
theorem u1_mul_self : u1 K * u1 K = 1 := by rw [u1, ← map_mul, T1_mul_self, map_one]

theorem eq_one_or_conj_of_fix_X0 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (β : MulAut (StatedProj (StatedSp 2 K))) (hβ : ∀ x ∈ X0 K, β x = x) :
    β = 1 ∨ β = MulAut.conj (u1 K) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨-, hform⟩ := RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2
  obtain ⟨A, σ, rfl⟩ := hform β
  set τ := conjSp 2 K A * fieldSp 2 K σ with hτdef
  have hτ : ∀ x, (SymplecticHigher.conjAut 2 K A * fieldAut 2 K σ) (proj 2 K x) =
      proj 2 K (τ x) := proj_lift A σ
  have : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
  have := Group.IsPerfect.range ((blkSL K).comp (MonoidHom.inl SL(2, K) SL(2, K)))
  have := Group.IsPerfect.range ((blkSL K).comp (MonoidHom.inr SL(2, K) SL(2, K)))
  have h1 := lift_fix_of_perfect τ _ hτ ((blkSL K).comp (MonoidHom.inl _ _)).range
    fun m hm => hβ _ (by obtain ⟨g, rfl⟩ := hm; exact (mem_X0 h2).mpr ⟨_, rfl⟩)
  have h₂ := lift_fix_of_perfect τ _ hτ ((blkSL K).comp (MonoidHom.inr _ _)).range
    fun m hm => hβ _ (by obtain ⟨g, rfl⟩ := hm; exact (mem_X0 h2).mpr ⟨_, rfl⟩)
  rcases TwinFr.sp4_aut_fix hodd τ (by
      rintro g h (rfl | rfl)
      · exact h₂ _ ⟨h, rfl⟩
      · exact h1 _ ⟨g, rfl⟩) with h | h
  · left
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := proj_surjective y
    rw [hτ, h, MulAut.one_apply, MulAut.one_apply]
  · right
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := proj_surjective y
    rw [hτ, h, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl

theorem noQ8Fix_X0 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    NoQ8Fix (StatedProj (StatedSp 2 K)) (X0 K) :=
  noQ8Fix_of_dichotomy ∅ (fun _ h => h.elim) fun β hβ => Or.inr (by
    rcases eq_one_or_conj_of_fix_X0 hodd h4 β hβ with rfl | rfl
    · exact mul_one 1
    · rw [← map_mul, u1_mul_self, map_one])

omit [Finite K] in
theorem X0_eq_sup (h2 : (2 : K) ≠ 0) : X0 K = E1 K ⊔ E2 K := by
  refine le_antisymm (fun x hx => ?_) (sup_le (E1_le_X0 h2) (E2_le_X0 h2))
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_X0 h2 hx
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem isPerfect_sl2_prod (h4 : 4 ≤ Nat.card K) : Group.IsPerfect (SL(2, K) × SL(2, K)) := by
  have h := (sl2_isPerfect (F := K) h4).commutator_eq_top
  refine ⟨?_⟩
  rw [_root_.commutator_def] at h ⊢
  rw [← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, h]

theorem isPerfect_X0 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect (X0 K) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have : Group.IsPerfect (SL(2, K) × SL(2, K)) := isPerfect_sl2_prod h4
  have hX : X0 K = ((proj 2 K).comp (blkSL K)).range := by
    ext x
    rw [mem_X0 h2]
    rfl
  rw [hX]
  exact Group.IsPerfect.range _

theorem sq_eq_one_of_central_E1 (hodd : Odd (Nat.card K)) {e : StatedProj (StatedSp 2 K)}
    (he : e ∈ E1 K) (hc : ∀ a ∈ E1 K, e * a = a * e) : e * e = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hZ : (⟨e, he⟩ : E1 K) ∈ Subgroup.center (E1 K) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
  rw [mem_center_iff_of_equiv_sl2 (E1Equiv h2).symm, mem_center_sl2_iff] at hZ
  have h1 : (E1Equiv h2).symm ⟨e, he⟩ * (E1Equiv h2).symm ⟨e, he⟩ = 1 := by
    rcases hZ with h | h <;> rw [h]
    · exact mul_one 1
    · exact Subtype.ext (by simp)
  have := congrArg Subtype.val ((E1Equiv h2).symm.injective (by rw [map_mul, h1, map_one] :
    (E1Equiv h2).symm (⟨e, he⟩ * ⟨e, he⟩) = (E1Equiv h2).symm 1))
  exact this

theorem sq_eq_one_of_central_E2 (hodd : Odd (Nat.card K)) {e : StatedProj (StatedSp 2 K)}
    (he : e ∈ E2 K) (hc : ∀ a ∈ E2 K, e * a = a * e) : e * e = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hZ : (⟨e, he⟩ : E2 K) ∈ Subgroup.center (E2 K) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2).symm
  rw [mem_center_iff_of_equiv_sl2 (E2Equiv h2).symm, mem_center_sl2_iff] at hZ
  have h1 : (E2Equiv h2).symm ⟨e, he⟩ * (E2Equiv h2).symm ⟨e, he⟩ = 1 := by
    rcases hZ with h | h <;> rw [h]
    · exact mul_one 1
    · exact Subtype.ext (by simp)
  have := congrArg Subtype.val ((E2Equiv h2).symm.injective (by rw [map_mul, h1, map_one] :
    (E2Equiv h2).symm (⟨e, he⟩ * ⟨e, he⟩) = (E2Equiv h2).symm 1))
  exact this

theorem noOddNormal_X0 (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) : NoOddNormal (X0 K) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  rw [X0_eq_sup h2]
  refine noOddNormal_sup (fun a ha b hb => commute_E1_E2 ha hb)
    (noOddNormal_of_equiv_sl2 hodd h4 (E1Equiv h2).symm)
    (noOddNormal_of_equiv_sl2 hodd h4 (E2Equiv h2).symm) fun z hz hzc hzo => ?_
  rw [← X0_eq_sup h2] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_X0 h2 hz
  have haa := sq_eq_one_of_central_E1 hodd ha fun c hc => by
    have h1 := hzc c (Subgroup.mem_sup_left hc)
    have h3 : b * c = c * b := (commute_E1_E2 hc hb).symm
    calc a * c = a * c * b * b⁻¹ := by group
      _ = c * (a * b) * b⁻¹ := by rw [mul_assoc a c b, ← h3, ← mul_assoc, h1]
      _ = c * a := by group
  have hbb := sq_eq_one_of_central_E2 hodd hb fun c hc => by
    have h1 := hzc c (Subgroup.mem_sup_right hc)
    have h3 : a * c = c * a := commute_E1_E2 ha hc
    calc b * c = a⁻¹ * (a * b * c) := by group
      _ = a⁻¹ * (c * (a * b)) := by rw [h1]
      _ = c * b := by rw [← mul_assoc c a b, ← h3]; group
  have hsq : (a * b) * (a * b) = 1 := by
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * a * (b * b) := by rw [← commute_E1_E2 ha hb]; group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hord : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hsq])
  rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hzo
    exact absurd hzo (by decide)

end CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4
