module

public import CFSG.ClassicalInvolution.Q3.Q3T6BSwap
public import CFSG.ClassicalInvolution.Q3.Q3T6BFree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem isPGroup_closure_pair {x d : F} (hx2 : x * x = 1) (hd2 : d * d = 1)
    (hxd : x * d = d * x) : IsPGroup 2 (Subgroup.closure ({x, d} : Set F)) := by
  have hE : IsMulCommutative (Subgroup.closure ({x, d} : Set F)) :=
    Subgroup.isMulCommutative_closure (by
      intro a ha b hb _
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      exacts [Commute.refl _, hxd, hxd.symm, Commute.refl _])
  have hsq : ∀ g ∈ Subgroup.closure ({x, d} : Set F), g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hx2
      · exact hd2
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        congrArg Subtype.val
          ((IsMulCommutative.is_comm : Std.Commutative (α := ↥(Subgroup.closure ({x, d} : Set F)))
            (· * ·)).comm ⟨a, ha⟩ ⟨b, hb⟩)
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  intro g
  refine ⟨1, ?_⟩
  have hg : g * g = 1 := Subtype.ext (hsq g.1 g.2)
  rw [pow_one, pow_two]
  exact hg

theorem exists_inverting_commuting {Y : Subgroup F} {x y d : F} (hY : Mem3 Y y) (hx2 : x * x = 1)
    (hd2 : d * d = 1) (hxd : x * d = d * x) (hxN : x ∈ Subgroup.normalizer (Y : Set F))
    (hdN : d ∈ Subgroup.normalizer (Y : Set F))
    (hout : ∀ a ∈ Y, orderOf a = 4 → a * x ≠ x * a)
    (hdtriv : ∀ k ∈ Y, ⁅d, k⁆ ∈ oddCoreOf Y) :
    ∃ κ ∈ Y, κ * x * κ⁻¹ = x * y ∧ κ * d = d * κ := by
  classical
  have hxy : x * y = y * x := Mem3.comm_of_mem_normalizer hY hxN
  set T : Subgroup F := Subgroup.closure ({x, d} : Set F) with hT
  have hxT : x ∈ T := Subgroup.subset_closure (Set.mem_insert x _)
  have hdT : d ∈ T := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hT2 : IsPGroup 2 T := isPGroup_closure_pair hx2 hd2 hxd
  have hTN : T ≤ Subgroup.normalizer (Y : Set F) :=
    (Subgroup.closure_le _).mpr (by
      rintro a (rfl | rfl)
      · exact hxN
      · exact hdN)
  set H : Subgroup F := Y ⊔ T with hH
  have hYH : Y ≤ H := le_sup_left
  have hHN : H ≤ Subgroup.normalizer (Y : Set F) := sup_le Subgroup.le_normalizer hTN
  obtain ⟨R, hRH, hTR⟩ := Asc77.IsSylow2In.exists_ge hT2 (le_sup_right : T ≤ H)
  have hR2 : IsPGroup 2 R := hRH.2.1
  have hxR : x ∈ R := hTR hxT
  have hdR : d ∈ R := hTR hdT
  have hRY : IsSylow2In (R ⊓ Y) Y := isSylow2In_inf_of_le_normalizer hRH hYH hHN
  have hnt : ¬ ∀ k ∈ Y, ⁅x, k⁆ ∈ oddCoreOf Y := by
    intro hall
    obtain ⟨a, haR, ha2⟩ := exists_sq_eq_of_isSylow2In hY hRY
    have hy2 : y * y = 1 := hY.mul_self
    have haY : a ∈ Y := haR.2
    have h1 : ⁅x, a⁆ ∈ oddCoreOf Y := hall a haY
    have h2 : ⁅x, a⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hxR haR.1) (R.inv_mem hxR)) (R.inv_mem haR.1)
    have h3 : ⁅x, a⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h1
        (hR2.to_le (Subgroup.zpowers_le.mpr h2))
    have hxa : a * x = x * a := (commutatorElement_eq_one_iff_mul_comm.mp h3).symm
    have hap : IsPGroup 2 (Subgroup.zpowers a) := hR2.to_le (Subgroup.zpowers_le.mpr haR.1)
    have h4 : 4 ≤ orderOf a := four_le_orderOf hap (by rw [ha2]; exact hY.ne_one)
    have h4' : orderOf a ∣ 4 := by
      apply orderOf_dvd_of_pow_eq_one
      calc a ^ 4 = (a * a) * (a * a) := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
        _ = 1 := by rw [ha2, hy2]
    exact hout a haY (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h4') h4) hxa
  obtain ⟨κ, hκR, hκ2, hκx⟩ := hY.exists_inverted hR2 hRY hxR hx2 hxN hnt
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  refine ⟨κ, hκR.2, ?_, ?_⟩
  ·
    have h5 : x * κ * x = κ⁻¹ := by
      have := hκx
      rwa [hxi] at this
    have h6 : x * κ⁻¹ * x⁻¹ = κ := by
      have h7 : (x * κ * x)⁻¹ = κ := by rw [h5, inv_inv]
      have h8 : (x * κ * x)⁻¹ = x⁻¹ * κ⁻¹ * x⁻¹ := by group
      rw [hxi] at h8 ⊢
      rw [← h8]
      exact h7
    calc κ * x * κ⁻¹ = κ * (x * κ⁻¹ * x⁻¹) * x := by group
      _ = κ * κ * x := by rw [h6]
      _ = y * x := by rw [hκ2]
      _ = x * y := hxy.symm
  ·
    have h1 : ⁅d, κ⁆ ∈ oddCoreOf Y := hdtriv κ hκR.2
    have h2 : ⁅d, κ⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hdR hκR.1) (R.inv_mem hdR)) (R.inv_mem hκR.1)
    have h3 : ⁅d, κ⁆ = 1 :=
      eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) h1
        (hR2.to_le (Subgroup.zpowers_le.mpr h2))
    exact (commutatorElement_eq_one_iff_mul_comm.mp h3).symm

variable {X : Subgroup F} {x y : F} {R : Subgroup F}

end CFSG.ClassicalInvolution.Q3.Q3T6B
