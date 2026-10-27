module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreBasic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Quaternion
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7RTwin

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem isQuatSub_of_isSylow2In {K V : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hV : IsSylow2In V K) : IsQuatSub V := by
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_quaternion_sylow_of_witness hK.witness
    (AscL62.sylowOfIsSylow2In'' hV)
  exact ⟨r - 2, by omega, ⟨(Subgroup.subgroupOfEquivOfLe hV.1).symm.trans e⟩⟩

omit [Finite F] in
theorem forall_comm_of_oddQuotAut_eq_one {K : Subgroup F} {g : F}
    (hg : g ∈ Subgroup.normalizer (K : Set F)) (h : oddQuotAut K (conjOn K g hg) = 1) :
    ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K := by
  intro k hk
  have h1 : oddQuotAut K (conjOn K g hg) ((⟨k, hk⟩ : ↥K) : OddQuot K) =
      ((⟨k, hk⟩ : ↥K) : OddQuot K) := by
    rw [h]
    rfl
  rw [oddQuotAut_mk] at h1
  have h2 : conjOn K g hg ⟨k, hk⟩ * (⟨k, hk⟩ : ↥K)⁻¹ ∈ classicalInvolutionOddCore ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
      mul_inv_cancel]
  have hmem : ⁅g, k⁆ ∈ K := by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hg k).mp hk) (K.inv_mem hk)
  refine mem_oddCoreOf_iff.mpr ⟨hmem, ?_⟩
  convert h2 using 1
  apply Subtype.ext
  simp [conjOn_apply, commutatorElement_def]

theorem forall_comm_of_centralizes {K V : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hV : IsSylow2In V K) {g : F} (hg : g ∈ Subgroup.normalizer (K : Set F))
    (hc : ∀ q ∈ V, g * q = q * g) : ∀ k ∈ K, ⁅g, k⁆ ∈ oddCoreOf K :=
  forall_comm_of_oddQuotAut_eq_one hg (oddQuotAut_conjOn_eq_one hK.witness
    (AscL62.sylowOfIsSylow2In'' hV) hg (fun q hq => hc q hq))

theorem mem_of_isSylow2In {K V : Subgroup F} {z : F} (hKz : IsUniqueInvolution K z)
    (hV : IsSylow2In V K) (hQuat : IsQuatSub V) : z ∈ V := by
  have hQcard : 2 ≤ Nat.card V := by
    have := hQuat.eight_le
    omega
  exact AscL62.mem_of_uniqueInvolution_of_pGroup hKz hV.1 hV.2.1 hQcard

theorem exists_inverted {K R : Subgroup F} {z w : F} (hK : IsClassical2A7 ⊤ K z)
    (hR2 : IsPGroup 2 R) (hRK : IsSylow2In (R ⊓ K) K) (hwR : w ∈ R) (hw2 : w * w = 1)
    (hwN : w ∈ Subgroup.normalizer (K : Set F)) (hnt : ¬ ∀ k ∈ K, ⁅w, k⁆ ∈ oddCoreOf K) :
    ∃ κ ∈ R ⊓ K, κ * κ = z ∧ w⁻¹ * κ * w = κ⁻¹ := by
  classical
  have hKz : IsUniqueInvolution K z := isUniqueInvolution hK
  set Qs : Subgroup F := R ⊓ K with hQs
  have hQsK : Qs ≤ K := inf_le_right
  have hQs2 : IsPGroup 2 Qs := hR2.to_le inf_le_left
  have hQuat : IsQuatSub Qs := isQuatSub_of_isSylow2In hK hRK
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := id hQuat
  have hzQ : z ∈ Qs := mem_of_isSylow2In hKz hRK hQuat
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconjQ : ∀ x : F, x ∈ Qs → w⁻¹ * x * w ∈ Qs := by
    intro x hx
    refine ⟨R.mul_mem (R.mul_mem (R.inv_mem hwR) hx.1) hwR, ?_⟩
    exact (mem_conj_iff_of_mem_normalizer hwN x).mpr hx.2
  let τ : ↥Qs ≃* ↥Qs :=
    { toFun := fun x => ⟨w⁻¹ * x * w, hconjQ x x.2⟩
      invFun := fun x => ⟨w * x * w⁻¹, by
        have h1 := hconjQ x x.2
        rw [hwi] at h1
        simpa [hwi] using h1⟩
      left_inv := fun x => by
        apply Subtype.ext
        show w * (w⁻¹ * (x : F) * w) * w⁻¹ = x
        group
      right_inv := fun x => by
        apply Subtype.ext
        show w⁻¹ * (w * (x : F) * w⁻¹) * w = x
        group
      map_mul' := fun x y => by
        apply Subtype.ext
        show w⁻¹ * ((x : F) * y) * w = (w⁻¹ * x * w) * (w⁻¹ * y * w)
        group }
  have hτ2 : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show w⁻¹ * (w⁻¹ * (x : F) * w) * w = x
    rw [hwi]
    calc w * (w * (x : F) * w) * w = (w * w) * x * (w * w) := by group
      _ = x := by rw [hw2]; group
  have hτ1 : ∃ x, τ x ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hnt
    refine forall_comm_of_centralizes hK hRK hwN (fun q hq => ?_)
    have hr1 : w⁻¹ * q * w = q := congrArg Subtype.val (hcon ⟨q, hq⟩)
    calc w * q = w * (w⁻¹ * q * w) := by rw [hr1]
      _ = q * w := by group
  have hgen : ∀ H : Subgroup ↥Qs, (∀ x : ↥Qs, orderOf x = 4 → x ∈ H) → H = ⊤ := by
    intro H hH
    have : NeZero (2 ^ k₁) := ⟨by positivity⟩
    exact AscFusion.quaternion_generated_by_order_four eQ H hH
  have hzu : ∀ x : ↥Qs, x * x = 1 → x = 1 ∨ x = ⟨z, hzQ⟩ := by
    intro x hx
    have hxG : (x : F) * (x : F) = 1 := congrArg Subtype.val hx
    rcases hKz.unique (x : F) (hQsK x.2) hxG with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hz2 : (⟨z, hzQ⟩ : ↥Qs) * ⟨z, hzQ⟩ = 1 := Subtype.ext hKz.sq
  obtain ⟨κ', hκ'4, hκ'⟩ := AscFusion.exists_inverted_order_four ⟨z, hzQ⟩ hz2 (fun x => hQs2 x) hzu
    hgen τ hτ2 hτ1
  set κ : F := (κ' : F) with hκ
  have hκK : κ ∈ K := hQsK κ'.2
  have hκ4 : orderOf κ = 4 := by rw [hκ, Subgroup.orderOf_coe]; exact hκ'4
  refine ⟨κ, κ'.2, ?_, ?_⟩
  · have h1 : (κ * κ) * (κ * κ) = 1 := by
      have : κ ^ 4 = 1 := by rw [← hκ4]; exact pow_orderOf_eq_one κ
      calc (κ * κ) * (κ * κ) = κ ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (κ * κ) (K.mul_mem hκK hκK) h1 with h | h
    · exfalso
      have : orderOf κ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hκ4] at this
      omega
    · exact h
  · have := congrArg Subtype.val hκ'
    simpa [τ, hκ] using this

end CFSG.ClassicalInvolution.A7Core
