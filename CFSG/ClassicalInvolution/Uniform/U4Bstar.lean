module

public import CFSG.ClassicalInvolution.Uniform.U4Action
public import CFSG.ClassicalInvolution.Asc77.AscFusionS13

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem Mem3.exists_two_sq_elements {K V : Subgroup F} {z : F} (hK : Mem3 K z)
    (hV : IsSylow2In V K) :
    ∃ a₁ ∈ V, ∃ a₂ ∈ V, a₁ * a₁ = z ∧ a₂ * a₂ = z ∧ (a₁ * a₂) * (a₁ * a₂) ≠ 1 := by
  have hKz : IsUniqueInvolution K z := hK.isUniqueInvolution
  obtain ⟨k₁, hk₁, ⟨eQ⟩⟩ := hK.isQuatSub_of_isSylow2In hV
  have : NeZero (2 ^ k₁) := ⟨by positivity⟩
  have hn2 : 2 ≤ 2 ^ k₁ := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k₁ := Nat.pow_le_pow_right (by norm_num) hk₁
  have hsq : ∀ i : ZMod (2 * 2 ^ k₁), ((eQ.symm (QuaternionGroup.xa i) : ↥V) : F) *
      ((eQ.symm (QuaternionGroup.xa i) : ↥V) : F) = z := by
    intro i
    set x : ↥V := eQ.symm (QuaternionGroup.xa i) with hx
    have hx4 : orderOf x = 4 := by
      rw [hx, MulEquiv.orderOf_eq]
      exact QuaternionGroup.orderOf_xa i
    set a : F := (x : F) with ha
    have ha4 : orderOf a = 4 := by rw [ha, Subgroup.orderOf_coe]; exact hx4
    have haK : a ∈ K := hV.1 x.2
    have h1 : (a * a) * (a * a) = 1 := by
      have : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
      calc (a * a) * (a * a) = a ^ 4 := by simp [pow_succ, mul_assoc]
        _ = 1 := this
    rcases hKz.unique (a * a) (K.mul_mem haK haK) h1 with h | h
    · exfalso
      have : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [ha4] at this
      omega
    · exact h
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : ↥V) : F), (eQ.symm (QuaternionGroup.xa 0)).2,
    ((eQ.symm (QuaternionGroup.xa 1) : ↥V) : F), (eQ.symm (QuaternionGroup.xa 1)).2,
    hsq 0, hsq 1, ?_⟩
  intro h
  apply AscFusion.quaternion_pair_prod_sq_ne_one (n := 2 ^ k₁) hn2
  have h' : (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) *
      (eQ.symm (QuaternionGroup.xa 0) * eQ.symm (QuaternionGroup.xa 1)) = 1 := Subtype.ext h
  have := congrArg eQ h'
  simpa [map_mul] using this

namespace Mem3

variable {K M A B R : Subgroup F} {z : F}

theorem le_normalizer_of_same (hA : Mem3 A z) (hB : Mem3 B z) :
    A ≤ Subgroup.normalizer (B : Set F) := by
  by_cases h : B = A
  · subst h
    exact Subgroup.le_normalizer
  · exact (hB.twin_facts hA h).1

theorem commute_of_mem_inf_twin (hK : Mem3 K z) (hM : Mem3 M z) (hne : K ≠ M)
    (hR2 : IsPGroup 2 R) {q q' : F} (hq : q ∈ R ⊓ K) (hq' : q' ∈ R ⊓ M) : q * q' = q' * q := by
  obtain ⟨-, -, hc⟩ := hK.twin_facts hM hne
  have h1 : ⁅q, q'⁆ ∈ oddCoreOf K :=
    (hc (Subgroup.commutator_mem_commutator hq.2 hq'.2)).1
  have h2 : ⁅q, q'⁆ ∈ R := by
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem hq.1 hq'.1) (R.inv_mem hq.1)) (R.inv_mem hq'.1)
  have h4 : ⁅q, q'⁆ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
      (hR2.to_le (Subgroup.zpowers_le.mpr h2))
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

end Mem3

omit [Finite F] in
theorem inv_eq_mul_mul_of_orderOf_four {a : F} (ha4 : orderOf a = 4) : a⁻¹ = a * (a * a) := by
  have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  calc a⁻¹ = a⁻¹ * a ^ 4 := by rw [ha4', mul_one]
    _ = a⁻¹ * (a * (a * (a * a))) := by simp [pow_succ, mul_assoc]
    _ = a * (a * a) := inv_mul_cancel_left a _

omit [Finite F] in
theorem conjSub_sup_aux (g : F) (A B : Subgroup F) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B := Subgroup.map_sup _ _ _

theorem exists_quad_sylow {K : Subgroup F} {z a : F} (hK : Mem3 K z) (ha4 : orderOf a = 4)
    (haz : a * z = z * a) (hne : K ≠ conjSub (a * a) K) :
    ∃ R : Subgroup F, IsPGroup 2 R ∧ a ∈ R ∧ IsSylow2In (R ⊓ K) K ∧
      (∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub a K, q * q' = q' * q) ∧
      (∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub (a * a) K, q * q' = q' * q) ∧
      (∀ q ∈ R ⊓ K, ∀ q' ∈ R ⊓ conjSub a⁻¹ K, q * q' = q' * q) ∧
      ∀ q ∈ R ⊓ K, a * q * a⁻¹ ∈ R ⊓ conjSub a K := by
  classical
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_orderOf_four ha4
  have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
  have hainv : a⁻¹ = a * (a * a) := inv_eq_mul_mul_of_orderOf_four ha4
  have haaz : (a * a) * z = z * (a * a) := by
    rw [mul_assoc, haz, ← mul_assoc, haz, mul_assoc]
  have hK₁z : Mem3 (conjSub a K) z := hK.conj_of_commute haz
  have hK₂z : Mem3 (conjSub (a * a) K) z := hK.conj_of_commute haaz
  have hK₃z : Mem3 (conjSub a⁻¹ K) z := hK.conj_of_commute (inv_comm_of_comm haz)
  have hnaK : a ∉ Subgroup.normalizer (K : Set F) := fun h => hne (by
    have := conjSub_eq_of_mem_normalizer (Subgroup.mul_mem _ h h)
    exact this.symm)
  have hK01 : K ≠ conjSub a K := fun h => hnaK (AscHypOmega.mem_normalizer_of_conjSub_eq h.symm)
  have hK03 : K ≠ conjSub a⁻¹ K := fun h => hnaK (by
    have := (Subgroup.normalizer (K : Set F)).inv_mem
      (AscHypOmega.mem_normalizer_of_conjSub_eq h.symm)
    simpa using this)
  have hK12 : conjSub a K ≠ conjSub (a * a) K := fun h => hK01 (by
    have := congrArg (conjSub a⁻¹) h
    rwa [conjSub_inv_conjSub, ← conjSub_mul, show a⁻¹ * (a * a) = a by group] at this)
  have hK13 : conjSub a K ≠ conjSub a⁻¹ K := fun h => hne (by
    have := congrArg (conjSub a) h
    rw [conjSub_conjSub_inv, ← conjSub_mul] at this
    exact this.symm)
  have hK23 : conjSub (a * a) K ≠ conjSub a⁻¹ K := fun h => hK03 (by
    have := congrArg (conjSub a) h
    rw [conjSub_conjSub_inv, ← conjSub_mul, ← hainv] at this
    exact this.symm)
  set X : Subgroup F := K ⊔ conjSub a K ⊔ conjSub (a * a) K ⊔ conjSub a⁻¹ K with hX
  have hXN : ∀ {M : Subgroup F}, Mem3 M z → X ≤ Subgroup.normalizer (M : Set F) := by
    intro M hM
    exact sup_le (sup_le (sup_le (hK.le_normalizer_of_same hM) (hK₁z.le_normalizer_of_same hM))
      (hK₂z.le_normalizer_of_same hM)) (hK₃z.le_normalizer_of_same hM)
  have hconjX : conjSub a X = X := by
    have e1 : conjSub a (conjSub a K) = conjSub (a * a) K := (conjSub_mul a a K).symm
    have e2 : conjSub a (conjSub (a * a) K) = conjSub a⁻¹ K := by
      rw [← conjSub_mul, ← hainv]
    have e3 : conjSub a (conjSub a⁻¹ K) = K := conjSub_conjSub_inv a K
    rw [hX, conjSub_sup_aux, conjSub_sup_aux, conjSub_sup_aux, e1, e2, e3]
    ac_rfl
  have haX : a ∈ Subgroup.normalizer (X : Set F) := AscHypOmega.mem_normalizer_of_conjSub_eq hconjX
  set H : Subgroup F := X ⊔ Subgroup.zpowers a with hH
  have hHN : H ≤ Subgroup.normalizer (X : Set F) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haX)
  obtain ⟨R, hRH, haR'⟩ := IsSylow2In.exists_ge ha2 (le_sup_right : Subgroup.zpowers a ≤ H)
  have hR2 : IsPGroup 2 R := hRH.2.1
  have haR : a ∈ R := haR' (Subgroup.mem_zpowers a)
  have hRX : IsSylow2In (R ⊓ X) X := isSylow2In_inf_of_le_normalizer hRH le_sup_left hHN
  have hRK : IsSylow2In (R ⊓ K) K := by
    have hKX : K ≤ X := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    have := isSylow2In_inf_of_le_normalizer hRX hKX (hXN hK)
    rwa [inf_assoc, inf_eq_right.mpr hKX] at this
  refine ⟨R, hR2, haR, hRK, ?_, ?_, ?_, ?_⟩
  · intro q hq q' hq'
    exact hK.commute_of_mem_inf_twin hK₁z hK01 hR2 hq hq'
  · intro q hq q' hq'
    exact hK.commute_of_mem_inf_twin hK₂z hne hR2 hq hq'
  · intro q hq q' hq'
    exact hK.commute_of_mem_inf_twin hK₃z hK03 hR2 hq hq'
  · intro q hq
    refine ⟨R.mul_mem (R.mul_mem haR hq.1) (R.inv_mem haR), ?_⟩
    exact conj_mem_conjSub hq.2

omit [Finite F] in
theorem conj_comm_aux {a x y : F} (h : x * y = y * x) :
    (a * x * a⁻¹) * (a * y * a⁻¹) = (a * y * a⁻¹) * (a * x * a⁻¹) := by
  calc (a * x * a⁻¹) * (a * y * a⁻¹) = a * (x * y) * a⁻¹ := by group
    _ = a * (y * x) * a⁻¹ := by rw [h]
    _ = (a * y * a⁻¹) * (a * x * a⁻¹) := by group

end CFSG.ClassicalInvolution.Uniform.U4
