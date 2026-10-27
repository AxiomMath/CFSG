module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12C
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1C
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Q8
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinOddCent
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoM12B
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu
open CFSG.ComponentClassification.M12Cover

theorem quat_conj_eq_inv : ∀ p q : QuaternionGroup 2, q * q = QuaternionGroup.a 2 → p ≠ 1 →
    p ≠ q → p ≠ q * q → p ≠ q * q * q → p * q * p⁻¹ = q⁻¹ := by
  decide

theorem mem_q8L_quat : ∀ p : QuaternionGroup 2,
    p ∈ q8L (QuaternionGroup.a 1) (QuaternionGroup.xa 0) := by
  decide

theorem card_quat : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

@[expose] def r1 : ↥NativeSporadic.M12 := ⟨m12Rep1, rep1_mem⟩

@[simp] theorem coe_r1 :
    (r1 : Equiv.Perm (Fin 12)) = m12Rep1 := rfl

structure Setting {G : Type} [Group G] (N : Subgroup G) (Δ : Set (Subgroup G)) where
  e : ↥N ≃* ↥NativeSporadic.M12
  cent : Subgroup.centralizer (N : Set G) = ⊥
  hyp : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ
  mem : ∀ K ∈ Δ, ∀ z : G, IsUniqueInvolution K z → z ∈ N

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem coe_symm_a_two {K : Subgroup G} (eK : ↥K ≃* QuaternionGroup 2) {z : G}
    (hz : IsUniqueInvolution K z) : ((eK.symm (QuaternionGroup.a 2) : ↥K) : G) = z := by
  have hsq : ((eK.symm (QuaternionGroup.a 2) : ↥K) : G) * (eK.symm (QuaternionGroup.a 2) : ↥K) =
      1 := by
    rw [← Subgroup.coe_mul, ← map_mul,
      show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by decide, map_one,
      Subgroup.coe_one]
  have hne : ((eK.symm (QuaternionGroup.a 2) : ↥K) : G) ≠ 1 := by
    intro h1
    have h2 : eK.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h1
    rw [MulEquiv.symm_apply_eq, map_one] at h2
    exact absurd h2 (by decide)
  exact (hz.unique _ (eK.symm _).2 hsq).resolve_left hne


namespace Setting

theorem isPGroup (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ) : IsPGroup 2 ↥K := by
  obtain ⟨⟨z, hz⟩, -⟩ := S.hyp.hyp.omega1 K hK
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  exact PhilipHall.Frame.isPGroup_of_oddCent S.hyp.hyp hK hz
    (oddCoreImg_centralizer_eq_bot S.e S.cent (S.mem K hK z hz) hz2) (S.hyp.twoGroup K hK)

theorem exists_equiv (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ) :
    Nonempty (↥K ≃* QuaternionGroup 2) :=
  S.hyp.quat K hK K (TL4.Vtx.isSylow2In_self (S.isPGroup hK))

theorem card_eq (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ) : Nat.card ↥K = 8 := by
  obtain ⟨eK⟩ := S.exists_equiv hK
  rw [Nat.card_congr eK.toEquiv, card_quat]

theorem pow_four (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ) {k : G} (hk : k ∈ K) :
    k ^ 4 = 1 := by
  obtain ⟨eK⟩ := S.exists_equiv hK
  have h1 : eK ⟨k, hk⟩ ^ 4 = 1 := by
    generalize eK ⟨k, hk⟩ = q
    revert q
    decide
  rw [← map_pow, ← map_one eK] at h1
  have h2 := congrArg Subtype.val (eK.injective h1)
  simpa using h2

omit [Finite G] in
theorem exists_sq_mem (S : Setting N Δ) (ι : QuaternionGroup 2 →* G) :
    ∃ q : QuaternionGroup 2, q * q = QuaternionGroup.a 2 ∧ ι q ∈ N := by
  by_cases h1 : ι (QuaternionGroup.a 1) ∈ N
  · exact ⟨_, by decide, h1⟩
  by_cases h2 : ι (QuaternionGroup.xa 0) ∈ N
  · exact ⟨_, by decide, h2⟩
  refine ⟨QuaternionGroup.a 1 * QuaternionGroup.xa 0, by decide, ?_⟩
  rw [map_mul]
  exact mul_mem_of_not_mem S.e S.cent h1 h2

theorem exists_conj_rep (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ) {z : G}
    (hz : IsUniqueInvolution K z) : ∃ c : G, c * z * c⁻¹ = (S.e.symm r1 : G) := by
  obtain ⟨eK⟩ := S.exists_equiv hK
  let ι : QuaternionGroup 2 →* G := K.subtype.comp eK.symm.toMonoidHom
  obtain ⟨q, hq, hqN⟩ := S.exists_sq_mem ι
  have hzN := S.mem K hK z hz
  have hqz : ι q * ι q = z := by
    rw [← map_mul, hq]
    exact coe_symm_a_two eK hz
  have hsq : ((S.e ⟨ι q, hqN⟩ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * S.e ⟨ι q, hqN⟩ =
      S.e ⟨z, hzN⟩ := by
    rw [← Subgroup.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext hqz
  have hzo : orderOf ((S.e ⟨z, hzN⟩ : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  obtain ⟨c, hc, hcz⟩ := MF163.exists_conj_rep1 (S.e ⟨z, hzN⟩).2 hzo (S.e ⟨ι q, hqN⟩).2 hsq
  have h1 : S.e ⟨z, hzN⟩ = ⟨c, hc⟩ * r1 * (⟨c, hc⟩ : ↥NativeSporadic.M12)⁻¹ := Subtype.ext hcz
  have h2 : (⟨z, hzN⟩ : ↥N) = S.e.symm ⟨c, hc⟩ * S.e.symm r1 * (S.e.symm ⟨c, hc⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← h1, MulEquiv.symm_apply_apply]
  refine ⟨(S.e.symm ⟨c, hc⟩ : G)⁻¹, ?_⟩
  have h3 := congrArg Subtype.val h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
  rw [h3]
  group

theorem le_of_rep (S : Setting N Δ) {K : Subgroup G} (hK : K ∈ Δ)
    (hz : IsUniqueInvolution K (S.e.symm r1 : G)) : K ≤ N := by
  obtain ⟨eK⟩ := S.exists_equiv hK
  let ι : QuaternionGroup 2 →* G := K.subtype.comp eK.symm.toMonoidHom
  obtain ⟨q, hq, hqN⟩ := S.exists_sq_mem ι
  intro x hxK
  by_contra hxN
  obtain ⟨g, hg⟩ := exists_phi_eq_beta S.e S.cent hxN
  set p := eK ⟨x, hxK⟩ with hp
  have hxp : ι p = x := by simp [ι, hp]
  have hq1 : ι 1 ∈ N := by rw [map_one]; exact N.one_mem
  have hq2 : ι (q * q) ∈ N := by rw [map_mul]; exact N.mul_mem hqN hqN
  have hq3 : ι (q * q * q) ∈ N := by
    rw [map_mul, map_mul]
    exact N.mul_mem (N.mul_mem hqN hqN) hqN
  have hinv : p * q * p⁻¹ = q⁻¹ := by
    refine quat_conj_eq_inv p q hq ?_ ?_ ?_ ?_ <;> intro hpe <;> apply hxN <;> rw [← hxp, hpe]
    exacts [hq1, hqN, hq2, hq3]
  have hxi : x * ι q * x⁻¹ = (ι q)⁻¹ := by
    have h1 := congrArg ι hinv
    rwa [map_mul, map_mul, map_inv, map_inv, hxp] at h1
  set i : ↥N := ⟨ι q, hqN⟩ with hi
  have hΦi : phi S.e x (S.e i) = (S.e i)⁻¹ := by
    rw [phi_apply, ← map_inv]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hxi
  have hxz : x * (S.e.symm r1 : G) = (S.e.symm r1 : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isUniqueInvolution hz hxK)
  have hΦr : phi S.e x r1 = r1 := by
    have h1 : phi S.e x (S.e (S.e.symm r1)) = S.e (S.e.symm r1) := by
      rw [phi_apply]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hxz, mul_inv_cancel_right]
    rwa [MulEquiv.apply_symm_apply] at h1
  have hβr : beta r1 = r1 := by
    have h1 : r1 = m12a := Subtype.ext m12Rep1_eq
    rw [h1, beta_m12a]
  have hgr : (g : Equiv.Perm (Fin 12)) * m12Rep1 = m12Rep1 * g := by
    rw [hg, MulAut.mul_apply, hβr, MulAut.conj_apply] at hΦr
    have h1 := congrArg Subtype.val hΦr
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_r1] at h1
    calc (g : Equiv.Perm (Fin 12)) * m12Rep1 = g * m12Rep1 * (g : Equiv.Perm (Fin 12))⁻¹ * g := by
          group
      _ = m12Rep1 * g := by rw [h1]
  have hi2 : ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) * S.e i = m12Rep1 := by
    have h1 : i * i = S.e.symm r1 := by
      apply Subtype.ext
      show ι q * ι q = _
      rw [← map_mul, hq]
      exact coe_symm_a_two eK hz
    rw [← Subgroup.coe_mul, ← map_mul, h1, MulEquiv.apply_symm_apply, coe_r1]
  obtain ⟨b, hb⟩ := qL_root (S.e i).2 hi2
  have h1 := qL_inv hb
  have h2 := qL_conj g.2 hgr (qL_beta hb)
  have h4 : (g : Equiv.Perm (Fin 12)) * (beta (S.e i) : Equiv.Perm (Fin 12)) *
      (g : Equiv.Perm (Fin 12))⁻¹ = ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))⁻¹ := by
    have h5 := congrArg Subtype.val hΦi
    rw [hg, MulAut.mul_apply, MulAut.conj_apply] at h5
    simpa using h5
  rw [h4] at h2
  have h5 : ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))⁻¹ = 1 ∨
      ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12))⁻¹ = m12Rep1 := by
    cases b
    · exact qL_meet h1 h2
    · exact qL_meet h2 h1
  rcases h5 with h5 | h5
  · rw [inv_eq_one] at h5
    rw [h5, one_mul] at hi2
    exact rep1_ne_one hi2.symm
  · have h6 : ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)) = m12Rep1 := by
      rw [← inv_inv ((S.e i : ↥NativeSporadic.M12) : Equiv.Perm (Fin 12)), h5, rep1_inv]
    rw [h6, rep1_mul_self] at hi2
    exact rep1_ne_one hi2.symm

end Setting

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12
