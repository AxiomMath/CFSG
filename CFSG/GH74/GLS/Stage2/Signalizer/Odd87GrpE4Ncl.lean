module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpSwap

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

variable {A : Type} [Group A] [Finite A]

theorem mem_of_pow_p_mem {p : ℕ} (hp : p.Prime) {T M : Subgroup A}
    (hTp : ∀ t ∈ T, ∀ m : ℕ, t ^ (p ^ m) = 1 → t = 1) {t : A} (ht : t ∈ T) {m : ℕ}
    (h : t ^ (p ^ m) ∈ M) : t ∈ M := by
  have hcop : Nat.Coprime (p ^ m) (orderOf t) := by
    refine Nat.Coprime.pow_left m ?_
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr ?_
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hpos : 0 < orderOf t := orderOf_pos t
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      omega
    have hord : orderOf (t ^ c) = p := by
      rw [orderOf_pow_of_dvd hc0 ⟨p, by rw [hc]; ring⟩, hc, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hc0)]
    have hone := hTp (t ^ c) (T.pow_mem ht _) 1 (by rw [pow_one, ← hord]; exact pow_orderOf_eq_one _)
    rw [hone, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hr]
  exact M.pow_mem h r

theorem ncl_eq_sup_of_normal {p : ℕ} (hp : p.Prime) {X J : Subgroup A}
    (hXp : IsPGroup p ↥X) (hop : pCore p A = ⊥) (hJ : IsComponent J) (hJn : J.Normal)
    (hJK : J ≤ ncl X)
    (hcomp : ∀ J' : Subgroup A, IsComponent J' → J' ≤ ncl X → J' = J)
    (hF : ∀ q : ℕ, q.Prime → X ≤ centralizer ((pCore q A : Subgroup A) : Set A))
    (hP : (J ⊔ centralizer (J : Set A) ⊔ X).Normal) : ncl X = J ⊔ X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hTz, hTp⟩ := ncl_cent_facts hp hXp hop hJ hJn hcomp hF
  set K : Subgroup A := ncl X with hK
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have := hJn
  set C : Subgroup A := centralizer (J : Set A) with hC
  have hCn : C.Normal := normal_centralizer_of_normal J
  have hXK : X ≤ K := Subgroup.le_normalClosure
  have hKle : K ≤ J ⊔ C ⊔ X :=
    Subgroup.normalClosure_le_normal (N := J ⊔ C ⊔ X) (le_sup_right : X ≤ J ⊔ C ⊔ X)
  have hdec : ∀ k ∈ K, ∃ j ∈ J, ∃ t ∈ K ⊓ C, ∃ x ∈ X, k = j * t * x := by
    intro k hk
    have hk' : k ∈ (((J ⊔ C) ⊔ X : Subgroup A) : Set A) := hKle hk
    rw [Subgroup.normal_mul (J ⊔ C) X] at hk'
    obtain ⟨m, hm, x, hx, rfl⟩ := hk'
    have hcomm : ∀ j ∈ J, ∀ c' ∈ C, j * c' = c' * j := fun j hj c' hc' =>
      Subgroup.mem_centralizer_iff.mp hc' j hj
    obtain ⟨j, hj, c', hc', rfl⟩ := exists_mul_of_mem_sup hcomm hm
    refine ⟨j, hj, c', ⟨?_, hc'⟩, x, hx, rfl⟩
    have : c' = j⁻¹ * (j * c' * x) * x⁻¹ := by group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem (hJK hj)) hk) (K.inv_mem (hXK hx))
  have hgen : ∀ g ∈ Group.conjugatesOfSet (X : Set A), g ∈ J ⊔ X := by
    intro g hg
    obtain ⟨b, hb, hbg⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨c0, rfl⟩ := isConj_iff.mp hbg
    have hgK : c0 * b * c0⁻¹ ∈ K := hKn.conj_mem b (hXK hb) c0
    obtain ⟨m0, hm0⟩ := hXp ⟨b, hb⟩
    have hb' : b ^ (p ^ m0) = 1 := by simpa using congrArg Subtype.val hm0
    have hgp : (c0 * b * c0⁻¹) ^ (p ^ m0) = 1 := by rw [conj_pow, hb']; group
    obtain ⟨j, hj, t, ht, x, hx, hdecg⟩ := hdec _ hgK
    have hcomm_tx : t * x = x * t := hTz t ht x (hXK hx)
    have hmK : j * x ∈ K := K.mul_mem (hJK hj) (hXK hx)
    have hcomm_tm : Commute t (j * x) := hTz t ht (j * x) hmK
    have hgeq : c0 * b * c0⁻¹ = (j * x) * t := by
      rw [hdecg, mul_assoc, hcomm_tx, ← mul_assoc]
    have hpow : (c0 * b * c0⁻¹) ^ (p ^ m0) = (j * x) ^ (p ^ m0) * t ^ (p ^ m0) := by
      rw [hgeq, (hcomm_tm.symm).mul_pow]
    have htM : t ^ (p ^ m0) ∈ J ⊔ X := by
      have h1 : t ^ (p ^ m0) = ((j * x) ^ (p ^ m0))⁻¹ := by
        rw [hgp] at hpow
        exact eq_inv_of_mul_eq_one_right hpow.symm
      rw [h1]
      exact inv_mem (Subgroup.pow_mem _ (Subgroup.mul_mem_sup hj hx) _)
    have htM' : t ∈ J ⊔ X := mem_of_pow_p_mem hp hTp ht htM
    rw [hgeq]
    exact mul_mem (Subgroup.mul_mem_sup hj hx) htM'
  have hKM : K ≤ J ⊔ X := by
    show Subgroup.normalClosure (X : Set A) ≤ J ⊔ X
    rw [Subgroup.normalClosure]
    exact (Subgroup.closure_le (J ⊔ X)).mpr hgen
  exact le_antisymm hKM (sup_le hJK hXK)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
