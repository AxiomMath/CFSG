module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerTits

public section


attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {X : Type*} [Group X]

theorem cube_mul_eq {g m : X} (hg : g ^ 3 = 1) :
    (g * m) ^ 3 = g * m * g⁻¹ * (g * g * m * (g * g)⁻¹) * m := by
  have h1 : (g * g)⁻¹ = g := by
    rw [inv_eq_iff_mul_eq_one, ← hg, pow_succ, pow_two]
  rw [h1]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]

theorem mul_eq_mul_conj (a b a' b' : X) :
    a' * b' = a * b * (b⁻¹ * (a⁻¹ * a') * b * (b⁻¹ * b')) := by
  group

theorem conj_conj_eq (g m : X) : g * (g * m * g⁻¹) * g⁻¹ = g * g * m * (g * g)⁻¹ := by
  group

theorem conj_mul_eq (a b m : X) : a * b * m * (a * b)⁻¹ = a * (b * m * b⁻¹) * a⁻¹ := by
  group

theorem inv_conj_conj_eq (t m : X) : t⁻¹ * (t * m * t⁻¹) * t⁻¹⁻¹ = m := by
  group

end Generic

theorem fix_of_mem_triKer {j : Fin 2} {k : Shat} (hk : k ∈ triKer j) {v : CVert}
    (hv : v ∈ ({cv0, cw0, cu j} : Set CVert)) : cvMul v k = v := by
  rcases hv with rfl | rfl | rfl
  · exact mem_vStab.1 hk.1.1
  · exact mem_vStab.1 hk.1.2
  · exact mem_vStab.1 hk.2

theorem mem_triKer_of_fix {j : Fin 2} {k : Shat}
    (h : ∀ v ∈ ({cv0, cw0, cu j} : Set CVert), cvMul v k = v) : k ∈ triKer j :=
  ⟨⟨mem_vStab.2 (h cv0 (Or.inl rfl)), mem_vStab.2 (h cw0 (Or.inr (Or.inl rfl)))⟩,
    mem_vStab.2 (h (cu j) (Or.inr (Or.inr rfl)))⟩

theorem conj_mem_triKer {j : Fin 2} {t k : Shat} (ht : t ∈ triStab j) (hk : k ∈ triKer j) :
    t * k * t⁻¹ ∈ triKer j := by
  refine mem_triKer_of_fix fun v hv => ?_
  have h1 : cvMul v t ∈ ({cv0, cw0, cu j} : Set CVert) := ((mem_cvSetStab.1 ht) v).2 hv
  rw [cvMul_mul, cvMul_mul, fix_of_mem_triKer hk h1, cvMul_inv_cancel]

theorem conj_mem_HS_iff_of_vStab {t x : Shat} (ht : t ∈ vStab cv0) (hx : x ∈ vStab cv0) :
    t * x * t⁻¹ ∈ HS ↔ x ∈ HS := by
  have hN : (commutator (vStab cv0)).Normal := commutator_normal ⊤ ⊤
  have h1 : t * x * t⁻¹ ∈ HS ↔ ((⟨t, ht⟩ : vStab cv0) * ⟨x, hx⟩ * (⟨t, ht⟩ : vStab cv0)⁻¹) ∈
      commutator (vStab cv0) :=
    coe_mem_HS_iff ((⟨t, ht⟩ : vStab cv0) * ⟨x, hx⟩ * (⟨t, ht⟩ : vStab cv0)⁻¹)
  refine h1.trans (Iff.trans ⟨fun h => ?_, fun h => hN.conj_mem _ h _⟩
    (coe_mem_HS_iff ⟨x, hx⟩).symm)
  exact (congrArg (· ∈ commutator (vStab cv0)) (inv_conj_conj_eq _ _)).mp
    (hN.conj_mem _ h (⟨t, ht⟩ : vStab cv0)⁻¹)

theorem conj_mem_HS_iff_of_triKer {j : Fin 2} {t k : Shat}
    (ht : t ∈ vStab cv0 ∨ t ∈ cEdgeStab) (hk : k ∈ triKer j) :
    t * k * t⁻¹ ∈ HS ↔ k ∈ HS := by
  rcases ht with ht | ht
  · exact conj_mem_HS_iff_of_vStab ht hk.1.1
  · exact conj_mem_HS_iff ht hk.1

theorem inv_mul_mem_triKer_of_isTriA {j : Fin 2} {a a' : Shat} (ha : IsTriA j a)
    (ha' : IsTriA j a') : a⁻¹ * a' ∈ triKer j :=
  ⟨⟨mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq ha.1, ha'.1]),
    mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq ha.2.2, ha'.2.2])⟩,
    mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq ha.2.1, ha'.2.1])⟩

theorem inv_mul_mem_triKer_of_isTriB {j : Fin 2} {b b' : Shat} (hb : IsTriB j b)
    (hb' : IsTriB j b') : b⁻¹ * b' ∈ triKer j :=
  ⟨⟨mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq hb.2.1, hb'.2.1]),
    mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq hb.1, hb'.1])⟩,
    mem_vStab.2 (by rw [cvMul_mul, cvMul_inv_of_eq hb.2.2, hb'.2.2])⟩

theorem conj_mul_mem_triKer {j : Fin 2} {a b : Shat} (ha : IsTriA j a) (hb : IsTriB j b)
    {k : Shat} (hk : k ∈ triKer j) :
    a * b * k * (a * b)⁻¹ ∈ triKer j ∧ (a * b * k * (a * b)⁻¹ ∈ HS ↔ k ∈ HS) := by
  have h1 := conj_mem_triKer (mem_triStab_of_isTriB hb) hk
  have e := conj_mul_eq a b k
  refine ⟨e ▸ conj_mem_triKer (mem_triStab_of_isTriA ha) h1, ?_⟩
  rw [e]
  exact (conj_mem_HS_iff_of_triKer (Or.inl (mem_vStab.2 ha.1)) h1).trans
    (conj_mem_HS_iff_of_triKer (Or.inr (swap_mem_cEdgeStab hb.1 hb.2.1)) hk)

theorem pow_three_mem_HS_iff {j : Fin 2} {a b a' b' : Shat} (ha : IsTriA j a)
    (hb : IsTriB j b) (hab : (a * b) ^ 3 = 1) (ha' : IsTriA j a') (hb' : IsTriB j b') :
    (a' * b') ^ 3 ∈ HS ↔ (a⁻¹ * a' ∈ HS ↔ b⁻¹ * b' ∈ HS) := by
  have hk₁ := inv_mul_mem_triKer_of_isTriA ha ha'
  have hk₂ := inv_mul_mem_triKer_of_isTriB hb hb'
  have hbinvT : b⁻¹ ∈ triStab j := inv_mem (mem_triStab_of_isTriB hb)
  have hbinvE : b⁻¹ ∈ cEdgeStab := inv_mem (swap_mem_cEdgeStab hb.1 hb.2.1)
  have hc : b⁻¹ * (a⁻¹ * a') * b⁻¹⁻¹ ∈ triKer j := conj_mem_triKer hbinvT hk₁
  have hcH : b⁻¹ * (a⁻¹ * a') * b⁻¹⁻¹ ∈ HS ↔ a⁻¹ * a' ∈ HS :=
    conj_mem_HS_iff_of_triKer (Or.inr hbinvE) hk₁
  rw [inv_inv] at hc hcH
  obtain ⟨m, hm⟩ : ∃ m, m = b⁻¹ * (a⁻¹ * a') * b * (b⁻¹ * b') := ⟨_, rfl⟩
  have hmK : m ∈ triKer j := hm ▸ mul_mem hc hk₂
  have hmH : m ∈ HS ↔ (a⁻¹ * a' ∈ HS ↔ b⁻¹ * b' ∈ HS) := by
    rw [hm]
    exact (mul_mem_HS_iff hc.1.1 hk₂.1.1).trans (iff_congr hcH Iff.rfl)
  obtain ⟨hm1K, -⟩ := conj_mul_mem_triKer ha hb hmK
  obtain ⟨hm2K, hm2H⟩ := conj_mul_mem_triKer ha hb hm1K
  have e2 := conj_conj_eq (a * b) m
  rw [e2] at hm2K hm2H
  have e3 : (a' * b') ^ 3 = a * b * m * (a * b)⁻¹ *
      (a * b * (a * b) * m * (a * b * (a * b))⁻¹) * m :=
    (congrArg (· ^ 3) ((mul_eq_mul_conj a b a' b').trans (congrArg _ hm.symm))).trans
      (cube_mul_eq hab)
  have hXY : a * b * m * (a * b)⁻¹ * (a * b * (a * b) * m * (a * b * (a * b))⁻¹) ∈ HS :=
    (mul_mem_HS_iff hm1K.1.1 hm2K.1.1).2 hm2H.symm
  rw [e3]
  exact ((mul_mem_HS_iff (mul_mem hm1K.1.1 hm2K.1.1) hmK.1.1).trans (iff_true_left hXY)).trans hmH

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
