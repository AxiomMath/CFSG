module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412Sfus
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG

@[expose] def Fv {G : Type} [Group G] (x v : G) : Set G :=
  {t | t * v = v * t ∧ t * t = 1 ∧ IsConj x t ∧ IsConj x (t * v)}

@[expose] def Ev {G : Type} [Group G] (x v : G) (S : Subgroup G) : Subgroup G :=
  Subgroup.closure ({v} ∪ (Fv x v ∩ (S : Set G)))

variable {G : Type} [Group G]

theorem Fv_conj {x v t g : G} (hv : g * v = v * g) (ht : t ∈ Fv x v) : g * t * g⁻¹ ∈ Fv x v := by
  obtain ⟨htv, ht2, hxt, hxtv⟩ := ht
  have hgv : g * v * g⁻¹ = v := by rw [hv]; group
  have e : (g * t * g⁻¹) * v = g * (t * v) * g⁻¹ := by
    calc (g * t * g⁻¹) * v = (g * t * g⁻¹) * (g * v * g⁻¹) := by rw [hgv]
      _ = g * (t * v) * g⁻¹ := by group
  refine ⟨?_, ?_, hxt.trans (isConj_iff.2 ⟨g, rfl⟩), ?_⟩
  · rw [e, htv]
    calc g * (v * t) * g⁻¹ = (g * v * g⁻¹) * (g * t * g⁻¹) := by group
      _ = v * (g * t * g⁻¹) := by rw [hgv]
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  · rw [e]
    exact hxtv.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem Fv_mul_v {x v t : G} (hv2 : v * v = 1) (ht : t ∈ Fv x v) : t * v ∈ Fv x v := by
  obtain ⟨htv, ht2, hxt, hxtv⟩ := ht
  refine ⟨?_, ?_, hxtv, ?_⟩
  · calc t * v * v = (t * v) * v := rfl
      _ = (v * t) * v := by rw [htv]
      _ = v * (t * v) := by group
  · calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [← htv]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [ht2, hv2, one_mul]
  · have : t * v * v = t := by rw [mul_assoc, hv2, mul_one]
    rw [this]
    exact hxt

end CFSG.GH74.GLS.Th2.P412

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem tt_mul_x {p w : G} : tt a p w * x = tt a p (w * z) := by
  unfold tt
  rw [← F.a_z_a]
  group

theorem tt_mul_z [Finite G] {p w : G} (hw : w ∈ T ⊓ K) : tt a p w * z = tt a (p * z) w := by
  unfold tt
  have hc : z * (a⁻¹ * w * a) = (a⁻¹ * w * a) * z := F.comm_PP' F.z_mem hw
  calc p * (a⁻¹ * w * a) * z = p * ((a⁻¹ * w * a) * z) := by group
    _ = p * (z * (a⁻¹ * w * a)) := by rw [hc]
    _ = p * z * (a⁻¹ * w * a) := by group

theorem tt_mul_v [Finite G] {p w : G} (hw : w ∈ T ⊓ K) :
    tt a p w * (z * x) = tt a (p * z) (w * z) := by
  have h1 : tt a p w * (z * x) = tt a p w * z * x := by group
  rw [h1, F.tt_mul_z hw]
  unfold tt
  rw [← F.a_z_a]
  group

theorem tt_inj [Finite G] {u u' w w' : G} (hu : u ∈ T ⊓ K) (hu' : u' ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hw' : w' ∈ T ⊓ K) (h : tt a u w = tt a u' w') : u = u' ∧ w = w' := by
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj hu hu'
    (conj_mem_conj (K := K) (T := T) (a := a) hw) (conj_mem_conj (K := K) (T := T) (a := a) hw') h
  exact ⟨h1, mul_left_cancel (mul_right_cancel h2)⟩

theorem exists_invol_not_mem_R [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) :
    ∃ s₁ ∈ T ⊓ K, s₁ * s₁ = 1 ∧ s₁ ∉ conjugate (T ⊓ CxK x K) a⁻¹ := by
  by_contra hcon
  push Not at hcon
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hle : T ⊓ K ≤ conjugate (T ⊓ CxK x K) a⁻¹ := by
    refine F.core.P_d8.le_closure_involutions.trans ?_
    rw [Subgroup.closure_le]
    rintro u ⟨hu, hu2⟩
    exact hcon u hu hu2
  have h1 := Subgroup.card_le_of_le hle
  rw [F.core.P_d8.card_eq, hR.2.2] at h1
  omega

theorem invol_not_mem_R_eq [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {s₁ p : G} (hs₁ : s₁ ∈ T ⊓ K) (hs₁2 : s₁ * s₁ = 1)
    (hs₁R : s₁ ∉ conjugate (T ⊓ CxK x K) a⁻¹) (hp : p ∈ T ⊓ K) (hp2 : p * p = 1)
    (hpR : p ∉ conjugate (T ⊓ CxK x K) a⁻¹) : p = s₁ ∨ p = z * s₁ := by
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have hs₁1 : s₁ ≠ 1 := fun h => hs₁R (h ▸ one_mem _)
  have hs₁z : s₁ ≠ z := fun h => hs₁R (h ▸ hzR)
  have hp1 : p ≠ 1 := fun h => hpR (h ▸ one_mem _)
  have hpz : p ≠ z := fun h => hpR (h ▸ hzR)
  obtain ⟨V₁, hV₁P, hV₁el, hV₁4, hs₁V₁⟩ := F.core.P_d8.exists_four_containing hs₁ hs₁2
  obtain ⟨V₂, hV₂P, hV₂el, hV₂4, hpV₂⟩ := F.core.P_d8.exists_four_containing hp hp2
  have hV₁' : IsFourSub (T ⊓ K) V₁ := ⟨hV₁P, hV₁el, hV₁4⟩
  have hV₂' : IsFourSub (T ⊓ K) V₂ := ⟨hV₂P, hV₂el, hV₂4⟩
  have hV₁R : V₁ ≠ conjugate (T ⊓ CxK x K) a⁻¹ := fun h => hs₁R (h ▸ hs₁V₁)
  have hV₂R : V₂ ≠ conjugate (T ⊓ CxK x K) a⁻¹ := fun h => hpR (h ▸ hpV₂)
  have heq : V₁ = V₂ := F.klein_unique_other hV₁' hR hV₂' hV₁R hV₂R
  have hpV₁ : p ∈ V₁ := by rw [heq]; exact hpV₂
  rcases F.four_eq hV₁' hs₁V₁ hs₁1 hs₁z p hpV₁ with h | h | h | h
  · exact absurd h hp1
  · exact absurd h hpz
  · exact Or.inl h
  · exact Or.inr h

theorem zs_T [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {t : G} (htT : t ∈ T) (ht2 : t * t = 1) (hxt : IsConj x t)
    (hxtv : IsConj x (t * (z * x))) :
    t = x ∨ t = z ∨ ∃ p ∈ T ⊓ K, ∃ w ∈ T ⊓ K, p * p = 1 ∧ w * w = 1 ∧
      p ∉ conjugate (T ⊓ CxK x K) a⁻¹ ∧ w ∉ conjugate (T ⊓ CxK x K) a⁻¹ ∧ t = tt a p w := by
  have hxv : ¬ IsConj x (z * x) :=
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have ht' : t ∈ (T ⊓ K) ⊔ conjugate (T ⊓ K) a := F.T_eq ▸ htT
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute F.core.comm_P_conj ht'
  have hcomm : p * q = q * p := F.core.comm_P_conj p hp q hq
  have hsq : (p * p) * (q * q) = 1 * 1 := by
    calc (p * p) * (q * q) = p * (p * q) * q := by group
      _ = p * (q * p) * q := by rw [hcomm]
      _ = (p * q) * (p * q) := by group
      _ = 1 * 1 := by rw [← hpq, ht2]; simp
  obtain ⟨hp2, hq2⟩ := eq_of_mul_eq_of_inf_eq_bot F.core.P_inf_conj
    (Subgroup.mul_mem _ hp hp) (one_mem _) (Subgroup.mul_mem _ hq hq) (one_mem _) hsq
  have hwP : a * q * a⁻¹ ∈ T ⊓ K := mem_conjugate_iff'.1 hq
  have hw2 : (a * q * a⁻¹) * (a * q * a⁻¹) = 1 := by
    calc (a * q * a⁻¹) * (a * q * a⁻¹) = a * (q * q) * a⁻¹ := by group
      _ = 1 := by rw [hq2]; group
  have hqw : q = a⁻¹ * (a * q * a⁻¹) * a := by group
  have hut : t = tt a p (a * q * a⁻¹) := by
    unfold tt
    rw [← hqw]
    exact hpq
  generalize a * q * a⁻¹ = w at hwP hw2 hut
  have hz2 : z * z = 1 := F.z_sq
  by_cases hp1 : p = 1
  · by_cases hw1 : w = 1
    · exfalso
      have ht1 : t = 1 := by rw [hut, hp1, hw1]; unfold tt; group
      rw [ht1] at hxt
      exact F.x_ne (isConj_one_left.1 hxt)
    · by_cases hwz : w = z
      · left
        rw [hut, hp1, hwz]
        unfold tt
        rw [F.a_z_a, one_mul]
      · exfalso
        have hwzP : w * z ∈ T ⊓ K := Subgroup.mul_mem _ hwP F.z_mem
        have hwzc : w * z = z * w := F.z_central w hwP
        have hwz2 : (w * z) * (w * z) = 1 := by
          calc (w * z) * (w * z) = w * (z * w) * z := by group
            _ = w * (w * z) * z := by rw [← hwzc]
            _ = (w * w) * (z * z) := by group
            _ = 1 := by rw [hw2, hz2, one_mul]
        have hwz1 : w * z ≠ 1 := by
          intro h
          apply hwz
          rw [mul_eq_one_iff_eq_inv.1 h]
          exact inv_eq_of_mul_eq_one_right hz2
        have h1 : IsConj (tt a z (w * z)) (z * x) :=
          F.isConj_tt_v_of_left F.z_mem hwzP hz2 hwz2 F.z_ne hwz1 (F.psi_R hzR)
        have h2 : t * (z * x) = tt a z (w * z) := by
          rw [hut, hp1, F.tt_mul_v hwP, one_mul]
        rw [h2] at hxtv
        exact hxv (hxtv.trans h1)
  · by_cases hw1 : w = 1
    · by_cases hpz : p = z
      · right; left
        rw [hut, hw1, hpz]
        unfold tt
        group
      · exfalso
        have hpzP : p * z ∈ T ⊓ K := Subgroup.mul_mem _ hp F.z_mem
        have hpzc : p * z = z * p := F.z_central p hp
        have hpz2 : (p * z) * (p * z) = 1 := by
          calc (p * z) * (p * z) = p * (z * p) * z := by group
            _ = p * (p * z) * z := by rw [← hpzc]
            _ = (p * p) * (z * z) := by group
            _ = 1 := by rw [hp2, hz2, one_mul]
        have hpz1 : p * z ≠ 1 := by
          intro h
          apply hpz
          rw [mul_eq_one_iff_eq_inv.1 h]
          exact inv_eq_of_mul_eq_one_right hz2
        have h1 : IsConj (tt a (p * z) z) (z * x) :=
          F.isConj_tt_v_of_right hpzP F.z_mem hpz2 hz2 hpz1 F.z_ne
            (by rw [F.a_z_a]; exact F.psi_x)
        have h2 : t * (z * x) = tt a (p * z) z := by
          have hw : (1 : G) ∈ T ⊓ K := one_mem _
          rw [hut, hw1, F.tt_mul_v hw, one_mul]
        rw [h2] at hxtv
        exact hxv (hxtv.trans h1)
    · right; right
      refine ⟨p, hp, w, hwP, hp2, hw2, ?_, ?_, hut⟩
      · intro hpR
        have h1 : IsConj (tt a p w) (z * x) :=
          F.isConj_tt_v_of_left hp hwP hp2 hw2 hp1 hw1 (F.psi_R hpR)
        rw [← hut] at h1
        exact hxv (hxt.trans h1)
      · intro hwR
        have h1 : IsConj (tt a p w) (z * x) :=
          F.isConj_tt_v_of_right hp hwP hp2 hw2 hp1 hw1 (F.psi_R hwR)
        rw [← hut] at h1
        exact hxv (hxt.trans h1)

theorem tt_mem_Fv [Finite G] (hG : C3Hyp G) {y : G} (hs : Th2Std x y K T S)
    (e7 : kBar K ≃* alternatingGroup (Fin 7)) (hP2 : 2 ≤ pRank 2 ↥(T ⊓ K))
    (hQ4 : Nat.card ↥(T ⊓ CxK x K) = 4) {p w : G} (hp : p ∈ T ⊓ K) (hw : w ∈ T ⊓ K)
    (hp2 : p * p = 1) (hw2 : w * w = 1) (hpR : p ∉ conjugate (T ⊓ CxK x K) a⁻¹)
    (hwR : w ∉ conjugate (T ⊓ CxK x K) a⁻¹) : tt a p w ∈ Fv x (z * x) := by
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hzR : z ∈ conjugate (T ⊓ CxK x K) a⁻¹ := F.z_mem_four hR
  have hpzP : p * z ∈ T ⊓ K := Subgroup.mul_mem _ hp F.z_mem
  have hwzP : w * z ∈ T ⊓ K := Subgroup.mul_mem _ hw F.z_mem
  have hpzc : p * z = z * p := F.z_central p hp
  have hwzc : w * z = z * w := F.z_central w hw
  have hpz2 : (p * z) * (p * z) = 1 := by
    calc (p * z) * (p * z) = p * (z * p) * z := by group
      _ = p * (p * z) * z := by rw [← hpzc]
      _ = (p * p) * (z * z) := by group
      _ = 1 := by rw [hp2, F.z_sq, one_mul]
  have hwz2 : (w * z) * (w * z) = 1 := by
    calc (w * z) * (w * z) = w * (z * w) * z := by group
      _ = w * (w * z) * z := by rw [← hwzc]
      _ = (w * w) * (z * z) := by group
      _ = 1 := by rw [hw2, F.z_sq, one_mul]
  have hpzR : p * z ∉ conjugate (T ⊓ CxK x K) a⁻¹ := fun h => hpR (by
    have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hzR)
    rwa [mul_inv_cancel_right] at this)
  have hwzR : w * z ∉ conjugate (T ⊓ CxK x K) a⁻¹ := fun h => hwR (by
    have := Subgroup.mul_mem _ h (Subgroup.inv_mem _ hzR)
    rwa [mul_inv_cancel_right] at this)
  have hS : tt a p w ∈ S := F.core.T_le_S (F.tt_mem_T hp hw)
  have hvc := F.S_centralizes_v _ hS
  refine ⟨?_, F.tt_sq hp hw hp2 hw2,
    (F.isConj_tt_x_of_not_mem_R hG hs e7 hP2 hQ4 hp hw hp2 hw2 hpR hwR).symm, ?_⟩
  · calc tt a p w * (z * x) = (tt a p w * (z * x) * (tt a p w)⁻¹) * tt a p w := by group
      _ = (z * x) * tt a p w := by rw [hvc]
  · rw [F.tt_mul_v hw]
    exact (F.isConj_tt_x_of_not_mem_R hG hs e7 hP2 hQ4 hpzP hwzP hpz2 hwz2 hpzR hwzR).symm

theorem x_mul_v [Finite G] : x * (z * x) = z := by
  calc x * (z * x) = (x * z) * x := by group
    _ = (z * x) * x := by rw [← F.zx_comm]
    _ = z * (x * x) := by group
    _ = z := by rw [F.x_sq, mul_one]

theorem z_mul_v [Finite G] : z * (z * x) = x := by
  calc z * (z * x) = (z * z) * x := by group
    _ = x := by rw [F.z_sq, one_mul]

theorem x_mem_Fv [Finite G] : x ∈ Fv x (z * x) := by
  refine ⟨?_, F.x_sq, IsConj.refl _, ?_⟩
  · rw [F.x_mul_v, mul_assoc, F.x_sq, mul_one]
  · rw [F.x_mul_v]
    exact F.isConj_x_z

theorem z_mem_Fv [Finite G] : z ∈ Fv x (z * x) := by
  refine ⟨?_, F.z_sq, F.isConj_x_z, ?_⟩
  · have h1 : (z * x) * z = x := by
      calc (z * x) * z = z * (x * z) := by group
        _ = z * (z * x) := by rw [← F.zx_comm]
        _ = x := F.z_mul_v
    rw [F.z_mul_v, h1]
  · have h1 : z * (z * x) = x := F.z_mul_v
    rw [h1]

end Frame

end CFSG.GH74.GLS.Th2.P43f
