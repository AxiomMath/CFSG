module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

namespace ZIKData

variable {Q Y V V' B K : Subgroup H} {ρ : H}

lemma fixed_mod_V (h : ZIKData Q Y V V' B K ρ) {q : H} (hq : q ∈ Q)
    (hv : ∃ v ∈ V, ρ * q * ρ⁻¹ = q * v) : q ∈ V := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := hVY.trans h.Y_le_Q
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    fun a ha b hb => h.Q_comm a (hVQ ha) b (hVQ hb)
  have hfpfV : MonoidHom.FixedPointFree (fun x : V => z4i_conjAut ρ V h.rho_norm_V x) :=
    z4i_conjAut_fpf ρ V h.rho_norm_V (fun x hxV hfix => h.rho_fpf_Q x (hVQ hxV) hfix)
  obtain ⟨v, hvV, hqv⟩ := hv
  obtain ⟨w, hw⟩ :=
    MonoidHom.FixedPointFree.commutatorMap_surjective hfpfV ⟨v⁻¹, V.inv_mem hvV⟩
  have hwH : (w : H) * (ρ * (w : H) * ρ⁻¹)⁻¹ = v⁻¹ := by
    have := congrArg (fun z : V => (z : H)) hw
    simpa [MonoidHom.commutatorMap_apply, div_eq_mul_inv, z4i_conjAut_apply] using this
  have hw' : ρ * (w : H) * ρ⁻¹ * (w : H)⁻¹ = v := by
    have := congrArg Inv.inv hwH
    simpa [mul_inv_rev, inv_inv, mul_assoc] using this
  have haux : (ρ * (w : H) * ρ⁻¹ * (w : H)⁻¹) * (ρ * (w : H)⁻¹ * ρ⁻¹) = (w : H)⁻¹ := by
    have h1 : ρ * (w : H)⁻¹ * ρ⁻¹ ∈ V := h.rho_norm_V _ (V.inv_mem w.2)
    calc (ρ * (w : H) * ρ⁻¹ * (w : H)⁻¹) * (ρ * (w : H)⁻¹ * ρ⁻¹)
        = (ρ * (w : H) * ρ⁻¹) * ((w : H)⁻¹ * (ρ * (w : H)⁻¹ * ρ⁻¹)) := by group
      _ = (ρ * (w : H) * ρ⁻¹) * ((ρ * (w : H)⁻¹ * ρ⁻¹) * (w : H)⁻¹) := by
            rw [hVc _ (V.inv_mem w.2) _ h1]
      _ = (ρ * (w : H) * ρ⁻¹ * (ρ * (w : H)⁻¹ * ρ⁻¹)) * (w : H)⁻¹ := by group
      _ = (w : H)⁻¹ := by
            rw [show ρ * (w : H) * ρ⁻¹ * (ρ * (w : H)⁻¹ * ρ⁻¹) = 1 by group]
            simp
  have hfix : ρ * (q * (w : H)⁻¹) * ρ⁻¹ = q * (w : H)⁻¹ := by
    calc ρ * (q * (w : H)⁻¹) * ρ⁻¹
        = (ρ * q * ρ⁻¹) * (ρ * (w : H)⁻¹ * ρ⁻¹) := by group
      _ = (q * v) * (ρ * (w : H)⁻¹ * ρ⁻¹) := by rw [hqv]
      _ = q * ((ρ * (w : H) * ρ⁻¹ * (w : H)⁻¹) * (ρ * (w : H)⁻¹ * ρ⁻¹)) := by
            rw [show v = ρ * (w : H) * ρ⁻¹ * (w : H)⁻¹ from hw'.symm]
            group
      _ = q * (w : H)⁻¹ := by rw [haux]
  have hq1 : q * (w : H)⁻¹ = 1 :=
    h.rho_fpf_Q _ (Q.mul_mem hq (hVQ (V.inv_mem w.2))) hfix
  have hqw : q = (w : H) := mul_inv_eq_one.mp hq1
  rw [hqw]; exact w.2

lemma rep_comm_mem_V (h : ZIKData Q Y V V' B K ρ) {a b c : H}
    (haK : a ∈ K) (hbK : b ∈ K) (hc : c = (a * b)⁻¹) (hw : ⁅a, b⁆ ∈ V) :
    ∀ r1 ∈ ({1, a, b, c} : Set H), ∀ r2 ∈ ({1, a, b, c} : Set H), ⁅r1, r2⁆ ∈ V := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVc : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k :=
    fun k hk v hv => h.K_cent_Y k hk v (hVY hv)
  have habK : a * b ∈ K := K.mul_mem haK hbK
  have hba : ⁅b, a⁆ ∈ V := by simpa [commutatorElement_inv] using V.inv_mem hw
  have hac : ⁅a, c⁆ ∈ V := by
    rw [hc, commutatorElement_inv_right]
    have h1 : ⁅a * b, a⁆ = ⁅a, b⁆⁻¹ := by
      have h2 : ⁅a * b, a⁆ = ⁅a, a * b⁆⁻¹ := by
        simpa [inv_inv] using congrArg Inv.inv (commutatorElement_inv (a * b) a)
      rw [h2, commutatorElement_mul_right_eq_mul_conj, commutatorElement_self, one_mul]
      rw [show a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆ from by rw [hVc a haK ⁅a,b⁆ hw]; group]
    rw [h1, show (a * b)⁻¹ * ⁅a, b⁆⁻¹ * (a * b) = ⁅a, b⁆⁻¹ from by
      rw [mul_assoc, ← hVc (a * b) habK ⁅a,b⁆⁻¹ (V.inv_mem hw)]
      group]
    exact V.inv_mem hw
  have hbc' : ⁅b, c⁆ ∈ V := by
    rw [hc, commutatorElement_inv_right]
    have h1 : ⁅a * b, b⁆ = ⁅a, b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_self, mul_one, mul_inv_cancel,
        one_mul]
    rw [h1, show (a * b)⁻¹ * ⁅a, b⁆ * (a * b) = ⁅a, b⁆ from by
      rw [mul_assoc, ← hVc (a * b) habK ⁅a,b⁆ hw]
      group]
    exact hw
  intro r1 hr1 r2 hr2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr1 hr2
  rcases hr1 with rfl | rfl | rfl | rfl <;> rcases hr2 with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · exact hw
  · exact hac
  · simp
  · exact hba
  · simp
  · exact hbc'
  · simp
  · simpa [commutatorElement_inv] using V.inv_mem hac
  · simpa [commutatorElement_inv] using V.inv_mem hbc'
  · simp

lemma comm_mem_V_of (h : ZIKData Q Y V V' B K ρ) {q1 q2 r1 r2 : H}
    (hq1 : q1 ∈ Q) (hq2 : q2 ∈ Q) (hr1 : r1 ∈ K) (hr2 : r2 ∈ K) (hrr : ⁅r1, r2⁆ ∈ V) :
    ⁅q1 * r1, q2 * r2⁆ ∈ V := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVc : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k :=
    fun k hk v hv => h.K_cent_Y k hk v (hVY hv)
  have hq2K : q2 ∈ K := h.Q_le_K hq2
  have hq1K : q1 ∈ K := h.Q_le_K hq1
  have hq2V : ∀ v ∈ V, q2 * v * q2⁻¹ = v := fun v hv => by
    rw [hVc q2 hq2K v hv]; group
  have hq1V : ∀ v ∈ V, q1 * v * q1⁻¹ = v := fun v hv => by
    rw [hVc q1 hq1K v hv]; group
  have hq1r2 : ⁅q1, r2⁆ ∈ V := by
    have h0 : ⁅r2, q1⁆ ∈ V := h.comm_KQ r2 hr2 q1 hq1
    have h1 : ⁅q1, r2⁆ = ⁅r2, q1⁆⁻¹ := by
      simpa [inv_inv] using congrArg Inv.inv (commutatorElement_inv q1 r2)
    rw [h1]; exact V.inv_mem h0
  have h4eq : ⁅r1, q2 * r2⁆ = ⁅r1, q2⁆ * ⁅r1, r2⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅r1, q2⁆ * q2 * ⁅r1, r2⁆ * q2⁻¹ = ⁅r1, q2⁆ * (q2 * ⁅r1, r2⁆ * q2⁻¹) by group,
      hq2V ⁅r1, r2⁆ hrr]
  have h5eq : ⁅q1, q2 * r2⁆ = ⁅q1, q2⁆ * ⁅q1, r2⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅q1, q2⁆ * q2 * ⁅q1, r2⁆ * q2⁻¹ = ⁅q1, q2⁆ * (q2 * ⁅q1, r2⁆ * q2⁻¹) by group,
      hq2V ⁅q1, r2⁆ hq1r2]
  have h4 : ⁅r1, q2 * r2⁆ ∈ V := by
    rw [h4eq]; exact V.mul_mem (h.comm_KQ r1 hr1 q2 hq2) hrr
  have h5 : ⁅q1, q2 * r2⁆ ∈ V := by
    rw [h5eq, commutatorElement_eq_one_iff_mul_comm.mpr (h.Q_comm q1 hq1 q2 hq2), one_mul]
    exact hq1r2
  rw [commutatorElement_mul_left_eq_conj_mul,
    show q1 * ⁅r1, q2 * r2⁆ * q1⁻¹ = ⁅r1, q2 * r2⁆ from hq1V _ h4]
  exact V.mul_mem h4 h5

theorem comm_mem_V (h : ZIKData Q Y V V' B K ρ) :
    ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ * k₂ * k₁⁻¹ * k₂⁻¹ ∈ V := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := hVY.trans h.Y_le_Q
  have hVc : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k :=
    fun k hk v hv => h.K_cent_Y k hk v (hVY hv)
  let Qn : Subgroup K := Q.subgroupOf K
  have hQnNorm : Qn.Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro y
    exact z4i_map_eq_of_forall_mem (MulAut.conj y) Qn (fun x hx => by
      apply Subgroup.mem_subgroupOf.mpr
      change (y : H) * (x : H) * (y : H)⁻¹ ∈ Q
      have hxQ : (x : H) ∈ Q := Subgroup.mem_subgroupOf.mp hx
      have h1 : (y : H) * (x : H) * (y : H)⁻¹ * (x : H)⁻¹ ∈ V := h.comm_KQ y y.2 x hxQ
      rw [show (y : H) * (x : H) * (y : H)⁻¹ =
        ((y : H) * (x : H) * (y : H)⁻¹ * (x : H)⁻¹) * (x : H) by group]
      exact Q.mul_mem (hVQ h1) hxQ)
  haveI : Qn.Normal := hQnNorm
  let T := K ⧸ Qn
  let π : K →* T := QuotientGroup.mk' Qn
  have hcardT : Nat.card T = 4 := h.relIndex_K
  let ρK : MulAut K := z4i_conjAut ρ K h.rho_norm_K
  have hρK3 : ρK ^ 3 = 1 := z4i_conjAut_pow_three ρ K h.rho_norm_K h.rho_pow_three
  have hfpfK : ∀ x : K, ρK x = x → x = 1 :=
    z4i_conjAut_fpf ρ K h.rho_norm_K (fun x hxK hfix => by
      have hxQ := h.rho_fpf_KQ x hxK (by rw [hfix]; simp)
      exact h.rho_fpf_Q x hxQ hfix)
  have hQmap : Qn.map ρK.toMonoidHom = Qn :=
    z4i_map_eq_of_forall_mem ρK Qn (fun x hx => by
      rw [Subgroup.mem_subgroupOf]
      exact h.rho_norm_Q x (Subgroup.mem_subgroupOf.mp hx))
  let ρT : MulAut T := z4i_quotAut ρK Qn hQmap
  have hρT3 : ρT ^ 3 = 1 := z4i_quotAut_pow_three ρK hρK3 Qn hQmap
  have hfpfT : ∀ x : T, ρT x = x → x = 1 := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | _ k =>
      rw [z4i_quotAut_mk] at hx
      change π (ρK k) = π k at hx
      have hk : (ρK k) * k⁻¹ ∈ Qn := by
        have h1 : π ((ρK k) * k⁻¹) = (1 : T) := by
          rw [map_mul, hx, map_inv, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h1
      have h2 : ρ * (k : H) * ρ⁻¹ * (k : H)⁻¹ ∈ Q := by
        have h3 : ((ρK k : K) : H) * ((k : K) : H)⁻¹ ∈ Q := by
          have h4 := Subgroup.mem_subgroupOf.mp hk
          convert h4 using 1
        rw [show ((ρK k : K) : H) = ρ * (k : H) * ρ⁻¹ from
          z4i_conjAut_apply ρ K h.rho_norm_K k] at h3
        simpa [mul_assoc] using h3
      have hkQn : k ∈ Qn := Subgroup.mem_subgroupOf.mpr (h.rho_fpf_KQ k k.2 h2)
      exact (QuotientGroup.eq_one_iff k).mpr hkQn
  haveI : IsMulCommutative T :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := T)
      (by rw [hcardT]; norm_num)
  have hcommT : ∀ a b : T, a * b = b * a := fun a b => mul_comm' a b
  have hQnNeTop : Qn ≠ ⊤ := by
    intro htop
    have h1 : Qn.index = 1 := by rw [htop, Subgroup.index_top]
    have h2 : Qn.index = 4 := h.relIndex_K
    omega
  obtain ⟨aK, haKQ⟩ : ∃ x : K, x ∉ Qn := by
    by_contra hc
    push Not at hc
    exact hQnNeTop (le_antisymm le_top (fun x _ => hc x))
  let a : H := aK
  have haK : a ∈ K := aK.2
  let b : H := ρ * a * ρ⁻¹
  have hbK : b ∈ K := h.rho_norm_K a haK
  let c : H := ρ * b * ρ⁻¹
  have hcK : c ∈ K := h.rho_norm_K b hbK
  have hbK' : (⟨b, hbK⟩ : K) = ρK aK := by
    apply Subtype.ext
    rw [z4i_conjAut_apply]
  have hcK' : (⟨c, hcK⟩ : K) = ρK ⟨b, hbK⟩ := by
    apply Subtype.ext
    rw [z4i_conjAut_apply]
  have hπa : π aK ≠ 1 := fun h1 => haKQ ((QuotientGroup.eq_one_iff aK).mp h1)
  have hπb : π ⟨b, hbK⟩ = ρT (π aK) := (z4i_quotAut_mk ρK Qn hQmap aK).symm
  have hπc : π ⟨c, hcK⟩ = ρT (π ⟨b, hbK⟩) := (z4i_quotAut_mk ρK Qn hQmap ⟨b, hbK⟩).symm
  have hcover : ∀ x : T, x = 1 ∨ x = π aK ∨ x = π ⟨b, hbK⟩ ∨ x = π ⟨c, hcK⟩ := by
    intro x
    rcases z4i_cover_of_card_four hcardT ρT hρT3 hfpfT hπa x with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl (by rw [hπb]; exact h1)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hπc, hπb]; exact h1)))
  have hsplit : ∀ x : K, (x ∈ Qn) ∨ (∃ q : Qn, x = (q : K) * aK) ∨
      (∃ q : Qn, x = (q : K) * ⟨b, hbK⟩) ∨ (∃ q : Qn, x = (q : K) * ⟨c, hcK⟩) := by
    intro x
    rcases hcover x with h1 | h1 | h1 | h1
    · exact Or.inl ((QuotientGroup.eq_one_iff x).mp h1)
    · have h1' : π x = π aK := h1
      have hq : x * aK⁻¹ ∈ Qn := by
        have h2 : π (x * aK⁻¹) = (1 : T) := by rw [map_mul, h1', map_inv, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h2
      exact Or.inr (Or.inl (Exists.intro ⟨x * aK⁻¹, hq⟩ (by group)))
    · have h1' : π x = π ⟨b, hbK⟩ := h1
      have hq : x * ⟨b, hbK⟩⁻¹ ∈ Qn := by
        have h2 : π (x * ⟨b, hbK⟩⁻¹) = (1 : T) := by rw [map_mul, h1', map_inv, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h2
      exact Or.inr (Or.inr (Or.inl (Exists.intro ⟨x * ⟨b, hbK⟩⁻¹, hq⟩ (by group))))
    · have h1' : π x = π ⟨c, hcK⟩ := h1
      have hq : x * ⟨c, hcK⟩⁻¹ ∈ Qn := by
        have h2 : π (x * ⟨c, hcK⟩⁻¹) = (1 : T) := by rw [map_mul, h1', map_inv, mul_inv_cancel]
        exact (QuotientGroup.eq_one_iff _).mp h2
      exact Or.inr (Or.inr (Or.inr (Exists.intro ⟨x * ⟨c, hcK⟩⁻¹, hq⟩ (by group))))
  have hsplitH : ∀ x ∈ K, ∃ q ∈ Q, ∃ r ∈ ({1, a, b, c} : Set H), x = q * r := by
    intro x hxK
    rcases hsplit ⟨x, hxK⟩ with h1 | ⟨q, h1⟩ | ⟨q, h1⟩ | ⟨q, h1⟩
    · exact ⟨x, Subgroup.mem_subgroupOf.mp h1, 1, by simp, by rw [mul_one]⟩
    · refine ⟨(q : H), Subgroup.mem_subgroupOf.mp q.2, a, by simp, ?_⟩
      have h2 := congrArg (fun z : K => (z : H)) h1
      simpa [a] using h2
    · refine ⟨(q : H), Subgroup.mem_subgroupOf.mp q.2, b, by simp, ?_⟩
      have h2 := congrArg (fun z : K => (z : H)) h1
      simpa [b] using h2
    · refine ⟨(q : H), Subgroup.mem_subgroupOf.mp q.2, c, by simp, ?_⟩
      have h2 := congrArg (fun z : K => (z : H)) h1
      simpa [c] using h2
  have hS_K : ∀ r ∈ ({1, a, b, c} : Set H), r ∈ K := by
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact K.one_mem
    · exact haK
    · exact hbK
    · exact hcK
  have hwQ : ⁅a, b⁆ ∈ Q := by
    have hwK : ⁅a, b⁆ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem haK hbK) (K.inv_mem haK)) (K.inv_mem hbK)
    have h1 : π (⟨⁅a, b⁆, hwK⟩ : K) = (1 : T) := by
      rw [show (⟨⁅a, b⁆, hwK⟩ : K) = ⁅aK, ⟨b, hbK⟩⁆ from by apply Subtype.ext; rfl,
        map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommT (π aK) (π ⟨b, hbK⟩))
    simpa using Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hbrc : a * b * c = 1 := by
    have hh : aK * ρK aK * ρK (ρK aK) = 1 := z4i_mul_rho_rho_sq ρK hρK3 hfpfK aK
    have hh' := congrArg (fun z : K => (z : H)) hh
    simpa [← hbK', ← hcK', b, c] using hh'
  have hc : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right hbrc
  have habK : a * b ∈ K := K.mul_mem haK hbK
  have hrho : ∃ v ∈ V, ρ * ⁅a, b⁆ * ρ⁻¹ = ⁅a, b⁆ * v := by
    have hwQinv : ⁅a, b⁆⁻¹ ∈ Q := Q.inv_mem hwQ
    have hmem : ⁅⁅a, b⁆⁻¹, (a * b)⁻¹⁆ ∈ V := by
      have h0 : ⁅(a * b)⁻¹, ⁅a, b⁆⁻¹⁆ ∈ V :=
        h.comm_KQ (a * b)⁻¹ (K.inv_mem habK) ⁅a, b⁆⁻¹ hwQinv
      simpa using V.inv_mem h0
    have hbcq : ⁅b, c⁆ = (a * b)⁻¹ * ⁅a, b⁆ * (a * b) := by
      rw [hc, commutatorElement_inv_right]
      have h1 : ⁅a * b, b⁆ = ⁅a, b⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_self, mul_one,
          mul_inv_cancel, one_mul]
      rw [h1]
    refine ⟨⁅⁅a, b⁆⁻¹, (a * b)⁻¹⁆, hmem, ?_⟩
    calc ρ * ⁅a, b⁆ * ρ⁻¹ = ⁅ρ * a * ρ⁻¹, ρ * b * ρ⁻¹⁆ :=
          conjugate_commutatorElement (g₁ := a) (g₂ := b) (g₃ := ρ)
      _ = ⁅b, c⁆ := rfl
      _ = (a * b)⁻¹ * ⁅a, b⁆ * (a * b) := hbcq
      _ = ⁅a, b⁆ * ⁅⁅a, b⁆⁻¹, (a * b)⁻¹⁆ := by group
  have hw : ⁅a, b⁆ ∈ V := fixed_mod_V h hwQ hrho
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨q1, hq1, r1, hr1, hx1⟩ := hsplitH k₁ hk₁
  obtain ⟨q2, hq2, r2, hr2, hx2⟩ := hsplitH k₂ hk₂
  rw [hx1, hx2]
  exact comm_mem_V_of h hq1 hq2 (hS_K r1 hr1) (hS_K r2 hr2)
    (rep_comm_mem_V h haK hbK hc hw r1 hr1 r2 hr2)

end ZIKData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
