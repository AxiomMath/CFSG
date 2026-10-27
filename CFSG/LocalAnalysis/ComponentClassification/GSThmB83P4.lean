module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step4b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

structure PData (H : L83Hyp h) where
  b : X
  b_ord : orderOf b = 2
  B_eq : h.B = zpowers b
  P_eq : h.P = h.T
  P_mem : ∀ w ∈ h.P, w = 1 ∨ w = h.a ∨ w = b ∨ w = h.a * b
  ba : b * h.a = h.a * b
  xbx : h.x⁻¹ * b * h.x = h.a * b
  xbx' : h.x * b * h.x⁻¹ = h.a * b
  normalizer_B : normalizer (h.B : Set X) = centralizer ({b} : Set X)
  Q_eq : h.Q = h.S ⊓ centralizer ({b} : Set X)

variable {H : L83Hyp h}

theorem nonempty_PData (H : L83Hyp h) : Nonempty (PData H) := by
  obtain ⟨b, hb2, hBb, hPT, hPmem, hba, hxbx, hxbx', hNB, hQb, -⟩ :=
    h.sec8_P4_setup H.T_eq H.C_eq H.card_P H.x_mul_x
  exact ⟨⟨b, hb2, hBb, hPT, hPmem, hba, hxbx', hxbx, hNB, hQb⟩⟩

namespace PData

variable (d : PData H)
include d

theorem b_mul_self : d.b * d.b = 1 := by
  rw [← pow_two, ← d.b_ord, pow_orderOf_eq_one]

theorem b_ne_one : d.b ≠ 1 := by
  intro h1
  have := d.b_ord
  rw [h1, orderOf_one] at this
  norm_num at this

theorem b_mem_B : d.b ∈ h.B := d.B_eq ▸ mem_zpowers d.b

theorem b_mem_P : d.b ∈ h.P := ⟨(h.B_le d.b_mem_B).1, (h.B_le d.b_mem_B).2⟩

theorem b_mem_Q : d.b ∈ h.Q := le_inf (h.B_le.trans inf_le_left) le_normalizer d.b_mem_B

theorem Q_le_centralizer_b : h.Q ≤ centralizer ({d.b} : Set X) := fun _ hy =>
  (Subgroup.mem_inf.mp (d.Q_eq ▸ hy)).2

theorem P_mul_self {p : X} (hp : p ∈ h.P) : p * p = 1 := by
  have haa := Six.a_mul_a_self h
  rcases d.P_mem p hp with rfl | rfl | rfl | rfl
  · rw [one_mul]
  · exact haa
  · exact d.b_mul_self
  · rw [show h.a * d.b * (h.a * d.b) = h.a * (d.b * h.a) * d.b by group, d.ba,
      show h.a * (h.a * d.b) * d.b = (h.a * h.a) * (d.b * d.b) by group, haa, d.b_mul_self,
      one_mul]

theorem P_comm_Q {w q : X} (hw : w ∈ h.P) (hq : q ∈ h.Q) : w * q = q * w := by
  have hb : d.b * q = q * d.b := (mem_centralizer_singleton_iff.mp (d.Q_le_centralizer_b hq)).symm
  have ha : h.a * q = q * h.a := (H.comm_a_of_mem_Q hq).symm
  rcases d.P_mem w hw with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact ha
  · exact hb
  · rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

theorem b_not_mem_M3 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : d.b ∉ h.M3 := by
  intro hbM
  have hbQ := d.b_mem_Q
  have hbK : d.b ∈ coreActionKernel h.K := by
    have := d.b_mem_B
    rw [← H.Q_inf_kernel] at this
    exact (Subgroup.mem_inf.mp this).2
  have h2 : (⟨d.b, H.Q_le_normalizer_K hbQ⟩ : normalizer (h.K : Set X)) ∈
      (Eight.oddBarAction h.K).ker := Eight.mem_ker_oddBarAction.mpr hbK
  have hQ1 : IsPGroup 2 ((h.Q ⊓ h.M3).subgroupOf h.M3) := isPGroup_Q1.comap_subtype
  have h3 := Eight.injOn_of_isPGroup (H.not_two_dvd_card_ker_modelHom hCF1 hCF2) hQ1
    (show (⟨d.b, hbM⟩ : ↥h.M3) ∈ (h.Q ⊓ h.M3).subgroupOf h.M3 from ⟨hbQ, hbM⟩)
    (one_mem _) (by
      rw [map_one]
      exact h2)
  exact d.b_ne_one (congrArg Subtype.val h3)

theorem a_ne_b (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) : h.a ≠ d.b := fun h1 =>
  d.b_not_mem_M3 hCF1 hCF2 (h1 ▸ h.a_mem_M3)

theorem conj_pow_odd {n : X} (hna : n * h.a = h.a * n) (hnb : n * d.b * n⁻¹ = h.a * d.b)
    (i : ℕ) : n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹ = h.a * d.b := by
  have hn2 : n ^ 2 * d.b * (n ^ 2)⁻¹ = d.b := by
    have h1 : n * (h.a * d.b) * n⁻¹ = d.b := by
      rw [show n * (h.a * d.b) * n⁻¹ = (n * h.a * n⁻¹) * (n * d.b * n⁻¹) by group, hnb,
        show n * h.a * n⁻¹ = h.a by rw [hna, mul_inv_cancel_right], ← mul_assoc,
        Six.a_mul_a_self h, one_mul]
    rw [pow_two, show n * n * d.b * (n * n)⁻¹ = n * (n * d.b * n⁻¹) * n⁻¹ by group, hnb, h1]
  induction i with
  | zero => simpa using hnb
  | succ i ih =>
    rw [show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring, pow_add,
      show n ^ 2 * n ^ (2 * i + 1) * d.b * (n ^ 2 * n ^ (2 * i + 1))⁻¹ =
        n ^ 2 * (n ^ (2 * i + 1) * d.b * (n ^ (2 * i + 1))⁻¹) * (n ^ 2)⁻¹ by group, ih,
      show n ^ 2 * (h.a * d.b) * (n ^ 2)⁻¹ = (n ^ 2 * h.a * (n ^ 2)⁻¹) * (n ^ 2 * d.b * (n ^ 2)⁻¹)
        by group, hn2]
    congr 1
    have hna2 : n ^ 2 * h.a = h.a * n ^ 2 := by
      rw [pow_two, mul_assoc, hna, ← mul_assoc, hna, mul_assoc]
    rw [hna2, mul_inv_cancel_right]

theorem normalizer_P_le_centralizer (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    normalizer ((h.P.subgroupOf h.C0 : Subgroup ↥h.C0) : Set ↥h.C0) ≤
      centralizer ((h.P.subgroupOf h.C0 : Subgroup ↥h.C0) : Set ↥h.C0) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := H.P_sylow_C0
  have hbP := d.b_mem_P
  have hbC : d.b ∈ h.C0 := P_le_C0 h hbP
  intro n hn
  have hna : (n : X) * h.a = h.a * n := mem_centralizer_singleton_iff.mp n.2.1
  have hnbP : (n : X) * d.b * (n : X)⁻¹ ∈ h.P := by
    have := (mem_normalizer_iff.mp hn ⟨d.b, hbC⟩).mp hbP
    exact this
  have key : d.b = (n : X)⁻¹ * ((n : X) * d.b * (n : X)⁻¹) * n := by group
  have hnb : (n : X) * d.b * (n : X)⁻¹ = d.b := by
    rcases d.P_mem _ hnbP with h1 | h1 | h1 | h1
    · exfalso
      rw [h1] at key
      exact d.b_ne_one (by rw [key]; group)
    · exfalso
      rw [h1, show (n : X)⁻¹ * h.a * n = h.a by rw [mul_assoc, ← hna, inv_mul_cancel_left]] at key
      exact d.a_ne_b hCF1 hCF2 key.symm
    · exact h1
    · exfalso
      obtain ⟨k, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
      obtain ⟨i, rfl⟩ := hr
      set n' : ↥h.C0 := n ^ (2 * i + 1) with hn'
      have hn'b : (n' : X) * d.b * (n' : X)⁻¹ = h.a * d.b := by
        rw [hn', SubgroupClass.coe_pow]
        exact d.conj_pow_odd hna h1 i
      have hdvd : 2 * i + 1 ∣ orderOf n := by
        rw [hm]
        exact dvd_mul_left _ _
      have hn'2 : IsPGroup 2 (zpowers n') := by
        refine IsPGroup.of_card (n := k) ?_
        rw [Nat.card_zpowers, hn', orderOf_pow_of_dvd (by omega) hdvd, hm,
          Nat.mul_div_cancel _ (by omega)]
      have hT2 : IsPGroup 2 (T : Subgroup ↥h.C0) := T.isPGroup'
      have hle : zpowers n' ≤ normalizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) := by
        rw [zpowers_le, hT]
        exact pow_mem hn _
      have hsup := IsPGroup.to_sup_of_normal_left' hT2 hn'2 hle
      have hmax := T.is_maximal' hsup le_sup_left
      have hn'T : n' ∈ (T : Subgroup ↥h.C0) := by
        rw [← hmax]
        exact mem_sup_right (mem_zpowers n')
      rw [hT] at hn'T
      have hc : (n' : X) * d.b = d.b * n' := d.P_comm_Q hn'T d.b_mem_Q
      rw [hc, mul_inv_cancel_right] at hn'b
      apply (show h.a ≠ 1 from fun h2 => by
        have := h.orderOf_a
        rw [h2, orderOf_one] at this
        norm_num at this)
      have := congrArg (fun t => t * d.b⁻¹) hn'b
      simp only [mul_inv_cancel, mul_inv_cancel_right] at this
      exact this.symm
  rw [mem_centralizer_iff]
  intro p hp
  have hp' : (p : X) ∈ h.P := hp
  have hnb' : (n : X) * d.b = d.b * n := by
    calc (n : X) * d.b = (n : X) * d.b * (n : X)⁻¹ * n := by group
      _ = d.b * n := by rw [hnb]
  apply Subtype.ext
  rcases d.P_mem _ hp' with h1 | h1 | h1 | h1 <;> simp only [Subgroup.coe_mul] <;> rw [h1]
  · group
  · exact hna.symm
  · exact hnb'.symm
  · rw [mul_assoc, ← hnb', ← mul_assoc, ← hna, mul_assoc]

theorem sq_mem_O0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ h.C0) : y * y ∈ h.O0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := H.P_sylow_C0
  have hP : normalizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) ≤
      centralizer ((T : Subgroup ↥h.C0) : Set ↥h.C0) := by
    rw [hT]
    exact d.normalizer_P_le_centralizer hCF1 hCF2
  set φ := MonoidHom.transferSylow T hP with hφ
  have hodd := MonoidHom.not_dvd_card_ker_transferSylow T hP
  have hker : φ.ker ≤ pPrimeCore 2 ↥h.C0 :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd⟩
  have h1 : (⟨y, hy⟩ : ↥h.C0) * ⟨y, hy⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    apply Subtype.ext
    have ht : ((φ ⟨y, hy⟩ : T) : ↥h.C0) ∈ h.P.subgroupOf h.C0 := hT ▸ (φ ⟨y, hy⟩).2
    exact Subtype.ext (d.P_mul_self ht)
  exact ⟨_, hker h1, rfl⟩

theorem mem_O0_mul_P (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {y : X}
    (hy : y ∈ h.C0) : ∃ o ∈ h.O0, ∃ p ∈ h.P, y = o * p := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := H.P_sylow_C0
  set O0' : Subgroup ↥h.C0 := pPrimeCore 2 ↥h.C0 with hO0'
  have hexp : ∀ z : ↥h.C0 ⧸ O0', z * z = 1 := by
    intro z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    obtain ⟨o, ho, hoz⟩ := mem_map.mp (d.sq_mem_O0 hCF1 hCF2 z.2)
    have : o = z * z := Subtype.ext hoz
    rw [← this]
    exact ho
  have h2 : IsPGroup 2 (↥h.C0 ⧸ O0') := fun z => ⟨1, by rw [pow_one, pow_two]; exact hexp z⟩
  have hsurj : Function.Surjective (QuotientGroup.mk' O0') := QuotientGroup.mk'_surjective _
  have htop : ((T.mapSurjective hsurj : Sylow 2 (↥h.C0 ⧸ O0')) : Subgroup (↥h.C0 ⧸ O0')) = ⊤ :=
    ((T.mapSurjective hsurj).is_maximal' (h2.to_subgroup ⊤) le_top).symm
  have hyT : QuotientGroup.mk' O0' ⟨y, hy⟩ ∈
      ((T : Subgroup ↥h.C0).map (QuotientGroup.mk' O0')) := by
    rw [← Sylow.coe_mapSurjective (hf := hsurj), htop]
    exact mem_top _
  obtain ⟨t, ht, hty⟩ := mem_map.mp hyT
  have ho' : t⁻¹ * ⟨y, hy⟩ ∈ O0' := QuotientGroup.eq.mp hty
  have htP : (t : X) ∈ h.P := by
    have : t ∈ h.P.subgroupOf h.C0 := hT ▸ ht
    exact this
  have hoO : (t : X)⁻¹ * y ∈ h.O0 := ⟨_, ho', rfl⟩
  have hconj : (t : X) * ((t : X)⁻¹ * y) * (t : X)⁻¹ ∈ h.O0 :=
    (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_O0 (P_le_C0 h htP).1) _).mp hoO
  refine ⟨_, hconj, t, htP, ?_⟩
  group

theorem sq_mul_mem_O0 (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {c t : X}
    (hc : c ∈ h.C0) (ht : t ∈ h.Q) (ht2 : t * t = 1) : c * t * (c * t) ∈ h.O0 := by
  obtain ⟨o, ho, p, hp, rfl⟩ := d.mem_O0_mul_P hCF1 hCF2 hc
  have hpt : p * t = t * p := d.P_comm_Q hp ht
  have hp2 := d.P_mul_self hp
  have htC : t ∈ centralizer ({h.a} : Set X) :=
    mem_centralizer_singleton_iff.mpr (H.comm_a_of_mem_Q ht)
  have hptC : p * t ∈ centralizer ({h.a} : Set X) := mul_mem (P_le_C0 h hp).1 htC
  have h1 : (p * t) * o * (p * t)⁻¹ ∈ h.O0 :=
    (mem_normalizer_iff.mp (H.centralizer_a_le_normalizer_O0 hptC) o).mp ho
  have h2 : (p * t) * (p * t) = 1 := by
    rw [show p * t * (p * t) = p * (t * p) * t by group, ← hpt,
      show p * (p * t) * t = (p * p) * (t * t) by group, hp2, ht2, one_mul]
  have h3 : o * p * t * (o * p * t) = o * ((p * t) * o * (p * t)⁻¹) * ((p * t) * (p * t)) := by
    group
  rw [h3, h2, mul_one]
  exact mul_mem ho h1

end PData

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
