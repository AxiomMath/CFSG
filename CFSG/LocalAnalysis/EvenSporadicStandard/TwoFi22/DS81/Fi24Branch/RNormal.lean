module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core2
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ComplementKer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ComplementInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ComplementUniq
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.GlueO23
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Shape54Good

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

private theorem conj_mem_Pg_of_mem_CNz {n : G} (hn : n ∈ CNz E z) {p : G}
    (hp : p ∈ Pg E z) : n * p * n⁻¹ ∈ Pg E z := by
  have hK : ∀ k ∈ CNz E z, n * k * n⁻¹ ∈ CNz E z := fun k hk =>
    (CNz E z).mul_mem ((CNz E z).mul_mem hn hk) ((CNz E z).inv_mem hn)
  have hK' : ∀ k ∈ CNz E z, n⁻¹ * k * n ∈ CNz E z := fun k hk =>
    (CNz E z).mul_mem ((CNz E z).mul_mem ((CNz E z).inv_mem hn) hk) hn
  exact TwoB.conj_mem_O2In_of_conj_mem hK hK' p hp

private theorem invUnder_commutator {C P : Subgroup G}
    (h : ∀ n ∈ C, ∀ p ∈ P, n * p * n⁻¹ ∈ P) : InvUnder C ⁅P, P⁆ := by
  intro n hn u hu
  have hmap : P.map (MulAut.conj n).toMonoidHom = P := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      change n * p * n⁻¹ ∈ P
      exact h n hn p hp
    · intro p hp
      refine ⟨n⁻¹ * p * n, ?_, ?_⟩
      · change n⁻¹ * p * n ∈ P
        simpa only [inv_inv] using h n⁻¹ (C.inv_mem hn) p hp
      · change n * (n⁻¹ * p * n) * n⁻¹ = p
        group
  have hcomm : ⁅P, P⁆.map (MulAut.conj n).toMonoidHom = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, hmap]
  have hmem : (MulAut.conj n).toMonoidHom u ∈ ⁅P, P⁆ := by
    have := Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hu
    rwa [hcomm] at this
  change n * u * n⁻¹ ∈ ⁅P, P⁆ at hmem
  exact hmem

private theorem mem_coset_or_coset_sq_of_relIndex_three {H K : Subgroup G} {r x : G}
    (hHK : H ≤ K) (hHn : (H.subgroupOf K).Normal) (hrK : r ∈ K) (hxK : x ∈ K)
    (hcard : H.relIndex K = 3) (hrH : r ∉ H) :
    x ∈ H ∨ (∃ q ∈ H, x = q * r) ∨ (∃ q ∈ H, x = q * r ^ 2) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : (H.subgroupOf K).Normal := hHn
  let Q := ↥K ⧸ H.subgroupOf K
  let q : ↥K →* Q := QuotientGroup.mk' (H.subgroupOf K)
  let rO : ↥K := ⟨r, hrK⟩
  let xO : ↥K := ⟨x, hxK⟩
  have hQcard : Nat.card Q = 3 := hcard
  have hqr_ne : q rO ≠ 1 := by
    intro h
    have hmem : rO ∈ H.subgroupOf K :=
      (QuotientGroup.eq_one_iff rO).mp (show (rO : Q) = 1 from h)
    exact hrH (by simpa [rO] using (Subgroup.mem_subgroupOf.mp hmem))
  have htop : Subgroup.zpowers (q rO) = ⊤ :=
    zpowers_eq_top_of_prime_card (p := 3) hQcard hqr_ne
  have hord_qr : orderOf (q rO) = 3 := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hQcard]
  have hx_mem : q xO ∈ Subgroup.zpowers (q rO) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_range, hk_eq⟩ :=
    Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hx_mem)
  have hk_lt : k < 3 := by
    rw [Finset.mem_range] at hk_range
    rwa [hord_qr] at hk_range
  interval_cases k
  · left
    have h1 : q xO = 1 := by simpa using hk_eq.symm
    have hmem : xO ∈ H.subgroupOf K := by
      refine (QuotientGroup.eq_one_iff xO).mp ?_
      show q xO = 1
      exact h1
    simpa [xO] using (Subgroup.mem_subgroupOf.mp hmem)
  · right; left
    have h1 : q xO = q rO := by
      have := hk_eq
      rw [pow_one] at this
      exact this.symm
    have hmem : xO * rO⁻¹ ∈ H.subgroupOf K := by
      refine (QuotientGroup.eq_one_iff (xO * rO⁻¹)).mp ?_
      show q (xO * rO⁻¹) = 1
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    refine ⟨x * r⁻¹, ?_, by group⟩
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [xO, rO] using this
  · right; right
    have h1 : q xO = (q rO) ^ 2 := hk_eq.symm
    have hmem : xO * (rO ^ 2)⁻¹ ∈ H.subgroupOf K := by
      refine (QuotientGroup.eq_one_iff (xO * (rO ^ 2)⁻¹)).mp ?_
      show q (xO * (rO ^ 2)⁻¹) = 1
      rw [map_mul, map_inv, map_pow, h1, mul_inv_cancel]
    refine ⟨x * (r ^ 2)⁻¹, ?_, by group⟩
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [xO, rO] using this

theorem R_normal_CNz (c : Core2 E t z) : ∀ n ∈ CNz E z, ∀ x ∈ Rg t z, n * x * n⁻¹ ∈ Rg t z := by
  classical
  have hO23_le : TwoFi22.O23In (CNz E z) ≤ CNz E z := Glue.O23In_le
  have hP_le_O23 : Pg E z ≤ TwoFi22.O23In (CNz E z) :=
    Glue.le_O23In (Pg_le_CNz E z) rfl
  haveI hPn : ((Pg E z).subgroupOf (CNz E z)).Normal := TwoB.normal_subgroupOf_O2In (CNz E z)
  have hC_le_normP : CNz E z ≤ normalizer (Pg E z : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf (Pg_le_CNz E z)
  have hPO_normal : ((Pg E z).subgroupOf (TwoFi22.O23In (CNz E z))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP_le_O23).mpr (hO23_le.trans hC_le_normP)
  have hrelIndex : (Pg E z).relIndex (TwoFi22.O23In (CNz E z)) = 3 := by
    have h := Subgroup.relIndex_mul_card (H := Pg E z) (K := TwoFi22.O23In (CNz E z))
    rw [inf_eq_left.mpr hP_le_O23, c.cocode.card_P, c.cocode.card_O23] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have hUinv : InvUnder (CNz E z) (Rg t z ⊓ E) := by
    rw [← c.pc]
    exact invUnder_commutator (C := CNz E z) (P := Pg E z)
      (fun n hn p hp => conj_mem_Pg_of_mem_CNz hn hp)
  have hPP : ∀ p ∈ Pg E z, ∀ q ∈ Pg E z, p * q * p⁻¹ * q⁻¹ ∈ Rg t z ⊓ E := by
    intro p hp q hq
    have hmem := Subgroup.commutator_mem_commutator hp hq
    rw [c.pc] at hmem
    simpa only [commutatorElement_def] using hmem
  have h3dvd : 3 ∣ Nat.card ↥(TwoFi22.O23In (CNz E z)) := by
    rw [c.cocode.card_O23]
    exact ⟨2 ^ 17, rfl⟩
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨rO, hrO_ord⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  set r : G := (rO : G) with hr
  have hrO : r ∈ TwoFi22.O23In (CNz E z) := by rw [hr]; exact rO.2
  have hord : orderOf r = 3 := by rw [hr, Subgroup.orderOf_coe, hrO_ord]
  have hr_CNz : r ∈ CNz E z := hO23_le hrO
  have hr_notP : r ∉ Pg E z := by
    intro hrP
    have hdvd : orderOf r ∣ Nat.card ↥(Pg E z) := Subgroup.orderOf_dvd_natCard (Pg E z) hrP
    rw [hord, c.cocode.card_P] at hdvd
    norm_num at hdvd
  have hNorm : NormSetting (Pg E z) E (Rg t z ⊓ E) r :=
    { U_le_E := inf_le_right
      E_le_P := c.rp.E_le_P
      E_sq := c.m24.E_sq
      E_comm := E_comm c.toCore1
      PP := hPP
      r_cube := by rw [← hord]; exact pow_orderOf_eq_one r
      r_P := fun p hp => conj_mem_Pg_of_mem_CNz hr_CNz hp
      r_U := fun u hu => hUinv r hr_CNz u hu
      r_E := fun e he =>
        c.cocode.r_E r hrO hord (Rg t z ⊓ E) inf_le_right hUinv c.rp.card_RE e he
      r_fpf := fun p hp h =>
        c.cocode.r_fpf r hrO hord p hp ((inf_le_right : Rg t z ⊓ E ≤ E) h) }
  obtain ⟨S, hSP, hUS, hSiff, hSE, hSdec⟩ := exists_normKer hNorm
  obtain ⟨A, hA_le, hEA, hAr, hHV⟩ := c.cocode.exists_A
  have hA_Nrm : A ≤ Nrm E := hA_le.trans inf_le_left
  have hA_J : A ≤ Jg t z := hA_le.trans inf_le_right
  have hPnorm_K : ∀ n ∈ Nrm E ⊓ Jg t z, ∀ p ∈ Pg E z, n * p * n⁻¹ ∈ Pg E z := by
    intro n hn p hp
    have hK : ∀ k ∈ Nrm E ⊓ Jg t z, n * k * n⁻¹ ∈ Nrm E ⊓ Jg t z := fun k hk =>
      (Nrm E ⊓ Jg t z).mul_mem ((Nrm E ⊓ Jg t z).mul_mem hn hk) ((Nrm E ⊓ Jg t z).inv_mem hn)
    have hK' : ∀ k ∈ Nrm E ⊓ Jg t z, n⁻¹ * k * n ∈ Nrm E ⊓ Jg t z := fun k hk =>
      (Nrm E ⊓ Jg t z).mul_mem ((Nrm E ⊓ Jg t z).mul_mem ((Nrm E ⊓ Jg t z).inv_mem hn) hk) hn
    have hp' : p ∈ TwoFi22.O2In (Nrm E ⊓ Jg t z) := by rw [c.cocode.O2_NV]; exact hp
    have h := TwoB.conj_mem_O2In_of_conj_mem hK hK' p hp'
    rwa [c.cocode.O2_NV] at h
  have hUinv_K : InvUnder (Nrm E ⊓ Jg t z) (Rg t z ⊓ E) := by
    rw [← c.pc]
    exact invUnder_commutator (C := Nrm E ⊓ Jg t z) (P := Pg E z) hPnorm_K
  have hAE : ∀ a ∈ A, ∀ e ∈ E, a * e * a⁻¹ ∈ E := by
    intro a ha e he
    exact (mem_Nrm.mp (hA_Nrm ha) e).mp he
  have hAR : ∀ a ∈ A, ∀ x ∈ Rg t z, a * x * a⁻¹ ∈ Rg t z := by
    intro a ha x hx
    exact c.jr.R_normal a (hA_J ha) x hx
  have hAP : ∀ a ∈ A, ∀ p ∈ Pg E z, a * p * a⁻¹ ∈ Pg E z := by
    intro a ha p hp
    exact hPnorm_K a (hA_le ha) p hp
  have hAS : ∀ a ∈ A, ∀ x ∈ S, a * x * a⁻¹ ∈ S := by
    intro a ha x hx
    refine normKer_conj hNorm hSiff (c := a) (hPnorm_K a (hA_le ha))
      (fun u hu => hUinv_K a (hA_le ha) u hu) ?_ x hx
    have hq : a⁻¹ * r * a * r⁻¹ ∈ Pg E z := by
      have := hAr a⁻¹ (A.inv_mem ha) r hrO hord
      simpa only [inv_inv] using this
    exact ⟨a⁻¹ * r * a * r⁻¹, hq, Or.inl (by group)⟩
  have hRS : Rg t z = S :=
    eq_of_complements (E := E) (z := z) (A := A) (U := Rg t z ⊓ E) (R := Rg t z) (S := S)
      hHV inf_le_right hUinv c.rp.card_RE hPP c.rp.R_le_P hSP inf_le_left hUS rfl hSE
      c.rp.P_decomp hSdec (E_comm c.toCore1) hAE hAR hAS hAP
  intro n hn x hx
  rw [hRS] at hx ⊢
  have hn_inv : n⁻¹ ∈ CNz E z := (CNz E z).inv_mem hn
  have hxO : n⁻¹ * r * n ∈ TwoFi22.O23In (CNz E z) := by
    simpa only [inv_inv] using Glue.O23In_conj_mem hrO hn_inv
  have hx_notP : n⁻¹ * r * n ∉ Pg E z := by
    intro hxP
    have hrP : r ∈ Pg E z := by
      have hconj := conj_mem_Pg_of_mem_CNz hn hxP
      rwa [show n * (n⁻¹ * r * n) * n⁻¹ = r by group] at hconj
    exact hr_notP hrP
  have hcls :=
    mem_coset_or_coset_sq_of_relIndex_three hP_le_O23 hPO_normal hrO hxO hrelIndex hr_notP
  have hcr : ∃ q ∈ Pg E z, n⁻¹ * r * n = q * r ∨ n⁻¹ * r * n = q * r ^ 2 := by
    rcases hcls with hxH | ⟨q, hq, hqx⟩ | ⟨q, hq, hqx⟩
    · exact absurd hxH hx_notP
    · exact ⟨q, hq, Or.inl hqx⟩
    · exact ⟨q, hq, Or.inr hqx⟩
  exact normKer_conj hNorm hSiff (c := n) (fun p hp => conj_mem_Pg_of_mem_CNz hn hp)
    (fun u hu => hUinv n hn u hu) hcr x hx

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
