module

public import CFSG.ClassicalInvolution.Asc77.AscT3VConj
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Pure

variable {G : Type} [Group G] [Finite G]

theorem w_sq_mem_of_card_eq {R Q : Subgroup G} {u : G} (huR : Subgroup.zpowers u ≤ R)
    (hcard : Nat.card R = 2 * Nat.card (Subgroup.zpowers u)) (hQR : Q ≤ R)
    (hQu : Nat.card Q = Nat.card (Subgroup.zpowers u)) : u ^ 2 ∈ Q := by
  set U := Subgroup.zpowers u with hU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have h1 : U.relIndex R = 2 := by
    have := Subgroup.relIndex_mul_card (H := U) (K := R)
    rw [inf_eq_left.mpr huR, hcard] at this
    exact Nat.eq_of_mul_eq_mul_right hUpos (by rw [this])
  have h2 : U.relIndex Q ≤ 2 := h1 ▸ Subgroup.relIndex_le_of_le_right hQR (by omega)
  have h3 := Subgroup.relIndex_mul_card (H := U) (K := Q)
  have h4 := Subgroup.relIndex_mul_card (H := Q) (K := U)
  have hpos : 0 < Nat.card ↥(Q ⊓ U) := Nat.card_pos
  have h5 : Q.relIndex U = U.relIndex Q := by
    rw [inf_comm, hQu] at h3
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h4, h3])
  have huU : u ∈ U := Subgroup.mem_zpowers u
  have h6 : Q.relIndex U = 1 ∨ Q.relIndex U = 2 := by
    have h0 : Q.relIndex U ≠ 0 := by
      intro h
      rw [h, zero_mul] at h4
      exact hUpos.ne' h4.symm
    omega
  rcases h6 with h6 | h6
  · have hT : Q.subgroupOf U = ⊤ := Subgroup.index_eq_one.mp h6
    have : (⟨u, huU⟩ : U) ∈ Q.subgroupOf U := hT ▸ Subgroup.mem_top _
    exact Q.pow_mem (Subgroup.mem_subgroupOf.mp this) 2
  · have := Subgroup.sq_mem_of_index_two h6 ⟨u, huU⟩
    exact Subgroup.mem_subgroupOf.mp this

theorem w_closure_pair_eq_of_card {R : Subgroup G} {u r : G} (huR : u ∈ R)
    (hcard : Nat.card R = 2 * Nat.card (Subgroup.zpowers u)) (hrR : r ∈ R)
    (hrU : r ∉ Subgroup.zpowers u) : R = Subgroup.closure {u, r} := by
  set H := Subgroup.closure ({u, r} : Set G) with hH
  have hHR : H ≤ R := (Subgroup.closure_le R).mpr (by
    rintro x (rfl | rfl)
    · exact huR
    · exact hrR)
  have hUH : Subgroup.zpowers u ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _))
  have hrH : r ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hUH
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHR
  have hpos : 0 < Nat.card (Subgroup.zpowers u) := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    rw [mul_one] at hk
    have e := Subgroup.eq_of_le_of_card_ge hUH hk.le
    rw [← e] at hrH
    exact hrU hrH
  have hkm : k * m = 2 := by
    have := hcard
    rw [hm, hk, mul_assoc] at this
    have h2 : Nat.card (Subgroup.zpowers u) * (k * m) = Nat.card (Subgroup.zpowers u) * 2 := by
      rw [this]
      ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  have hm1 : m = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp ⟨k, by rw [← hkm, mul_comm]⟩ with h | h
    · exact h
    · exfalso
      rw [h] at hkm
      have : k = 1 := by omega
      exact hk1 this
  rw [hm1, mul_one] at hm
  exact (Subgroup.eq_of_le_of_card_ge hHR hm.le).symm

theorem w_isUniqueInvolution_zpowers {u : G} {k : ℕ} (hu : orderOf u = 2 ^ (k + 1)) :
    IsUniqueInvolution (Subgroup.zpowers u) (u ^ 2 ^ k) where
  mem := Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _
  ne_one := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hu] at h1
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  sq := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
  unique := by
    intro y hy hy2
    obtain ⟨c, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : u ^ (2 * c) = 1 := by
      rw [two_mul, zpow_add]; exact hy2
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hu] at h2
    have h3 : ((2 : ℤ) ^ k) ∣ c := by
      have e : ((2 ^ (k + 1) : ℕ) : ℤ) = 2 * 2 ^ k := by push_cast; ring
      rw [e] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    obtain ⟨m, rfl⟩ := h3
    have e : u ^ ((2 : ℤ) ^ k * m) = (u ^ 2 ^ k) ^ m := by
      rw [zpow_mul]; norm_cast
    rw [e]
    have hsq : u ^ 2 ^ k * u ^ 2 ^ k = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← hu, pow_orderOf_eq_one]
    rcases Int.even_or_odd m with hm | hm
    · exact Or.inl ((invol_zpow hsq m).1 hm)
    · exact Or.inr ((invol_zpow hsq m).2 hm)

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.w_dData (d : Std20 p f K K' J S R R' W V z t) {r : G} (hrR : r ∈ R)
    (hrW : r ∉ W) :
    ∃ u : G, Subgroup.zpowers u = K ⊓ W ∧ Sec71.DData (CoreAssembly.conjClass K) W R K u r z := by
  have hp := d.branch.odd
  have hq := d.branch.five
  obtain ⟨u, hu⟩ := Thompson.exists_zpowers_eq_inf_W hp hq d.hyp d.hW d.late_R_mem_D
  have hRcl := Thompson.eq_closure_pair hp hq d.hyp d.hW d.late_R_mem_D hu hrR hrW
  obtain ⟨K₂, z₂, hd⟩ := Sec71.exists_dData hp hq d.hyp d.hW d.late_R_mem_D hu hRcl
  have hΩg := d.late_hΩ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩg d.late_R_mem_D.1
  have hK₂ : K₂ = K :=
    Sec6Gen.eq_of_le_of_le hΩg hd.memK d.late_mem_K d.hR.2.1 (by omega) hd.le d.hR.1
  subst hK₂
  have hz₂ : z₂ = z := hd.uinv.eq d.viol.hzK
  subst hz₂
  have hKW : Subgroup.zpowers u = K₂ ⊓ W := by
    rw [hu, d.late_R_eq, inf_assoc, inf_eq_right.mpr d.hWS, inf_comm]
  exact ⟨u, hKW, hd⟩

theorem Std20.w_modular (d : Std20 p f K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbX : b ∉ sec20X (CoreAssembly.conjClass K) z K K')
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) {Q : Subgroup G} (hQR : Q ≤ R)
    (hQb : Q ≤ Subgroup.centralizer ({b} : Set G)) (hQnc : ¬ IsCyclic ↥Q)
    (hQ8 : 8 ≤ Nat.card Q) (hQcard : 2 * Nat.card Q = Nat.card R) :
    ∃ u : G, ∃ k : ℕ, 2 ≤ k ∧ Subgroup.zpowers u = K ⊓ W ∧ orderOf u = 2 ^ (k + 1) ∧
      (∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∧
      ∃ r ∈ R, r ∉ W ∧ b * r = r * b := by
  classical
  have hKWU := d.late_KW
  have hcyc : IsCyclic ↥(K ⊓ W) := by
    obtain ⟨-, -, -, hc, -⟩ := hKWU
    exact hc
  obtain ⟨u, hu⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (K ⊓ W)).mp hcyc
  have hcR : Nat.card R = 2 * Nat.card ↥(K ⊓ W) :=
    Sec7.natCard_eq_two_mul_of_mem_USet d.branch.odd d.hyp hKWU d.late_mem_K d.hR
  have hcRu : Nat.card R = 2 * Nat.card (Subgroup.zpowers u) := by rw [hu]; exact hcR
  have hUQ : Nat.card (Subgroup.zpowers u) = Nat.card Q := by rw [hu]; omega
  have huR : Subgroup.zpowers u ≤ R := by
    rw [hu, d.late_R_eq]
    exact fun x hx => ⟨hx.1, d.hWS hx.2⟩
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) := S.isPGroup'.to_le (huR.trans d.hRS)
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  have hn3 : 3 ≤ n := by
    by_contra h
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have huo : orderOf u = 2 ^ (k + 1) := by rw [← Nat.card_zpowers, hn]
  obtain ⟨r, hrQ, hrU⟩ : ∃ r ∈ Q, r ∉ K ⊓ W := by
    by_contra h
    push Not at h
    apply hQnc
    have hle : Q ≤ Subgroup.zpowers u := hu ▸ h
    exact Subgroup.isCyclic_of_le hle
  have hrR : r ∈ R := hQR hrQ
  have hrW : r ∉ W := fun h => hrU ⟨d.hR.1 hrR, h⟩
  have hra : b * r = r * b := (Subgroup.mem_centralizer_singleton_iff.mp (hQb hrQ)).symm
  refine ⟨u, k, by omega, hu, huo, ?_, r, hrR, hrW, hra⟩
  have hu2 : b * u ^ 2 * b⁻¹ = u ^ 2 := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (hQb (w_sq_mem_of_card_eq huR hcRu hQR hUQ.symm))
    calc b * u ^ 2 * b⁻¹ = u ^ 2 * b * b⁻¹ := by rw [h]
      _ = u ^ 2 := by group
  have hbW : b ∈ Subgroup.normalizer (W : Set G) := d.hWN hbS
  have hconj : ∀ x ∈ K ⊓ W, b * x * b⁻¹ ∈ K ⊓ W := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp hbN x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp hbW x).mp hx.2⟩
  have hxU : b * u * b⁻¹ ∈ Subgroup.zpowers u := by
    rw [hu]
    exact hconj u (hu ▸ Subgroup.mem_zpowers u)
  have hu1 : b * u * b⁻¹ ≠ u := by
    intro h
    apply hbX
    have hcl := w_closure_pair_eq_of_card (huR (Subgroup.mem_zpowers u)) hcRu hrR
      (hu ▸ hrU)
    have hbR : ∀ x ∈ R, x * b = b * x := by
      intro x hx
      rw [hcl] at hx
      have hle : Subgroup.closure ({u, r} : Set G) ≤ Subgroup.centralizer ({b} : Set G) := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          calc y * b = b * y * b⁻¹ * b := by rw [h]
            _ = b * y := by group
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hra.symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    have hV2 : IsPGroup 2 ↥(Subgroup.zpowers b) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hbS)
    have hVK : ∀ y ∈ Subgroup.zpowers b, conjSub y K = K := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mp (Subgroup.zpowers_le.mpr hbN hy)
    have hcomm : ∀ x ∈ R, ∀ v ∈ Subgroup.zpowers b, x * v = v * x := by
      intro x hx v hv
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_right (show Commute x b from hbR x hx) i).eq
    have hmem : b ∈ centralizerModOdd (S : Subgroup G) K :=
      ⟨hbS, hbN, Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer hbN, fun k hk =>
        Sec6Gen.commutator_mem_oddCoreOf_of_centralizes d.viol.hzK d.hR hV2 hVK hcomm k hk b
          (Subgroup.mem_zpowers b)⟩
    exact le_sec20X_right (d.hR'.1 (d.late_stepA c7 hmem))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxU
  have hcomm : Commute (b * u * b⁻¹) u := by
    rw [← hm]
    exact Commute.zpow_left (Commute.refl u) m
  have hc : Commute (b * u * b⁻¹) u⁻¹ := hcomm.inv_right
  have hyU : b * u * b⁻¹ * u⁻¹ ∈ Subgroup.zpowers u :=
    Subgroup.mul_mem _ hxU (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
  have hyy : b * u * b⁻¹ * u⁻¹ * (b * u * b⁻¹ * u⁻¹) = 1 := by
    calc b * u * b⁻¹ * u⁻¹ * (b * u * b⁻¹ * u⁻¹) =
        b * u * b⁻¹ * (u⁻¹ * (b * u * b⁻¹)) * u⁻¹ := by group
      _ = b * u * b⁻¹ * ((b * u * b⁻¹) * u⁻¹) * u⁻¹ := by rw [← hc.eq]
      _ = (b * (u * u) * b⁻¹) * (u * u)⁻¹ := by group
      _ = 1 := by rw [← sq, hu2, mul_inv_cancel]
  have hy : b * u * b⁻¹ * u⁻¹ = u ^ 2 ^ k :=
    ((w_isUniqueInvolution_zpowers huo).unique _ hyU hyy).resolve_left
      (fun h => hu1 (by rw [← mul_inv_eq_one]; exact h))
  have hbu : b * u * b⁻¹ = u ^ ((2 : ℤ) ^ k + 1) := by
    rw [zpow_add_one, show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      ← hy]
    group
  intro x hx
  rw [← hu] at hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hbu, ← zpow_mul, ← zpow_mul, mul_comm]

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
