module

public import CFSG.GF2Type.Smith1979.IdxFourIdentMon2
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU

namespace MonAux

theorem mem_normalizer_D5_iff {g : G12} :
    g ∈ Subgroup.normalizer (D5 : Set G12) ↔ ∀ d ∈ D5, g * d * g⁻¹ ∈ D5 := by
  refine ⟨fun h d hd => (Subgroup.mem_normalizer_iff.1 h d).1 hd, fun h => ?_⟩
  refine Subgroup.mem_normalizer_iff.2 fun d => ⟨h d, fun hd => ?_⟩
  have h1 := conj_inv_mem_D5 h _ hd
  rwa [show g⁻¹ * (g * d * g⁻¹) * g = d by group] at h1

end MonAux

open MonAux

theorem exists_twist (X E : Subgroup G12) (hXg : X ≤ gammaU) (hEX : E ≤ X)
    (hEn : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hX4 : Nat.card X = 4 * Nat.card E) (hXcard : Nat.card X = 39191040)
    (hEu : ∀ e ∈ E, e * theta0e = theta0e * e) (hD5 : D5 ≤ E)
    (hfr : ∀ x ∈ X, ∃ e ∈ E, ∃ n ∈ X, (∀ d ∈ D5, n * d * n⁻¹ ∈ D5) ∧ x = e * n)
    (hA6 : ∀ π ∈ alternatingGroup (Fin 6), permE π ∈ E) :
    ∃ m ∈ monGamma, Nsub ≤ X.map (MulAut.conj m).toMonoidHom := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G12, Q = X ⊓ Subgroup.normalizer (D5 : Set G12) := ⟨_, rfl⟩
  have mem_Q : ∀ {x : G12}, x ∈ Q ↔ x ∈ X ∧ ∀ d ∈ D5, x * d * x⁻¹ ∈ D5 := by
    intro x
    rw [hQ, Subgroup.mem_inf, mem_normalizer_D5_iff]
  have hQX : Q ≤ X := fun x hx => (mem_Q.1 hx).1
  have hQm : Q ≤ monGamma := fun x hx =>
    mem_monGamma_of_normalizes_D5 (hXg (mem_Q.1 hx).1) (mem_Q.1 hx).2
  have hRlin : E ⊓ Q ≤ monLin := fun x hx =>
    Subgroup.mem_inf.2 ⟨hQm (Subgroup.mem_inf.1 hx).2, Subgroup.mem_centralizer_iff.2
      fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (hEu x (Subgroup.mem_inf.1 hx).1).symm⟩
  have hR0E : R0 ≤ E := by
    rintro _ ⟨c, π, hc, hπ, rfl⟩
    exact mul_mem (hD5 ⟨c, hc, rfl⟩) (hA6 π hπ)
  have hR0Q : R0 ≤ Q := fun r hr => mem_Q.2 ⟨hEX (hR0E hr), fun _ hd =>
    mul_mem_D5_of_mem_monGamma (monLin_le_monGamma (R0_le_monLin hr)) hd⟩
  have hEc : Nat.card E = 9797760 := by omega
  have hQ4 : Nat.card Q = 4 * Nat.card (E ⊓ Q : Subgroup G12) := by
    haveI : (E.subgroupOf X).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hEn g g.2 n hn⟩
    have hsup : E.subgroupOf X ⊔ Q.subgroupOf X = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨e, he, n, hn, hnD, rfl⟩ := hfr x hx
      exact Subgroup.mul_mem_sup (x := (⟨e, hEX he⟩ : X)) (y := (⟨n, hn⟩ : X)) he
        (mem_Q.2 ⟨hn, hnD⟩)
    have h1 := Subgroup.relIndex_sup_left (Q.subgroupOf X) (E.subgroupOf X)
    rw [hsup, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hQX] at h1
    have h2 : E.relIndex X = 4 := by
      have h := Subgroup.relIndex_mul_card E X
      rw [inf_of_le_left hEX, hEc, hXcard] at h
      omega
    have h3 := Subgroup.relIndex_mul_card E Q
    rw [(h1.symm.trans h2 : E.relIndex Q = 4)] at h3
    omega
  have hQc : Nat.card Q = 349920 := by
    have d1 : 87480 ∣ Nat.card (E ⊓ Q : Subgroup G12) := by
      rw [← card_R0]
      exact Subgroup.card_dvd_of_le (le_inf hR0E hR0Q)
    have d2 : Nat.card (E ⊓ Q : Subgroup G12) ∣ 524880 := by
      have h := Subgroup.card_dvd_of_le hRlin
      rwa [card_monLin] at h
    have d3 : Nat.card (E ⊓ Q : Subgroup G12) ∣ 9797760 := by
      rw [← hEc]
      exact Subgroup.card_dvd_of_le inf_le_left
    have d4 : Nat.card Q ∣ 1049760 := by
      have h := Subgroup.card_dvd_of_le hQm
      rwa [card_monGamma] at h
    rw [hQ4] at d4 ⊢
    obtain ⟨k, hk⟩ := d1
    rw [hk] at d2 d3 d4 ⊢
    have hk6 : k ≤ 6 := by
      have := Nat.le_of_dvd (by norm_num) d2
      omega
    interval_cases k <;> omega
  haveI : (R0.subgroupOf monGamma).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using mul_mem_R0_of_mem_monGamma g.2 hn⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : monGamma →* monGamma ⧸ R0.subgroupOf monGamma,
      φ = QuotientGroup.mk' (R0.subgroupOf monGamma) := ⟨_, rfl⟩
  have hφs : Function.Surjective φ := hφ ▸ QuotientGroup.mk'_surjective _
  have hφk : φ.ker = R0.subgroupOf monGamma := hφ ▸ QuotientGroup.ker_mk' _
  have hD : Nat.card (monGamma ⧸ R0.subgroupOf monGamma) = 12 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (R0.subgroupOf monGamma)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (R0_le_Nsub.trans Nsub_le_monGamma)).toEquiv, card_R0, card_monGamma] at h
    omega
  haveI : Finite (monGamma ⧸ R0.subgroupOf monGamma) :=
    Nat.finite_of_card_ne_zero (by rw [hD]; norm_num)
  have himage : ∀ H : Subgroup G12, R0 ≤ H → H ≤ monGamma → Nat.card H = 349920 →
      ((H.subgroupOf monGamma).map φ).index = 3 ∧
        Nat.card ((H.subgroupOf monGamma).map φ) = 2 ^ 2 := by
    intro H hR0H hHm hHc
    have hker : φ.ker ≤ H.subgroupOf monGamma := by
      rw [hφk]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hR0H hx
    have hi : (H.subgroupOf monGamma).index = 3 := by
      have h := Subgroup.card_mul_index (H.subgroupOf monGamma)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHm).toEquiv, hHc, card_monGamma] at h
      omega
    have hmi : ((H.subgroupOf monGamma).map φ).index = 3 := by
      rw [Subgroup.index_map_eq _ hφs hker, hi]
    have h := Subgroup.card_mul_index ((H.subgroupOf monGamma).map φ)
    rw [hmi, hD] at h
    exact ⟨hmi, by omega⟩
  obtain ⟨hQi, hQ2⟩ := himage Q hR0Q hQm hQc
  obtain ⟨hNi, hN2⟩ := himage Nsub R0_le_Nsub Nsub_le_monGamma card_Nsub
  have hQs : ¬ 2 ∣ ((Q.subgroupOf monGamma).map φ).index := by rw [hQi]; decide
  have hNs : ¬ 2 ∣ ((Nsub.subgroupOf monGamma).map φ).index := by rw [hNi]; decide
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (monGamma ⧸ R0.subgroupOf monGamma)
    ((IsPGroup.of_card hQ2).toSylow hQs) ((IsPGroup.of_card hN2).toSylow hNs)
  obtain ⟨m, rfl⟩ := hφs x
  refine ⟨m, m.2, fun n hn => ?_⟩
  have h2 : φ ⟨n, Nsub_le_monGamma hn⟩ ∈
      ((φ m • (IsPGroup.of_card hQ2).toSylow hQs : Sylow 2 _) : Subgroup _) := by
    rw [hx, IsPGroup.toSylow_coe]
    exact Subgroup.mem_map_of_mem φ hn
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply, IsPGroup.toSylow_coe] at h2
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.1 h2
  have hk : q⁻¹ * (m⁻¹ * ⟨n, Nsub_le_monGamma hn⟩ * m) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hqe, inv_mul_cancel]
  rw [hφk, Subgroup.mem_subgroupOf] at hk
  rw [Subgroup.mem_subgroupOf] at hq
  have hy : (m : G12)⁻¹ * n * m ∈ Q := by simpa using mul_mem hq (hR0Q hk)
  exact Subgroup.mem_map.2 ⟨(m : G12)⁻¹ * n * m, hQX hy, by simp [mul_assoc]⟩

end CFSG.GF2Type.Smith1979.IdxFour
