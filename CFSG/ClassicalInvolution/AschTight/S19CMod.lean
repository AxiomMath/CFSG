module

public import CFSG.ClassicalInvolution.AschTight.S19BCtl
public import CFSG.ClassicalInvolution.AschTight.S19BFus
public import CFSG.ClassicalInvolution.AschTight.Sec7L714A

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_of_card_eq {R Q : Subgroup G} {u : G} (huR : Subgroup.zpowers u ≤ R)
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

variable {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G] {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem exists_modular (hd : Sec19DataT p f K z S W L t V) {a : G} (haS : a ∈ (S : Subgroup G))
    (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) {Q : Subgroup G}
    (hQS : Q ≤ (S : Subgroup G) ⊓ K) (hQa : Q ≤ Subgroup.centralizer ({a} : Set G))
    (hQnc : ¬ IsCyclic Q) (hQ8 : 8 ≤ Nat.card Q)
    (hQcard : 2 * Nat.card Q = Nat.card ↥((S : Subgroup G) ⊓ K)) :
    ∃ u : G, ∃ k : ℕ, 2 ≤ k ∧ Subgroup.zpowers u = K ⊓ W ∧ orderOf u = 2 ^ (k + 1) ∧
      (∀ x ∈ K ⊓ W, a * x * a⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) ∧
      ∃ r ∈ (S : Subgroup G) ⊓ K, r ∉ K ⊓ W ∧ a * r = r * a := by
  have hd0 := hd.toSec19Data
  have ht := hd.tight
  obtain ⟨-, -, -, hcyc, -⟩ := S19B.inf_mem_USet hd
  obtain ⟨u, hu⟩ := S19B.exists_zpowers_eq_of_isCyclic hcyc
  have hcardR := S1911.card_inf_eq hd0
  have hUQ : Nat.card (Subgroup.zpowers u) = Nat.card Q := by rw [hu]; omega
  have huR : Subgroup.zpowers u ≤ (S : Subgroup G) ⊓ K := by
    rw [hu]
    exact fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) := S.isPGroup'.to_le (huR.trans inf_le_left)
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
  have hra : a * r = r * a := (Subgroup.mem_centralizer_singleton_iff.mp (hQa hrQ)).symm
  refine ⟨u, k, by omega, hu, huo, ?_, r, hQS hrQ, hrU, hra⟩
  have hu2 : a * u ^ 2 * a⁻¹ = u ^ 2 := by
    have h := Subgroup.mem_centralizer_singleton_iff.mp
      (hQa (sq_mem_of_card_eq huR (by rw [hcardR, hu]) (hQS.trans le_rfl) hUQ.symm))
    calc a * u ^ 2 * a⁻¹ = u ^ 2 * a * a⁻¹ := by rw [h]
      _ = u ^ 2 := by group
  have haN : a ∈ Subgroup.normalizer (K : Set G) := by
    rw [normalizer_eq_centralizer_of_tight ht.toTightBranch]
    exact hd.hSz haS
  have haW : a ∈ Subgroup.normalizer (W : Set G) := S19B.le_normalizer_W hd haS
  have hconj : ∀ x ∈ K ⊓ W, a * x * a⁻¹ ∈ K ⊓ W := fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp haN x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp haW x).mp hx.2⟩
  have hxU : a * u * a⁻¹ ∈ Subgroup.zpowers u := by
    rw [hu]
    exact hconj u (hu ▸ Subgroup.mem_zpowers u)
  have hu1 : a * u * a⁻¹ ≠ u := by
    intro h
    apply haX
    refine Subgroup.mem_sup_right (S19B.mem_centralizerModOdd_K hd haS ?_)
    have hcl := S19B.closure_pair_eq_of_card (huR (Subgroup.mem_zpowers u))
      (by rw [hcardR, hu]) (hQS hrQ) (hu ▸ hrU)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [SetLike.mem_coe, hcl] at hx
    have hle : Subgroup.closure ({u, r} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        calc y * a = a * y * a⁻¹ * a := by rw [h]
          _ = a * y := by group
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hra.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hxU
  have hcomm : Commute (a * u * a⁻¹) u := by
    rw [← hm]
    exact Commute.zpow_left (Commute.refl u) m
  have hc : Commute (a * u * a⁻¹) u⁻¹ := hcomm.inv_right
  have hyU : a * u * a⁻¹ * u⁻¹ ∈ Subgroup.zpowers u :=
    Subgroup.mul_mem _ hxU (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
  have hyy : a * u * a⁻¹ * u⁻¹ * (a * u * a⁻¹ * u⁻¹) = 1 := by
    calc a * u * a⁻¹ * u⁻¹ * (a * u * a⁻¹ * u⁻¹) =
        a * u * a⁻¹ * (u⁻¹ * (a * u * a⁻¹)) * u⁻¹ := by group
      _ = a * u * a⁻¹ * ((a * u * a⁻¹) * u⁻¹) * u⁻¹ := by rw [← hc.eq]
      _ = (a * (u * u) * a⁻¹) * (u * u)⁻¹ := by group
      _ = 1 := by rw [← sq, hu2, mul_inv_cancel]
  have hy : a * u * a⁻¹ * u⁻¹ = u ^ 2 ^ k :=
    ((Sec7.isUniqueInvolution_zpowers huo).unique _ hyU hyy).resolve_left
      (fun h => hu1 (by rw [← mul_inv_eq_one]; exact h))
  have hau : a * u * a⁻¹ = u ^ ((2 : ℤ) ^ k + 1) := by
    rw [zpow_add_one, show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hy]
    group
  intro x hx
  rw [← hu] at hx
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hau, ← zpow_mul, ← zpow_mul, mul_comm]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
