module

public import CFSG.ClassicalInvolution.AschTight.S1916InvQD
public import CFSG.ClassicalInvolution.AschTight.S19BFus

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.GorensteinWalter

theorem two_pow_dvd_sub_or_add {n : ℕ} {k : ℤ} (h : (2 : ℤ) ^ (n + 2) ∣ k ^ 2 - 1) :
    (2 : ℤ) ^ (n + 1) ∣ k - 1 ∨ (2 : ℤ) ^ (n + 1) ∣ k + 1 := by
  obtain ⟨m, hm⟩ := h
  rcases Int.even_or_odd k with ⟨b, rfl⟩ | ⟨a, rfl⟩
  · exfalso
    have e1 : (b + b) ^ 2 - 1 = 2 * (2 * b * b - 1) + 1 := by ring
    have e2 : (2 : ℤ) ^ (n + 2) * m = 2 * (2 ^ (n + 1) * m) := by ring
    rw [e1, e2] at hm
    generalize 2 * b * b - 1 = B at hm
    generalize (2 : ℤ) ^ (n + 1) * m = M at hm
    omega
  · have hm' : a * (a + 1) = 2 ^ n * m := by
      have : (4 : ℤ) * (a * (a + 1)) = 4 * (2 ^ n * m) := by
        rw [show (4 : ℤ) * (a * (a + 1)) = (2 * a + 1) ^ 2 - 1 by ring, hm]
        ring
      exact mul_left_cancel₀ (by norm_num) this
    rcases Int.even_or_odd a with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · left
      have hco : IsCoprime ((2 : ℤ) ^ n) (c + c + 1) :=
        IsCoprime.pow_left ⟨-c, 1, by ring⟩
      have hdvd : (2 : ℤ) ^ n ∣ (c + c) * (c + c + 1) := ⟨m, hm'⟩
      obtain ⟨d, hd⟩ := hco.dvd_of_dvd_mul_right hdvd
      exact ⟨d, by rw [pow_succ]; linear_combination 2 * hd⟩
    · right
      have hco : IsCoprime ((2 : ℤ) ^ n) (2 * c + 1) :=
        IsCoprime.pow_left ⟨-c, 1, by ring⟩
      have hdvd : (2 : ℤ) ^ n ∣ (2 * c + 1 + 1) * (2 * c + 1) := ⟨m, by rw [← hm']; ring⟩
      obtain ⟨d, hd⟩ := hco.dvd_of_dvd_mul_right hdvd
      exact ⟨d, by rw [pow_succ]; linear_combination 2 * hd⟩

variable {G : Type} [Group G]

theorem conj_eq_z_mul_or {u a : G} {N : ℕ} (hN : orderOf u = 2 ^ N) (h4 : 4 ≤ orderOf u)
    (hau : a * u * a⁻¹ ∈ Subgroup.zpowers u) (ha2 : a * a = 1) (hnc : a * u * a⁻¹ ≠ u)
    (hni : a * u * a⁻¹ ≠ u⁻¹) :
    8 ≤ orderOf u ∧ (a * u * a⁻¹ = u ^ (orderOf u / 2) * u ∨
      a * u * a⁻¹ = u ^ (orderOf u / 2) * u⁻¹) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by
    have : 2 ^ 2 ≤ 2 ^ N := hN ▸ h4
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hau
  have hk2 : u ^ (k ^ 2 - 1) = 1 := by
    have h1 : a * (a * u * a⁻¹) * a⁻¹ = u := by
      calc a * (a * u * a⁻¹) * a⁻¹ = (a * a) * u * (a * a)⁻¹ := by group
        _ = u := by rw [ha2]; group
    rw [← hk, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ← hk, ← zpow_mul] at h1
    rw [zpow_sub, zpow_one, sq, h1, mul_inv_cancel]
  have hdvd : ((2 ^ (n + 2) : ℕ) : ℤ) ∣ k ^ 2 - 1 := hN ▸ orderOf_dvd_iff_zpow_eq_one.mpr hk2
  push_cast at hdvd
  have h21 : orderOf u / 2 = 2 ^ (n + 1) := by rw [hN, pow_succ]; omega
  have hz : u ^ (orderOf u / 2) = u ^ ((2 : ℤ) ^ (n + 1)) := by
    rw [h21, ← zpow_natCast]
    push_cast
    rfl
  have hoz : ((orderOf u : ℕ) : ℤ) = (2 : ℤ) ^ (n + 1) * 2 := by
    rw [hN]
    push_cast
    ring
  have hz2 : u ^ ((2 : ℤ) ^ (n + 1)) * u ^ ((2 : ℤ) ^ (n + 1)) = 1 := by
    rw [← zpow_add, ← mul_two, ← hoz, zpow_natCast, pow_orderOf_eq_one]
  have hzj : ∀ j : ℤ, (u ^ ((2 : ℤ) ^ (n + 1))) ^ j = 1 ∨
      (u ^ ((2 : ℤ) ^ (n + 1))) ^ j = u ^ ((2 : ℤ) ^ (n + 1)) := fun j =>
    CFSG.ClassicalInvolution.Disconnected.AschTight.eq_one_or_eq_of_mem_zpowers_of_mul_self hz2
      (Subgroup.zpow_mem_zpowers _ _)
  have hform : a * u * a⁻¹ = u ^ (orderOf u / 2) * u ∨
      a * u * a⁻¹ = u ^ (orderOf u / 2) * u⁻¹ := by
    rw [hz]
    rcases two_pow_dvd_sub_or_add hdvd with ⟨j, hj⟩ | ⟨j, hj⟩
    · have e : a * u * a⁻¹ = (u ^ ((2 : ℤ) ^ (n + 1))) ^ j * u := by
        rw [← hk, ← zpow_mul, ← zpow_add_one, ← hj]
        ring_nf
      rcases hzj j with h | h
      · exact absurd (by rw [e, h, one_mul]) hnc
      · left
        rw [e, h]
    · have e : a * u * a⁻¹ = (u ^ ((2 : ℤ) ^ (n + 1))) ^ j * u⁻¹ := by
        rw [← hk, ← zpow_mul, ← zpow_neg_one, ← zpow_add, ← hj]
        ring_nf
      rcases hzj j with h | h
      · exact absurd (by rw [e, h, one_mul]) hni
      · right
        rw [e, h]
  refine ⟨?_, hform⟩
  by_contra h8
  have hn0 : n = 0 := by
    have : 2 ^ (n + 2) < 2 ^ 3 := by rw [← hN]; omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega
  subst hn0
  have hu4 : u ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 ^ (0 + 2) by norm_num, ← hN, pow_orderOf_eq_one]
  have hhalf : u ^ (orderOf u / 2) = u ^ 2 := by rw [hN]; norm_num
  rcases hform with h | h
  · apply hni
    rw [h, hhalf, eq_inv_iff_mul_eq_one]
    calc u ^ 2 * u * u = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := hu4
  · apply hnc
    rw [h, hhalf, sq, mul_inv_cancel_right]

variable [Finite G] {p f : ℕ} [Fact p.Prime] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem not_forall_comm_of_not_mem (hDT : Sec19DataT p f K z S W L t V) {s : G}
    (hsS : s ∈ (S : Subgroup G)) (hsX : s ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ¬ ∀ u ∈ K ⊓ W, s * u = u * s := by
  intro hcomm'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have ht := hd.tight
  obtain ⟨⟨e⟩, hFcard, hF, h3⟩ := Hall196.exists_data_of_tightBranchD ht
  have haN : s ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd).ge (hd.hSz hsS)
  have hac : ∀ y ∈ (S : Subgroup G) ⊓ K ⊓ W, s * y = y * s := fun y hy =>
    hcomm' y ⟨hy.1.2, hy.2⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨s, hsS⟩
  have h2 : orderOf s = 2 ^ n := by rw [← hn, Subgroup.orderOf_mk]
  have hcard : Nat.card ↥((S : Subgroup G) ⊓ K) ≤ 2 * Nat.card ↥((S : Subgroup G) ⊓ K ⊓ W) := by
    have e1 : (S : Subgroup G) ⊓ K ⊓ W = K ⊓ W := by
      ext x
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hd.hWS h.2, h.1⟩, h.2⟩⟩
    rw [e1, S1911.card_inf_eq hd]
  have hmem : normalizerToPGammaL2Mod e hFcard hF h3 ⟨s, haN⟩ ∈
      pGammaL2PGLRange (GaloisField p f) := by
    rcases Nat.even_or_odd f with hfe | hfo
    · exact mem_range_inl_of_centralizes ht.branch.odd ht.branch.five hfe e hFcard hF h3
        (S1911.inf_mem_rSet hd) inf_le_right (S1911.comm_of_mem hd) hcard ⟨n, h2⟩ haN hac
    · refine innerDiagonalTwo_of_odd hfo e hFcard hF h3 ⟨s, haN⟩ ?_
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h2]
  exact hsX ((S1916.psi_mem_iff hd e hFcard hF h3 ⟨s, haN⟩).mp hmem)

theorem exists_gen_conj_eq (hDT : Sec19DataT p f K z S W L t V) {a : G} (haS : a ∈ (S : Subgroup G))
    (ha2 : a * a = 1) (haX : a ∉ sec19X K z ⊔ centralizerModOdd ⊤ K) :
    ∃ u : G, Subgroup.zpowers u = K ⊓ W ∧ 8 ≤ orderOf u ∧ u ^ (orderOf u / 2) = z ∧
      (a * u * a⁻¹ = z * u ∨ a * u * a⁻¹ = z * u⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  obtain ⟨-, -, -, hcyc, -⟩ := S19B.inf_mem_USet hDT
  obtain ⟨u₀, hu₀⟩ := hcyc.exists_generator
  set u : G := (u₀ : G) with hu
  have hU : Subgroup.zpowers u = K ⊓ W := (Hall196.eq_zpowers_of_generator hu₀).symm
  have huo : orderOf u = Nat.card ↥(K ⊓ W) := by
    rw [hu, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hu₀]
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := S.isPGroup'.to_le (inf_le_right.trans hd.hWS)
  obtain ⟨N, hN⟩ := hU2.exists_card_eq
  have h4 : 4 ≤ orderOf u := by rw [huo, S1911.card_inf_eq_card hDT]; exact ef.four
  have haN : a ∈ Subgroup.normalizer (K : Set G) := (S1916.sd_normalizer_eq hd).ge (hd.hSz haS)
  have hauK : a * u * a⁻¹ ∈ K ⊓ W := by
    have huKW : u ∈ K ⊓ W := hU ▸ Subgroup.mem_zpowers u
    exact ⟨(Subgroup.mem_normalizer_iff.mp haN u).mp huKW.1,
      (Subgroup.mem_normalizer_iff.mp (S19B.le_normalizer_W hDT haS) u).mp huKW.2⟩
  have hconj : ∀ j : ℤ, a * u ^ j * a⁻¹ = (a * u * a⁻¹) ^ j := fun j => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  have hnc : a * u * a⁻¹ ≠ u := by
    intro h
    apply not_forall_comm_of_not_mem hDT haS haX
    intro x hx
    rw [← hU] at hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    calc a * u ^ j = a * u ^ j * a⁻¹ * a := by group
      _ = u ^ j * a := by rw [hconj, h]
  have hni : a * u * a⁻¹ ≠ u⁻¹ := by
    intro h
    apply S1916.not_forall_inv_of_not_mem hDT haS haX
    intro x hx
    rw [← hU] at hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [hconj, h, inv_zpow]
  obtain ⟨h8, hform⟩ := conj_eq_z_mul_or (huo.trans hN) h4 (hU ▸ hauK) ha2 hnc hni
  have hev : Even (orderOf u) := by
    rw [huo, hN]
    exact (Nat.even_pow' (by rintro rfl; rw [huo, hN] at h4; norm_num at h4)).mpr even_two
  have hzu : u ^ (orderOf u / 2) = z := by
    have hmem : u ^ (orderOf u / 2) ∈ K := (hU ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers u) _ :
      u ^ (orderOf u / 2) ∈ K ⊓ W).1
    exact (hI.unique _ hmem (Hall196.pow_half_mul_self hev)).resolve_left
      (Hall196.pow_half_ne_one (by omega))
  rw [hzu] at hform
  exact ⟨u, hU, h8, hzu, hform⟩

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
