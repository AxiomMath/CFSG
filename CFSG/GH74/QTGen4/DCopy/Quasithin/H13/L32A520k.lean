module

public import CFSG.Quasithin.H13.L32A520k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A520j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Holt
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace E9R_F4
open CFSG.Quasithin.H13.L32A.E9R_F4

variable {T L V H Y R : Subgroup G} (B : E9R_F4 T L V H Y R)
include B

theorem cRP_le_c0_F4 : cRP Y R ≤ c0 H Y := fun c hc => by
  refine mem_centralizerSection.mpr ⟨B.R_le_H_F4 hc.1, B.R_le_N_Y_F4 hc.1, B.HQ_F4 (B.R_le_H_F4 hc.1),
    fun y hy => ?_⟩
  obtain ⟨q, hq, p, hp, rfl⟩ := B.mem_Y_F4 hy
  have hpc : p * c = c * p := Subgroup.mem_centralizer_iff.mp hc.2 p hp
  have hcq : c * q⁻¹ * c⁻¹ ∈ pCoreOf 2 Y :=
    (Subgroup.mem_normalizer_iff.mp (B.HQ_F4 (B.R_le_H_F4 hc.1)) _).mp (inv_mem hq)
  have e : q * p * c * (q * p)⁻¹ * c⁻¹ = q * (c * q⁻¹ * c⁻¹) := by
    rw [show q * p * c * (q * p)⁻¹ * c⁻¹ = q * (p * c) * p⁻¹ * q⁻¹ * c⁻¹ by group, hpc]
    group
  rw [e]
  exact mul_mem hq hcq

theorem card_elem_le_F4 {E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk2 : k ≤ 2 := (CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hEH hE hk).trans
    (pRank_le_two_of_pCoreOf_ne_bot B.S.hyp.fsu.qtke B.S.hz.1.2 Nat.prime_three (by norm_num))
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem cube_mem_P2_F4 {c : G} (hc : c ∈ cRP Y R) (hc3 : c ^ 3 ∈ pP Y R) :
    c ^ 3 ∈ pP2 T V Y R := by
  have hc0 := B.cRP_le_c0_F4 hc
  obtain ⟨m, hm⟩ := B.R3_F4 ⟨c, hc.1⟩
  have hm' : c ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcM := (B.toE9Ctx_F4.c0_le_N_K_F4.trans B.toE9Ctx_F4.normalizer_K_le_F4) hc0
  have ht := B.toE9Ctx_F4.psi_facts_F4.2.2.2 c (B.R_le_H_F4 hc.1) hcM m hm'
  exact ⟨hc3.1, hc3.2, ht⟩

theorem cent_le_P_F4 : cRP Y R ≤ pP Y R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro c₀ hc₀
  by_contra hc₀P

  obtain ⟨m₀, hm₀⟩ := B.R3_F4 ⟨c₀, hc₀.1⟩
  have hm₀' : c₀ ^ 3 ^ m₀ ∈ pP Y R := by
    have : c₀ ^ 3 ^ m₀ = 1 := by simpa using congrArg Subtype.val hm₀
    rw [this]
    exact one_mem _
  have hex : ∃ n : ℕ, c₀ ^ 3 ^ n ∈ pP Y R := ⟨m₀, hm₀'⟩
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := fun h => hc₀P (by have := Nat.find_spec hex; rw [← hn, h] at this; simpa)
  set c := c₀ ^ 3 ^ (n - 1) with hcdef
  have hcR : c ∈ cRP Y R := (cRP Y R).pow_mem hc₀ _
  have hcP : c ∉ pP Y R := Nat.find_min hex (by omega : n - 1 < n)
  have hc3 : c ^ 3 ∈ pP Y R := by
    have h := Nat.find_spec hex
    rw [← hn] at h
    rw [hcdef, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]
    exact h
  have hc3P2 := B.cube_mem_P2_F4 hcR hc3

  have hc31 : c ^ 3 ≠ 1 := by
    intro h1
    have hcomm : ∀ p ∈ pP Y R, p * c = c * p := fun p hp =>
      Subgroup.mem_centralizer_iff.mp hcR.2 p hp
    set E := pP Y R ⊔ Subgroup.zpowers c with hE
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((pP Y R : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (B.R_le_N_P_F4 hcR.1)
    have hmemE : ∀ x ∈ E, ∃ p ∈ pP Y R, ∃ z : ℤ, x = p * c ^ z := fun x hx => by
      obtain ⟨p, hp, w, hw, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hcN).mp hx
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact ⟨p, hp, z, rfl⟩
    have hcz : ∀ p ∈ pP Y R, ∀ z : ℤ, p * c ^ z = c ^ z * p := fun p hp z =>
      ((Commute.zpow_right (hcomm p hp) z))
    have hElem : IsElemAbelian 3 E := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨p, hp, z, hpz⟩ := hmemE a a.2
        obtain ⟨p', hp', z', hpz'⟩ := hmemE b b.2
        change (a : G) * b = b * a
        rw [hpz, hpz']
        have hc1 : Commute p (p' * c ^ z') :=
          Commute.mul_right (B.P_comm_F4 hp hp') (hcz p hp z')
        have hc2 : Commute (c ^ z) (p' * c ^ z') :=
          Commute.mul_right (hcz p' hp' z).symm (Commute.zpow_zpow_self c z z')
        exact Commute.mul_left hc1 hc2
      · obtain ⟨p, hp, z, rfl⟩ := hmemE x hx
        have e2 : (c ^ z) ^ 3 = (c ^ 3) ^ z := by
          rw [← zpow_natCast (c ^ z) 3, ← zpow_mul, ← zpow_natCast c 3, ← zpow_mul, mul_comm]
        have e : (p * c ^ z) ^ 3 = p ^ 3 * (c ^ 3) ^ z := by
          rw [Commute.mul_pow (hcz p hp z) 3, e2]
        rw [e, B.P_cube_F4 hp, h1, one_zpow, one_mul]
    have hEH : E ≤ H := sup_le (inf_le_left.trans B.R_le_H_F4)
      (Subgroup.zpowers_le.mpr (B.R_le_H_F4 hcR.1))
    have hcard := B.card_elem_le_F4 hEH hElem
    have hPE : pP Y R ≤ E := le_sup_left
    have hne : (pP Y R).relIndex E ≠ 1 := fun h =>
      hcP (Subgroup.relIndex_eq_one.mp h (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))
    have hm := relIndex_mul_card' hPE
    rw [B.card_P_F4] at hm
    have hpos : (pP Y R).relIndex E ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega

  have hP2 : pP2 T V Y R = Subgroup.zpowers (c ^ 3) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc3P2) ?_).symm
    rw [B.card_P2_F4, Nat.card_zpowers, orderOf_eq_prime (B.P_cube_F4 ((P2_le_P T V Y R) hc3P2)) hc31]

  obtain ⟨r, hr, hr0⟩ := Set.not_subset.mp B.nc0
  have hrC : r ∉ cRP Y R := fun h => hr0 (B.cRP_le_c0_F4 h)
  apply hrC

  have hrcr : r * c * r⁻¹ ∈ cRP Y R := by
    refine ⟨R.mul_mem (R.mul_mem hr hcR.1) (R.inv_mem hr), Subgroup.mem_centralizer_iff.mpr
      fun p hp => ?_⟩
    have hp' : r⁻¹ * p * r ∈ pP Y R := by
      have := (Subgroup.mem_normalizer_iff.mp (B.R_le_N_P_F4 (R.inv_mem hr)) p).mp hp
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hcR.2 _ hp'
    calc p * (r * c * r⁻¹) = r * ((r⁻¹ * p * r) * c) * r⁻¹ := by group
      _ = r * (c * (r⁻¹ * p * r)) * r⁻¹ := by rw [h1]
      _ = r * c * r⁻¹ * p := by group
  have hrc3 : (r * c * r⁻¹) ^ 3 ∈ pP Y R := by
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp (B.R_le_N_P_F4 hr) _).mp hc3
  have hrc3P2 := B.cube_mem_P2_F4 hrcr hrc3
  rw [conj_pow] at hrc3P2

  have hrN : r ∈ Subgroup.normalizer ((pP2 T V Y R : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : x ∈ Subgroup.zpowers (c ^ 3) := by rw [← hP2]; exact hx
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    rw [← conj_zpow]
    exact (pP2 T V Y R).zpow_mem hrc3P2 z

  have hcP2 : pP2 T V Y R ≤ Subgroup.centralizer ({r} : Set G) := fun p hp => by
    have h1 := B.R_comm_P_F4 hr ((P2_le_P T V Y R) hp)
    have h2 : p * r * p⁻¹ * r⁻¹ ∈ pP2 T V Y R := by
      rw [show p * r * p⁻¹ * r⁻¹ = p * (r * p⁻¹ * r⁻¹) by group]
      exact mul_mem hp ((Subgroup.mem_normalizer_iff.mp hrN _).mp (inv_mem hp))
    have h3 : p * r * p⁻¹ * r⁻¹ ∈ pP1 T L V Y R ⊓ pP2 T V Y R := ⟨h1, h2⟩
    rw [B.P1_inf_P2_F4, Subgroup.mem_bot] at h3
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
      _ = r * p := by rw [h3, one_mul]
  have hcP1 : pP1 T L V Y R ≤ Subgroup.centralizer ({r} : Set G) := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact B.R_comm_P1_F4 hr hp
  refine ⟨hr, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have := (B.P_le_F4.trans (sup_le hcP2 hcP1)) hp
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem P2_eq_zpowers_F4 {k₀ : G} (hk : k₀ ∈ pP2 T V Y R) (hk1 : k₀ ≠ 1) :
    pP2 T V Y R = Subgroup.zpowers k₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hk) ?_).symm
  rw [B.card_P2_F4, Nat.card_zpowers, orderOf_eq_prime (B.P_cube_F4 ((P2_le_P T V Y R) hk)) hk1]

theorem exists_k0_F4 : ∃ k₀ ∈ pP2 T V Y R, k₀ ≠ 1 := by
  by_contra h
  push Not at h
  have hb : pP2 T V Y R = ⊥ := eq_bot_iff.mpr fun x hx => h x hx
  have := B.card_P2_F4
  rw [hb, Subgroup.card_bot] at this
  exact absurd this (by norm_num)

theorem mem_cRP_of_comm_F4 {k₀ r : G} (hk : k₀ ∈ pP2 T V Y R) (hk1 : k₀ ≠ 1) (hr : r ∈ R)
    (hkr : k₀ * r = r * k₀) : r ∈ cRP Y R := by
  have hcP2 : pP2 T V Y R ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [B.P2_eq_zpowers_F4 hk hk1, Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hkr
  have hcP1 : pP1 T L V Y R ≤ Subgroup.centralizer ({r} : Set G) := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact B.R_comm_P1_F4 hr hp
  refine ⟨hr, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have := (B.P_le_F4.trans (sup_le hcP2 hcP1)) hp
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem relIndex_P_F4 : (pP Y R).relIndex R = 3 ∧ ∀ r ∈ R, r ^ 3 ∈ pP Y R := by
  obtain ⟨k₀, hk, hk1⟩ := B.exists_k0_F4
  have hk₀P : k₀ ∈ pP Y R := (P2_le_P T V Y R) hk
  let σ : ↥R →* ↥(pP1 T L V Y R) := MonoidHom.mk' (fun r =>
    ⟨k₀ * r * k₀⁻¹ * (r : G)⁻¹, B.R_comm_P_F4 r.2 hk₀P⟩) (fun r s => by
      apply Subtype.ext
      have hc := B.R_comm_P1_F4 r.2 (B.R_comm_P_F4 s.2 hk₀P)
      simp only [Subgroup.coe_mul]
      calc k₀ * (r * s) * k₀⁻¹ * ((r : G) * s)⁻¹ =
          k₀ * r * k₀⁻¹ * (r : G)⁻¹ * ((r : G) * (k₀ * s * k₀⁻¹ * (s : G)⁻¹) * (r : G)⁻¹) := by
            group
        _ = k₀ * r * k₀⁻¹ * (r : G)⁻¹ * (k₀ * s * k₀⁻¹ * (s : G)⁻¹) := by
            rw [← hc]
            group)
  have hker : σ.ker = (pP Y R).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : k₀ * r * k₀⁻¹ * (r : G)⁻¹ = 1 := congrArg Subtype.val h
      have hkr : k₀ * r = r * k₀ := by
        calc k₀ * (r : G) = k₀ * r * k₀⁻¹ * (r : G)⁻¹ * (r * k₀) := by group
          _ = r * k₀ := by rw [h1, one_mul]
      exact B.cent_le_P_F4 (B.mem_cRP_of_comm_F4 hk hk1 r.2 hkr)
    · intro h
      apply Subtype.ext
      change k₀ * r * k₀⁻¹ * (r : G)⁻¹ = 1
      rw [B.P_comm_F4 hk₀P h]
      group
  have hidx : (pP Y R).relIndex R ≤ 3 := by
    change ((pP Y R).subgroupOf R).index ≤ 3
    rw [← hker, Subgroup.index_ker, ← B.card_P1_F4]
    exact Nat.card_le_card_of_injective (fun x : σ.range => (x : ↥(pP1 T L V Y R)))
      Subtype.val_injective
  have hne : (pP Y R).relIndex R ≠ 1 := fun h =>
    B.nc0 ((Subgroup.relIndex_eq_one.mp h).trans (inf_le_right.trans B.toE9Ctx_F4.Y_le_c0_F4))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := B.R3_F4.exists_card_eq
  have hdvd : (pP Y R).relIndex R ∣ 3 ^ n := hn ▸ Subgroup.index_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  refine ⟨?_, fun r hr => ?_⟩
  · rcases i with _ | _ | i
    · exact absurd hi (by simpa using hne)
    · simpa using hi
    · rw [hi] at hidx
      have h1 : 3 ^ (i + 1 + 1) = 9 * 3 ^ i := by ring
      have h2 : 0 < 3 ^ i := pow_pos (by norm_num) i
      omega
  · have h1 : σ (⟨r, hr⟩ ^ 3) = 1 := by
      rw [map_pow]
      exact Subtype.ext (by
        simpa using B.P_cube_F4 (B.P1_le_P_F4 (σ ⟨r, hr⟩).2))
    have h2 : (⟨r, hr⟩ : ↥R) ^ 3 ∈ (pP Y R).subgroupOf R := hker ▸ h1
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h2
    exact h2

theorem cube_mem_P1_F4 {r : G} (hr : r ∈ R) : r ^ 3 ∈ pP1 T L V Y R := by
  have hr3 := B.relIndex_P_F4.2 r hr
  by_cases hrP : r ∈ pP Y R
  · rw [B.P_cube_F4 hrP]
    exact one_mem _
  set Z := pP Y R ⊓ Subgroup.centralizer ({r} : Set G) with hZ
  have hP1Z : pP1 T L V Y R ≤ Z := fun p hp => Subgroup.mem_inf.mpr
    ⟨B.P1_le_P_F4 hp, Subgroup.mem_centralizer_singleton_iff.mpr (B.R_comm_P1_F4 hr hp)⟩
  have hZP : Z ≤ pP Y R := inf_le_left
  have hZne : Z ≠ pP Y R := fun h => hrP (B.cent_le_P_F4 ⟨hr, Subgroup.mem_centralizer_iff.mpr
    fun p hp => by
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (h ▸ hp : p ∈ Z)).2⟩)
  have h3 : (pP1 T L V Y R).relIndex (pP Y R) = 3 := by
    have hm := relIndex_mul_card' B.P1_le_P_F4
    rw [B.card_P_F4, B.card_P1_F4] at hm
    omega
  have hm := Subgroup.relIndex_mul_relIndex _ _ _ hP1Z hZP
  rw [h3] at hm
  have hd : Z.relIndex (pP Y R) ∣ 3 := ⟨_, by rw [mul_comm] at hm; exact hm.symm⟩
  have hZP1 : Z ≤ pP1 T L V Y R := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (le_antisymm hZP (Subgroup.relIndex_eq_one.mp h)) hZne
    · rw [h] at hm
      have h1 : (pP1 T L V Y R).relIndex Z = 1 := by omega
      exact Subgroup.relIndex_eq_one.mp h1
  exact hZP1 (Subgroup.mem_inf.mpr ⟨hr3, Subgroup.mem_centralizer_singleton_iff.mpr
    (by rw [← pow_succ, ← pow_succ'])⟩)

theorem inf_M_le_P_F4 {r : G} (hr : r ∈ R) (hrM : r ∈ Subgroup.normalizer (L : Set G)) :
    r ∈ pP Y R := by
  have hc0 := B.toE9Ctx_F4.c1_inf_le_c0_F4 (B.R_le_c1_F4 hr) (B.toE9Ctx_F4.HM_le_N_K_F4 (B.R_le_H_F4 hr) hrM)
  refine B.cent_le_P_F4 ⟨hr, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
  have h := (mem_centralizerSection.mp hc0).2.2.2 p hp.2
  have hR : p * r * p⁻¹ * r⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hp.1 hr) (R.inv_mem hp.1)) (R.inv_mem hr)
  have h1 := B.mem_R_inf_Q_F4 hR h
  calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
    _ = r * p := by rw [h1, one_mul]

end E9R_F4

end CFSG.Quasithin.H13.L32A
