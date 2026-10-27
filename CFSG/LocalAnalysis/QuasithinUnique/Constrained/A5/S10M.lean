module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10Th
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.TwoThree
public import Certificates.Certificate17027
public import Certificates.Certificate5952

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

section Generic

variable {G : Type*} [Group G]

theorem eq_one_of_two_pow_of_odd {x : G} {k b : ℕ} (hb : Odd b) (hk : x ^ 2 ^ k = 1)
    (hodd : x ^ b = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ b := orderOf_dvd_of_pow_eq_one hodd
  have hcop : Nat.Coprime (2 ^ k) b := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hb)
  have : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

theorem pResidual2_le {M : Subgroup G} [Finite G] : pResidualOf 2 M ≤ M := by
  rw [pResidualOf_eq_opResidual]
  exact opResidual_le 2 M

theorem le_normalizer_pResidual2 [Finite G] (M : Subgroup G) :
    M ≤ Subgroup.normalizer ((pResidualOf 2 M : Subgroup G) : Set G) := by
  rw [pResidualOf_eq_opResidual]
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 M)).mp
    (opResidual_normal 2 M)

theorem mem_pResidual2_of_coprime [Finite G] {M : Subgroup G} {m : G} (hm : m ∈ M)
    (h : (orderOf m).Coprime 2) : m ∈ pResidualOf 2 M := by
  rw [pResidualOf_eq_opResidual]
  exact mem_opResidual_of_coprime hm h

end Generic

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem S_le_M (C : StdCfg T M H S L) : S ≤ M := C.hcs.le_T.trans C.hcs.setting.le

theorem T_le_M (C : StdCfg T M H S L) : T ≤ M := C.hcs.setting.le


theorem M_le_T_sup_W (C : StdCfg T M H S L) : M ≤ T ⊔ pResidualOf 2 M := by
  set Tm : Subgroup ↥M := T.subgroupOf M with hTm
  set Wm : Subgroup ↥M := (pResidualOf 2 M).subgroupOf M with hWm
  have hWmn : Wm.Normal := by
    rw [hWm, pResidualOf_eq_opResidual]
    exact opResidual_normal 2 M
  have h2grp : IsPGroup 2 (↥M ⧸ Wm) := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_opResidual (p := 2) (A := M) m.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    rw [hWm, Subgroup.mem_subgroupOf, pResidualOf_eq_opResidual]
    exact hk
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h2grp
  have hWidx : Wm.index = 2 ^ n := by rw [Subgroup.index]; exact hn
  have hTidx : ¬ 2 ∣ Tm.index := (C.sylow_T_of_le C.hcs.setting.le).2.2
  have hdvd1 : (Tm ⊔ Wm).index ∣ Tm.index := Subgroup.index_dvd_of_le le_sup_left
  have hdvd2 : (Tm ⊔ Wm).index ∣ Wm.index := Subgroup.index_dvd_of_le le_sup_right
  rw [hWidx] at hdvd2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
  have hj0 : j = 0 := by
    by_contra hne
    apply hTidx
    refine dvd_trans ?_ hdvd1
    rw [hj]
    exact dvd_pow_self 2 hne
  have htop : Tm ⊔ Wm = ⊤ := by
    rw [← Subgroup.index_eq_one, hj, hj0, pow_zero]
  intro m hm
  have hmem : (⟨m, hm⟩ : ↥M) ∈ Tm ⊔ Wm := by rw [htop]; trivial
  have h1 : (Tm ⊔ Wm).map M.subtype = T ⊔ pResidualOf 2 M := by
    rw [Subgroup.map_sup, hTm, hWm, Subgroup.map_subgroupOf_eq_of_le C.T_le_M,
      Subgroup.map_subgroupOf_eq_of_le pResidual2_le]
  rw [← h1]
  exact ⟨⟨m, hm⟩, hmem, rfl⟩

theorem T_normalizes_S (C : StdCfg T M H S L) : T ≤ Subgroup.normalizer (S : Set G) := by
  have hn : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two C.F.index_two
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer C.hcs.le_T).mp hn


theorem IS_norm (C : StdCfg T M H S L) :
    M ≤ Subgroup.normalizer ((pResidualOf 2 M ⊔ S : Subgroup G) : Set G) := by
  have hSW : S ≤ Subgroup.normalizer ((pResidualOf 2 M : Subgroup G) : Set G) :=
    C.S_le_M.trans (le_normalizer_pResidual2 M)
  have key : ∀ t ∈ T, ∀ n ∈ pResidualOf 2 M ⊔ S, t * n * t⁻¹ ∈ pResidualOf 2 M ⊔ S := by
    intro t ht n hn
    rw [sup_comm] at hn
    have hn' : n ∈ ((S ⊔ pResidualOf 2 M : Subgroup G) : Set G) := hn
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S _ hSW] at hn'
    obtain ⟨s, hs, w, hw, rfl⟩ := hn'
    have hs' : t * s * t⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (C.T_normalizes_S ht) s).mp hs
    have hw' : t * w * t⁻¹ ∈ pResidualOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pResidual2 M (C.T_le_M ht)) w).mp hw
    have : t * (s * w) * t⁻¹ = (t * s * t⁻¹) * (t * w * t⁻¹) := by group
    rw [this, sup_comm]
    exact Subgroup.mul_mem_sup hs' hw'
  have hTn : T ≤ Subgroup.normalizer ((pResidualOf 2 M ⊔ S : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key t ht x hx, fun hx => ?_⟩
    have := key t⁻¹ (inv_mem ht) _ hx
    simpa [mul_assoc] using this
  exact C.M_le_T_sup_W.trans (sup_le hTn (le_sup_left.trans Subgroup.le_normalizer))

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem rg_W
    {w : G} (hw : w ∈ pResidualOf 2 M) : X.rg w ∈ O4PlusTwo ∧ (X.rg w) ^ 3 = 1 := by
  have hWM : ∀ x ∈ pResidualOf 2 M, x ∈ M := fun x hx => pResidual2_le hx
  rw [pResidualOf_eq_opResidual] at hw
  simp only [pResidualOf_eq_opResidual] at hWM
  unfold opResidual at hw hWM
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨hxM, hxc⟩ := hx
    refine ⟨X.rg_mem_O4 hxM, ?_⟩
    set g := X.rg x with hg
    have hgO : g ∈ O4PlusTwo := X.rg_mem_O4 hxM
    have h72 : g ^ 72 = 1 := by
      have h1 : (⟨g, hgO⟩ : ↥O4PlusTwo) ^ Nat.card ↥O4PlusTwo = 1 := pow_card_eq_one'
      have h2 : Nat.card ↥O4PlusTwo = 72 := by
        rw [← X.rho_range_eq]
        exact X.card_range_rho
      rw [h2] at h1
      have := congrArg Subtype.val h1
      simpa using this
    have hn : g ^ orderOf x = 1 := by
      rw [hg, ← X.rg_pow hxM, pow_orderOf_eq_one, X.rg_one]
    have h9 : g ^ 9 = 1 := by
      have hd1 : orderOf g ∣ 72 := orderOf_dvd_of_pow_eq_one h72
      have hd2 : orderOf g ∣ orderOf x := orderOf_dvd_of_pow_eq_one hn
      have hco2 : Nat.Coprime (orderOf g) 2 := Nat.Coprime.coprime_dvd_left hd2 hxc
      have hco8 : Nat.Coprime (orderOf g) 8 := by
        have := Nat.Coprime.pow_right 3 hco2
        simpa using this
      have hd3 : orderOf g ∣ 9 := by
        have : orderOf g ∣ 9 * 8 := by simpa [mul_comm] using hd1
        exact hco8.dvd_of_dvd_mul_right this
      exact orderOf_dvd_iff_pow_eq_one.mp hd3
    exact odd_cube hgO h9
  | one =>
    refine ⟨?_, ?_⟩
    · rw [X.rg_one]; exact one_mem _
    · rw [X.rg_one]; exact one_pow 3
  | mul a b ha hb iha ihb =>
    have haM : a ∈ M := hWM a ha
    have hbM : b ∈ M := hWM b hb
    refine ⟨X.rg_mem_O4 (mul_mem haM hbM), ?_⟩
    rw [X.rg_mul haM hbM]
    exact Esub_mul iha.1 ihb.1 iha.2 ihb.2
  | inv a ha iha =>
    have haM : a ∈ M := hWM a ha
    refine ⟨X.rg_mem_O4 (inv_mem haM), ?_⟩
    rw [X.rg_inv haM, inv_pow, iha.2, inv_one]

theorem T_inf_W_le_P
    {t : G} (ht : t ∈ T) (hw : t ∈ pResidualOf 2 M) : t ∈ borelP M L := by
  have htM : t ∈ M := C.T_le_M ht
  obtain ⟨hO, h3⟩ := X.rg_W hw
  obtain ⟨k, hk⟩ := C.hcs.setting.isPGroup ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : X.rg t ^ 2 ^ k = 1 := by rw [← X.rg_pow htM, hk', X.rg_one]
  have := eq_one_of_two_pow_of_odd (b := 3) (by decide) h1 h3
  exact (X.rg_eq_one_iff htM).mp this

theorem exists_lift_W
    {g : GL (Fin 4) (ZMod 2)} (hg : g ∈ O4PlusTwo) (h3 : g ^ 3 = 1) :
    ∃ e ∈ pResidualOf 2 M, e ^ 3 = 1 ∧ X.rg e = g := by
  obtain ⟨m, hmM, hmg⟩ := X.exists_of_mem_O4 hg
  have hpos : 0 < orderOf m := orderOf_pos m
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  set d : G := m ^ 2 ^ a with hd
  have hdM : d ∈ M := pow_mem hmM _
  have hdb : d ^ b = 1 := by
    rw [hd, ← pow_mul, ← hab]
    exact pow_orderOf_eq_one m
  have hdW : d ∈ pResidualOf 2 M := by
    refine mem_pResidual2_of_coprime hdM ?_
    have : orderOf d ∣ b := orderOf_dvd_of_pow_eq_one hdb
    exact Nat.Coprime.coprime_dvd_left this (Nat.coprime_two_left.mpr hb).symm
  have hrd : X.rg d = g ^ 2 ^ a := by rw [hd, X.rg_pow hmM, hmg]
  have h2a : ¬ 3 ∣ 2 ^ a := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hmod : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2 := by omega
  have hpowg : g ^ 2 ^ a = g ^ (2 ^ a % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ a) 3, pow_add, pow_mul, h3, one_pow, one_mul]
  have hP2 : ∀ x ∈ borelP M L, x ^ 32 = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥(borelP M L)) ^ Nat.card ↥(borelP M L) = 1 := pow_card_eq_one'
    rw [X.card_P] at h1
    have := congrArg Subtype.val h1
    simpa using this
  have hcube : ∀ e : G, e ∈ M → e ^ b = 1 → X.rg e ^ 3 = 1 → e ^ 3 = 1 := by
    intro e heM heb he3
    have heP : e ^ 3 ∈ borelP M L := by
      rw [← X.rg_eq_one_iff (pow_mem heM 3), X.rg_pow heM]
      exact he3
    have h32 := hP2 _ heP
    have : (e ^ 3) ^ b = 1 := by rw [← pow_mul, mul_comm, pow_mul, heb, one_pow]
    exact eq_one_of_two_pow_of_odd (k := 5) hb (by simpa using h32) this
  rcases hmod with h1 | h2
  · have hrg : X.rg d = g := by rw [hrd, hpowg, h1, pow_one]
    exact ⟨d, hdW, hcube d hdM hdb (by rw [hrg]; exact h3), hrg⟩
  · have hrg' : X.rg d⁻¹ = g := by
      rw [X.rg_inv hdM, hrd, hpowg, h2]
      have : g ^ 2 * g = 1 := by rw [← pow_succ]; exact h3
      exact inv_eq_of_mul_eq_one_right this
    exact ⟨d⁻¹, inv_mem hdW, hcube d⁻¹ (inv_mem hdM) (by rw [inv_pow, hdb, inv_one])
      (by rw [hrg']; exact h3), hrg'⟩

theorem mem_P_of_rg_cube {x : G} (hxM : x ∈ M) (h3 : X.rg x ^ 3 = 1)
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ borelP M L := by
  obtain ⟨k, hk⟩ := h2
  have h1 : X.rg x ^ 2 ^ k = 1 := by rw [← X.rg_pow hxM, hk, X.rg_one]
  have := eq_one_of_two_pow_of_odd (b := 3) (by decide) h1 h3
  exact (X.rg_eq_one_iff hxM).mp this

theorem IS_inf :
    T ⊓ (pResidualOf 2 M ⊔ S) = S := by
  apply le_antisymm
  · rintro t ⟨htT, htWS⟩
    have hSW : S ≤ Subgroup.normalizer ((pResidualOf 2 M : Subgroup G) : Set G) :=
      C.S_le_M.trans (le_normalizer_pResidual2 M)
    rw [sup_comm] at htWS
    have h1 : t ∈ ((S ⊔ pResidualOf 2 M : Subgroup G) : Set G) := htWS
    rw [Subgroup.coe_mul_of_left_le_normalizer_right S _ hSW] at h1
    obtain ⟨s, hs, w, hw, hsw⟩ := h1
    have hwT : w ∈ T := by
      have : w = s⁻¹ * t := by rw [← hsw]; group
      rw [this]
      exact T.mul_mem (T.inv_mem (C.hcs.le_T hs)) htT
    have hwP := X.T_inf_W_le_P hwT hw
    rw [← hsw]
    exact S.mul_mem hs (X.P_le_S hwP)
  · exact le_inf C.hcs.le_T le_sup_right

theorem trans_P
    {v w : G} (hv : v ∈ borelP M L) (hw : w ∈ borelP M L)
    (hvZ : v ∉ centerOf (borelP M L)) (hwZ : w ∉ centerOf (borelP M L)) (hv2 : v ^ 2 = 1)
    (hw2 : w ^ 2 = 1) : ∃ m ∈ M, m⁻¹ * v * m = w := by
  have hz1 : C.zU ≠ 1 := C.zU_ne_one
  have hnz : ∀ {x : G}, x ∈ borelP M L → x ∉ centerOf (borelP M L) → X.th x ≠ 0 :=
    fun {x} hx hxZ h => hxZ ((X.centerOf_P_iff x).mpr ((X.th_eq_zero_iff hx).mp h))
  have hq0 : ∀ {x : G}, x ∈ borelP M L → x ^ 2 = 1 → quadHyp (X.th x) = 0 := by
    intro x hx hx2
    rcases X.sq_th hx with ⟨-, h⟩ | ⟨h1, -⟩
    · exact h
    · exfalso
      apply hz1
      rw [← h1, ← pow_two]
      exact hx2
  have hthv := hnz hv hvZ
  have hthw := hnz hw hwZ
  obtain ⟨m1, hm1⟩ := X.trans_sing (X.th v) (X.th w) ⟨hq0 hv hv2, hthv⟩ ⟨hq0 hw hw2, hthw⟩
  have hm1M : (m1 : G) ∈ M := C.M1_le_M m1.2
  have hrg : ((X.rg (m1 : G) : GL (Fin 4) (ZMod 2)) : Mat4) = X.rhoM m1 := by
    rw [X.rg_of_mem hm1M]
    exact X.rho'_eq_rho m1
  obtain ⟨hmv, hthmv⟩ := X.th_conj hm1M hv
  have h1 : X.th ((m1 : G) * v * (m1 : G)⁻¹) = X.th w := by rw [hthmv, hrg]; exact hm1
  rcases X.th_fiber hmv hw h1 with h | h
  · refine ⟨(m1 : G)⁻¹, inv_mem hm1M, ?_⟩
    rw [inv_inv, h]
  · obtain ⟨y, hy⟩ := Bf_nondeg (X.th w) hthw
    obtain ⟨p, hp, hpy⟩ := X.th_exists y
    have hpM : p ∈ M := C.P_le_M hp
    have hcomm := X.comm_th hp hw
    rw [hpy, Bf_comm, hy] at hcomm
    have hzp : C.zp 1 = C.zU := by simp [StdCfg.zp]
    rw [hzp] at hcomm
    have e1 : p * w * p⁻¹ = C.zU * w := by
      calc p * w * p⁻¹ = (p * w * p⁻¹ * w⁻¹) * w := by group
        _ = C.zU * w := by rw [hcomm]
    have hwM : w ∈ M := C.P_le_M hw
    refine ⟨(p * (m1 : G))⁻¹, inv_mem (mul_mem hpM hm1M), ?_⟩
    rw [inv_inv]
    calc p * (m1 : G) * v * (p * (m1 : G))⁻¹ = p * ((m1 : G) * v * (m1 : G)⁻¹) * p⁻¹ := by group
      _ = p * (w * C.zU) * p⁻¹ := by rw [h]
      _ = (p * w * p⁻¹) * (p * C.zU * p⁻¹) := by group
      _ = (C.zU * w) * C.zU := by
          rw [e1]
          have : p * C.zU * p⁻¹ = C.zU := by
            have hc : C.zU * p = p * C.zU := X.zU_comm_M hpM
            calc p * C.zU * p⁻¹ = C.zU * p * p⁻¹ := by rw [hc]
              _ = C.zU := by group
          rw [this]
      _ = w := by
          rw [X.zU_comm_M hwM]
          calc w * C.zU * C.zU = w * (C.zU * C.zU) := by group
            _ = w := by rw [C.zU_mul_self, mul_one]

theorem sl23_core
    {Y : Subgroup G} {c : G} (hY : IsTwoThree Y c) (hYM : Y ≤ M) (hcM : c ∈ M) :
    Y ≤ pCoreOf 2 M := by
  rw [X.pCore_M_eq]
  have hc3 : c ^ 3 = 1 := by rw [← hY.order_three]; exact pow_orderOf_eq_one c
  have hzM : ∀ g ∈ Subgroup.zpowers c, g ∈ M := fun g hg =>
    (Subgroup.zpowers_le.mpr hcM) hg
  have hzN : ∀ g ∈ Subgroup.zpowers c, g ∈ Subgroup.normalizer (Y : Set G) := fun g hg =>
    (Subgroup.zpowers_le.mpr hY.normalizes) hg
  have hg3 : ∀ g ∈ Subgroup.zpowers c, g ^ 3 = 1 := by
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have hcomm : ⁅Y, Subgroup.zpowers c⁆ ≤ borelP M L := by
    rw [Subgroup.commutator_le]
    intro y hy g hg
    rw [commutatorElement_def]
    have hyM : y ∈ M := hYM hy
    have hgM : g ∈ M := hzM g hg
    have hconjM : y * g * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM hgM) (M.inv_mem hyM)
    have hmem : y * g * y⁻¹ * g⁻¹ ∈ Y := by
      have h1 : g * y⁻¹ * g⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hzN g hg) y⁻¹).mp (Y.inv_mem hy)
      have : y * g * y⁻¹ * g⁻¹ = y * (g * y⁻¹ * g⁻¹) := by group
      rw [this]
      exact Y.mul_mem hy h1
    have hcM' : y * g * y⁻¹ * g⁻¹ ∈ M := M.mul_mem hconjM (M.inv_mem hgM)
    refine X.mem_P_of_rg_cube hcM' ?_ ?_
    · have hb3 : X.rg g ^ 3 = 1 := by rw [← X.rg_pow hgM, hg3 g hg, X.rg_one]
      have hconj3 : (X.rg (y * g * y⁻¹)) ^ 3 = 1 := by
        rw [← X.rg_pow hconjM, conj_pow, hg3 g hg]
        simp [X.rg_one]
      have hinv3 : (X.rg g⁻¹) ^ 3 = 1 := by
        rw [X.rg_inv hgM, inv_pow, hb3, inv_one]
      rw [X.rg_mul hconjM (M.inv_mem hgM)]
      exact Esub_mul (X.rg_mem_O4 hconjM) (X.rg_mem_O4 (M.inv_mem hgM)) hconj3 hinv3
    · obtain ⟨k, hk⟩ := hY.isPGroup ⟨_, hmem⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  rw [← hY.generated]
  exact hcomm

end Sec

end CFSG.QuasithinUnique.A5
