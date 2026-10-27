module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3ReducedA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem three_pow_dvd_pow_pow_add_one {m k : ℕ} (hm : 1 ≤ m) (hk : k % 3 = 2) :
    3 ^ m ∣ k ^ 3 ^ (m - 1) + 1 := by
  have hcop : Nat.Coprime k (3 ^ m) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    omega
  have h1 : (k ^ 3 ^ (m - 1)) ^ 2 ≡ 1 [MOD 3 ^ m] := by
    have := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow Nat.prime_three (by omega), pow_mul] at this
    exact this
  have hκ3 : (k ^ 3 ^ (m - 1)) % 3 = 2 := by
    obtain ⟨c, hc⟩ : Odd (3 ^ (m - 1)) := Odd.pow (by decide)
    rw [Nat.pow_mod, hk, hc, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize k ^ 3 ^ (m - 1) = κ at h1 hκ3
  have hκ2 : 2 ≤ κ := by
    by_contra h
    omega
  have hdvd : 3 ^ m ∣ κ ^ 2 - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h1.symm
  rw [show κ ^ 2 - 1 = (κ + 1) * (κ - 1) by
    simpa using Nat.pow_two_sub_pow_two κ 1] at hdvd
  refine Nat.Coprime.dvd_of_dvd_mul_right ?_ hdvd
  refine Nat.Coprime.pow_left _ ?_
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  omega

theorem exists_pow_conj_eq_inv_of_isCyclic {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    [IsCyclic T] (hT : IsPGroup 3 T) {s : X} (hs : ∀ y ∈ T, s * y * s⁻¹ ∈ T)
    (hfpf : ∀ x ∈ T, s * x * s⁻¹ = x → x = 1) :
    ∃ j : ℕ, ∀ y ∈ T, s ^ j * y * (s ^ j)⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  obtain ⟨m, hm⟩ := hT.exists_card_eq
  have hord : orderOf (g : X) = 3 ^ m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hm]
  have hgT : (g : X) ∈ T := g.2
  have hmem : ∀ y ∈ T, ∃ i : ℤ, (g : X) ^ i = y := by
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · refine ⟨0, fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hmem y hy
    have : (g : X) = 1 := by
      rw [← orderOf_eq_one_iff, hord]
      simp
    simp [this]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, s * (g : X) * s⁻¹ = (g : X) ^ k := by
      obtain ⟨i, hi⟩ := hmem _ (hs _ hgT)
      have hmemz : s * (g : X) * s⁻¹ ∈ Subgroup.zpowers (g : X) := ⟨i, hi⟩
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmemz)
      exact ⟨n, hn.symm⟩
    have hconj : ∀ j : ℕ, s ^ j * (g : X) * (s ^ j)⁻¹ = (g : X) ^ (k ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc s ^ (j + 1) * (g : X) * (s ^ (j + 1))⁻¹
            = s * (s ^ j * (g : X) * (s ^ j)⁻¹) * s⁻¹ := by group
          _ = s * (g : X) ^ (k ^ j) * s⁻¹ := by rw [ih]
          _ = (s * (g : X) * s⁻¹) ^ (k ^ j) := conj_pow.symm
          _ = ((g : X) ^ k) ^ (k ^ j) := by rw [hk]
          _ = (g : X) ^ (k ^ (j + 1)) := by rw [← pow_mul, pow_succ']
    have hN : 0 < orderOf s := orderOf_pos s
    have hk3 : k % 3 ≠ 0 := by
      intro h0
      have h1 : (g : X) ^ (k ^ orderOf s) = (g : X) ^ 1 := by
        rw [← hconj, pow_orderOf_eq_one]
        simp
      have h2 := pow_eq_pow_iff_modEq.mp h1
      rw [hord] at h2
      have h3 : k ^ orderOf s ≡ 1 [MOD 3] := h2.of_dvd (dvd_pow_self 3 hm1.ne')
      have h4 : k ^ orderOf s % 3 = 1 % 3 := h3
      rw [Nat.pow_mod, h0, zero_pow hN.ne'] at h4
      omega
    have hk1 : k % 3 ≠ 1 := by
      intro h1
      have hxT : (g : X) ^ 3 ^ (m - 1) ∈ T := T.pow_mem hgT _
      have hfix : s * (g : X) ^ 3 ^ (m - 1) * s⁻¹ = (g : X) ^ 3 ^ (m - 1) := by
        rw [← conj_pow, hk, ← pow_mul, pow_eq_pow_iff_modEq, hord]
        have h5 : k ≡ 1 [MOD 3] := by
          show k % 3 = 1 % 3
          omega
        have h6 := Nat.ModEq.mul_left' (3 ^ (m - 1)) h5
        rw [← pow_succ, Nat.sub_add_cancel hm1, mul_one] at h6
        rw [mul_comm]
        exact h6
      have h7 := hfpf _ hxT hfix
      have h8 : orderOf (g : X) ∣ 3 ^ (m - 1) := orderOf_dvd_iff_pow_eq_one.mpr h7
      rw [hord] at h8
      have := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h8
      omega
    have hk2 : k % 3 = 2 := by omega
    have hdiv := three_pow_dvd_pow_pow_add_one hm1 hk2
    refine ⟨3 ^ (m - 1), fun y hy => ?_⟩
    obtain ⟨i, rfl⟩ := hmem y hy
    have h1 : s ^ 3 ^ (m - 1) * (g : X) * (s ^ 3 ^ (m - 1))⁻¹ = (g : X)⁻¹ := by
      rw [hconj, eq_inv_iff_mul_eq_one, ← pow_succ]
      exact orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hdiv)
    rw [← conj_zpow, h1, inv_zpow]

theorem pow_conj_eq_inv_of_odd {X : Type*} [Group X] {T : Subgroup X} {n : X}
    (hinv : ∀ y ∈ T, n * y * n⁻¹ = y⁻¹) {c : ℕ} (hc : Odd c) :
    ∀ y ∈ T, n ^ c * y * (n ^ c)⁻¹ = y⁻¹ := by
  obtain ⟨d, rfl⟩ := hc
  induction d with
  | zero => simpa using hinv
  | succ d ih =>
    intro y hy
    have h2 : n * y⁻¹ * n⁻¹ = y := by rw [hinv _ (T.inv_mem hy), inv_inv]
    calc n ^ (2 * (d + 1) + 1) * y * (n ^ (2 * (d + 1) + 1))⁻¹
        = n * (n * (n ^ (2 * d + 1) * y * (n ^ (2 * d + 1))⁻¹) * n⁻¹) * n⁻¹ := by group
      _ = n * (n * y⁻¹ * n⁻¹) * n⁻¹ := by rw [ih y hy]
      _ = n * y * n⁻¹ := by rw [h2]
      _ = y⁻¹ := hinv y hy

theorem mem_normalizer_of_conj_eq_inv {X : Type*} [Group X] [Finite X] {Rb K : Subgroup X}
    (hRK : Rb ≤ Subgroup.normalizer (K : Set X))
    (hC : ∀ m ∈ K, (∀ y ∈ Rb ⊓ K, m * y = y * m) → m ∈ Rb) {n : X} (hn : n ∈ K)
    (hinv : ∀ y ∈ Rb ⊓ K, n * y * n⁻¹ = y⁻¹) : n ∈ Subgroup.normalizer (Rb : Set X) := by
  refine Subgroup.mem_normalizer_fintype fun r hr => ?_
  have hrb : r ∈ Rb := hr
  have hrK : r * n * r⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hRK hrb) n).mp hn
  have ha : ∀ y ∈ Rb ⊓ K, (r * n * r⁻¹) * y * (r * n * r⁻¹)⁻¹ = y⁻¹ := by
    intro y hy
    have hy' : r⁻¹ * y * r ∈ Rb ⊓ K := by
      refine ⟨Rb.mul_mem (Rb.mul_mem (Rb.inv_mem hrb) hy.1) hrb, ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp (hRK (Rb.inv_mem hrb)) y).mp hy.2
      simpa using this
    calc (r * n * r⁻¹) * y * (r * n * r⁻¹)⁻¹
        = r * (n * (r⁻¹ * y * r) * n⁻¹) * r⁻¹ := by group
      _ = r * (r⁻¹ * y * r)⁻¹ * r⁻¹ := by rw [hinv _ hy']
      _ = y⁻¹ := by group
  have hmK : (r * n * r⁻¹) * n⁻¹ ∈ K := K.mul_mem hrK (K.inv_mem hn)
  have hcomm : ∀ y ∈ Rb ⊓ K, ((r * n * r⁻¹) * n⁻¹) * y = y * ((r * n * r⁻¹) * n⁻¹) := by
    intro y hy
    have h1 : n * y⁻¹ * n⁻¹ = y := by rw [hinv _ (Subgroup.inv_mem _ hy), inv_inv]
    have h2 : n⁻¹ * y * n = y⁻¹ := by
      calc n⁻¹ * y * n = n⁻¹ * (n * y⁻¹ * n⁻¹) * n := by rw [h1]
        _ = y⁻¹ := by group
    have h3 : ((r * n * r⁻¹) * n⁻¹) * y * ((r * n * r⁻¹) * n⁻¹)⁻¹ = y := by
      calc ((r * n * r⁻¹) * n⁻¹) * y * ((r * n * r⁻¹) * n⁻¹)⁻¹
          = (r * n * r⁻¹) * (n⁻¹ * y * n) * (r * n * r⁻¹)⁻¹ := by group
        _ = (r * n * r⁻¹) * y⁻¹ * (r * n * r⁻¹)⁻¹ := by rw [h2]
        _ = ((r * n * r⁻¹) * y * (r * n * r⁻¹)⁻¹)⁻¹ := by group
        _ = y := by rw [ha y hy, inv_inv]
    exact mul_inv_eq_iff_eq_mul.mp h3
  have hmRb := hC _ hmK hcomm
  have : n * r * n⁻¹ = ((r * n * r⁻¹) * n⁻¹)⁻¹ * r := by group
  rw [this]
  exact Rb.mul_mem (Rb.inv_mem hmRb) hrb

theorem mem_of_commute_of_center_eq_bot {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥)
    {T : Subgroup K}
    (hfix : ∀ f : MulAut K, (∀ x ∈ T, f x = x) → ∃ t ∈ T, f = MulAut.conj t) {m : K}
    (hm : ∀ x ∈ T, m * x = x * m) : m ∈ T := by
  obtain ⟨t, htT, ht⟩ := hfix (MulAut.conj m) fun x hx => by
    rw [MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (hm x hx)
  have hc : t⁻¹ * m ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := congrArg (fun f : MulAut K => f z) ht
    simp only [MulAut.conj_apply] at h
    calc z * (t⁻¹ * m) = t⁻¹ * (t * z * t⁻¹) * m := by group
      _ = t⁻¹ * (m * z * m⁻¹) * m := by rw [h]
      _ = t⁻¹ * m * z := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc ▸ htT

theorem D1CaseTwoData3.exists_inverting_two_element (hOut : KFactOutCyclic)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) {G : Type} [Group G] [Finite G]
    {P : Sylow 3 G} {M H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData3 3 P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 3 M H) :
    ∃ t : H, (t : G) ∈ Subgroup.normalizer (R : Set G) ∧
      IsPGroup 2 (Subgroup.zpowers (t : G)) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) 3) t ∈ Kb ∧
      ∀ y ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ Kb,
        QuotientGroup.mk' (primeComplementCore (G := H) 3) t * y *
          (QuotientGroup.mk' (primeComplementCore (G := H) 3) t)⁻¹ = y⁻¹ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set O := primeComplementCore (G := H) 3
  have hiso : IsCaseTwoGroup 3 Kb :=
    hd.cfg.red.isCaseTwoGroup_of_not_le3 hd.cfg.catalog hOut hS hd.cyclic hd.rank hKb hKX
  have hRN : (Rbar : Subgroup (H ⧸ O)) ≤ Subgroup.normalizer (Kb : Set (H ⧸ O)) :=
    hd.cfg.red.sylow_le_normalizer_component hKb
  have hZ : Subgroup.center Kb = ⊥ :=
    hd.cfg.red.center_eq_bot_of_isCyclic hKb (hd.cyclic Kb hKb)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hKb.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨-, -, hloc⟩ := hKL 3 Kb hiso
  obtain ⟨⟨s, hsN, hsfpf⟩, hfix, -⟩ := hloc T
  have hcyc : IsCyclic ((Rbar : Subgroup (H ⧸ O)) ⊓ Kb : Subgroup (H ⧸ O)) := hd.cyclic Kb hKb
  have hpg : IsPGroup 3 ((Rbar : Subgroup (H ⧸ O)) ⊓ Kb : Subgroup (H ⧸ O)) :=
    Rbar.isPGroup'.to_le inf_le_left
  have hTmem : ∀ y : H ⧸ O, y ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Kb ↔
      ∃ x ∈ (T : Subgroup Kb), (x : H ⧸ O) = y := by
    intro y
    rw [← hT, Subgroup.mem_map]
    rfl
  have hs' : ∀ y ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Kb,
      (s : H ⧸ O) * y * (s : H ⧸ O)⁻¹ ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Kb := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hTmem y).mp hy
    refine (hTmem _).mpr ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN x).mp hx, rfl⟩
  have hfpf' : ∀ x ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Kb,
      (s : H ⧸ O) * x * (s : H ⧸ O)⁻¹ = x → x = 1 := by
    intro y hy hfy
    obtain ⟨x, hx, rfl⟩ := (hTmem y).mp hy
    have h1 : s * x * s⁻¹ = x := Subtype.ext hfy
    have h2 := hsfpf x hx h1
    rw [h2]
    rfl
  obtain ⟨j, hj⟩ := exists_pow_conj_eq_inv_of_isCyclic hpg hs' hfpf'
  have hnK : (s : H ⧸ O) ^ j ∈ Kb := Kb.pow_mem s.2 j
  have hC : ∀ m ∈ Kb, (∀ y ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Kb, m * y = y * m) →
      m ∈ (Rbar : Subgroup (H ⧸ O)) := by
    intro m hm hcomm
    have key := mem_of_commute_of_center_eq_bot hZ hfix (m := ⟨m, hm⟩) fun x hx =>
      Subtype.ext (hcomm x ((hTmem x).mpr ⟨x, hx, rfl⟩))
    exact ((hTmem m).mpr ⟨⟨m, hm⟩, key, rfl⟩).1
  have hnorm := mem_normalizer_of_conj_eq_inv hRN hC hnK hj
  have hO' : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  have hRp : IsPGroup 3 (R.subgroupOf H) := hd.cfg.ext.isPGroup.comap_subtype (K := H)
  obtain ⟨g, hgN, hgn⟩ := exists_mem_normalizer_mk_eq_of_mem_normalizer hp O hO' hRp
    (x := (s : H ⧸ O) ^ j) (by rw [← hd.cfg.rbar]; exact hnorm)
  have hgR : (g : G) ∈ Subgroup.normalizer (R : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxR : x ∈ R := hx
    have hxH : x ∈ H := hd.cfg.ext.le_H hxR
    have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨x, hxH⟩).mp
      (Subgroup.mem_subgroupOf.mpr hxR)
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨e, c, hc, hec⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hdvd : c ∣ orderOf g := ⟨2 ^ e, by rw [hec]; ring⟩
  have hord : orderOf (g ^ c) = 2 ^ e := by
    rw [orderOf_pow_of_dvd hc.pos.ne' hdvd, hec, Nat.mul_div_cancel _ hc.pos]
  refine ⟨g ^ c, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hgR c
  · refine IsPGroup.of_card (n := e) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hord]
  · rw [map_pow, hgn]
    exact Kb.pow_mem hnK c
  · intro y hy
    rw [map_pow, hgn]
    exact pow_conj_eq_inv_of_odd hj hc y hy

end CFSG.LocalAnalysis.RankThreeTheoremC
