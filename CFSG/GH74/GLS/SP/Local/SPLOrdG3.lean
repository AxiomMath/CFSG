module

public import CFSG.GH74.GLS.IVK.Lifted.B2Split
public import CFSG.GH74.GLS.SP.Local.SPLOrdNI
public import CFSG.GH74.GLS.SP.Local.SPLOrdG1

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G3

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem d_pos (hs : SPLSetup D.toSPLNot0) : 4 ≤ D.d := by
  have h4 := four_dvd_d D.toSPLNot0 hs.odd_q
  have hq := hs.q_ge
  unfold SPLNot0.d
  split_ifs with h <;> omega

omit [Finite G] in
theorem d_eq (_hs : SPLSetup D.toSPLNot0) : D.d = D.e * 2 ^ (D.n - 1) := by
  have h := Nat.ordProj_mul_ordCompl_eq_self D.d 2
  unfold SPLNot0.e SPLNot0.n
  rw [Nat.add_sub_cancel, mul_comm]
  exact h.symm

omit [Finite G] in
theorem exists_gen_A (_hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∃ a₀ ∈ D.A, orderOf a₀ = D.e ∧ ∀ a ∈ D.A, a ∈ zpowers a₀ := by
  have := hc.A_cyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥D.A)
  refine ⟨(g : G), g.2, ?_, ?_⟩
  · rw [← hc.A_card, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  · intro a ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem mem_zpowers_mul_of_coprime {a b : G} (hc : Commute a b)
    (hco : Nat.Coprime (orderOf a) (orderOf b)) : a ∈ zpowers (a * b) ∧ b ∈ zpowers (a * b) := by
  have hab : (a * b) ^ (orderOf a) = b ^ (orderOf a) := by
    rw [hc.mul_pow, pow_orderOf_eq_one, one_mul]
  have hba : (a * b) ^ (orderOf b) = a ^ (orderOf b) := by
    rw [hc.mul_pow, pow_orderOf_eq_one, mul_one]
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (orderOf a : ℤ) + v * (orderOf b : ℤ) = 1 := by
    have := Nat.isCoprime_iff_coprime.mpr hco
    obtain ⟨u, v, h⟩ := this
    exact ⟨u, v, h⟩
  constructor
  · have h1 : a = (a ^ orderOf b) ^ v := by
      have e1 : a ^ (u * (orderOf a : ℤ)) = 1 := by
        rw [zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
      calc a = a ^ (u * (orderOf a : ℤ) + v * (orderOf b : ℤ)) := by rw [huv, zpow_one]
        _ = a ^ (u * (orderOf a : ℤ)) * a ^ (v * (orderOf b : ℤ)) := zpow_add _ _ _
        _ = (a ^ orderOf b) ^ v := by rw [e1, one_mul, zpow_mul', zpow_natCast]
    have hmem : ((a * b) ^ orderOf b) ^ v ∈ zpowers (a * b) :=
      Subgroup.zpow_mem _ (Subgroup.pow_mem _ (mem_zpowers _) _) _
    rw [hba] at hmem
    rwa [← h1] at hmem
  · have h1 : b = (b ^ orderOf a) ^ u := by
      have e1 : b ^ (v * (orderOf b : ℤ)) = 1 := by
        rw [zpow_mul', zpow_natCast, pow_orderOf_eq_one, one_zpow]
      calc b = b ^ (u * (orderOf a : ℤ) + v * (orderOf b : ℤ)) := by rw [huv, zpow_one]
        _ = b ^ (u * (orderOf a : ℤ)) * b ^ (v * (orderOf b : ℤ)) := zpow_add _ _ _
        _ = (b ^ orderOf a) ^ u := by rw [e1, mul_one, zpow_mul', zpow_natCast]
    have hmem : ((a * b) ^ orderOf a) ^ u ∈ zpowers (a * b) :=
      Subgroup.zpow_mem _ (Subgroup.pow_mem _ (mem_zpowers _) _) _
    rw [hab] at hmem
    rwa [← h1] at hmem

omit [Finite G] in
theorem exists_g0 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∃ g₀ : G, zpowers g₀ = D.A ⊔ zpowers D.x ∧ orderOf g₀ = D.d ∧
      D.z * g₀ * D.z⁻¹ = g₀⁻¹ ∧ g₀ ^ (D.d / 2) = D.t ∧
      (∀ i ∈ D.I, g₀ * i * g₀⁻¹ = D.x * i * D.x⁻¹) ∧ D.z ∉ zpowers g₀ ∧
      g₀ ^ 2 ∈ D.A ⊔ zpowers (D.x ^ 2) := by
  have hodd : Odd D.e := e_odd D hs
  have hd := d_eq D hs
  have hd4 := d_pos D hs
  have hn3 := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  obtain ⟨a₀, ha₀A, ha₀ord, ha₀gen⟩ := exists_gen_A D hs hc
  have hxord : orderOf D.x = 2 ^ (D.n - 1) := hc.x_ord
  have hcomm : Commute a₀ D.x := hc.A_x a₀ ha₀A
  have hco : Nat.Coprime (orderOf a₀) (orderOf D.x) := by
    rw [ha₀ord, hxord]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
  have hg₀ord : orderOf (a₀ * D.x) = D.d := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, ha₀ord, hxord, hd]
  obtain ⟨hmem1, hmem2⟩ := mem_zpowers_mul_of_coprime hcomm hco
  have hzrel : D.z * (a₀ * D.x) * D.z⁻¹ = (a₀ * D.x)⁻¹ := by
    have h1 := hc.A_inv a₀ ha₀A
    have h2 := z_inv_x D hs hc
    calc D.z * (a₀ * D.x) * D.z⁻¹ = (D.z * a₀ * D.z⁻¹) * (D.z * D.x * D.z⁻¹) := by group
      _ = a₀⁻¹ * D.x⁻¹ := by rw [h1, h2]
      _ = (a₀ * D.x)⁻¹ := by rw [mul_inv_rev, (hcomm.inv_inv).eq]
  refine ⟨a₀ * D.x, ?_, hg₀ord, hzrel, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [zpowers_le]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₀A) (Subgroup.mem_sup_right (mem_zpowers _))
    · refine sup_le (fun a ha => ?_) (zpowers_le.mpr hmem2)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (ha₀gen a ha)
      exact Subgroup.zpow_mem _ hmem1 _
  ·
    have hd2 : D.d / 2 = D.e * 2 ^ (D.n - 2) := by
      have : D.d = 2 * (D.e * 2 ^ (D.n - 2)) := by
        rw [hd]
        have : D.n - 1 = (D.n - 2) + 1 := by omega
        rw [this, pow_succ]; ring
      omega
    rw [hd2, hcomm.mul_pow]
    have hao : a₀ ^ (D.e * 2 ^ (D.n - 2)) = 1 := by
      rw [pow_mul, ← ha₀ord, pow_orderOf_eq_one, one_pow]
    have hxo : D.x ^ (D.e * 2 ^ (D.n - 2)) = D.t := by
      rw [mul_comm, pow_mul, hc.x_pow]
      obtain ⟨m, hm⟩ := hodd
      have htt := t_mul_t D hs
      rw [hm, pow_succ, pow_mul, sq, htt, one_pow, one_mul]
    rw [hao, hxo, one_mul]
  · intro i hi
    have hxi : D.x * i * D.x⁻¹ ∈ D.I := I_normalized D hc D.x (x_mem_Ct D hc) i hi
    have h2 : a₀ * (D.x * i * D.x⁻¹) = (D.x * i * D.x⁻¹) * a₀ := hc.AI_comm a₀ ha₀A _ hxi
    calc a₀ * D.x * i * (a₀ * D.x)⁻¹ = a₀ * (D.x * i * D.x⁻¹) * a₀⁻¹ := by group
      _ = D.x * i * D.x⁻¹ := by rw [h2]; group
  ·
    intro hz
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
    have hcz : D.z * (a₀ * D.x) = (a₀ * D.x) * D.z := by
      rw [← hk]
      exact ((Commute.refl (a₀ * D.x)).zpow_left k).symm.eq.symm
    have h1 : (a₀ * D.x) = (a₀ * D.x)⁻¹ := by
      calc (a₀ * D.x) = D.z * (a₀ * D.x) * D.z⁻¹ := by rw [hcz]; group
        _ = (a₀ * D.x)⁻¹ := hzrel
    have h2 : (a₀ * D.x) ^ 2 = 1 := by
      rw [pow_two]
      calc (a₀ * D.x) * (a₀ * D.x) = (a₀ * D.x) * (a₀ * D.x)⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel _
    have h3 : D.d ∣ 2 := hg₀ord ▸ orderOf_dvd_of_pow_eq_one h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  ·
    rw [hcomm.mul_pow]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ ha₀A _))
      (Subgroup.mem_sup_right (mem_zpowers _))

omit [Finite G] in
theorem K₁_inv_unique (hs : SPLSetup D.toSPLNot0) {a : G} (ha : a ∈ D.K₁) (haa : a * a = 1) :
    a = 1 ∨ a = D.z := by
  obtain ⟨F, hF1, hF2, hFq, ⟨ε⟩⟩ := hs.comps.sl₁
  have hodd : Odd (Nat.card F) := by rw [hFq]; exact hs.odd_q
  by_cases h1 : a = 1
  · left; exact h1
  · right
    have hord : orderOf (⟨a, ha⟩ : ↥D.K₁) = 2 :=
      orderOf_eq_prime (by apply Subtype.ext; simpa [pow_two] using haa)
        (by intro h; apply h1; simpa using congrArg Subtype.val h)
    have hz : D.z ∈ D.K₁ := z_mem_K₁ (D := D.toSPLNot0) hs
    have hordz : orderOf (⟨D.z, hz⟩ : ↥D.K₁) = 2 := by
      rw [Subgroup.orderOf_mk]; exact hs.syl.z_inv
    have := CFSG.GH74.GLS.IVK.Lifted.statedSL_two_involution_unique hodd
      (t₁ := ε ⟨a, ha⟩) (t₂ := ε ⟨D.z, hz⟩) (by rw [MulEquiv.orderOf_eq]; exact hord)
      (by rw [MulEquiv.orderOf_eq]; exact hordz)
    have h2 := ε.injective this
    exact congrArg Subtype.val h2

theorem mem_zpowers_of_mem_ker_diagHom (hs : SPLSetup D.toSPLNot0) {k : ↥D.K₁}
    (hk : k ∈ (diagHom D hs).ker) : (k : G) ∈ zpowers D.z := by
  have hk0 : (k : G) * (D.t * (k : G) * D.t⁻¹) = 1 := hk
  have hkK₂ : (k : G) ∈ D.K₂ := by
    have : (k : G) = (D.t * (k : G) * D.t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk0
    rw [this]
    exact D.K₂.inv_mem (t_conj_K₁ D hs _ k.2)
  rw [← hs.comps.inf_eq]; exact ⟨k.2, hkK₂⟩

theorem diagHom_z (hs : SPLSetup D.toSPLNot0) :
    diagHom D hs ⟨D.z, z_mem_K₁ (D := D.toSPLNot0) hs⟩ = 1 := by
  show D.z * (D.t * D.z * D.t⁻¹) = 1
  rw [t_conj_z D hs, z_mul_z D hs]

theorem ker_diagHom (hs : SPLSetup D.toSPLNot0) :
    Nat.card ↥(diagHom D hs).ker = 2 := by
  have hz : D.z ∈ D.K₁ := z_mem_K₁ (D := D.toSPLNot0) hs
  have hker : (diagHom D hs).ker = zpowers (⟨D.z, hz⟩ : ↥D.K₁) := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (mem_zpowers_of_mem_ker_diagHom D hs hk)
      exact mem_zpowers_iff.mpr ⟨j, Subtype.ext (by simpa using hj)⟩
    · rintro ⟨j, rfl⟩
      rw [map_zpow, diagHom_z D hs, one_zpow]
  rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk]
  exact hs.syl.z_inv

theorem I_eq_diag (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    D.I = (diagHom D hs).range := by
  apply le_antisymm
  · have hle : (diagHom D hs).range ≤ D.I := by
      rintro _ ⟨k, rfl⟩
      exact diag_mem_I D hs hc k.2
    have h1 := Subgroup.card_mul_index (diagHom D hs).ker
    rw [Subgroup.index_ker, ker_diagHom D hs] at h1
    have h2 := card_K₁_eq D hs hc
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm.le
  · rintro _ ⟨k, rfl⟩
    exact diag_mem_I D hs hc k.2

theorem exists_diag_of_mem_I (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {i : G}
    (hi : i ∈ D.I) : ∃ k ∈ D.K₁, i = k * (D.t * k * D.t⁻¹) := by
  rw [I_eq_diag D hs hc] at hi
  obtain ⟨k, hk⟩ := hi
  exact ⟨(k : G), k.2, hk.symm⟩

omit [Finite G] in
theorem isConj_z_refl {g₀ : G} (hzrel : D.z * g₀ * D.z⁻¹ = g₀⁻¹) (m : ℤ) :
    IsConj D.z (D.z * g₀ ^ (2 * m)) := by
  have hzconj : ∀ k : ℤ, D.z * g₀ ^ k * D.z⁻¹ = g₀ ^ (-k) := by
    intro k
    rw [← conj_zpow, hzrel, inv_zpow']
  refine isConj_iff.mpr ⟨g₀ ^ (-m), ?_⟩
  have h1 := hzconj m
  have h2 := hzconj (2 * m)
  have e1 : g₀ ^ (-m) * D.z * (g₀ ^ (-m))⁻¹ = g₀ ^ (-m) * (D.z * g₀ ^ m * D.z⁻¹) * D.z := by
    rw [← zpow_neg, neg_neg]; group
  rw [e1, h1]
  calc g₀ ^ (-m) * g₀ ^ (-m) * D.z = g₀ ^ (-(2 * m)) * D.z := by
        rw [← zpow_add]; congr 2; ring
    _ = (D.z * g₀ ^ (2 * m) * D.z⁻¹) * D.z := by rw [h2]
    _ = D.z * g₀ ^ (2 * m) := by group

theorem isConj_z_it (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {i : G} (hi : i ∈ D.I)
    (hii : i * i = 1) (hi1 : i ≠ 1) : IsConj D.z (i * D.t) := by
  have htt := t_mul_t D hs
  have hti : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨k, hk, rfl⟩ := exists_diag_of_mem_I D hs hc hi
  have hu : D.t * k * D.t⁻¹ ∈ D.K₂ := t_conj_K₁ D hs k hk
  have hcomm : k * (D.t * k * D.t⁻¹) = (D.t * k * D.t⁻¹) * k := hs.comps.comm k hk _ hu
  have hk2 : k * k ∈ zpowers D.z := by
    have h : (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹)) = 1 := by
      calc (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹))
          = (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹)) := by
            calc (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹))
                = k * (k * (D.t * k * D.t⁻¹)) * (D.t * k * D.t⁻¹) := by group
              _ = k * ((D.t * k * D.t⁻¹) * k) * (D.t * k * D.t⁻¹) := by rw [hcomm]
              _ = (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹)) := by group
        _ = 1 := hii
    have hK₂ : k * k ∈ D.K₂ := by
      have : k * k = ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact D.K₂.inv_mem (D.K₂.mul_mem hu hu)
    rw [← hs.comps.inf_eq]
    exact ⟨D.K₁.mul_mem hk hk, hK₂⟩
  have hkz : k * k = D.z := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk2
    rcases zpow_z_cases D hs j with h1 | h1
    · exfalso
      rw [h1] at hj
      rcases K₁_inv_unique D hs hk hj.symm with h2 | h2
      · apply hi1; rw [h2]; simp
      · apply hi1
        rw [h2, t_conj_z D hs, z_mul_z D hs]
    · rw [h1] at hj; exact hj.symm
  have hz1 : D.z * k = k * D.z := z_comm_K₁ D hs hk
  have hres : k * (D.t * k * D.t⁻¹) * D.t = k * (D.t * D.z) * k⁻¹ := by
    calc k * (D.t * k * D.t⁻¹) * D.t = k * D.t * k := by group
      _ = (k * D.t * k⁻¹) * (k * k) := by group
      _ = (k * D.t * k⁻¹) * D.z := by rw [hkz]
      _ = k * (D.t * D.z) * k⁻¹ := by
        have : k⁻¹ * D.z = D.z * k⁻¹ := by
          calc k⁻¹ * D.z = k⁻¹ * (D.z * k) * k⁻¹ := by group
            _ = k⁻¹ * (k * D.z) * k⁻¹ := by rw [hz1]
            _ = D.z * k⁻¹ := by group
        calc (k * D.t * k⁻¹) * D.z = k * D.t * (k⁻¹ * D.z) := by group
          _ = k * D.t * (D.z * k⁻¹) := by rw [this]
          _ = k * (D.t * D.z) * k⁻¹ := by group
  rw [hres]
  exact hs.syl.tz_conj.trans (isConj_iff.mpr ⟨k, rfl⟩)

omit [Finite G] in
theorem x_le_normalizer_I (hc : SPL2Ct D.toSPLNot2) : zpowers D.x ≤ normalizer (D.I : Set G) := by
  rw [zpowers_le, mem_normalizer_iff]
  intro i
  constructor
  · intro hi; exact I_normalized D hc D.x (x_mem_Ct D hc) i hi
  · intro hi
    have := I_normalized D hc D.x⁻¹ ((D.Ct).inv_mem (x_mem_Ct D hc)) _ hi
    have e : D.x⁻¹ * (D.x * i * D.x⁻¹) * D.x⁻¹⁻¹ = i := by group
    rwa [e] at this

theorem sigma_not_inner (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ¬ ∃ j ∈ D.I, ∀ i ∈ D.I, D.x * i * D.x⁻¹ = j * i * j⁻¹ := by
  classical
  obtain ⟨hNn, F₀, hF1, hF2, hFq, ⟨eP⟩⟩ := hc.quot
  have hNnormal := hNn
  set Y : Subgroup G := D.I ⊔ zpowers D.x with hYdef
  have hYCt : Y ≤ D.Ct := M_le_Ct D hc
  have hxY : D.x ∈ Y := Subgroup.mem_sup_right (mem_zpowers _)
  have hIY : D.I ≤ Y := le_sup_left
  let x' : ↥Y := ⟨D.x, hxY⟩
  have hInormal : (D.I.subgroupOf Y).Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : ↥Y) : G) ∈ D.I
    exact I_normalized D hc g (hYCt g.2) n hn⟩
  have hY : ∀ y : ↥Y, ∃ i ∈ D.I.subgroupOf Y, ∃ k : ℤ, y = i * x' ^ k := by
    intro y
    obtain ⟨i, hi, w, hw, hiw⟩ := mem_sup_of_le_normalizer (x_le_normalizer_I D hc) y.2
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    refine ⟨⟨i, hIY hi⟩, hi, k, Subtype.ext ?_⟩
    simpa [x'] using hiw
  have hN' : (zpowers (D.x ^ 2)).subgroupOf Y = zpowers (x' ^ 2) := by
    ext y
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa [x'] using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [x'] using congrArg Subtype.val hk⟩
  have hIN : D.I.subgroupOf Y ⊓ (zpowers (D.x ^ 2)).subgroupOf Y = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    have h : (y : G) ∈ D.I ⊓ zpowers (D.x ^ 2) := ⟨hy1, hy2⟩
    rw [Z_inf_I D hc] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp h))
  have hqF : Nat.card F₀ = D.q := hFq
  have hcardP : Nat.card (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) = D.q * (D.q ^ 2 - 1) := by
    rw [Nat.card_congr eP.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula F₀, hqF]
  have hcard : 2 * Nat.card ↥(D.I.subgroupOf Y) = Nat.card (↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y) := by
    rw [hcardP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIY).toEquiv,
      ← card_K₁ (D := D.toSPLNot0) hs]
    exact card_K₁_eq D hs hc
  have hcenter : ∀ p : ↥Y ⧸ (zpowers (D.x ^ 2)).subgroupOf Y, (∀ r, p * r = r * p) → p = 1 := by
    intro p hp
    have hc' : eP p ∈ Subgroup.center (CFSG.GorensteinWalter.PGL2 F₀) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨r, rfl⟩ := eP.surjective g
      rw [← map_mul, ← map_mul, hp r]
    rw [CFSG.GorensteinWalter.pgl2_center_eq_bot F₀] at hc'
    exact eP.injective (by simpa using Subgroup.mem_bot.mp hc')
  rintro ⟨j, hj, hjx⟩
  apply conj_not_inner (D.I.subgroupOf Y) ((zpowers (D.x ^ 2)).subgroupOf Y) x' hY hN' hIN hcard hcenter
  refine ⟨⟨j, hIY hj⟩, hj, fun i hi => Subtype.ext ?_⟩
  simpa [x'] using hjx i hi

end G3

end CFSG.GH74.GLS.SP.Local
