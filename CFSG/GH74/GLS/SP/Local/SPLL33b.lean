module

public import CFSG.GH74.GLS.SP.Local.SPLPsl2Kgu
public import CFSG.GH74.GLS.SP.Local.SPLA

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

@[expose] def SPLNot3.T₀ {G : Type} [Group G] (D : SPLNot3 G) : Subgroup G :=
  zpowers (D.x ^ 2) ⊔ zpowers D.z

@[expose] def SPLNot3.C₀ {G : Type} [Group G] (D : SPLNot3 G) : Subgroup G :=
  centralizer (D.Y₀ : Set G)

section L33b

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem mem_sup_of_le_normalizer {N H : Subgroup G} (h : H ≤ normalizer (N : Set G)) {g : G}
    (hg : g ∈ N ⊔ H) : ∃ n ∈ N, ∃ k ∈ H, g = n * k := by
  have hset := coe_mul_of_right_le_normalizer_left N H h
  have hg' : g ∈ (↑(N ⊔ H) : Set G) := hg
  rw [hset] at hg'
  obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp hg'
  exact ⟨n, hn, k, hk, hnk.symm⟩

omit [Finite G] in
theorem A_norm_Ct (hc : SPL2Ct D.toSPLNot2) : ∀ c ∈ D.Ct, ∀ a ∈ D.A, c * a * c⁻¹ ∈ D.A := by
  intro c hcC a ha
  rw [hc.A_eq] at ha ⊢
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  let g : ↥D.Ct := ⟨c, hcC⟩
  refine Subgroup.mem_map.mpr ⟨g * a' * g⁻¹, ?_, by simp [g]⟩
  exact (inferInstance : (pPrimeCore 2 ↥D.Ct).Normal).conj_mem a' ha' g

omit [Finite G] in
theorem Ct_le_normalizer_A (hc : SPL2Ct D.toSPLNot2) : D.Ct ≤ normalizer (D.A : Set G) := by
  intro c hcC
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact A_norm_Ct D hc c hcC h hh
  · intro hh
    have := A_norm_Ct D hc c⁻¹ (Subgroup.inv_mem _ hcC) _ hh
    simpa [mul_assoc] using this

theorem z_comm_t (hs : SPLSetup D.toSPLNot0) : D.z * D.t = D.t * D.z :=
  (mem_centralizer_singleton_iff.mp (t_mem_Cz hs)).symm

theorem z_mem_Ct (hs : SPLSetup D.toSPLNot0) : D.z ∈ D.Ct :=
  mem_centralizer_singleton_iff.mpr (z_comm_t D hs)

theorem T0_le_Ct (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : D.T₀ ≤ D.Ct := by
  refine sup_le ?_ ?_
  · rw [zpowers_le]; exact D.Ct.pow_mem (x_mem_Ct D hc) 2
  · rw [zpowers_le]; exact z_mem_Ct D hs

theorem T0_comm_t (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ∀ s ∈ D.T₀, s * D.t = D.t * s :=
  fun _ hsT => mem_centralizer_singleton_iff.mp (T0_le_Ct D hs hc hsT)

omit [Finite G] in
theorem T0_pgroup (_hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : IsPGroup 2 ↥D.T₀ := by
  obtain ⟨k, hk2, hk, ⟨e⟩⟩ := hc.xz_dih
  have hcard : Nat.card ↥(zpowers D.x ⊔ zpowers D.z) = 2 ^ D.n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hk2]
  have hQ : IsPGroup 2 ↥(zpowers D.x ⊔ zpowers D.z) := IsPGroup.of_card hcard
  have hle : D.T₀ ≤ zpowers D.x ⊔ zpowers D.z := by
    refine sup_le ?_ le_sup_right
    rw [zpowers_le]
    exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (mem_zpowers D.x) 2)
  exact hQ.to_le hle

omit [Finite G] in
theorem t_mem_T0 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) : D.t ∈ D.T₀ := by
  have hn := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have : D.t = (D.x ^ 2) ^ (2 ^ (D.n - 3)) := by
    rw [← pow_mul, ← hc.x_pow]
    congr 1
    have h : D.n - 2 = (D.n - 3) + 1 := by omega
    rw [h, pow_succ]
    ring
  rw [this]
  exact Subgroup.mem_sup_left (Subgroup.pow_mem _ (mem_zpowers _) _)

theorem T0_le_normalizer_A (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    D.T₀ ≤ normalizer (D.A : Set G) :=
  (T0_le_Ct D hs hc).trans (Ct_le_normalizer_A D hc)

theorem mem_A_sup_T0 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {g : G}
    (hg : g ∈ D.A ⊔ D.T₀) : ∃ a ∈ D.A, ∃ s ∈ D.T₀, g = a * s :=
  mem_sup_of_le_normalizer (T0_le_normalizer_A D hs hc) hg

omit [Finite G] in
theorem z_conj_xpow (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (m : ℤ) :
    D.z * D.x ^ m * D.z⁻¹ = (D.x ^ m)⁻¹ := by
  rw [← conj_zpow, z_inv_x D hs hc, inv_zpow]

omit [Finite G] in
theorem T0_elems (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {s : G} (hsT : s ∈ D.T₀) :
    (∃ m : ℤ, s = D.x ^ (2 * m)) ∨ (∃ m : ℤ, s = D.x ^ (2 * m) * D.z) := by
  have hzz : D.z * D.z = 1 := z_mul_z D hs
  have hx2 : ∀ m : ℤ, (D.x ^ 2) ^ m = D.x ^ (2 * m) := by
    intro m
    rw [zpow_mul]
    norm_cast
  have hzx2 : D.z * D.x ^ 2 * D.z⁻¹ = (D.x ^ 2)⁻¹ := by
    rw [← conj_pow, z_inv_x D hs hc, inv_pow]
  have hconj : ∀ h ∈ zpowers (D.x ^ 2), D.z * h * D.z⁻¹ ∈ zpowers (D.x ^ 2) := by
    intro h hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hh
    rw [← conj_zpow, hzx2, inv_zpow]
    exact Subgroup.inv_mem _ (zpow_mem_zpowers _ _)
  have hnorm : zpowers D.z ≤ normalizer (zpowers (D.x ^ 2) : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    constructor
    · exact hconj h
    · intro hh
      have key : h ∈ zpowers (D.x ^ 2) := by
        have := hconj _ hh
        have e : D.z * (D.z * h * D.z⁻¹) * D.z⁻¹ = h := by
          calc D.z * (D.z * h * D.z⁻¹) * D.z⁻¹ = (D.z * D.z) * h * (D.z * D.z)⁻¹ := by group
            _ = h := by rw [hzz]; group
        rwa [e] at this
      exact key
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_le_normalizer hnorm hsT
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  rw [hx2]
  rcases Int.even_or_odd' j with ⟨k, rfl | rfl⟩
  · left
    refine ⟨m, ?_⟩
    have : D.z ^ (2 * k) = 1 := by
      rw [zpow_mul, zpow_two, hzz, one_zpow]
    rw [this, mul_one]
  · right
    refine ⟨m, ?_⟩
    have : D.z ^ (2 * k + 1) = D.z := by
      have h2 : D.z ^ (2 * k) = 1 := by rw [zpow_mul, zpow_two, hzz, one_zpow]
      rw [zpow_add_one, h2, one_mul]
    rw [this]

omit [Finite G] in
theorem T0_inv_conj (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {s : G}
    (hsT : s ∈ D.T₀) (hs2 : s * s = 1) (hst : s ≠ D.t) (hs1 : s ≠ 1) : IsConj D.z s := by
  have htt := t_mul_t D hs
  have hn := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  rcases T0_elems D hs hc hsT with ⟨m, rfl⟩ | ⟨m, rfl⟩
  ·
    exfalso
    have h4 : D.x ^ ((4 : ℤ) * m) = 1 := by
      have e : (4 : ℤ) * m = 2 * m + 2 * m := by ring
      rw [e, zpow_add]; exact hs2
    have hdvd : ((2 ^ (D.n - 1) : ℕ) : ℤ) ∣ (4 : ℤ) * m := by
      rw [← hc.x_ord]; exact orderOf_dvd_iff_zpow_eq_one.mpr h4
    have hp : (2 : ℕ) ^ (D.n - 1) = 4 * 2 ^ (D.n - 3) := by
      have : D.n - 1 = (D.n - 3) + 2 := by omega
      rw [this, pow_add]; ring
    rw [hp] at hdvd
    obtain ⟨m', hm'⟩ := hdvd
    have hm2 : m = (2 : ℤ) ^ (D.n - 3) * m' := by
      push_cast at hm'
      have h5 : (4 : ℤ) * (2 ^ (D.n - 3) * m') = 4 * m := by linarith
      exact (mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h5).symm
    have ht : D.x ^ (2 * m) = D.t ^ m' := by
      have e1 : (2 : ℤ) * m = ((2 ^ (D.n - 2) : ℕ) : ℤ) * m' := by
        rw [hm2]
        have : (2 : ℕ) ^ (D.n - 2) = 2 * 2 ^ (D.n - 3) := by
          have : D.n - 2 = (D.n - 3) + 1 := by omega
          rw [this, pow_succ]; ring
        rw [this]; push_cast; ring
      rw [e1, zpow_mul, zpow_natCast, hc.x_pow]
    rw [ht] at hst hs1
    rcases Int.even_or_odd' m' with ⟨k, rfl | rfl⟩
    · apply hs1
      rw [zpow_mul, zpow_two, htt, one_zpow]
    · apply hst
      rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul]
  ·
    refine isConj_iff.mpr ⟨D.x ^ m, ?_⟩
    have h1 : D.z * (D.x ^ m)⁻¹ * D.z⁻¹ = D.x ^ m := by
      rw [← conj_inv, z_conj_xpow D hs hc, inv_inv]
    have hxm : D.x ^ (2 * m) = D.x ^ m * D.x ^ m := by
      rw [two_mul, zpow_add]
    calc D.x ^ m * D.z * (D.x ^ m)⁻¹
        = D.x ^ m * (D.z * (D.x ^ m)⁻¹ * D.z⁻¹) * D.z := by group
      _ = D.x ^ m * D.x ^ m * D.z := by rw [h1]
      _ = D.x ^ (2 * m) * D.z := by rw [hxm]

theorem Q_decomp (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) (h3 : SPL3X D) {c : G}
    (hcC : c ∈ D.Ct) (hc0 : ∀ y ∈ D.Y₀, c * y = y * c) :
    ∃ y ∈ D.Y₀, ∃ a ∈ D.A, ∃ s ∈ D.T₀, c = y * (a * s) := by
  classical
  have hcI : ∀ i ∈ D.I, c * i * c⁻¹ ∈ D.I := fun i hi => I_normalized D hc c hcC i hi
  have hcI' : ∀ i ∈ D.I, c⁻¹ * i * c ∈ D.I := by
    intro i hi
    have := I_normalized D hc c⁻¹ (Subgroup.inv_mem _ hcC) i hi
    simpa using this
  let γ : ↥D.I ≃* ↥D.I :=
    { toFun := fun k => ⟨c * k * c⁻¹, hcI k k.2⟩
      invFun := fun k => ⟨c⁻¹ * k * c, hcI' k k.2⟩
      left_inv := fun k => Subtype.ext (by show c⁻¹ * (c * (k : G) * c⁻¹) * c = k; group)
      right_inv := fun k => Subtype.ext (by show c * (c⁻¹ * (k : G) * c) * c⁻¹ = k; group)
      map_mul' := fun a b => Subtype.ext (by
        show c * ((a : G) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹)
        group) }
  obtain ⟨F, hFfield, hFfin, hFq, ⟨e⟩⟩ := hc.I_L2
  have hFq' : Nat.card F = D.q := hFq
  obtain ⟨k, hk1, hkq⟩ := hs.q_pow
  have hq : Nat.card F = D.p ^ k := by rw [hFq']; exact hkq
  have hY₀I : D.Y₀ ≤ D.I := Y₀_le_I D hs hc h3
  have hWc : Nat.card ↥(D.Y₀.subgroupOf D.I) = Nat.card F := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY₀I).toEquiv, Y₀_card D hs h3, hFq']
  have hWp : IsPGroup D.p ↥(D.Y₀.subgroupOf D.I) := by
    refine IsPGroup.of_card (n := k) ?_
    rw [hWc, hq]
  have hγ : ∀ w ∈ D.Y₀.subgroupOf D.I, γ w = w := by
    intro w hw
    have hwY : (w : G) ∈ D.Y₀ := hw
    apply Subtype.ext
    show c * (w : G) * c⁻¹ = w
    calc c * (w : G) * c⁻¹ = ((w : G) * c) * c⁻¹ := by rw [hc0 _ hwY]
      _ = w := by group
  obtain ⟨w₀, hw₀, hw₀γ⟩ := aut_fixing_sylow_inner D.p k hs.prime hs.p_ne_two hq hk1 e
    (D.Y₀.subgroupOf D.I) hWp hWc γ hγ
  have hy : (w₀ : G) ∈ D.Y₀ := hw₀
  have hyCt : (w₀ : G) ∈ D.Ct := hy.1
  have hg : (w₀ : G)⁻¹ * c ∈ centralizer (D.I : Set G) ⊓ D.Ct := by
    refine ⟨mem_centralizer_iff.mpr (fun i hi => ?_),
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyCt) hcC⟩
    have e : c * i * c⁻¹ = (w₀ : G) * i * (w₀ : G)⁻¹ := congrArg Subtype.val (hw₀γ ⟨i, hi⟩)
    calc i * ((w₀ : G)⁻¹ * c) = ((w₀ : G)⁻¹ * ((w₀ : G) * i * (w₀ : G)⁻¹) * (w₀ : G)) * ((w₀ : G)⁻¹ * c) := by
          group
      _ = ((w₀ : G)⁻¹ * (c * i * c⁻¹) * (w₀ : G)) * ((w₀ : G)⁻¹ * c) := by rw [e]
      _ = ((w₀ : G)⁻¹ * c) * i := by group
  rw [hc.cen_I] at hg
  obtain ⟨a, ha, s, hsT, has⟩ := mem_A_sup_T0 D hs hc hg
  refine ⟨(w₀ : G), hy, a, ha, s, hsT, ?_⟩
  rw [← has]
  group

end L33b

end CFSG.GH74.GLS.SP.Local
