module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem isSubnormal_trans {H M K : Subgroup G} (h₁ : IsSubnormal H M) (h₂ : IsSubnormal M K) :
    IsSubnormal H K :=
  h₁.trans h₂

theorem isSubnormal_of_normal_subgroupOf {H K : Subgroup G} (hHK : H ≤ K)
    (hN : (H.subgroupOf K).Normal) : IsSubnormal H K :=
  IsSubnormal.step hHK hN (IsSubnormal.refl K)

theorem isSubnormal_map_mulEquiv {G' : Type*} [Group G'] (e : G ≃* G') {H K : Subgroup G}
    (h : IsSubnormal H K) : IsSubnormal (H.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  h.map e.toMonoidHom

theorem isSubnormal_map_conj {H K : Subgroup G} (h : IsSubnormal H K) (g : G) :
    IsSubnormal (H.map (MulAut.conj g).toMonoidHom) (K.map (MulAut.conj g).toMonoidHom) :=
  isSubnormal_map_mulEquiv (MulAut.conj g) h

theorem isSubnormal_inf {H K : Subgroup G} (h : IsSubnormal H K) (L : Subgroup G) :
    IsSubnormal (H ⊓ L) (K ⊓ L) :=
  h.inf L

end Subnormal

section Quaternion

theorem exists_pow_orderOf_eq_two {P : Type*} [Group P] (hP : IsPGroup 2 P) {x : P} (hx : x ≠ 1) :
    ∃ n : ℕ, orderOf (x ^ n) = 2 := by
  obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hP x
  cases j with
  | zero => exact absurd (orderOf_eq_one_iff.mp (by simpa using hj)) hx
  | succ j =>
    refine ⟨2 ^ j, ?_⟩
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hj]; exact pow_dvd_pow 2 (Nat.le_succ j)), hj, pow_succ]
    simp

theorem exists_mem_orderOf_eq_two_of_isPGroup {P : Type*} [Group P] (hP : IsPGroup 2 P)
    {H : Subgroup P} (hH : H ≠ ⊥) : ∃ x ∈ H, orderOf x = 2 := by
  obtain ⟨⟨x, hxH⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hP (x := x) fun h => hx1 (Subtype.ext h)
  exact ⟨x ^ n, H.pow_mem hxH n, hn⟩

theorem exists_mem_orderOf_eq_two_of_isPGroup_subgroup {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) : ∃ x ∈ P, orderOf x = 2 := by
  obtain ⟨⟨x, hxP⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hP (x := ⟨x, hxP⟩) hx1
  refine ⟨x ^ n, P.pow_mem hxP n, ?_⟩
  rw [← hn, ← Subgroup.orderOf_coe]
  rfl

theorem mem_of_isPGroup_of_unique_involution {P : Type*} [Group P] (hP : IsPGroup 2 P) {u : P}
    (hu : ∀ x : P, orderOf x = 2 → x = u) {H : Subgroup P} (hH : H ≠ ⊥) : u ∈ H := by
  obtain ⟨x, hxH, hx⟩ := exists_mem_orderOf_eq_two_of_isPGroup hP hH
  exact hu x hx ▸ hxH

private theorem div_gcd_eq_two_iff (m : ℕ) (hm : 0 < m) (v : ℕ) (hv : v < 2 * m) :
    2 * m / Nat.gcd (2 * m) v = 2 ↔ v = m := by
  constructor
  · intro h
    have h1 : 2 * Nat.gcd (2 * m) v = 2 * m := by
      have := Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * m) v)
      rw [h] at this
      exact this
    have hg : Nat.gcd (2 * m) v = m := by omega
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right (2 * m) v
    rw [hg] at hk
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [Nat.gcd_zero_right] at hg
      omega
    have hk_lt : k < 2 := by
      refine Nat.lt_of_mul_lt_mul_left (a := m) ?_
      rw [← hk]
      omega
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hv0 (by simpa using hk)
    have hk1 : k = 1 := by omega
    rw [hk, hk1, mul_one]
  · rintro rfl
    rw [Nat.gcd_eq_right (dvd_mul_left v 2)]
    exact Nat.mul_div_cancel 2 hm

theorem quaternionGroup_orderOf_eq_two_iff (m : ℕ) [NeZero m] (q : QuaternionGroup m) :
    orderOf q = 2 ↔ q = QuaternionGroup.a (m : ZMod (2 * m)) := by
  have hm_pos : 0 < m := NeZero.pos m
  have hm_lt : m < 2 * m := by omega
  cases q with
  | xa i =>
    rw [QuaternionGroup.orderOf_xa]
    simp
  | a i =>
    rw [QuaternionGroup.orderOf_a, QuaternionGroup.a.injEq,
      div_gcd_eq_two_iff m hm_pos i.val (ZMod.val_lt i)]
    constructor
    · intro h
      apply ZMod.val_injective
      rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]
    · rintro rfl
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt]

theorem isPGroup_two_quaternionGroup_two_pow (k : ℕ) : IsPGroup 2 (QuaternionGroup (2 ^ k)) := by
  refine IsPGroup.of_card (n := k + 2) ?_
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  ring

theorem quaternionGroup_a_mem_of_ne_bot (k : ℕ) {H : Subgroup (QuaternionGroup (2 ^ k))}
    (hH : H ≠ ⊥) : QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k)) ∈ H :=
  mem_of_isPGroup_of_unique_involution (isPGroup_two_quaternionGroup_two_pow k)
    (fun _ hx => (quaternionGroup_orderOf_eq_two_iff _ _).mp hx) hH

theorem isPGroup_two_of_mulEquiv_quaternionGroup {P : Type*} [Group P] {k : ℕ}
    (e : P ≃* QuaternionGroup (2 ^ k)) : IsPGroup 2 P :=
  (isPGroup_two_quaternionGroup_two_pow k).of_equiv e.symm

theorem exists_unique_involution_of_mulEquiv_quaternionGroup {P : Type*} [Group P] {k : ℕ}
    (e : P ≃* QuaternionGroup (2 ^ k)) :
    ∃ u : P, orderOf u = 2 ∧ (∀ x : P, orderOf x = 2 → x = u) ∧
      ∀ H : Subgroup P, H ≠ ⊥ → u ∈ H := by
  have huniq : ∀ x : P, orderOf x = 2 →
      x = e.symm (QuaternionGroup.a ((2 ^ k : ℕ) : ZMod (2 * 2 ^ k))) := by
    intro x hx
    rw [e.eq_symm_apply]
    exact (quaternionGroup_orderOf_eq_two_iff _ _).mp (by rwa [← MulEquiv.orderOf_eq e] at hx)
  refine ⟨_, ?_, huniq, fun H hH => mem_of_isPGroup_of_unique_involution
    (isPGroup_two_of_mulEquiv_quaternionGroup e) huniq hH⟩
  rw [MulEquiv.orderOf_eq]
  exact (quaternionGroup_orderOf_eq_two_iff _ _).mpr rfl

end Quaternion

section Involutions

theorem exists_conj_mem_sylow_of_orderOf_eq_two {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {t : H} (ht : orderOf t = 2) :
    ∃ c s : H, s ∈ S ∧ orderOf s = 2 ∧ c * s * c⁻¹ = t := by
  have hP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; simp)
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq H S Q
  have htQ : t ∈ ((c • S : Sylow 2 H) : Subgroup H) := hQ (Subgroup.mem_zpowers t)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at htQ
  obtain ⟨s, hsS, hst⟩ := htQ
  refine ⟨c, s, hsS, ?_, ?_⟩
  · rw [← ht, ← hst]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) s).symm
  · simpa using hst

theorem exists_conj_of_orderOf_eq_two {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (hS : ∀ x y : (S : Subgroup H), orderOf x = 2 → orderOf y = 2 → x = y) {x y : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : ∃ c : H, c * x * c⁻¹ = y := by
  obtain ⟨c, s, hs, hs2, rfl⟩ := exists_conj_mem_sylow_of_orderOf_eq_two S hx
  obtain ⟨d, s', hs', hs2', rfl⟩ := exists_conj_mem_sylow_of_orderOf_eq_two S hy
  have hss' : s = s' :=
    congrArg Subtype.val (hS ⟨s, hs⟩ ⟨s', hs'⟩ (by rwa [Subgroup.orderOf_mk])
      (by rwa [Subgroup.orderOf_mk]))
  subst hss'
  exact ⟨d * c⁻¹, by group⟩

variable {G : Type*} [Group G] [Finite G] {J : Subgroup G} {z : G}

theorem eq_of_orderOf_eq_two_of_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hcent : J ≤ Subgroup.centralizer ({z} : Set G)) (S : Sylow 2 J)
    (hS : ∀ x y : (S : Subgroup J), orderOf x = 2 → orderOf y = 2 → x = y)
    {t : G} (htJ : t ∈ J) (ht : orderOf t = 2) : t = z := by
  obtain ⟨c, hc⟩ := exists_conj_of_orderOf_eq_two S hS
    (x := ⟨z, hzJ⟩) (y := ⟨t, htJ⟩) (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk])
  have hcz : (c : G) * z = z * c := by
    have := Subgroup.mem_centralizer_iff.mp (hcent c.2) z rfl
    exact this.symm
  have : (c : G) * z * (c : G)⁻¹ = t := congrArg Subtype.val hc
  rw [← this, hcz, mul_assoc, mul_inv_cancel, mul_one]

theorem eq_of_orderOf_eq_two_of_quaternion_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hcent : J ≤ Subgroup.centralizer ({z} : Set G)) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    {t : G} (htJ : t ∈ J) (ht : orderOf t = 2) : t = z := by
  obtain ⟨r, -, ⟨e⟩⟩ := hS
  obtain ⟨u, -, hu, -⟩ := exists_unique_involution_of_mulEquiv_quaternionGroup e
  exact eq_of_orderOf_eq_two_of_sylow hzJ hz hcent S
    (fun x y hx hy => (hu x hx).trans (hu y hy).symm) htJ ht

omit [Finite G] in
theorem mem_of_isPGroup_of_unique_involution_subgroup
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {P : Subgroup G} (hPJ : P ≤ J) (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) : z ∈ P := by
  obtain ⟨x, hxP, hx⟩ := exists_mem_orderOf_eq_two_of_isPGroup_subgroup hP hP1
  exact hU x (hPJ hxP) hx ▸ hxP

theorem unique_involution_of_quaternion_sylow (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hcent : J ≤ Subgroup.centralizer ({z} : Set G)) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    (∀ t ∈ J, orderOf t = 2 → t = z) ∧
      ∀ P : Subgroup G, P ≤ J → IsPGroup 2 P → P ≠ ⊥ → z ∈ P := by
  have hU : ∀ t ∈ J, orderOf t = 2 → t = z := fun t htJ ht =>
    eq_of_orderOf_eq_two_of_quaternion_sylow hzJ hz hcent S hS htJ ht
  exact ⟨hU, fun _ hPJ hP hP1 => mem_of_isPGroup_of_unique_involution_subgroup hU hPJ hP hP1⟩

end Involutions

section TightlyEmbedded

variable {G : Type*} [Group G]

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa using MulEquiv.orderOf_eq (MulAut.conj g) x

theorem mem_map_conj_iff {J : Subgroup G} {g x : G} :
    x ∈ J.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem map_conj_eq_iff_mem_normalizer {J : Subgroup G} {g : G} :
    J.map (MulAut.conj g).toMonoidHom = J ↔ g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq, ← SetLike.coe_set_eq, Subgroup.coe_map]
  rfl

theorem map_conj_eq_map_conj_iff {J : Subgroup G} {g h : G} :
    J.map (MulAut.conj g).toMonoidHom = J.map (MulAut.conj h).toMonoidHom ↔
      h⁻¹ * g ∈ Subgroup.normalizer (J : Set G) := by
  rw [← map_conj_eq_iff_mem_normalizer]
  have key : ∀ a b : G, (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
    intro a b
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  have hinj := Subgroup.map_injective (f := (MulAut.conj h⁻¹).toMonoidHom)
    (MulAut.conj h⁻¹).injective
  rw [← hinj.eq_iff, key, key, inv_mul_cancel,
    map_conj_eq_iff_mem_normalizer.mpr (Subgroup.one_mem _)]

theorem map_conj_centralizer_singleton (g z : G) :
    (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
  ext x
  rw [mem_map_conj_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g * z) * g⁻¹ := by rw [h]
      _ = x * (g * z * g⁻¹) := by group
  · intro h
    calc z * (g⁻¹ * x * g) = g⁻¹ * (g * z * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * z * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * x * g * z := by group

theorem isSubnormal_map_conj_centralizer {J : Subgroup G} {z : G}
    (h : IsSubnormal J (Subgroup.centralizer ({z} : Set G))) (g : G) :
    IsSubnormal (J.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) := by
  rw [← map_conj_centralizer_singleton]
  exact isSubnormal_map_conj h g

variable {J : Subgroup G} {z : G}

theorem normalizer_le_centralizer_of_unique_involution (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  have hmem : c * z * c⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hc z).mp hzJ
  have h := hU _ hmem (by rw [orderOf_conj_eq, hz])
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem eq_conj_of_mem_map_conj_of_unique_involution
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) {g t : G}
    (htg : t ∈ J.map (MulAut.conj g).toMonoidHom) (ht : orderOf t = 2) : t = g * z * g⁻¹ := by
  have h := hU _ (mem_map_conj_iff.mp htg)
    (by simpa using (orderOf_conj_eq g⁻¹ t).trans ht)
  rw [← h]
  group

theorem tightlyEmbedded_iff_centralizer_le_normalizer_of_unique_involution [Finite G]
    (hzJ : z ∈ J) (hz : orderOf z = 2) (hU : ∀ t ∈ J, orderOf t = 2 → t = z) :
    classicalInvolutionTightlyEmbedded J ↔
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  constructor
  · intro hTE c hc
    by_contra hcN
    have hcz : z * c = c * z := Subgroup.mem_centralizer_iff.mp hc z rfl
    have hzmem : z ∈ J ⊓ J.map (MulAut.conj c).toMonoidHom := by
      refine ⟨hzJ, mem_map_conj_iff.mpr ?_⟩
      rwa [mul_assoc, hcz, inv_mul_cancel_left]
    have h2 : 2 ∣ Nat.card (J ⊓ J.map (MulAut.conj c).toMonoidHom : Subgroup G) := by
      have := Subgroup.orderOf_dvd_natCard _ hzmem
      rwa [hz] at this
    exact (hTE c hcN).not_two_dvd_nat h2
  · intro hC g hg
    by_contra hodd
    have heven : 2 ∣ Nat.card (J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have h1 : (x : G) = z := hU _ x.2.1 hx'
    have h2 := eq_conj_of_mem_map_conj_of_unique_involution hU x.2.2 hx'
    rw [h1] at h2
    have hgc : g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      exact (mul_inv_eq_iff_eq_mul.mp h2.symm).symm
    exact hg (hC hgc)

theorem centralizer_eq_normalizer_of_tightlyEmbedded [Finite G] (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) (hTE : classicalInvolutionTightlyEmbedded J) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.normalizer (J : Set G) :=
  le_antisymm
    ((tightlyEmbedded_iff_centralizer_le_normalizer_of_unique_involution hzJ hz hU).mp hTE)
    (normalizer_le_centralizer_of_unique_involution hzJ hz hU)

theorem conj_eq_iff_map_conj_eq_of_tightlyEmbedded [Finite G] (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hU : ∀ t ∈ J, orderOf t = 2 → t = z) (hTE : classicalInvolutionTightlyEmbedded J)
    (g h : G) :
    g * z * g⁻¹ = h * z * h⁻¹ ↔
      J.map (MulAut.conj g).toMonoidHom = J.map (MulAut.conj h).toMonoidHom := by
  rw [map_conj_eq_map_conj_iff, ← centralizer_eq_normalizer_of_tightlyEmbedded hzJ hz hU hTE,
    Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro e
    calc z * (h⁻¹ * g) = h⁻¹ * (h * z * h⁻¹) * g := by group
      _ = h⁻¹ * (g * z * g⁻¹) * g := by rw [e]
      _ = h⁻¹ * g * z := by group
  · intro e
    calc g * z * g⁻¹ = h * (h⁻¹ * g * z) * g⁻¹ := by group
      _ = h * (z * (h⁻¹ * g)) * g⁻¹ := by rw [e]
      _ = h * z * h⁻¹ := by group

theorem tightlyEmbedded_iff_centralizer_le_normalizer [Finite G] (hzJ : z ∈ J)
    (hz : orderOf z = 2) (hcent : J ≤ Subgroup.centralizer ({z} : Set G)) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    classicalInvolutionTightlyEmbedded J ↔
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
  tightlyEmbedded_iff_centralizer_le_normalizer_of_unique_involution hzJ hz
    (fun _ htJ ht => eq_of_orderOf_eq_two_of_quaternion_sylow hzJ hz hcent S hS htJ ht)

theorem conj_of_tightlyEmbedded [Finite G] (hzJ : z ∈ J) (hz : orderOf z = 2)
    (hcent : J ≤ Subgroup.centralizer ({z} : Set G)) (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hTE : classicalInvolutionTightlyEmbedded J) :
    (∀ g h : G, g * z * g⁻¹ = h * z * h⁻¹ ↔
        J.map (MulAut.conj g).toMonoidHom = J.map (MulAut.conj h).toMonoidHom) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (J : Set G) →
        Odd (Nat.card (J ⊓ J.map (MulAut.conj g).toMonoidHom : Subgroup G)) :=
  ⟨conj_eq_iff_map_conj_eq_of_tightlyEmbedded hzJ hz
      (fun _ htJ ht => eq_of_orderOf_eq_two_of_quaternion_sylow hzJ hz hcent S hS htJ ht) hTE,
    hTE⟩

end TightlyEmbedded

end CFSG.ClassicalInvolution
