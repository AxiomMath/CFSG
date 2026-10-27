module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductions
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def InvThree {X : Type*} [Group X] (J : Subgroup X) : Prop :=
  ∃ a ∈ J, ∃ g ∈ J, orderOf a = 3 ∧ g * a * g⁻¹ = a⁻¹

theorem InvThree.mono {X : Type*} [Group X] {J J' : Subgroup X} (h : J ≤ J')
    (hJ : InvThree J) : InvThree J' := by
  obtain ⟨a, ha, g, hg, h3, hi⟩ := hJ
  exact ⟨a, h ha, g, h hg, h3, hi⟩

theorem InvThree.map_injective {X Y : Type*} [Group X] [Group Y] {J : Subgroup X} (f : X →* Y)
    (hf : Function.Injective f) (hJ : InvThree J) : InvThree (J.map f) := by
  obtain ⟨a, ha, g, hg, h3, hi⟩ := hJ
  refine ⟨f a, ⟨a, ha, rfl⟩, f g, ⟨g, hg, rfl⟩, ?_, ?_⟩
  · rw [orderOf_injective f hf a, h3]
  · rw [← map_inv, ← map_mul, ← map_mul, hi, map_inv]

theorem InvThree.of_top_subgroup {X : Type*} [Group X] {J : Subgroup X}
    (h : InvThree (⊤ : Subgroup ↥J)) : InvThree J := by
  have := h.map_injective J.subtype J.subtype_injective
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this

theorem InvThree.to_top {X : Type*} [Group X] {J : Subgroup X} (h : InvThree J) :
    InvThree (⊤ : Subgroup ↥J) := by
  obtain ⟨a, ha, g, hg, h3, hi⟩ := h
  refine ⟨⟨a, ha⟩, trivial, ⟨g, hg⟩, trivial, ?_, Subtype.ext (by simpa using hi)⟩
  rw [← Subgroup.orderOf_coe]
  exact h3

theorem InvThree.of_mulEquiv {X Y : Type*} [Group X] [Group Y] {J : Subgroup X} (e : ↥J ≃* Y)
    (h : InvThree (⊤ : Subgroup Y)) : InvThree J := by
  apply InvThree.of_top_subgroup
  have := h.map_injective e.symm.toMonoidHom e.symm.injective
  rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at this

namespace BlockInvThree

theorem invThree_perm {n : ℕ} (hn : 3 ≤ n) : InvThree (⊤ : Subgroup (Equiv.Perm (Fin n))) := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  refine ⟨Equiv.swap i0 i1 * Equiv.swap i0 i2, trivial, Equiv.swap i1 i2, trivial,
    (Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12).orderOf, ?_⟩
  have e1 : Equiv.swap i1 i2 * Equiv.swap i0 i1 * (Equiv.swap i1 i2)⁻¹ = Equiv.swap i0 i2 := by
    rw [← Equiv.swap_apply_apply, Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_left]
  have e2 : Equiv.swap i1 i2 * Equiv.swap i0 i2 * (Equiv.swap i1 i2)⁻¹ = Equiv.swap i0 i1 := by
    rw [← Equiv.swap_apply_apply, Equiv.swap_apply_of_ne_of_ne h01 h02, Equiv.swap_apply_right]
  calc Equiv.swap i1 i2 * (Equiv.swap i0 i1 * Equiv.swap i0 i2) * (Equiv.swap i1 i2)⁻¹
      = (Equiv.swap i1 i2 * Equiv.swap i0 i1 * (Equiv.swap i1 i2)⁻¹) *
          (Equiv.swap i1 i2 * Equiv.swap i0 i2 * (Equiv.swap i1 i2)⁻¹) := by group
    _ = (Equiv.swap i0 i1 * Equiv.swap i0 i2)⁻¹ := by
      rw [e1, e2, mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]

theorem invThree_prod_perm {r k : ℕ} (hk : 3 ≤ k) :
    InvThree (⊤ : Subgroup (Equiv.Perm (Fin r) × Equiv.Perm (Fin k))) := by
  have h := (invThree_perm hk).map_injective
    (MonoidHom.inr (Equiv.Perm (Fin r)) (Equiv.Perm (Fin k))) (fun x y h => by
      simpa using congrArg Prod.snd h)
  exact h.mono le_top

theorem exists_two_pow_orderOf_three {Y : Type*} [Group Y] {N : Subgroup Y} (hN : IsPGroup 2 N)
    {x : Y} (hx3 : x ^ 3 ∈ N) (hx : x ∉ N) : ∃ k : ℕ, orderOf (x ^ 2 ^ k) = 3 := by
  obtain ⟨k, hk⟩ := hN ⟨x ^ 3, hx3⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, orderOf_eq_prime ?_ ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hk']
  · intro h1
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
    have hx1 : x ∈ N := by
      have hz : x ^ (3 : ℤ) ∈ N := by simpa using hx3
      have hw : x ^ ((2 : ℤ) ^ k) = 1 := by
        rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, zpow_natCast]
        exact h1
      obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, 3 * u + 2 ^ k * v = 1 := by
        have := Nat.Coprime.gcd_eq_one hcop
        refine ⟨Nat.gcdA 3 (2 ^ k), Nat.gcdB 3 (2 ^ k), ?_⟩
        have h := Nat.gcd_eq_gcd_ab 3 (2 ^ k)
        rw [this] at h
        push_cast at h
        linarith
      have : x = (x ^ (3 : ℤ)) ^ u * (x ^ ((2 : ℤ) ^ k)) ^ v := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
      rw [this, hw, one_zpow, mul_one]
      exact N.zpow_mem hz u
    exact hx hx1

end BlockInvThree

open BlockInvThree

theorem InvThree.of_quotient_pCore {Q : Type*} [Group Q] [Finite Q]
    (h : InvThree (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q))) : InvThree (⊤ : Subgroup Q) := by
  set O := CFSG.pCore 2 Q
  have : O.Normal := CFSG.pCore_normal
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  have hO : Nat.Coprime 3 (Nat.card O) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨abar, -, gbar, -, h3, hinv⟩ := h
  obtain ⟨a₀, rfl⟩ := QuotientGroup.mk'_surjective O abar
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective O gbar
  set q := QuotientGroup.mk' O
  have ha3 : a₀ ^ 3 ∈ O := by
    rw [← QuotientGroup.eq_one_iff (N := O)]
    change q (a₀ ^ 3) = 1
    rw [map_pow, ← h3, pow_orderOf_eq_one]
  have ha : a₀ ∉ O := by
    intro hm
    have : q a₀ = 1 := (QuotientGroup.eq_one_iff (N := O) a₀).mpr hm
    rw [this, orderOf_one] at h3
    omega
  obtain ⟨k, hk⟩ := exists_two_pow_orderOf_three hO2 ha3 ha
  set a₁ := a₀ ^ 2 ^ k
  set U := Subgroup.zpowers a₁
  have hU : IsPGroup 3 U := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk, pow_one])
  have hconj1 : q g₀ * q a₁ * (q g₀)⁻¹ = (q a₁)⁻¹ := by
    simp only [a₁, map_pow]
    rw [← conj_pow, hinv, inv_pow]
  have hconj : ∀ m : ℤ, q g₀ * (q a₁) ^ m * (q g₀)⁻¹ = ((q a₁) ^ m)⁻¹ := by
    intro m
    rw [← conj_zpow, hconj1, inv_zpow]
  have hbU : q g₀ ∈ Subgroup.normalizer ((U.map q : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    rw [MonoidHom.map_zpowers] at hn ⊢
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [hconj m]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers _ m)
  obtain ⟨t, -, htN, hteq⟩ := exists_lift_mem_normalizer Nat.prime_three O hO hU le_top
    (Subgroup.mem_top g₀) hbU
  refine ⟨a₁, trivial, t, trivial, hk, ?_⟩
  have h1 : t * a₁ * t⁻¹ ∈ U :=
    (Subgroup.mem_normalizer_iff.mp htN a₁).mp (Subgroup.mem_zpowers a₁)
  have h2 : a₁⁻¹ ∈ U := Subgroup.inv_mem _ (Subgroup.mem_zpowers a₁)
  refine eq_of_mk_eq_of_isPGroup Nat.prime_three O hO hU h1 h2 ?_
  change q (t * a₁ * t⁻¹) = q a₁⁻¹
  rw [map_mul, map_mul, map_inv, map_inv, hteq]
  exact hconj1

theorem InvThree.of_quotient_pCore_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y]
    {J : Subgroup X} (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Y) (h : InvThree (⊤ : Subgroup Y)) :
    InvThree J := by
  apply InvThree.of_top_subgroup
  apply InvThree.of_quotient_pCore
  have := h.map_injective e.symm.toMonoidHom e.symm.injective
  rwa [Subgroup.map_top_of_surjective _ e.symm.surjective] at this

namespace BlockInvThree

theorem conj_comm_eq_inv_of_mem_center {Y : Type*} [Group Y] {x g : Y}
    (hz : g * x * g⁻¹ * x ∈ Subgroup.center Y) :
    g * (x * g * x⁻¹ * g⁻¹) * g⁻¹ = (x * g * x⁻¹ * g⁻¹)⁻¹ := by
  set z := g * x * g⁻¹ * x
  have hc := Subgroup.mem_center_iff.mp hz
  have e1 : g * x * g⁻¹ = z * x⁻¹ := by simp only [z]; group
  have hgz : g * z * g⁻¹ = z := by rw [hc g]; group
  have hzx : z * x * z⁻¹ = x := by rw [← hc x]; group
  have hgg : (g * g) * x * (g * g)⁻¹ = x := by
    calc (g * g) * x * (g * g)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by group
      _ = g * (z * x⁻¹) * g⁻¹ := by rw [e1]
      _ = (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
      _ = z * (z * x⁻¹)⁻¹ := by rw [hgz, e1]
      _ = z * x * z⁻¹ := by group
      _ = x := hzx
  have hc' : x⁻¹ * (g * g)⁻¹ = (g * g)⁻¹ * x⁻¹ := by
    have : (g * g) * x = x * (g * g) := by
      calc (g * g) * x = (g * g) * x * (g * g)⁻¹ * (g * g) := by group
        _ = x * (g * g) := by rw [hgg]
    rw [← mul_inv_rev, ← mul_inv_rev, this]
  calc g * (x * g * x⁻¹ * g⁻¹) * g⁻¹ = g * x * g * (x⁻¹ * (g * g)⁻¹) := by group
    _ = g * x * g * ((g * g)⁻¹ * x⁻¹) := by rw [hc']
    _ = (x * g * x⁻¹ * g⁻¹)⁻¹ := by group

end BlockInvThree

theorem InvThree.of_map_center {Y : Type*} [Group Y] {P : Subgroup Y}
    (h : InvThree (P.map (QuotientGroup.mk' (Subgroup.center Y)))) : InvThree P := by
  set q := QuotientGroup.mk' (Subgroup.center Y)
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨g, hg, rfl⟩, h3, hinv⟩ := h
  have hz : g * x * g⁻¹ * x ∈ Subgroup.center Y := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center Y), MonoidHom.mem_ker]
    change q (g * x * g⁻¹ * x) = 1
    rw [map_mul, map_mul, map_mul, map_inv, hinv, inv_mul_cancel]
  set b := x * g * x⁻¹ * g⁻¹
  have hb : g * b * g⁻¹ = b⁻¹ := conj_comm_eq_inv_of_mem_center hz
  have hbP : b ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hx hg) (P.inv_mem hx)) (P.inv_mem hg)
  have hqb : q b = q x ^ 2 := by
    have : q g * (q x)⁻¹ * (q g)⁻¹ = q x := by
      rw [← inv_inj, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, ← mul_assoc, hinv]
    calc q b = q x * (q g * (q x)⁻¹ * (q g)⁻¹) := by simp only [b, map_mul, map_inv]; group
      _ = q x ^ 2 := by rw [this, sq]
  have hob : orderOf (q b) = 3 := by
    rw [hqb, orderOf_pow' _ two_ne_zero, h3]
    norm_num
  have h3b : 3 ∣ orderOf b := hob ▸ orderOf_map_dvd q b
  have hb3 : b ^ 3 ∈ Subgroup.center Y := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center Y), MonoidHom.mem_ker]
    change q (b ^ 3) = 1
    rw [map_pow, ← hob, pow_orderOf_eq_one]
  have hb6 : b ^ 6 = 1 := by
    have e1 : g * b ^ 3 * g⁻¹ = (b ^ 3)⁻¹ := by rw [← conj_pow, hb, inv_pow]
    have e2 : g * b ^ 3 * g⁻¹ = b ^ 3 := by
      rw [(Subgroup.mem_center_iff.mp hb3 g)]; group
    have : b ^ 3 = (b ^ 3)⁻¹ := e2.symm.trans e1
    calc b ^ 6 = b ^ 3 * b ^ 3 := by rw [← pow_add]
      _ = (b ^ 3)⁻¹ * b ^ 3 := by rw [← this]
      _ = 1 := inv_mul_cancel _
  have h6 : orderOf b ∣ 6 := orderOf_dvd_of_pow_eq_one hb6
  have hob' : orderOf b = 3 ∨ orderOf b = 6 := by
    have h6' : orderOf b ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨h6, by norm_num⟩
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at h6'
    simp only [Finset.mem_insert, Finset.mem_singleton] at h6'
    rcases h6' with h | h | h | h <;> rw [h] at h3b ⊢ <;> omega
  refine ⟨b ^ 4, P.pow_mem hbP 4, g, hg, ?_, ?_⟩
  · rw [orderOf_pow' _ (by norm_num)]
    rcases hob' with h | h <;> rw [h] <;> norm_num
  · rw [← conj_pow, hb, inv_pow]

namespace BlockInvThree

variable {G : Type} [Group G]

theorem exists_inverted_of_invThree {M S L : Subgroup G}
    (h : InvThree (barM M (Subgroup.normalizer (S : Set G) ⊓ L))) :
    ∃ a ∈ Subgroup.normalizer (S : Set G) ⊓ L, ∃ g ∈ Subgroup.normalizer (S : Set G) ⊓ L,
      orderOf a = 3 ∧ g * a * g⁻¹ * a ∈ pCoreOf 2 M := by
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨_, ⟨a₀, ha₀, rfl⟩, _, ⟨g₀, hg₀, rfl⟩, h3, hinv⟩ := h
  have ha₀' := Subgroup.mem_subgroupOf.mp ha₀
  have hg₀' := Subgroup.mem_subgroupOf.mp hg₀
  have hQ : IsPGroup 2 (pCoreOf 2 M) := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have ha3 : (a₀ : G) ^ 3 ∈ pCoreOf 2 M := by
    have : q (a₀ ^ 3) = 1 := by rw [map_pow, ← h3, pow_orderOf_eq_one]
    simpa using (mk_pCore_two_eq_one_iff (a₀ ^ 3)).mp this
  have ha : (a₀ : G) ∉ pCoreOf 2 M := by
    intro hm
    have : q a₀ = 1 := (mk_pCore_two_eq_one_iff a₀).mpr hm
    rw [this, orderOf_one] at h3
    omega
  obtain ⟨k, hk⟩ := exists_two_pow_orderOf_three hQ ha3 ha
  refine ⟨(a₀ : G) ^ 2 ^ k, Subgroup.pow_mem _ ha₀' _, g₀, hg₀', hk, ?_⟩
  have : q (g₀ * a₀ ^ 2 ^ k * g₀⁻¹ * a₀ ^ 2 ^ k) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_pow, ← conj_pow, hinv, inv_pow, inv_mul_cancel]
  simpa using (mk_pCore_two_eq_one_iff _).mp this

end BlockInvThree

end CFSG.AGLEmbedding
