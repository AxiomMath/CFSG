module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.EightQuaternionCandidates
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import CFSG.Adapters.FrobeniusKernel

public section

namespace CFSG.Semidihedral.GL2Recognition

open Matrix MulAction
open scoped Pointwise

namespace SharpFourM11

section Sharp

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def SharplyFourTransitive (G Ω : Type*) [Group G] [MulAction G Ω] : Prop :=
  ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b → ∃! g : G, ∀ i, g • a i = b i

theorem injective_vec4 {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem SharplyFourTransitive.eq_one (h : SharplyFourTransitive G Ω) {g : G} {a : Fin 4 → Ω}
    (ha : Function.Injective a) (hg : ∀ i, g • a i = a i) : g = 1 :=
  (h a a ha ha).unique hg fun i => one_smul G (a i)

theorem SharplyFourTransitive.eq_one_of_fix (h : SharplyFourTransitive G Ω) {g : G}
    {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (ha : g • a = a) (hb : g • b = b) (hc : g • c = c) (hd : g • d = d) : g = 1 :=
  h.eq_one (injective_vec4 hab hac had hbc hbd hcd) fun i => by fin_cases i <;> assumption

theorem SharplyFourTransitive.existsUnique_vec4 (h : SharplyFourTransitive G Ω)
    {a b c d a' b' c' d' : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (hab' : a' ≠ b') (hac' : a' ≠ c') (had' : a' ≠ d')
    (hbc' : b' ≠ c') (hbd' : b' ≠ d') (hcd' : c' ≠ d') :
    ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' ∧ g • d = d' := by
  obtain ⟨g, hg, huniq⟩ := h _ _ (injective_vec4 hab hac had hbc hbd hcd)
    (injective_vec4 hab' hac' had' hbc' hbd' hcd')
  refine ⟨g, ⟨hg 0, hg 1, hg 2, hg 3⟩, fun g' hg' => huniq g' fun i => ?_⟩
  fin_cases i
  exacts [hg'.1, hg'.2.1, hg'.2.2.1, hg'.2.2.2]

theorem exists_notMem [Finite Ω] (s : Finset Ω) (hs : s.card < Nat.card Ω) : ∃ ω, ω ∉ s := by
  classical
  let := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ] at hs
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  exact ⟨ω, hω⟩

theorem SharplyFourTransitive.exists_triple [Finite Ω] (h : SharplyFourTransitive G Ω)
    (hΩ : 7 ≤ Nat.card Ω) {a b c a' b' c' : Ω} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') :
    ∃ g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  classical
  obtain ⟨d, hd⟩ := exists_notMem {a, b, c} ((Finset.card_le_three).trans_lt (by omega))
  obtain ⟨d', hd'⟩ := exists_notMem {a', b', c'} ((Finset.card_le_three).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd hd'
  obtain ⟨g, ⟨h1, h2, h3, -⟩, -⟩ := h.existsUnique_vec4 hab hac (Ne.symm hd.1) hbc
    (Ne.symm hd.2.1) (Ne.symm hd.2.2) hab' hac' (Ne.symm hd'.1) hbc' (Ne.symm hd'.2.1)
    (Ne.symm hd'.2.2)
  exact ⟨g, h1, h2, h3⟩

theorem SharplyFourTransitive.card_eq [Finite Ω] (h : SharplyFourTransitive G Ω)
    (hΩ : 4 ≤ Nat.card Ω) : Nat.card G = (Nat.card Ω).descFactorial 4 := by
  classical
  let := Fintype.ofFinite Ω
  obtain ⟨e₀⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := Ω)
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hΩ)
  let F : G → (Fin 4 ↪ Ω) := fun g => ⟨fun i => g • e₀ i, (MulAction.injective g).comp e₀.injective⟩
  have hF : Function.Bijective F := by
    refine ⟨fun g g' hgg' => ?_, fun b => ?_⟩
    · have hi : ∀ i, g • e₀ i = g' • e₀ i := fun i => DFunLike.congr_fun hgg' i
      exact (h e₀ (F g) e₀.injective (F g).injective).unique (fun i => rfl) fun i => (hi i).symm
    · obtain ⟨g, hg, -⟩ := h e₀ b e₀.injective b.injective
      exact ⟨g, Function.Embedding.ext hg⟩
  rw [Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_embedding_eq,
    Fintype.card_fin, Nat.card_eq_fintype_card]

end Sharp

section Stabilizers

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

abbrev stab2 (G : Type*) [Group G] [MulAction G Ω] (x y : Ω) : Subgroup G :=
  stabilizer G x ⊓ stabilizer G y

abbrev stab3 (G : Type*) [Group G] [MulAction G Ω] (x y z : Ω) : Subgroup G :=
  stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z

theorem mem_stab2 {x y : Ω} {g : G} : g ∈ stab2 G x y ↔ g • x = x ∧ g • y = y := by
  simp [Subgroup.mem_inf, mem_stabilizer_iff]

theorem mem_stab3 {x y z : Ω} {g : G} :
    g ∈ stab3 G x y z ↔ g • x = x ∧ g • y = y ∧ g • z = z := by
  simp [Subgroup.mem_inf, mem_stabilizer_iff, and_assoc]

theorem stab3_le_stab2 (x y z : Ω) : stab3 G x y z ≤ stab2 G x y := inf_le_left

theorem ncard_ne_ne [Finite Ω] {x y : Ω} (hxy : x ≠ y) :
    {ω | ω ≠ x ∧ ω ≠ y}.ncard = Nat.card Ω - 2 := by
  classical
  let := Fintype.ofFinite Ω
  rw [Set.ncard_eq_toFinset_card', Nat.card_eq_fintype_card]
  have hset : {ω | ω ≠ x ∧ ω ≠ y}.toFinset = (Finset.univ.erase x).erase y := by
    ext ω
    simp [and_comm]
  rw [hset, Finset.card_erase_of_mem (by simp [hxy.symm]), Finset.card_erase_of_mem (by simp),
    Finset.card_univ]
  omega

end Stabilizers

section Kernel

variable {G : Type} {Ω : Type*} [Group G] [MulAction G Ω]

theorem exists_kernel [Finite G] [Finite Ω] (h : SharplyFourTransitive G Ω)
    (hΩ : Nat.card Ω = 11) {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hP : stab3 G x y z ≠ ⊥) :
    ∃ L : Subgroup G, L ≤ stab2 G x y ∧ (∀ l ∈ L, l • z = z → l = 1) ∧ Nat.card L = 9 ∧
      ∀ p ∈ stab3 G x y z, ∀ l ∈ L, p * l * p⁻¹ ∈ L := by
  classical
  have hPH : stab3 G x y z ≤ stab2 G x y := stab3_le_stab2 x y z
  have memP' : ∀ g : stab2 G x y, g ∈ (stab3 G x y z).subgroupOf (stab2 G x y) ↔
      (g : G) • z = z := fun g => by
    rw [Subgroup.mem_subgroupOf, mem_stab3]
    have hg := mem_stab2.1 g.2
    exact ⟨fun hg' => hg'.2.2, fun hz => ⟨hg.1, hg.2, hz⟩⟩
  have hP'bot : (stab3 G x y z).subgroupOf (stab2 G x y) ≠ ⊥ := by
    obtain ⟨p, hp1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP
    refine Subgroup.ne_bot_iff_exists_ne_one.2
      ⟨⟨⟨p, hPH p.2⟩, Subgroup.mem_subgroupOf.2 p.2⟩, fun h1 => hp1 ?_⟩
    have := congrArg (fun q => ((q : stab2 G x y) : G)) (congrArg Subtype.val h1)
    exact Subtype.ext this
  obtain ⟨u, hu⟩ := exists_notMem {x, y, z} ((Finset.card_le_three).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨g₀, hg₀x, hg₀y, hg₀z⟩ := h.exists_triple (by omega) hxy hxz hyz hxy (Ne.symm hu.1)
    (Ne.symm hu.2.1)
  have hP'top : (stab3 G x y z).subgroupOf (stab2 G x y) ≠ ⊤ := by
    intro htop
    have hmem : (⟨g₀, mem_stab2.2 ⟨hg₀x, hg₀y⟩⟩ : stab2 G x y) ∈
        (stab3 G x y z).subgroupOf (stab2 G x y) := htop ▸ Subgroup.mem_top _
    exact hu.2.2 (hg₀z.symm.trans ((memP' _).1 hmem))
  have hfrob : ∀ g : stab2 G x y, g ∉ (stab3 G x y z).subgroupOf (stab2 G x y) →
      (stab3 G x y z).subgroupOf (stab2 G x y) ⊓
        (MulAut.conj g • (stab3 G x y z).subgroupOf (stab2 G x y)) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hq1, hq2⟩ := hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv] at hq2
    rw [memP'] at hq1 hq2
    have hgz : (g : G) • z ≠ z := fun hz => hg ((memP' g).2 hz)
    have hgx := (mem_stab2.1 g.2).1
    have hgy := (mem_stab2.1 g.2).2
    have hqx := (mem_stab2.1 q.2).1
    have hqy := (mem_stab2.1 q.2).2
    have hq' : (q : G) • ((g : G) • z) = (g : G) • z := by
      have h2 : (g : G)⁻¹ • (q : G) • (g : G) • z = z := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul] using hq2
      calc (q : G) • ((g : G) • z) = (g : G) • ((g : G)⁻¹ • (q : G) • (g : G) • z) := by
            rw [smul_inv_smul]
        _ = (g : G) • z := by rw [h2]
    have hgzx : (g : G) • z ≠ x := fun hzx => hxz (smul_left_cancel _ (hgx.trans hzx.symm))
    have hgzy : (g : G) • z ≠ y := fun hzy => hyz (smul_left_cancel _ (hgy.trans hzy.symm))
    have h1 : (q : G) = 1 := h.eq_one_of_fix hxy hxz (Ne.symm hgzx) hyz (Ne.symm hgzy)
      (Ne.symm hgz) hqx hqy hq1 hq'
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  obtain ⟨K, -, hKn, -, hKP, hKcard⟩ :=
    CFSG.Adapters.frobenius_kernel _ hP'bot hP'top hfrob
  have hstab : (stab3 G x y z).subgroupOf (stab2 G x y) =
      MulAction.stabilizer (stab2 G x y) z := by
    ext g
    rw [memP', mem_stabilizer_iff, Subgroup.smul_def]
  have horbit : MulAction.orbit (stab2 G x y) z = {ω | ω ≠ x ∧ ω ≠ y} := by
    ext ω
    constructor
    · rintro ⟨g, rfl⟩
      have hg := mem_stab2.1 g.2
      show g • z ≠ x ∧ g • z ≠ y
      rw [Subgroup.smul_def]
      exact ⟨fun hzx => hxz (smul_left_cancel _ (hg.1.trans hzx.symm)),
        fun hzy => hyz (smul_left_cancel _ (hg.2.trans hzy.symm))⟩
    · rintro ⟨hωx, hωy⟩
      obtain ⟨g, hgx, hgy, hgz⟩ := h.exists_triple (by omega) hxy hxz hyz hxy (Ne.symm hωx)
        (Ne.symm hωy)
      exact ⟨⟨g, mem_stab2.2 ⟨hgx, hgy⟩⟩, hgz⟩
  have hindex : ((stab3 G x y z).subgroupOf (stab2 G x y)).index = 9 := by
    rw [hstab, index_stabilizer, horbit, ncard_ne_ne hxy, hΩ]
  refine ⟨K.map (stab2 G x y).subtype, Subgroup.map_subtype_le K, ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩ hkz
    have hk' : k ∈ K ⊓ (stab3 G x y z).subgroupOf (stab2 G x y) := ⟨hk, (memP' k).2 hkz⟩
    rw [hKP, Subgroup.mem_bot] at hk'
    rw [hk', map_one]
  · rw [Subgroup.card_map_of_injective (stab2 G x y).subtype_injective, hKcard, hindex]
  · rintro p hp _ ⟨k, hk, rfl⟩
    exact ⟨⟨p, hPH hp⟩ * k * ⟨p, hPH hp⟩⁻¹, hKn.conj_mem k hk _, rfl⟩

end Kernel

section Regular

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

theorem smul_ne_of_mem_stab2 {x y z : Ω} (hxz : x ≠ z) (hyz : y ≠ z) {g : G}
    (hg : g ∈ stab2 G x y) : g • z ≠ x ∧ g • z ≠ y := by
  obtain ⟨hgx, hgy⟩ := mem_stab2.1 hg
  refine ⟨fun hzx => hxz ?_, fun hzy => hyz ?_⟩
  · rw [← hgx] at hzx
    exact (smul_left_cancel _ hzx).symm
  · rw [← hgy] at hzy
    exact (smul_left_cancel _ hzy).symm

theorem exists_mem_smul_eq [Finite Ω] (hΩ : Nat.card Ω = 11) {L : Subgroup G} {x y z : Ω}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hLH : L ≤ stab2 G x y)
    (hfree : ∀ l ∈ L, l • z = z → l = 1) (hL9 : Nat.card L = 9) :
    ∀ ω, ω ≠ x → ω ≠ y → ∃ l ∈ L, l • z = ω := by
  classical
  let F : L → {ω : Ω | ω ≠ x ∧ ω ≠ y} := fun l =>
    ⟨(l : G) • z, smul_ne_of_mem_stab2 hxz hyz (hLH l.2)⟩
  have hFinj : Function.Injective F := fun l l' hll' => by
    have h1 : ((l' : G)⁻¹ * l) • z = z := by
      rw [mul_smul, inv_smul_eq_iff]
      exact (congrArg Subtype.val hll' :)
    have h2 := hfree _ (L.mul_mem (L.inv_mem l'.2) l.2) h1
    exact Subtype.ext (inv_mul_eq_one.1 h2).symm
  have hcard : Nat.card L = Nat.card {ω : Ω | ω ≠ x ∧ ω ≠ y} := by
    rw [hL9, Nat.card_coe_set_eq, ncard_ne_ne hxy, hΩ]
  have hFbij := (Nat.bijective_iff_injective_and_card F).2 ⟨hFinj, hcard⟩
  intro ω hωx hωy
  obtain ⟨l, hl⟩ := hFbij.2 ⟨ω, hωx, hωy⟩
  exact ⟨l, l.2, congrArg Subtype.val hl⟩

theorem eq_one_of_commute [FaithfulSMul G Ω] {L : Subgroup G} {x y z : Ω}
    (htrans : ∀ ω, ω ≠ x → ω ≠ y → ∃ l ∈ L, l • z = ω) {c : G} (hc : c ∈ stab3 G x y z)
    (hcomm : ∀ l ∈ L, c * l = l * c) : c = 1 := by
  obtain ⟨hcx, hcy, hcz⟩ := mem_stab3.1 hc
  refine eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  rw [one_smul]
  by_cases hωx : ω = x
  · rw [hωx, hcx]
  by_cases hωy : ω = y
  · rw [hωy, hcy]
  obtain ⟨l, hl, rfl⟩ := htrans ω hωx hωy
  rw [← mul_smul, hcomm l hl, mul_smul, hcz]

theorem commute_of_conj_mem_zpowers {l₀ p q : G} (hp : p * l₀ * p⁻¹ ∈ Subgroup.zpowers l₀)
    (hq : q * l₀ * q⁻¹ ∈ Subgroup.zpowers l₀) :
    (q * p)⁻¹ * (p * q) * l₀ = l₀ * ((q * p)⁻¹ * (p * q)) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hp
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hq
  have h1 : (p * q) * l₀ * (p * q)⁻¹ = l₀ ^ (m * n) := by
    calc (p * q) * l₀ * (p * q)⁻¹ = p * (q * l₀ * q⁻¹) * p⁻¹ := by group
      _ = (p * l₀ * p⁻¹) ^ n := by rw [← hn, conj_zpow]
      _ = l₀ ^ (m * n) := by rw [← hm, _root_.zpow_mul]
  have h2 : (q * p) * l₀ * (q * p)⁻¹ = l₀ ^ (n * m) := by
    calc (q * p) * l₀ * (q * p)⁻¹ = q * (p * l₀ * p⁻¹) * q⁻¹ := by group
      _ = (q * l₀ * q⁻¹) ^ m := by rw [← hm, conj_zpow]
      _ = l₀ ^ (n * m) := by rw [← hn, _root_.zpow_mul]
  have h3 : (p * q) * l₀ * (p * q)⁻¹ = (q * p) * l₀ * (q * p)⁻¹ := by rw [h1, h2, mul_comm]
  calc (q * p)⁻¹ * (p * q) * l₀ = (q * p)⁻¹ * ((p * q) * l₀ * (p * q)⁻¹) * (p * q) := by group
    _ = (q * p)⁻¹ * ((q * p) * l₀ * (q * p)⁻¹) * (p * q) := by rw [h3]
    _ = l₀ * ((q * p)⁻¹ * (p * q)) := by group

theorem commute_of_card_nine {L : Subgroup G} (hL9 : Nat.card L = 9) :
    ∀ l ∈ L, ∀ m ∈ L, l * m = m * l := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := L)
    (by rw [hL9]; norm_num)
  intro l hl m hm
  exact congrArg Subtype.val (hc.is_comm.comm ⟨l, hl⟩ ⟨m, hm⟩)

theorem pow_three_eq_one [FaithfulSMul G Ω] {L : Subgroup G} {x y z : Ω}
    (hL9 : Nat.card L = 9) (htrans : ∀ ω, ω ≠ x → ω ≠ y → ∃ l ∈ L, l • z = ω)
    (hnorm : ∀ p ∈ stab3 G x y z, ∀ l ∈ L, p * l * p⁻¹ ∈ L)
    (hnc : ∃ p ∈ stab3 G x y z, ∃ q ∈ stab3 G x y z, p * q ≠ q * p) :
    ∀ l ∈ L, l ^ 3 = 1 := by
  have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL9]; norm_num)
  intro l hl
  have hdvd : orderOf l ∣ 9 := by
    have := orderOf_dvd_natCard (⟨l, hl⟩ : L)
    rwa [Subgroup.orderOf_mk, hL9] at this
  have h9 : orderOf l ≠ 9 := by
    intro h9
    have hz : Subgroup.zpowers l = L := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.2 hl) (by rw [Nat.card_zpowers, h9, hL9])
    obtain ⟨p, hp, q, hq, hpq⟩ := hnc
    have hc := commute_of_conj_mem_zpowers (hz ▸ hnorm p hp l hl) (hz ▸ hnorm q hq l hl)
    have hcmem : (q * p)⁻¹ * (p * q) ∈ stab3 G x y z :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hq hp))
        (Subgroup.mul_mem _ hp hq)
    have hcL : ∀ m ∈ L, (q * p)⁻¹ * (p * q) * m = m * ((q * p)⁻¹ * (p * q)) := by
      intro m hm
      rw [← hz] at hm
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
      exact Commute.zpow_right hc k
    have h1 := eq_one_of_commute htrans hcmem hcL
    rw [inv_mul_eq_one] at h1
    exact hpq h1.symm
  have h3 : orderOf l ∣ 3 := by
    have hmem : orderOf l ∈ Nat.divisors 9 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h
    · rw [h]; exact one_dvd 3
    · rw [h]
    · exact absurd h h9
  exact orderOf_dvd_iff_pow_eq_one.1 h3

end Regular

section Coordinates

variable {G : Type*} [Group G]

@[expose] def coordElem (l₁ l₂ : G) (v : Fin 2 → ZMod 3) : G := l₁ ^ (v 0).val * l₂ ^ (v 1).val

theorem pow_val_add {l : G} (hl : l ^ 3 = 1) (a b : ZMod 3) :
    l ^ (a + b).val = l ^ a.val * l ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hl, pow_add]

theorem pow_val_mul {l : G} (hl : l ^ 3 = 1) (a b : ZMod 3) :
    l ^ (a * b).val = (l ^ b.val) ^ a.val := by
  rw [ZMod.val_mul, ← pow_eq_pow_mod _ hl, mul_comm, pow_mul]

variable {l₁ l₂ : G}

theorem coordElem_add (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1) (hc : Commute l₁ l₂)
    (v w : Fin 2 → ZMod 3) :
    coordElem l₁ l₂ (v + w) = coordElem l₁ l₂ v * coordElem l₁ l₂ w := by
  simp only [coordElem, Pi.add_apply, pow_val_add h₁, pow_val_add h₂]
  exact (hc.pow_pow _ _).mul_mul_mul_comm _ _

theorem coordElem_smul (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1) (hc : Commute l₁ l₂) (a : ZMod 3)
    (v : Fin 2 → ZMod 3) : coordElem l₁ l₂ (a • v) = coordElem l₁ l₂ v ^ a.val := by
  simp only [coordElem, Pi.smul_apply, smul_eq_mul, pow_val_mul h₁, pow_val_mul h₂]
  exact ((hc.pow_pow _ _).mul_pow _).symm

theorem coordElem_zero : coordElem l₁ l₂ 0 = 1 := by
  simp [coordElem]

theorem coordElem_e₁ : coordElem l₁ l₂ ![1, 0] = l₁ := by
  simp [coordElem, ZMod.val_one]

theorem coordElem_e₂ : coordElem l₁ l₂ ![0, 1] = l₂ := by
  simp [coordElem, ZMod.val_one]

theorem eq_zero_of_coordElem_eq_one (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1) (hl₁ : l₁ ≠ 1)
    (hl₂ : l₂ ∉ Subgroup.zpowers l₁) {v : Fin 2 → ZMod 3} (hv : coordElem l₁ l₂ v = 1) :
    v = 0 := by
  have key : ∀ a b : ℕ, a < 3 → b < 3 → l₁ ^ a * l₂ ^ b = 1 → a = 0 ∧ b = 0 := by
    intro a b ha hb hab
    have hb' : l₂ ^ b ∈ Subgroup.zpowers l₁ := by
      rw [eq_inv_of_mul_eq_one_right hab]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers l₁) a)
    interval_cases b
    · rw [pow_zero, mul_one] at hab
      interval_cases a
      · exact ⟨rfl, rfl⟩
      · exact absurd (by simpa using hab) hl₁
      · refine absurd ?_ hl₁
        have h3 := h₁
        rw [pow_succ, hab, one_mul] at h3
        exact h3
    · exact absurd (by simpa using hb') hl₂
    · refine absurd ?_ hl₂
      have h4 : l₂ = (l₂ ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h₂, one_mul]
      rw [h4]
      exact Subgroup.pow_mem _ hb' 2
  obtain ⟨h0, h1⟩ := key _ _ (v 0).val_lt (v 1).val_lt hv
  funext i
  fin_cases i
  · exact (ZMod.val_eq_zero _).1 h0
  · exact (ZMod.val_eq_zero _).1 h1

theorem coordElem_injective (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1) (hc : Commute l₁ l₂)
    (hl₁ : l₁ ≠ 1) (hl₂ : l₂ ∉ Subgroup.zpowers l₁) : Function.Injective (coordElem l₁ l₂) := by
  intro v w hvw
  have hsplit := coordElem_add h₁ h₂ hc (v - w) w
  rw [sub_add_cancel, hvw] at hsplit
  exact sub_eq_zero.1 (eq_zero_of_coordElem_eq_one h₁ h₂ hl₁ hl₂ (mul_eq_right.1 hsplit.symm))

@[expose] def colMatrix (u₁ u₂ : Fin 2 → ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  Matrix.of fun i j => ![u₁, u₂] j i

theorem colMatrix_mulVec (u₁ u₂ v : Fin 2 → ZMod 3) :
    colMatrix u₁ u₂ *ᵥ v = v 0 • u₁ + v 1 • u₂ := by
  ext i
  simp [colMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

theorem conj_coordElem (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1) (hc : Commute l₁ l₂) {p : G}
    {u₁ u₂ : Fin 2 → ZMod 3} (hu₁ : p * l₁ * p⁻¹ = coordElem l₁ l₂ u₁)
    (hu₂ : p * l₂ * p⁻¹ = coordElem l₁ l₂ u₂) (v : Fin 2 → ZMod 3) :
    p * coordElem l₁ l₂ v * p⁻¹ = coordElem l₁ l₂ (colMatrix u₁ u₂ *ᵥ v) := by
  rw [colMatrix_mulVec, coordElem_add h₁ h₂ hc, coordElem_smul h₁ h₂ hc,
    coordElem_smul h₁ h₂ hc, ← hu₁, ← hu₂, conj_pow, conj_pow]
  simp only [coordElem]
  group

theorem exists_matrixRep {P L : Subgroup G} (h₁ : l₁ ^ 3 = 1) (h₂ : l₂ ^ 3 = 1)
    (hc : Commute l₁ l₂) (hl₁ : l₁ ≠ 1) (hl₂ : l₂ ∉ Subgroup.zpowers l₁) (hl₁L : l₁ ∈ L)
    (hl₂L : l₂ ∈ L) (hsurj : ∀ l ∈ L, ∃ v, coordElem l₁ l₂ v = l)
    (hnorm : ∀ p ∈ P, ∀ l ∈ L, p * l * p⁻¹ ∈ L)
    (hcent : ∀ p ∈ P, (∀ l ∈ L, p * l = l * p) → p = 1) :
    ∃ A : P →* GL (Fin 2) (ZMod 3), Function.Injective A ∧
      ∀ (p : P) (v : Fin 2 → ZMod 3), (p : G) * coordElem l₁ l₂ v * (p : G)⁻¹ =
        coordElem l₁ l₂ ((A p : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) := by
  have hu : ∀ p : P, ∃ u₁ u₂ : Fin 2 → ZMod 3, (p : G) * l₁ * (p : G)⁻¹ = coordElem l₁ l₂ u₁ ∧
      (p : G) * l₂ * (p : G)⁻¹ = coordElem l₁ l₂ u₂ := fun p => by
    obtain ⟨u₁, hu₁⟩ := hsurj _ (hnorm p p.2 l₁ hl₁L)
    obtain ⟨u₂, hu₂⟩ := hsurj _ (hnorm p p.2 l₂ hl₂L)
    exact ⟨u₁, u₂, hu₁.symm, hu₂.symm⟩
  choose u₁ u₂ hu₁ hu₂ using hu
  have hA₀ : ∀ (p : P) v, (p : G) * coordElem l₁ l₂ v * (p : G)⁻¹ =
      coordElem l₁ l₂ (colMatrix (u₁ p) (u₂ p) *ᵥ v) := fun p v =>
    conj_coordElem h₁ h₂ hc (hu₁ p) (hu₂ p) v
  have hinj := coordElem_injective h₁ h₂ hc hl₁ hl₂
  have hext : ∀ M N : Matrix (Fin 2) (Fin 2) (ZMod 3), (∀ v, M *ᵥ v = N *ᵥ v) → M = N :=
    fun M N hMN => Matrix.toLin'.injective (LinearMap.ext fun v => by
      simp only [Matrix.toLin'_apply, hMN v])
  have hA₀one : colMatrix (u₁ 1) (u₂ 1) = 1 := hext _ _ fun v => hinj (by
    rw [← hA₀, one_mulVec]
    simp)
  have hA₀mul : ∀ p q : P, colMatrix (u₁ (p * q)) (u₂ (p * q)) =
      colMatrix (u₁ p) (u₂ p) * colMatrix (u₁ q) (u₂ q) := fun p q => hext _ _ fun v => hinj (by
    rw [← hA₀ (p * q) v, ← mulVec_mulVec, ← hA₀ p, ← hA₀ q]
    simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
    group)
  let A₁ : P →* Matrix (Fin 2) (Fin 2) (ZMod 3) :=
    { toFun := fun p => colMatrix (u₁ p) (u₂ p), map_one' := hA₀one, map_mul' := hA₀mul }
  refine ⟨A₁.toHomUnits, ?_, fun p v => hA₀ p v⟩
  rw [injective_iff_map_eq_one]
  intro p hp
  have hp' : colMatrix (u₁ p) (u₂ p) = 1 := by
    have := congrArg Units.val hp
    simpa [A₁] using this
  apply Subtype.ext
  refine hcent p p.2 fun l hl => ?_
  obtain ⟨v, rfl⟩ := hsurj l hl
  have hpv := hA₀ p v
  rw [hp', one_mulVec] at hpv
  calc (p : G) * coordElem l₁ l₂ v = ((p : G) * coordElem l₁ l₂ v * (p : G)⁻¹) * p := by group
    _ = coordElem l₁ l₂ v * p := by rw [hpv]

end Coordinates

section Quaternion

theorem sq_eq_neg_one_of_pow_four : ∀ a b c d : ZMod 3, !![a, b; c, d] ^ 4 = 1 →
    !![a, b; c, d] ^ 2 ≠ 1 → !![a, b; c, d] ^ 2 = -1 := by
  decide +kernel

theorem exists_qElem_of_sq_eq_neg_one : ∀ a b c d : ZMod 3, !![a, b; c, d] ^ 2 = -1 →
    ∃ i, (qElem i : Matrix (Fin 2) (Fin 2) (ZMod 3)) = !![a, b; c, d] := by
  decide +kernel

theorem mem_Q₀_of_pow_four {g : GL (Fin 2) (ZMod 3)} (h4 : g ^ 4 = 1) (h2 : g ^ 2 ≠ 1) :
    g ∈ Q₀ := by
  rw [mem_Q₀_iff]
  have hM := Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
  have h4' : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 4 = 1 := by
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
  have h2' : (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) ^ 2 ≠ 1 := fun h => h2 (Units.ext (by
    rw [Units.val_pow_eq_pow_val, h, Units.val_one]))
  rw [hM] at h4' h2'
  obtain ⟨i, hi⟩ :=
    exists_qElem_of_sq_eq_neg_one _ _ _ _ (sq_eq_neg_one_of_pow_four _ _ _ _ h4' h2')
  exact ⟨i, Units.ext (hi.trans hM.symm)⟩

theorem range_eq_Q₀ {P : Type*} [Group P] (A : P →* GL (Fin 2) (ZMod 3))
    (hA : Function.Injective A) (ψ : P ≃* QuaternionGroup 2) : A.range = Q₀ := by
  have hQ4 : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
  have hQ2 : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = QuaternionGroup.a 1 ^ 2 := by
    decide
  have ha1 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  have hord4 : ∀ p : P, ψ p ^ 2 ≠ 1 → A p ∈ Q₀ := fun p hp => by
    apply mem_Q₀_of_pow_four
    · rw [← map_pow, show p ^ 4 = 1 from ψ.injective (by rw [map_pow, hQ4, map_one]), map_one]
    · intro h2
      apply hp
      rw [← map_pow] at h2
      rw [← map_pow, hA (h2.trans (map_one A).symm), map_one]
  have hle : A.range ≤ Q₀ := by
    rintro _ ⟨p, rfl⟩
    by_cases hp : ψ p ^ 2 = 1
    · rcases hQ2 _ hp with h1 | h1
      · rw [show p = 1 from ψ.injective (by rw [h1, map_one]), map_one]
        exact Q₀.one_mem
      · have hp' : p = (ψ.symm (QuaternionGroup.a 1)) ^ 2 :=
          ψ.injective (by rw [h1, map_pow, MulEquiv.apply_symm_apply])
        rw [hp', map_pow]
        exact Q₀.pow_mem (hord4 _ (by rw [MulEquiv.apply_symm_apply]; exact ha1)) 2
    · exact hord4 p hp
  have hcard : Nat.card A.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hA).toEquiv, Nat.card_congr ψ.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Q₀, hcard])

end Quaternion

section Transport

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

@[expose] noncomputable def transportHom (f : Ω ≃ Fin 11) : G →* Equiv.Perm (Fin 11) :=
  (Equiv.permCongrHom f).toMonoidHom.comp (MulAction.toPermHom G Ω)

theorem transportHom_apply (f : Ω ≃ Fin 11) (g : G) (i : Fin 11) :
    transportHom f g i = f (g • f.symm i) := rfl

theorem transportHom_apply_apply (f : Ω ≃ Fin 11) (g : G) (ω : Ω) :
    transportHom f g (f ω) = f (g • ω) := by
  rw [transportHom_apply, Equiv.symm_apply_apply]

theorem transportHom_injective [FaithfulSMul G Ω] (f : Ω ≃ Fin 11) :
    Function.Injective (transportHom (G := G) f) := by
  intro g g' hgg'
  refine eq_of_smul_eq_smul (α := Ω) fun ω => f.injective ?_
  rw [← transportHom_apply_apply, ← transportHom_apply_apply, hgg']

theorem mem_range_transportHom_iff (f : Ω ≃ Fin 11) (p : Equiv.Perm (Fin 11)) :
    p ∈ (transportHom (G := G) f).range ↔ ∃ g : G, ∀ i, p i = f (g • f.symm i) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, fun i => rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Equiv.ext fun i => (hg i).symm⟩

theorem fin11_cases (i : Fin 11) : i = 9 ∨ i = 10 ∨ ∃ v, i = planePoint v := by
  by_cases hi : i.val < 9
  · exact Or.inr (Or.inr ⟨planeVector i, (planePoint_planeVector i hi).symm⟩)
  · have h : i.val = 9 ∨ i.val = 10 := by omega
    rcases h with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))

theorem planePoint_ne_nine (v : Fin 2 → ZMod 3) : planePoint v ≠ 9 := fun h => by
  have := planePoint_lt v
  rw [h] at this
  exact absurd this (by decide)

theorem planePoint_ne_ten (v : Fin 2 → ZMod 3) : planePoint v ≠ 10 := fun h => by
  have := planePoint_lt v
  rw [h] at this
  exact absurd this (by decide)

theorem transportHom_eq_affinePerm {f : Ω ≃ Fin 11} {x y : Ω} {ι : (Fin 2 → ZMod 3) → Ω}
    (hfx : f x = 9) (hfy : f y = 10) (hfι : ∀ v, f (ι v) = planePoint v) {g : G}
    {M : GL (Fin 2) (ZMod 3)} {t : Fin 2 → ZMod 3} (hgx : g • x = x) (hgy : g • y = y)
    (hgι : ∀ v, g • ι v = ι ((M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v + t)) :
    transportHom f g = affinePerm M t := by
  refine Equiv.ext fun i => ?_
  rcases fin11_cases i with rfl | rfl | ⟨v, rfl⟩
  · rw [← hfx, transportHom_apply_apply, hgx, hfx, affinePerm_of_le _ _ _ (by decide)]
  · rw [← hfy, transportHom_apply_apply, hgy, hfy, affinePerm_of_le _ _ _ (by decide)]
  · rw [← hfι, transportHom_apply_apply, hgι, hfι, hfι, affinePerm_planePoint]

theorem exists_coordEquiv [Finite Ω] (hΩ : Nat.card Ω = 11) {x y : Ω} (hxy : x ≠ y)
    {ι : (Fin 2 → ZMod 3) → Ω} (hι : Function.Injective ι) (hιx : ∀ v, ι v ≠ x)
    (hιy : ∀ v, ι v ≠ y) :
    ∃ f : Ω ≃ Fin 11, f x = 9 ∧ f y = 10 ∧ ∀ v, f (ι v) = planePoint v := by
  classical
  let g₀ : Fin 11 → Ω := fun i => if i = 9 then x else if i = 10 then y else ι (planeVector i)
  have hg9 : g₀ 9 = x := by simp [g₀]
  have hg10 : g₀ 10 = y := by simp [g₀]
  have hgv : ∀ v, g₀ (planePoint v) = ι v := fun v => by
    simp only [g₀, planePoint_ne_nine v, planePoint_ne_ten v, ite_false, planeVector_planePoint]
  have hinj : Function.Injective g₀ := by
    intro i j hij
    rcases fin11_cases i with rfl | rfl | ⟨v, rfl⟩ <;>
      rcases fin11_cases j with rfl | rfl | ⟨w, rfl⟩
    · rfl
    · rw [hg9, hg10] at hij
      exact absurd hij hxy
    · rw [hg9, hgv] at hij
      exact absurd hij.symm (hιx w)
    · rw [hg10, hg9] at hij
      exact absurd hij.symm hxy
    · rfl
    · rw [hg10, hgv] at hij
      exact absurd hij.symm (hιy w)
    · rw [hgv, hg9] at hij
      exact absurd hij (hιx v)
    · rw [hgv, hg10] at hij
      exact absurd hij (hιy v)
    · rw [hgv, hgv] at hij
      rw [hι hij]
  have hbij : Function.Bijective g₀ := (Nat.bijective_iff_injective_and_card g₀).2
    ⟨hinj, by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hΩ]⟩
  refine ⟨(Equiv.ofBijective g₀ hbij).symm, ?_, ?_, fun v => ?_⟩
  · exact (Equiv.symm_apply_eq _).2 hg9.symm
  · exact (Equiv.symm_apply_eq _).2 hg10.symm
  · exact (Equiv.symm_apply_eq _).2 (hgv v).symm

end Transport

section Affine

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

theorem eq_of_mem_zpowers_of_pow_three {l m : G} (hl : l ^ 3 = 1)
    (hm : m ∈ Subgroup.zpowers l) : m = 1 ∨ m = l ∨ m = l ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
  rw [zpow_eq_zpow_emod' k hl]
  obtain ⟨r, hr⟩ : ∃ r, k % ((3 : ℕ) : ℤ) = r := ⟨_, rfl⟩
  have h0 : 0 ≤ r := hr ▸ Int.emod_nonneg k (by norm_num)
  have h3 : r < 3 := hr ▸ Int.emod_lt_of_pos k (by norm_num)
  rw [hr]
  interval_cases r
  · exact Or.inl (zpow_zero l)
  · exact Or.inr (Or.inl (zpow_one l))
  · exact Or.inr (Or.inr ((zpow_two l).trans (pow_two l).symm))

theorem exists_affine [FaithfulSMul G Ω] [Finite Ω] (hΩ : Nat.card Ω = 11) {x y z : Ω}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {L : Subgroup G} (hLH : L ≤ stab2 G x y)
    (hfree : ∀ l ∈ L, l • z = z → l = 1) (hL9 : Nat.card L = 9)
    (hnorm : ∀ p ∈ stab3 G x y z, ∀ l ∈ L, p * l * p⁻¹ ∈ L)
    (ψ : stab3 G x y z ≃* QuaternionGroup 2) :
    ∃ (f₀ : Ω ≃ Fin 11) (ι : (Fin 2 → ZMod 3) → Ω) (l₁ l₂ : G)
      (A : stab3 G x y z →* GL (Fin 2) (ZMod 3)),
      f₀ x = 9 ∧ f₀ y = 10 ∧ (∀ v, f₀ (ι v) = planePoint v) ∧ ι 0 = z ∧
      l₁ ∈ stab2 G x y ∧ l₂ ∈ stab2 G x y ∧
      (∀ v, l₁ • ι v = ι (v + ![1, 0])) ∧ (∀ v, l₂ • ι v = ι (v + ![0, 1])) ∧
      Function.Injective A ∧ A.range = Q₀ ∧
      ∀ (p : stab3 G x y z) v,
        (p : G) • ι v = ι ((A p : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) := by
  classical
  have htrans := exists_mem_smul_eq hΩ hxy hxz hyz hLH hfree hL9
  have hcomm := commute_of_card_nine hL9
  have hnc : ∃ p ∈ stab3 G x y z, ∃ q ∈ stab3 G x y z, p * q ≠ q * p := by
    refine ⟨ψ.symm (QuaternionGroup.a 1), (ψ.symm _).2, ψ.symm (QuaternionGroup.xa 0),
      (ψ.symm _).2, fun hpq => ?_⟩
    have hpq' : ψ.symm (QuaternionGroup.a 1) * ψ.symm (QuaternionGroup.xa 0) =
        ψ.symm (QuaternionGroup.xa 0) * ψ.symm (QuaternionGroup.a 1) := Subtype.ext hpq
    have h2 := congrArg ψ hpq'
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide)
  have h3 := pow_three_eq_one hL9 htrans hnorm hnc
  obtain ⟨w, hw⟩ := exists_notMem {x, y, z} ((Finset.card_le_three).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨l₁, hl₁L, hl₁z⟩ := htrans w hw.1 hw.2.1
  obtain ⟨w', hw'⟩ := exists_notMem {x, y, z, w, l₁ • w}
    ((Finset.card_le_five).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw'
  obtain ⟨l₂, hl₂L, hl₂z⟩ := htrans w' hw'.1 hw'.2.1
  have hl₁1 : l₁ ≠ 1 := by
    rintro rfl
    rw [one_smul] at hl₁z
    exact hw.2.2 hl₁z.symm
  have hl₂ : l₂ ∉ Subgroup.zpowers l₁ := by
    intro hmem
    rcases eq_of_mem_zpowers_of_pow_three (h3 l₁ hl₁L) hmem with rfl | rfl | rfl
    · rw [one_smul] at hl₂z
      exact hw'.2.2.1 hl₂z.symm
    · exact hw'.2.2.2.1 (hl₂z.symm.trans hl₁z)
    · rw [pow_two, mul_smul, hl₁z] at hl₂z
      exact hw'.2.2.2.2 hl₂z.symm
  have hc : Commute l₁ l₂ := hcomm l₁ hl₁L l₂ hl₂L
  have hφL : ∀ v, coordElem l₁ l₂ v ∈ L := fun v =>
    L.mul_mem (L.pow_mem hl₁L _) (L.pow_mem hl₂L _)
  have hinj := coordElem_injective (h3 l₁ hl₁L) (h3 l₂ hl₂L) hc hl₁1 hl₂
  have hsurj : ∀ l ∈ L, ∃ v, coordElem l₁ l₂ v = l := by
    have : Finite L := Nat.finite_of_card_ne_zero (by rw [hL9]; norm_num)
    let F : (Fin 2 → ZMod 3) → L := fun v => ⟨coordElem l₁ l₂ v, hφL v⟩
    have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
      ⟨fun v w hvw => hinj (congrArg Subtype.val hvw), by
        rw [hL9, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
        norm_num⟩
    intro l hl
    obtain ⟨v, hv⟩ := hF.2 ⟨l, hl⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  obtain ⟨A, hA, hAconj⟩ := exists_matrixRep (P := stab3 G x y z) (h3 l₁ hl₁L) (h3 l₂ hl₂L) hc
    hl₁1 hl₂ hl₁L hl₂L hsurj hnorm fun p hp hpc => eq_one_of_commute htrans hp hpc
  let ι : (Fin 2 → ZMod 3) → Ω := fun v => coordElem l₁ l₂ v • z
  have hι : Function.Injective ι := fun v u hvu => by
    have h1 : (coordElem l₁ l₂ u)⁻¹ * coordElem l₁ l₂ v = 1 := hfree _
      (L.mul_mem (L.inv_mem (hφL u)) (hφL v)) (by
        rw [mul_smul, inv_smul_eq_iff]
        exact hvu)
    exact hinj (inv_mul_eq_one.1 h1).symm
  obtain ⟨f₀, hfx, hfy, hfι⟩ := exists_coordEquiv hΩ hxy hι
    (fun v => (smul_ne_of_mem_stab2 hxz hyz (hLH (hφL v))).1)
    (fun v => (smul_ne_of_mem_stab2 hxz hyz (hLH (hφL v))).2)
  have htransl : ∀ u, coordElem l₁ l₂ u ∈ L → ∀ v, coordElem l₁ l₂ u • ι v = ι (v + u) :=
    fun u _ v => by
      change coordElem l₁ l₂ u • coordElem l₁ l₂ v • z = coordElem l₁ l₂ (v + u) • z
      rw [← mul_smul, ← coordElem_add (h3 l₁ hl₁L) (h3 l₂ hl₂L) hc, add_comm]
  refine ⟨f₀, ι, l₁, l₂, A, hfx, hfy, hfι, ?_, hLH hl₁L, hLH hl₂L, fun v => ?_, fun v => ?_,
    hA, range_eq_Q₀ A hA ψ, fun p v => ?_⟩
  · change coordElem l₁ l₂ 0 • z = z
    rw [coordElem_zero, one_smul]
  · have := htransl ![1, 0] (hφL _) v
    rwa [coordElem_e₁] at this
  · have := htransl ![0, 1] (hφL _) v
    rwa [coordElem_e₂] at this
  · have hpz : (p : G) • z = z := (mem_stab3.1 p.2).2.2
    change (p : G) • coordElem l₁ l₂ v • z =
      coordElem l₁ l₂ ((A p : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v) • z
    rw [← hAconj p v, mul_smul, mul_smul, inv_smul_eq_iff.2 hpz.symm]

end Affine

section Candidate

variable {G : Type*} {Ω : Type*} [Group G] [MulAction G Ω]

theorem exists_candidate (h : SharplyFourTransitive G Ω) {x y z : Ω} {f₀ : Ω ≃ Fin 11}
    {ι : (Fin 2 → ZMod 3) → Ω} (hfx : f₀ x = 9) (hfy : f₀ y = 10)
    (hfι : ∀ v, f₀ (ι v) = planePoint v) (hz : ι 0 = z) {l₁ l₂ : G}
    (hl₁ : l₁ ∈ stab2 G x y) (hl₂ : l₂ ∈ stab2 G x y)
    (hl₁ι : ∀ v, l₁ • ι v = ι (v + ![1, 0])) (hl₂ι : ∀ v, l₂ • ι v = ι (v + ![0, 1]))
    {A : stab3 G x y z →* GL (Fin 2) (ZMod 3)} (hA : Function.Injective A) (hAr : A.range = Q₀)
    (hAι : ∀ (p : stab3 G x y z) v,
      (p : G) • ι v = ι ((A p : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ v)) :
    ∃ (α : MulAut Q₀) (σ : Equiv.Perm (Fin 11)), orderOf α = 3 ∧ IsCandidateSigma α σ ∧
      candidateGroup σ ≤ (transportHom (G := G) f₀).range := by
  classical
  have hfz : f₀ z = 0 := by
    rw [← hz, hfι]
    rfl
  have hfw : f₀ (ι vecE) = 1 := by
    rw [hfι]
    rfl
  have hne : ∀ {a b : Ω} {i j : Fin 11}, f₀ a = i → f₀ b = j → i ≠ j → a ≠ b :=
    fun ha hb hij hab => hij (by rw [← ha, ← hb, hab])
  have hxy : x ≠ y := hne hfx hfy (by decide)
  have hxz : x ≠ z := hne hfx hfz (by decide)
  have hxw : x ≠ ι vecE := hne hfx hfw (by decide)
  have hyz : y ≠ z := hne hfy hfz (by decide)
  have hyw : y ≠ ι vecE := hne hfy hfw (by decide)
  have hzw : z ≠ ι vecE := hne hfz hfw (by decide)
  obtain ⟨σ, ⟨hσx, hσy, hσz, hσw⟩, -⟩ := h.existsUnique_vec4 hxy hxz hxw hyz hyw hzw
    hyz hxy.symm hyw hxz.symm hzw hxw
  have hσix : σ⁻¹ • x = z := inv_smul_eq_iff.2 hσz.symm
  have hσiy : σ⁻¹ • y = x := inv_smul_eq_iff.2 hσx.symm
  have hσiz : σ⁻¹ • z = y := inv_smul_eq_iff.2 hσy.symm
  have hσiw : σ⁻¹ • ι vecE = ι vecE := inv_smul_eq_iff.2 hσw.symm
  have hconjP : ∀ p ∈ stab3 G x y z, σ * p * σ⁻¹ ∈ stab3 G x y z := fun p hp => by
    obtain ⟨hpx, hpy, hpz⟩ := mem_stab3.1 hp
    refine mem_stab3.2 ⟨?_, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hσix, hpz, hσz]
    · rw [mul_smul, mul_smul, hσiy, hpx, hσx]
    · rw [mul_smul, mul_smul, hσiz, hpy, hσy]
  have hconjP' : ∀ p ∈ stab3 G x y z, σ⁻¹ * p * σ ∈ stab3 G x y z := fun p hp => by
    obtain ⟨hpx, hpy, hpz⟩ := mem_stab3.1 hp
    refine mem_stab3.2 ⟨?_, ?_, ?_⟩
    · rw [mul_smul, mul_smul, hσx, hpy, hσiy]
    · rw [mul_smul, mul_smul, hσy, hpz, hσiz]
    · rw [mul_smul, mul_smul, hσz, hpx, hσix]
  have hσ3 : σ ^ 3 = 1 := by
    have hcube : ∀ ω : Ω, σ ^ 3 • ω = σ • σ • σ • ω := fun ω => by
      rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul]
    exact h.eq_one_of_fix hxy hxz hxw hyz hyw hzw
      (by rw [hcube, hσx, hσy, hσz]) (by rw [hcube, hσy, hσz, hσx])
      (by rw [hcube, hσz, hσx, hσy]) (by rw [hcube, hσw, hσw, hσw])
  let ασ : MulAut (stab3 G x y z) :=
    { toFun := fun p => ⟨σ * p * σ⁻¹, hconjP p p.2⟩
      invFun := fun p => ⟨σ⁻¹ * p * σ, hconjP' p p.2⟩
      left_inv := fun p => Subtype.ext (by group)
      right_inv := fun p => Subtype.ext (by group)
      map_mul' := fun p q => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hασ : ∀ p, ((ασ p : stab3 G x y z) : G) = σ * p * σ⁻¹ := fun p => rfl
  let A' : stab3 G x y z ≃* Q₀ := (MonoidHom.ofInjective hA).trans (MulEquiv.subgroupCongr hAr)
  have hA' : ∀ p, ((A' p : Q₀) : GL (Fin 2) (ZMod 3)) = A p := fun p => rfl
  let α : MulAut Q₀ := (A'.symm.trans ασ).trans A'
  have hα : ∀ q, α q = A' (ασ (A'.symm q)) := fun q => rfl
  have hσ' : IsCandidateSigma α (transportHom f₀ σ) := by
    refine ⟨?_, ?_, ?_, fun q => ?_⟩
    · rw [← hfx, transportHom_apply_apply, hσx, hfy]
    · rw [← hfy, transportHom_apply_apply, hσy, hfz]
    · rw [← hfz, transportHom_apply_apply, hσz, hfx]
    · obtain ⟨p, rfl⟩ := A'.surjective q
      rw [hα, MulEquiv.symm_apply_apply, hA', hA', ← hfι, ← hfι, ← hAι, ← hAι,
        transportHom_apply_apply, hασ, mul_smul, mul_smul, hσiw]
  have hα3 : α ^ 3 = 1 := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨p, rfl⟩ := A'.surjective q
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hα,
      MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [hασ, hασ, hασ]
    have h3' : σ * σ * σ = 1 := (pow_three' σ).symm.trans hσ3
    calc σ * (σ * (σ * (p : G) * σ⁻¹) * σ⁻¹) * σ⁻¹ = (σ * σ * σ) * p * (σ * σ * σ)⁻¹ := by
          group
      _ = p := by rw [h3', one_mul, inv_one, mul_one]
  have hα1 : α ≠ 1 := by
    intro h1
    have hσ1' : IsCandidateSigma 1 (transportHom f₀ σ) := h1 ▸ hσ'
    have hfix : ∀ j, σ • f₀.symm (ptTable j) = f₀.symm (ptTable j) := fun j => by
      have hj := sigma_ptTable_of_isCandidateSigma (f := id) (fun i => rfl) hσ1' j
      rw [transportHom_apply] at hj
      exact f₀.injective (by rw [hj, Equiv.apply_symm_apply]; rfl)
    have hd : ∀ i j : Fin 8, i ≠ j → f₀.symm (ptTable i) ≠ f₀.symm (ptTable j) := fun i j hij =>
      f₀.symm.injective.ne (by revert i j; decide)
    have hσ1 : σ = 1 := h.eq_one_of_fix (hd 0 1 (by decide)) (hd 0 2 (by decide))
      (hd 0 3 (by decide)) (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      (hfix 0) (hfix 1) (hfix 2) (hfix 3)
    rw [hσ1, one_smul] at hσx
    exact hxy hσx
  have hα3' : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  have hT1 : transportHom f₀ l₁ = genH₁ := transportHom_eq_affinePerm hfx hfy hfι
    (mem_stab2.1 hl₁).1 (mem_stab2.1 hl₁).2 fun v => by rw [hl₁ι, Units.val_one, one_mulVec]
  have hT2 : transportHom f₀ l₂ = genH₂ := transportHom_eq_affinePerm hfx hfy hfι
    (mem_stab2.1 hl₂).1 (mem_stab2.1 hl₂).2 fun v => by rw [hl₂ι, Units.val_one, one_mulVec]
  have hAp : ∀ (q : Q₀), A (A'.symm q) = q := fun q => by
    rw [← hA', MulEquiv.apply_symm_apply]
  have hT3 : transportHom f₀ (A'.symm ⟨I₀, I₀_mem_Q₀⟩ : G) = genH₃ :=
    transportHom_eq_affinePerm hfx hfy hfι (mem_stab3.1 (A'.symm _).2).1
      (mem_stab3.1 (A'.symm _).2).2.1 fun v => by rw [hAι, hAp, add_zero]
  have hT4 : transportHom f₀ (A'.symm ⟨J₀, J₀_mem_Q₀⟩ : G) = genH₄ :=
    transportHom_eq_affinePerm hfx hfy hfι (mem_stab3.1 (A'.symm _).2).1
      (mem_stab3.1 (A'.symm _).2).2.1 fun v => by rw [hAι, hAp, add_zero]
  refine ⟨α, transportHom f₀ σ, hα3', hσ', ?_⟩
  rw [candidateGroup, Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl | rfl | rfl)
  · exact ⟨l₁, hT1⟩
  · exact ⟨l₂, hT2⟩
  · exact ⟨_, hT3⟩
  · exact ⟨_, hT4⟩
  · exact ⟨σ, rfl⟩

theorem exists_transport_eq_M11
    [FaithfulSMul G Ω] (h : SharplyFourTransitive G Ω)
    (hG : Nat.card G = 7920) (f₀ : Ω ≃ Fin 11) {α : MulAut Q₀} (hα : orderOf α = 3)
    {σ : Equiv.Perm (Fin 11)} (hσ : IsCandidateSigma α σ)
    (hK : candidateGroup σ ≤ (transportHom (G := G) f₀).range) :
    ∃ f : Ω ≃ Fin 11, (transportHom (G := G) f).range = CFSG.Open.StatedM11 := by
  classical
  have hT := transportHom_injective (G := G) f₀
  have hcardT : Nat.card (transportHom (G := G) f₀).range = 7920 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hT).toEquiv, hG]
  rcases (eight_quaternion_candidates_force_M11 α hα).2 σ hσ with ⟨k, hkK, hk1, hk4⟩ | ⟨c, hc⟩
  · exfalso
    obtain ⟨g, rfl⟩ := hK hkK
    obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hk4
    let a : Fin 4 → Ω := fun i => f₀.symm (t.equivFin.symm (Fin.cast htcard.symm i))
    have ha : Function.Injective a := fun i j hij =>
      Fin.cast_injective _ (t.equivFin.symm.injective (Subtype.ext (f₀.symm.injective hij)))
    have hfix : ∀ i, g • a i = a i := fun i => by
      have hmem := ht (t.equivFin.symm (Fin.cast htcard.symm i)).2
      rw [Finset.mem_filter, transportHom_apply] at hmem
      exact f₀.injective (by rw [hmem.2, Equiv.apply_symm_apply])
    exact hk1 (by rw [h.eq_one ha hfix, map_one])
  · have hcardM : Nat.card ↥(MulAut.conj c • CFSG.Blueprint.NativeSporadic.M11 :
        Subgroup (Equiv.Perm (Fin 11))) = 7920 := by
      rw [← Nat.card_congr (Subgroup.equivSMul (MulAut.conj c) _).toEquiv, card_nativeM11]
    have heq : MulAut.conj c • CFSG.Blueprint.NativeSporadic.M11 =
        (transportHom (G := G) f₀).range :=
      Subgroup.eq_of_le_of_card_ge (hc.trans hK) (by rw [hcardT, hcardM])
    refine ⟨f₀.trans (Equiv.symm c), ?_⟩
    ext p
    rw [statedM11_eq_nativeM11, ← Subgroup.smul_mem_pointwise_smul_iff (a := MulAut.conj c)
      (S := CFSG.Blueprint.NativeSporadic.M11) (x := p), heq, MulAut.smul_def, MulAut.conj_apply]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨g, Equiv.ext fun i => ?_⟩
      simp [transportHom_apply, Equiv.Perm.inv_def]
    · rintro ⟨g, hg⟩
      refine ⟨g, Equiv.ext fun i => ?_⟩
      have hgi := DFunLike.congr_fun hg (c i)
      simp only [transportHom_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
        Equiv.symm_apply_apply] at hgi
      simp only [transportHom_apply, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
        hgi, Equiv.symm_apply_apply]

end Candidate

end SharpFourM11

open SharpFourM11 in
theorem sharply_four_transitive_quaternion_action_exact_M11
    {G : Type} {Ω : Type*} [Group G]
    [Finite G] [MulAction G Ω] [FaithfulSMul G Ω] (hΩ : Nat.card Ω = 11)
    (hsharp : ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : G, ∀ i, g • a i = b i)
    (hQ : ∃ x y z : Ω, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      Nonempty (↥(stabilizer G x ⊓ stabilizer G y ⊓ stabilizer G z) ≃* QuaternionGroup 2)) :
    ∃ f : Ω ≃ Fin 11,
      (∀ p : Equiv.Perm (Fin 11), p ∈ CFSG.Open.StatedM11 ↔
        ∃ g : G, ∀ i, p i = f (g • f.symm i)) ∧
      Nonempty (G ≃* CFSG.Open.StatedM11) := by
  have h : SharplyFourTransitive G Ω := hsharp
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  obtain ⟨x, y, z, hxy, hxz, hyz, ⟨ψ⟩⟩ := hQ
  have hG : Nat.card G = 7920 := by
    rw [h.card_eq (by omega), hΩ]
    decide
  have hP : stab3 G x y z ≠ ⊥ := by
    intro hbot
    have h8 : Nat.card (stab3 G x y z) = 8 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [hbot, Subgroup.card_bot] at h8
    omega
  obtain ⟨L, hLH, hfree, hL9, hnorm⟩ := exists_kernel h hΩ hxy hxz hyz hP
  obtain ⟨f₀, ι, l₁, l₂, A, hfx, hfy, hfι, hz, hl₁, hl₂, hl₁ι, hl₂ι, hA, hAr, hAι⟩ :=
    exists_affine hΩ hxy hxz hyz hLH hfree hL9 hnorm ψ
  obtain ⟨α, σ, hα, hσ, hK⟩ :=
    exists_candidate h hfx hfy hfι hz hl₁ hl₂ hl₁ι hl₂ι hA hAr hAι
  obtain ⟨f, hf⟩ := exists_transport_eq_M11 h hG f₀ hα hσ hK
  refine ⟨f, fun p => ?_,
    ⟨(MonoidHom.ofInjective (transportHom_injective f)).trans (MulEquiv.subgroupCongr hf)⟩⟩
  rw [← hf, mem_range_transportHom_iff]

end CFSG.Semidihedral.GL2Recognition
