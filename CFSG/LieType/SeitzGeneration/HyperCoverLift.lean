module

public import CFSG.LieType.Chevalley.RootHyperplaneGenerationR
public import CFSG.LieType.SeitzGeneration.OrthCubeBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.LieType.Chevalley

section Lift

variable {K S : Type*} [Group K] [Group S]

theorem commute_of_mem_ker {ρ : K →* S} (hker : ρ.ker ≤ Subgroup.center K) {z : K}
    (hz : z ∈ ρ.ker) (g : K) : Commute z g :=
  ((Subgroup.mem_center_iff.1 (hker hz)) g).symm

theorem exists_lift_pow_eq_one_of_conj_inv (ρ : K →* S) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) {p : ℕ} (hp : Odd p) {a n : S} (ha : a ^ p = 1)
    (hn : n * a * n⁻¹ = a⁻¹) : ∃ x : K, ρ x = a ∧ x ^ p = 1 := by
  obtain ⟨m, rfl⟩ := hp
  obtain ⟨a₀, rfl⟩ := hρ a
  obtain ⟨n₀, rfl⟩ := hρ n
  obtain ⟨u, hu⟩ : ∃ u, u = a₀ ^ (2 * m + 1) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = n₀ * a₀ * n₀⁻¹ * a₀ := ⟨_, rfl⟩
  have huk : u ∈ ρ.ker := by rw [hu, MonoidHom.mem_ker, map_pow, ha]
  have hck : c ∈ ρ.ker := by
    rw [hc, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hn, inv_mul_cancel]
  have h1 : n₀ * a₀ * n₀⁻¹ = c * a₀⁻¹ := by rw [hc]; group
  have h2 : u = c ^ (2 * m + 1) * u⁻¹ := by
    have e1 : n₀ * u * n₀⁻¹ = u := by
      rw [← (commute_of_mem_ker hker huk n₀).eq, mul_inv_cancel_right]
    calc u = n₀ * u * n₀⁻¹ := e1.symm
      _ = (n₀ * a₀ * n₀⁻¹) ^ (2 * m + 1) := by rw [conj_pow, hu]
      _ = c ^ (2 * m + 1) * u⁻¹ := by
        rw [h1, (commute_of_mem_ker hker hck a₀⁻¹).mul_pow, inv_pow, ← hu]
  have hcp : c ^ (2 * m + 1) = u * u := by
    calc c ^ (2 * m + 1) = c ^ (2 * m + 1) * u⁻¹ * u := (inv_mul_cancel_right _ _).symm
      _ = u * u := by rw [← h2]
  have hwk : c ^ (m + 1) * u⁻¹ ∈ ρ.ker :=
    ρ.ker.mul_mem (ρ.ker.pow_mem hck _) (ρ.ker.inv_mem huk)
  have hwp : (c ^ (m + 1) * u⁻¹) ^ (2 * m + 1) = u := by
    rw [((commute_of_mem_ker hker hck u⁻¹).pow_left (m + 1)).mul_pow, ← pow_mul,
      mul_comm (m + 1) (2 * m + 1), pow_mul, hcp, inv_pow, ← sq, ← pow_mul,
      show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ', mul_inv_cancel_right]
  refine ⟨a₀ * (c ^ (m + 1) * u⁻¹)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, (MonoidHom.mem_ker).1 hwk, inv_one, mul_one]
  · rw [((commute_of_mem_ker hker hwk a₀).symm.inv_right).mul_pow, inv_pow, hwp, ← hu,
      mul_inv_cancel]

theorem commute_lift_of_conj_inv (ρ : K →* S) (hker : ρ.ker ≤ Subgroup.center K) {p : ℕ}
    (hp : Odd p) {x y m : K} (hxy : Commute (ρ x) (ρ y)) (hyp : ρ y ^ p = 1)
    (hmx : Commute (ρ m) (ρ x)) (hmy : ρ m * ρ y * (ρ m)⁻¹ = (ρ y)⁻¹) : Commute x y := by
  obtain ⟨c, hc⟩ : ∃ c, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = x * m * x⁻¹ * m⁻¹ := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k, k = m * y * m⁻¹ * y := ⟨_, rfl⟩
  have hck : c ∈ ρ.ker := by
    rw [hc, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxy.eq,
      mul_inv_cancel_right, mul_inv_cancel]
  have hdk : d ∈ ρ.ker := by
    rw [hd, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hmx.eq,
      mul_inv_cancel_right, mul_inv_cancel]
  have hkk : k ∈ ρ.ker := by
    rw [hk, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hmy, inv_mul_cancel]
  have hxm : x * m * x⁻¹ = d * m := by rw [hd]; group
  have hxy' : x * y * x⁻¹ = c * y := by rw [hc]; group
  have hmyk : m * y * m⁻¹ = k * y⁻¹ := by rw [hk]; group
  have e1 : x * (m * y * m⁻¹) * x⁻¹ = c * (m * y * m⁻¹) := by
    calc x * (m * y * m⁻¹) * x⁻¹ =
        (x * m * x⁻¹) * (x * y * x⁻¹) * (x * m * x⁻¹)⁻¹ := by group
      _ = d * (m * c * y * m⁻¹) * d⁻¹ := by rw [hxm, hxy']; group
      _ = m * c * y * m⁻¹ := by
        rw [(commute_of_mem_ker hker hdk _).eq, mul_inv_cancel_right]
      _ = c * (m * y * m⁻¹) := by rw [← (commute_of_mem_ker hker hck m).eq]; group
  have e2 : x * (m * y * m⁻¹) * x⁻¹ = c⁻¹ * (m * y * m⁻¹) := by
    rw [hmyk]
    calc x * (k * y⁻¹) * x⁻¹ = (x * k) * y⁻¹ * x⁻¹ := by group
      _ = k * (x * y * x⁻¹)⁻¹ := by rw [← (commute_of_mem_ker hker hkk x).eq]; group
      _ = k * (c * y)⁻¹ := by rw [hxy']
      _ = c⁻¹ * (k * y⁻¹) := by
        rw [mul_inv_rev, ← mul_assoc,
          (commute_of_mem_ker hker (ρ.ker.inv_mem hck) (k * y⁻¹)).eq]
  have hcc : c = c⁻¹ := mul_right_cancel (e1.symm.trans e2)
  have hc2 : c ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hcc]
    exact mul_inv_cancel c
  have hyk : y ^ p ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, hyp]
  have hcp : c ^ p = 1 := by
    have h1 : x * y ^ p * x⁻¹ = y ^ p := by
      rw [← (commute_of_mem_ker hker hyk x).eq, mul_inv_cancel_right]
    have h2 : x * y ^ p * x⁻¹ = c ^ p * y ^ p := by
      rw [← conj_pow, hxy', (commute_of_mem_ker hker hck y).mul_pow]
    exact mul_right_cancel ((h2.symm.trans h1).trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hcp)
    rw [(Nat.coprime_two_left.2 hp).gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  show x * y = y * x
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [← hc, hc1, one_mul]

theorem commute_lift_of_coprime (ρ : K →* S) (hker : ρ.ker ≤ Subgroup.center K) {p q : ℕ}
    (hpq : Nat.Coprime p q) {x g : K} (hxg : Commute (ρ x) (ρ g)) (hx : x ^ p = 1)
    (hg : ρ g ^ q = 1) : Commute x g := by
  obtain ⟨c, hc⟩ : ∃ c, c = x * g * x⁻¹ * g⁻¹ := ⟨_, rfl⟩
  have hck : c ∈ ρ.ker := by
    rw [hc, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxg.eq,
      mul_inv_cancel_right, mul_inv_cancel]
  have hxg' : x * g * x⁻¹ = c * g := by rw [hc]; group
  have hgx' : g * x * g⁻¹ = c⁻¹ * x := by rw [hc]; group
  have hcp : c ^ p = 1 := by
    have h1 : g * x ^ p * g⁻¹ = c⁻¹ ^ p * x ^ p := by
      rw [← conj_pow, hgx', (commute_of_mem_ker hker (ρ.ker.inv_mem hck) x).mul_pow]
    rw [hx, mul_one, mul_one, mul_inv_cancel, inv_pow] at h1
    exact inv_eq_one.1 h1.symm
  have hgk : g ^ q ∈ ρ.ker := by rw [MonoidHom.mem_ker, map_pow, hg]
  have hcq : c ^ q = 1 := by
    have h1 : x * g ^ q * x⁻¹ = g ^ q := by
      rw [← (commute_of_mem_ker hker hgk x).eq, mul_inv_cancel_right]
    have h2 : x * g ^ q * x⁻¹ = c ^ q * g ^ q := by
      rw [← conj_pow, hxg', (commute_of_mem_ker hker hck g).mul_pow]
    exact mul_right_cancel ((h2.symm.trans h1).trans (one_mul _).symm)
  have hc1 : c = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_of_pow_eq_one hcq)
    rw [hpq.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
    exact h
  show x * g = g * x
  calc x * g = (x * g * x⁻¹ * g⁻¹) * (g * x) := by group
    _ = g * x := by rw [← hc, hc1, one_mul]

theorem eq_top_of_map_eq_top_of_perfect [Group.IsPerfect K] (ρ : K →* S)
    (hker : ρ.ker ≤ Subgroup.center K) {H : Subgroup K} (h : H.map ρ = ⊤) : H = ⊤ := by
  have hdec : ∀ g : K, ∃ h₀ ∈ H, ∃ z ∈ Subgroup.center K, g = h₀ * z := by
    intro g
    have : ρ g ∈ H.map ρ := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨h₀, hh₀, e⟩ := this
    refine ⟨h₀, hh₀, h₀⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  have hcomm : commutator K ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec g₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec g₂
    have c1 := Subgroup.mem_center_iff.mp hz₁
    have c2 := Subgroup.mem_center_iff.mp hz₂
    have e : a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
      calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
          = a₁ * (z₁ * (a₂ * z₂)) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * (a₂ * z₂ * z₁) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [← c1 (a₂ * z₂)]
        _ = a₁ * a₂ * (z₂ * a₁⁻¹) * z₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * a₂ * (a₁⁻¹ * z₂) * z₂⁻¹ * a₂⁻¹ := by rw [← c2 a₁⁻¹]
        _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group
    rw [commutatorElement_def, e]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha₁ ha₂) (H.inv_mem ha₁)) (H.inv_mem ha₂)
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := K)]
  exact hcomm

end Lift

theorem exists_plane_of_two {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e₁ e₂ : G}
    (h12 : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    ∃ F : Subgroup G, IsElemAbelian p F ∧ Nat.card F = p ^ 2 ∧
      (∀ x ∈ F, ∃ i j : ℤ, x = e₁ ^ i * e₂ ^ j) ∧ e₁ ∈ F ∧ e₂ ∈ F := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := fun h => by
    have := (hi 1 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne2 : e₂ ≠ 1 := fun h => by
    have := (hi 0 1 (by rw [h]; simp)).2
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have hc12 : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : G) (b : G)
    rw [← hk, ← hl]
    exact h12.zpow_zpow k l
  let f₂ : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hc12
  have hf : Function.Injective f₂ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : G) * b = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← hl] at hab'
    obtain ⟨hpk, hpl⟩ := hi k l hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨n, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨n, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    rw [ha, hb]
    rfl
  have hcard : Nat.card (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    ring
  refine ⟨f₂.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩,
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard, fun x hx => ?_,
    ⟨(⟨e₁, Subgroup.mem_zpowers e₁⟩, 1), by simp [f₂]⟩,
    ⟨(1, ⟨e₂, Subgroup.mem_zpowers e₂⟩), by simp [f₂]⟩⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' x.1 z.1) (mul_comm' x.2 z.2)
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow]
    have hpow : ∀ (e : G) (he : e ^ p = 1) (a : ↥(Subgroup.zpowers e)), a ^ p = 1 := by
      intro e he a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      change (a : G) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
    have : x ^ p = 1 := Prod.ext (hpow e₁ h₁ x.1) (hpow e₂ h₂ x.2)
    rw [this, map_one]
  · obtain ⟨⟨a, b⟩, rfl⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    refine ⟨k, l, ?_⟩
    change (a : G) * b = _
    rw [← hk, ← hl]

theorem zpow_mul_zpow_pow_eq_one {G : Type*} [Group G] {p : ℕ} {x y : G} (hxy : Commute x y)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (i j : ℤ) : (x ^ i * y ^ j) ^ p = 1 := by
  rw [(hxy.zpow_zpow i j).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow,
    one_zpow, one_mul]

theorem zpow_eq_one_of_dvd_exp {G : Type*} [Group G] {p : ℕ} {x : G} (hx : x ^ p = 1)
    {i : ℤ} (h : (p : ℤ) ∣ i) : x ^ i = 1 := by
  obtain ⟨t, rfl⟩ := h
  rw [zpow_mul, zpow_natCast, hx, one_zpow]

theorem exists_hyperGen_of_cover {K S : Type*} [Group K] [Group S] [Finite K]
    [Group.IsPerfect K] (ρ : K →* S) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    (hrp : r ≠ p) (hz : p ∣ Nat.card ρ.ker) {a b n m : S} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : Commute a b) (hind : ∀ i j : ℤ, a ^ i * b ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j)
    (hn : n * a * n⁻¹ = a⁻¹) (hma : Commute m a) (hmb : m * b * m⁻¹ = b⁻¹)
    {D : Subgroup S} (hD : ∀ x ∈ D, ∃ i j : ℤ, x = a ^ i * b ^ j) (hDc : Nat.card D = p ^ 2)
    (hgen : (⊤ : Subgroup S) ≤ Subgroup.closure (hyperRSet ⊤ D r p)) :
    ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ HyperGen p ⊤ E := by
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' p hz
  set z : K := (z₀ : K) with hzdef
  have hzk : z ∈ ρ.ker := z₀.2
  have hzo : orderOf z = p := by rw [hzdef, Subgroup.orderOf_coe, hz₀]
  have hzp : z ^ p = 1 := hzo ▸ pow_orderOf_eq_one z
  have hzρ : ρ z = 1 := hzk
  obtain ⟨a₁, ha₁ρ, ha₁p⟩ := exists_lift_pow_eq_one_of_conj_inv ρ hρ hker hpodd ha hn
  obtain ⟨b₁, hb₁ρ, hb₁p⟩ := exists_lift_pow_eq_one_of_conj_inv ρ hρ hker hpodd hb hmb
  obtain ⟨m₁, rfl⟩ := hρ m
  have hab₁ : Commute a₁ b₁ :=
    commute_lift_of_conj_inv ρ hker hpodd (m := m₁) (by rw [ha₁ρ, hb₁ρ]; exact hab)
      (by rw [hb₁ρ]; exact hb) (by rw [ha₁ρ]; exact hma) (by rw [hb₁ρ]; exact hmb)
  obtain ⟨E, hE, hEc, -, hzE, haE, hbE⟩ := exists_cube_of_three hp
    (commute_of_mem_ker hker hzk a₁) (commute_of_mem_ker hker hzk b₁) hab₁ hzp ha₁p hb₁p (by
      intro i j k h
      have h' := congrArg ρ h
      rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, hzρ, one_zpow, one_mul, ha₁ρ, hb₁ρ,
        map_one] at h'
      obtain ⟨hj, hk⟩ := hind j k h'
      rw [zpow_eq_one_of_dvd_exp ha₁p hj, zpow_eq_one_of_dvd_exp hb₁p hk, mul_one,
        mul_one] at h
      refine ⟨?_, hj, hk⟩
      rw [← hzo]
      exact orderOf_dvd_iff_zpow_eq_one.2 h)
  refine ⟨E, hE, hEc, ?_⟩
  have hmap : (Subgroup.closure {k : K | k ∈ (⊤ : Subgroup K) ∧ ∃ F : Subgroup K, F ≤ E ∧
      F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f}).map ρ = ⊤ := by
    rw [MonoidHom.map_closure, eq_top_iff]
    refine hgen.trans (Subgroup.closure_mono ?_)
    rintro s ⟨-, ⟨e, he⟩, B, hBD, hBi, hsB⟩
    obtain ⟨s₁, rfl⟩ := hρ s
    refine ⟨s₁, ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
    obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one B with h | h
      · exfalso
        rw [h, Subgroup.relIndex_bot_left, hDc] at hBi
        have : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
        rw [pow_one] at this
        omega
      · exact h
    obtain ⟨i, j, rfl⟩ := hD x (hBD hxB)
    have hxp : (a ^ i * b ^ j) ^ p = 1 := zpow_mul_zpow_pow_eq_one hab ha hb i j
    set x₁ := a₁ ^ i * b₁ ^ j with hx₁
    have hx₁ρ : ρ x₁ = a ^ i * b ^ j := by rw [hx₁, map_mul, map_zpow, map_zpow, ha₁ρ, hb₁ρ]
    have hx₁p : x₁ ^ p = 1 := zpow_mul_zpow_pow_eq_one hab₁ ha₁p hb₁p i j
    have hxo : orderOf (a ^ i * b ^ j) = p := orderOf_eq_prime hxp hx1
    obtain ⟨F, -, hFc, hFgen, -, -⟩ := exists_plane_of_two hp (commute_of_mem_ker hker hzk x₁)
      hzp hx₁p (by
        intro u v h
        have h' := congrArg ρ h
        rw [map_mul, map_zpow, map_zpow, hzρ, one_zpow, one_mul, hx₁ρ, map_one] at h'
        have hv : (p : ℤ) ∣ v := by rw [← hxo]; exact orderOf_dvd_iff_zpow_eq_one.2 h'
        rw [zpow_eq_one_of_dvd_exp hx₁p hv, mul_one] at h
        refine ⟨?_, hv⟩
        rw [← hzo]
        exact orderOf_dvd_iff_zpow_eq_one.2 h)
    have hFE : F ≤ E := by
      intro f hf
      obtain ⟨u, v, rfl⟩ := hFgen f hf
      exact E.mul_mem (E.zpow_mem hzE u)
        (E.zpow_mem (E.mul_mem (E.zpow_mem haE i) (E.zpow_mem hbE j)) v)
    have hFi : F.relIndex E = p := by
      have h1 : Nat.card (F.subgroupOf E) * F.relIndex E = Nat.card E :=
        Subgroup.card_mul_index _
      have h2 : Nat.card (F.subgroupOf E) = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
      rw [h2, hFc, hEc, show p ^ 3 = p ^ 2 * p by ring] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) h1
    refine ⟨F, hFE, hFi, fun f hf => ?_⟩
    have hxs : Commute x₁ s₁ := by
      refine commute_lift_of_coprime ρ hker (Nat.Coprime.pow_right e
        ((Nat.coprime_primes hp hr).2 hrp.symm)) ?_ hx₁p he
      rw [hx₁ρ]
      exact (Subgroup.mem_centralizer_iff.1 hsB _ hxB)
    obtain ⟨u, v, rfl⟩ := hFgen f hf
    exact (((commute_of_mem_ker hker hzk s₁).zpow_left u).mul_left (hxs.zpow_left v)).eq
  have htop := eq_top_of_map_eq_top_of_perfect ρ hker hmap
  show (⊤ : Subgroup K) ≤ Subgroup.closure _
  rw [htop]

end CFSG.LieType.SeitzGeneration
