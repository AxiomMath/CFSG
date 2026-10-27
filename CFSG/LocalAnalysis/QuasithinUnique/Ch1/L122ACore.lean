module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Vol2Native.L122A

open CFSG.Open

@[expose] def OutPLifts (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ ξ : MulAut K, (∃ k : K, ξ ^ p = MulAut.conj k) → ∃ k : K, (MulAut.conj k * ξ) ^ p = 1

theorem congr_conj {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (k : K) :
    MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  apply MulEquiv.ext
  intro m
  change e (k * e.symm m * k⁻¹) = e k * m * (e k)⁻¹
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]

theorem OutPLifts.of_mulEquiv {p : ℕ} {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : OutPLifts p K) : OutPLifts p K' := by
  intro ξ' ⟨k', hk'⟩
  set ξ : MulAut K := (MulAut.congr e).symm ξ' with hξ
  have hξp : ξ ^ p = MulAut.conj (e.symm k') := by
    rw [hξ, ← map_pow, hk']
    apply (MulAut.congr e).injective
    rw [MulEquiv.apply_symm_apply, congr_conj, e.apply_symm_apply]
  obtain ⟨k, hk⟩ := h ξ ⟨e.symm k', hξp⟩
  refine ⟨e k, ?_⟩
  have := congrArg (MulAut.congr e) hk
  rw [map_pow, map_mul, congr_conj, hξ, MulEquiv.apply_symm_apply, map_one] at this
  exact this

section Prod

variable {X : Type*} [Group X]

@[expose] def prodSub (N₁ N₂ : Subgroup X) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) :
    Subgroup X where
  carrier := {x | ∃ a ∈ N₁, ∃ b ∈ N₂, x = a * b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    refine ⟨a * a', N₁.mul_mem ha ha', b * b', N₂.mul_mem hb hb', ?_⟩
    have h : b * a' = a' * b := (hc a' ha' b hb).symm
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [h]
      _ = a * a' * (b * b') := by group
  one_mem' := ⟨1, N₁.one_mem, 1, N₂.one_mem, (mul_one 1).symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, N₁.inv_mem ha, b⁻¹, N₂.inv_mem hb, ?_⟩
    rw [← mul_inv_rev, ← hc a ha b hb]

variable {N₁ N₂ : Subgroup X} {hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a}

theorem mem_prodSub {x : X} : x ∈ prodSub N₁ N₂ hc ↔ ∃ a ∈ N₁, ∃ b ∈ N₂, x = a * b := Iff.rfl

theorem conj_mem_prodSub {x y : X} (h₁ : x ∈ Subgroup.normalizer (N₁ : Set X))
    (h₂ : x ∈ Subgroup.normalizer (N₂ : Set X)) (hy : y ∈ prodSub N₁ N₂ hc) :
    x * y * x⁻¹ ∈ prodSub N₁ N₂ hc := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  refine ⟨x * a * x⁻¹, (Subgroup.mem_normalizer_iff.mp h₁ a).mp ha, x * b * x⁻¹,
    (Subgroup.mem_normalizer_iff.mp h₂ b).mp hb, ?_⟩
  group

theorem mul_pow_mem_prodSub {x n : X} (h₁ : x ∈ Subgroup.normalizer (N₁ : Set X))
    (h₂ : x ∈ Subgroup.normalizer (N₂ : Set X)) (hn : n ∈ prodSub N₁ N₂ hc) (p : ℕ)
    (hx : x ^ p ∈ prodSub N₁ N₂ hc) : (n * x) ^ p ∈ prodSub N₁ N₂ hc := by
  have key : ∀ k : ℕ, ∃ m ∈ prodSub N₁ N₂ hc, (n * x) ^ k = m * x ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, (prodSub N₁ N₂ hc).one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨m, hm, hmk⟩ := ih
      have hxk₁ : x ^ k ∈ Subgroup.normalizer (N₁ : Set X) := Subgroup.pow_mem _ h₁ k
      have hxk₂ : x ^ k ∈ Subgroup.normalizer (N₂ : Set X) := Subgroup.pow_mem _ h₂ k
      refine ⟨m * (x ^ k * n * (x ^ k)⁻¹), (prodSub N₁ N₂ hc).mul_mem hm
        (conj_mem_prodSub hxk₁ hxk₂ hn), ?_⟩
      rw [pow_succ, hmk]
      group
  obtain ⟨m, hm, hmp⟩ := key p
  rw [hmp]
  exact (prodSub N₁ N₂ hc).mul_mem hm hx

end Prod

section Fixed

variable {X : Type*} [Group X]

theorem exists_fixed_elt {p : ℕ} (hp : p.Prime) {N : Subgroup X} [Finite N]
    (hpN : p ∣ Nat.card N) {z : X} (hz : orderOf z = p)
    (hzN : z ∈ Subgroup.normalizer (N : Set X)) :
    ∃ u ∈ N, orderOf u = p ∧ z * u = u * z := by
  have : Fact p.Prime := ⟨hp⟩
  let g : Subgroup.normalizer (N : Set X) := ⟨z, hzN⟩
  let T : Subgroup (Subgroup.normalizer (N : Set X)) := Subgroup.zpowers g
  have hg : orderOf g = p := by rw [← hz]; exact (Subgroup.orderOf_coe g).symm
  have hT : IsPGroup p T := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  have hmod := hT.card_modEq_card_fixedPoints N
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints T N) :=
    (hmod.dvd_iff (dvd_refl p)).mp hpN
  let S : Subgroup N := (Subgroup.centralizer ({z} : Set X)).subgroupOf N
  have hset : (MulAction.fixedPoints T N : Set N) = (S : Set N) := by
    ext a
    simp only [SetLike.mem_coe]
    constructor
    · intro ha
      have h1 : g • a = a := ha ⟨g, Subgroup.mem_zpowers g⟩
      have h2 : z * (a : X) * z⁻¹ = a := congrArg Subtype.val h1
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      calc (a : X) * z = z * (a : X) * z⁻¹ * z := by rw [h2]
        _ = z * (a : X) := by group
    · intro ha t
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at ha
      have h1 : g • a = a := by
        apply Subtype.ext
        change z * (a : X) * z⁻¹ = a
        calc z * (a : X) * z⁻¹ = (a : X) * z * z⁻¹ := by rw [ha]
          _ = a := by group
      have h2 : g ∈ MulAction.stabilizer (Subgroup.normalizer (N : Set X)) a := h1
      obtain ⟨t, ht⟩ := t
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
      exact (MulAction.stabilizer _ a).zpow_mem h2 m
  have hcard : Nat.card (MulAction.fixedPoints T N) = Nat.card S := by
    rw [hset]
    rfl
  rw [hcard] at hdvd
  have : Finite S := Finite.of_injective _ S.subtype_injective
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := S) p hdvd
  refine ⟨((u : N) : X), (u : N).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hu]
  · have h := u.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at h
    exact h.symm

end Fixed

section Rank

variable {X : Type*} [Group X]

@[expose] def powHom (p : ℕ) [NeZero p] (g : X) (hg : g ^ p = 1) : Multiplicative (ZMod p) →* X where
  toFun a := g ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hg]

theorem powHom_apply (p : ℕ) [NeZero p] (g : X) (hg : g ^ p = 1) (a : Multiplicative (ZMod p)) :
    powHom p g hg a = g ^ (Multiplicative.toAdd a).val := rfl

theorem mem_of_pow_mem {p : ℕ} (hp : p.Prime) {g : X} (hg : orderOf g = p) {P : Subgroup X}
    {i : ℕ} (hi : ¬ p ∣ i) (h : g ^ i ∈ P) : g ∈ P := by
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi).symm hp.one_lt
  have : g = (g ^ i) ^ j := by
    rw [← pow_mul, pow_eq_pow_mod _ hgp, hj, pow_one]
  rw [this]
  exact P.pow_mem h j

variable [Finite X]

theorem three_le_pRank {p : ℕ} (hp : p.Prime) {N₁ N₂ : Subgroup X}
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) (hd : ∀ a ∈ N₁, a ∈ N₂ → a = 1)
    {z u₁ u₂ : X} (hz : orderOf z = p) (hu₁ : orderOf u₁ = p) (hu₂ : orderOf u₂ = p)
    (h₁ : u₁ ∈ N₁) (h₂ : u₂ ∈ N₂) (hzN : z ∉ prodSub N₁ N₂ hc) (hzu₁ : z * u₁ = u₁ * z)
    (hzu₂ : z * u₂ = u₂ * z) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hzp : z ^ p = 1 := hz ▸ pow_orderOf_eq_one z
  have hu₁p : u₁ ^ p = 1 := hu₁ ▸ pow_orderOf_eq_one u₁
  have hu₂p : u₂ ^ p = 1 := hu₂ ▸ pow_orderOf_eq_one u₂
  have hu₁u₂ : Commute u₁ u₂ := hc u₁ h₁ u₂ h₂
  have hzu₁' : Commute z u₁ := hzu₁
  have hzu₂' : Commute z u₂ := hzu₂
  let φ₂ := (powHom p u₁ hu₁p).noncommCoprod (powHom p u₂ hu₂p)
    (fun m n => (hu₁u₂.pow_pow _ _))
  let φ := (powHom p z hzp).noncommCoprod φ₂
    (fun m n => by
      obtain ⟨n₁, n₂⟩ := n
      simp only [φ₂, powHom_apply]
      exact ((hzu₁'.pow_pow _ _).mul_right (hzu₂'.pow_pow _ _)))
  have hφ : ∀ (a b c : Multiplicative (ZMod p)), φ (a, b, c) =
      z ^ (Multiplicative.toAdd a).val *
        (u₁ ^ (Multiplicative.toAdd b).val * u₂ ^ (Multiplicative.toAdd c).val) := by
    intro a b c
    rfl
  have hval : ∀ a : Multiplicative (ZMod p), (Multiplicative.toAdd a).val = 0 → a = 1 := by
    intro a ha
    have : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).mp ha
    exact toAdd_eq_zero.mp this
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b, c⟩ h
    rw [hφ] at h
    have hzi : z ^ (Multiplicative.toAdd a).val ∈ prodSub N₁ N₂ hc := by
      have : z ^ (Multiplicative.toAdd a).val =
          (u₁ ^ (Multiplicative.toAdd b).val * u₂ ^ (Multiplicative.toAdd c).val)⁻¹ :=
        eq_inv_of_mul_eq_one_left h
      rw [this]
      refine (prodSub N₁ N₂ hc).inv_mem ?_
      exact ⟨u₁ ^ (Multiplicative.toAdd b).val, N₁.pow_mem h₁ _,
        u₂ ^ (Multiplicative.toAdd c).val, N₂.pow_mem h₂ _, rfl⟩
    have hdiv : p ∣ (Multiplicative.toAdd a).val := by
      by_contra hnd
      exact hzN (mem_of_pow_mem hp hz hnd hzi)
    have ha : a = 1 := by
      apply hval
      have hlt := ZMod.val_lt (Multiplicative.toAdd a)
      exact Nat.eq_zero_of_dvd_of_lt hdiv hlt
    rw [ha] at h
    simp only [toAdd_one, ZMod.val_zero, pow_zero, one_mul] at h
    have hb' : u₁ ^ (Multiplicative.toAdd b).val ∈ N₂ := by
      have : u₁ ^ (Multiplicative.toAdd b).val = (u₂ ^ (Multiplicative.toAdd c).val)⁻¹ :=
        eq_inv_of_mul_eq_one_left h
      rw [this]
      exact N₂.inv_mem (N₂.pow_mem h₂ _)
    have hb1 : u₁ ^ (Multiplicative.toAdd b).val = 1 := hd _ (N₁.pow_mem h₁ _) hb'
    have hc1 : u₂ ^ (Multiplicative.toAdd c).val = 1 := by
      rw [hb1, one_mul] at h
      exact h
    have hb : b = 1 := by
      apply hval
      have hlt := ZMod.val_lt (Multiplicative.toAdd b)
      have hdvd : p ∣ (Multiplicative.toAdd b).val := by
        have := orderOf_dvd_of_pow_eq_one hb1
        rwa [hu₁] at this
      exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
    have hc : c = 1 := by
      apply hval
      have hlt := ZMod.val_lt (Multiplicative.toAdd c)
      have hdvd : p ∣ (Multiplicative.toAdd c).val := by
        have := orderOf_dvd_of_pow_eq_one hc1
        rwa [hu₂] at this
      exact Nat.eq_zero_of_dvd_of_lt hdvd hlt
    rw [ha, hb, hc]
    rfl
  have hcomm : ∀ a b : Multiplicative (ZMod p) × Multiplicative (ZMod p) × Multiplicative (ZMod p),
      a * b = b * a := fun a b => mul_comm a b
  have hpow : ∀ a : Multiplicative (ZMod p) × Multiplicative (ZMod p) × Multiplicative (ZMod p),
      a ^ p = 1 := by
    intro a
    have hx : ∀ y : Multiplicative (ZMod p), y ^ p = 1 := fun y => by
      change Multiplicative.ofAdd (p • Multiplicative.toAdd y) = 1
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
    exact Prod.ext (hx _) (Prod.ext (hx _) (hx _))
  have hA : Nat.card (Multiplicative (ZMod p) × Multiplicative (ZMod p) × Multiplicative (ZMod p))
      = p ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod,
      show Nat.card (Multiplicative (ZMod p)) = p from by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]]
    ring
  exact CFSG.SectionRank.le_pRank_of_injective hp.one_lt hcomm hpow hA φ hinj (le_top)

end Rank

section Lift

variable {X : Type*} [Group X]

theorem nmh_coe (N : Subgroup X) (y : Subgroup.normalizer (N : Set X)) (c : N) :
    ((Subgroup.normalizerMonoidHom N y c : N) : X) = (y : X) * c * (y : X)⁻¹ := rfl

theorem commute_pow_of_nmh_pow_eq_one {N : Subgroup X} {y : X}
    (hy : y ∈ Subgroup.normalizer (N : Set X)) {p : ℕ}
    (h : (Subgroup.normalizerMonoidHom N ⟨y, hy⟩) ^ p = 1) : ∀ c ∈ N, y ^ p * c = c * y ^ p := by
  intro c hc
  have h1 : Subgroup.normalizerMonoidHom N ((⟨y, hy⟩ : Subgroup.normalizer (N : Set X)) ^ p) = 1 := by
    rw [map_pow]
    exact h
  have h2 := congrArg (fun f : MulAut N => ((f ⟨c, hc⟩ : N) : X)) h1
  simp only [nmh_coe] at h2
  have h3 : y ^ p * c * (y ^ p)⁻¹ = c := h2
  calc y ^ p * c = y ^ p * c * (y ^ p)⁻¹ * y ^ p := by group
    _ = c * y ^ p := by rw [h3]

theorem nmh_pow_eq_conj {N : Subgroup X} {y : X} (hy : y ∈ Subgroup.normalizer (N : Set X))
    {p : ℕ} {n : N} (h : ∀ c : N, y ^ p * c * (y ^ p)⁻¹ = n * c * n⁻¹) :
    (Subgroup.normalizerMonoidHom N ⟨y, hy⟩) ^ p = MulAut.conj n := by
  rw [← map_pow]
  apply MulEquiv.ext
  intro c
  apply Subtype.ext
  rw [nmh_coe]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h c

variable {N₁ N₂ : Subgroup X} {hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a}

theorem lift_step {p : ℕ} (hp : p.Prime)
    (hz₁ : ∀ a ∈ N₁, (∀ b ∈ N₁, a * b = b * a) → a = 1)
    (hz₂ : ∀ a ∈ N₂, (∀ b ∈ N₂, a * b = b * a) → a = 1)
    (hout₁ : OutPLifts p N₁) (hout₂ : OutPLifts p N₂) {x : X}
    (hn₁ : x ∈ Subgroup.normalizer (N₁ : Set X)) (hn₂ : x ∈ Subgroup.normalizer (N₂ : Set X))
    (hxN : x ∉ prodSub N₁ N₂ hc) (hxp : x ^ p ∈ prodSub N₁ N₂ hc) :
    ∃ y : X, orderOf y = p ∧ y ∈ Subgroup.normalizer (N₁ : Set X) ∧
      y ∈ Subgroup.normalizer (N₂ : Set X) ∧ y ∉ prodSub N₁ N₂ hc := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hxp
  have hα₁ : (Subgroup.normalizerMonoidHom N₁ ⟨x, hn₁⟩) ^ p = MulAut.conj (⟨a, ha⟩ : N₁) := by
    apply nmh_pow_eq_conj
    intro c
    rw [hab]
    have hbc : b * (c : X) = (c : X) * b := (hc c c.2 b hb).symm
    calc a * b * (c : X) * (a * b)⁻¹ = a * (b * (c : X)) * b⁻¹ * a⁻¹ := by group
      _ = a * ((c : X) * b) * b⁻¹ * a⁻¹ := by rw [hbc]
      _ = a * c * a⁻¹ := by group
  have hα₂ : (Subgroup.normalizerMonoidHom N₂ ⟨x, hn₂⟩) ^ p = MulAut.conj (⟨b, hb⟩ : N₂) := by
    apply nmh_pow_eq_conj
    intro c
    rw [hab]
    have hac : a * (c : X) = (c : X) * a := hc a ha c c.2
    have hw : a * (b * (c : X) * b⁻¹) = (b * (c : X) * b⁻¹) * a :=
      hc a ha _ ((Subgroup.mem_normalizer_iff.mp
        (Subgroup.le_normalizer (show b ∈ N₂ from hb)) c).mp c.2)
    calc a * b * (c : X) * (a * b)⁻¹ = a * (b * (c : X) * b⁻¹) * a⁻¹ := by group
      _ = b * (c : X) * b⁻¹ := by rw [hw]; group
  obtain ⟨k₁, hk₁⟩ := hout₁ _ ⟨⟨a, ha⟩, hα₁⟩
  obtain ⟨k₂, hk₂⟩ := hout₂ _ ⟨⟨b, hb⟩, hα₂⟩
  have hnN : (k₁ : X) * (k₂ : X) ∈ prodSub N₁ N₂ hc := ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩
  have hk₂N₁ : (k₂ : X) ∈ Subgroup.normalizer (N₁ : Set X) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => hc h hh k₂ k₂.2)
  have hk₁N₂ : (k₁ : X) ∈ Subgroup.normalizer (N₂ : Set X) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => (hc k₁ k₁.2 h hh).symm)
  have hy₁ : (k₁ : X) * (k₂ : X) * x ∈ Subgroup.normalizer (N₁ : Set X) :=
    ((Subgroup.normalizer (N₁ : Set X)).mul_mem
      ((Subgroup.normalizer (N₁ : Set X)).mul_mem (Subgroup.le_normalizer k₁.2) hk₂N₁)) hn₁
  have hy₂ : (k₁ : X) * (k₂ : X) * x ∈ Subgroup.normalizer (N₂ : Set X) :=
    ((Subgroup.normalizer (N₂ : Set X)).mul_mem
      ((Subgroup.normalizer (N₂ : Set X)).mul_mem hk₁N₂ (Subgroup.le_normalizer k₂.2))) hn₂
  have hact₁ : Subgroup.normalizerMonoidHom N₁ ⟨(k₁ : X) * (k₂ : X) * x, hy₁⟩ =
      MulAut.conj k₁ * Subgroup.normalizerMonoidHom N₁ ⟨x, hn₁⟩ := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [nmh_coe]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, nmh_coe]
    have hw : (k₂ : X) * (x * c * x⁻¹) = (x * c * x⁻¹) * k₂ :=
      (hc _ ((Subgroup.mem_normalizer_iff.mp hn₁ c).mp c.2) k₂ k₂.2).symm
    calc (k₁ : X) * k₂ * x * c * ((k₁ : X) * k₂ * x)⁻¹
        = (k₁ : X) * ((k₂ : X) * (x * c * x⁻¹) * (k₂ : X)⁻¹) * (k₁ : X)⁻¹ := by group
      _ = (k₁ : X) * (x * c * x⁻¹) * (k₁ : X)⁻¹ := by rw [hw]; group
  have hact₂ : Subgroup.normalizerMonoidHom N₂ ⟨(k₁ : X) * (k₂ : X) * x, hy₂⟩ =
      MulAut.conj k₂ * Subgroup.normalizerMonoidHom N₂ ⟨x, hn₂⟩ := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [nmh_coe]
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, nmh_coe]
    have hw : (k₁ : X) * ((k₂ : X) * (x * c * x⁻¹) * (k₂ : X)⁻¹) =
        ((k₂ : X) * (x * c * x⁻¹) * (k₂ : X)⁻¹) * k₁ :=
      hc k₁ k₁.2 _ (N₂.mul_mem (N₂.mul_mem k₂.2 ((Subgroup.mem_normalizer_iff.mp hn₂ c).mp c.2))
        (N₂.inv_mem k₂.2))
    calc (k₁ : X) * k₂ * x * c * ((k₁ : X) * k₂ * x)⁻¹
        = (k₁ : X) * ((k₂ : X) * (x * c * x⁻¹) * (k₂ : X)⁻¹) * (k₁ : X)⁻¹ := by group
      _ = (k₂ : X) * (x * c * x⁻¹) * (k₂ : X)⁻¹ := by rw [hw]; group
  have hp₁ : ∀ c ∈ N₁, ((k₁ : X) * k₂ * x) ^ p * c = c * ((k₁ : X) * k₂ * x) ^ p :=
    commute_pow_of_nmh_pow_eq_one hy₁ (by rw [hact₁]; exact hk₁)
  have hp₂ : ∀ c ∈ N₂, ((k₁ : X) * k₂ * x) ^ p * c = c * ((k₁ : X) * k₂ * x) ^ p :=
    commute_pow_of_nmh_pow_eq_one hy₂ (by rw [hact₂]; exact hk₂)
  obtain ⟨a', ha', b', hb', hy'⟩ := mul_pow_mem_prodSub hn₁ hn₂ hnN p ⟨a, ha, b, hb, hab⟩
  have ha1 : a' = 1 := by
    apply hz₁ a' ha' fun c hcN => ?_
    have h1 := hp₁ c hcN
    rw [hy'] at h1
    have hbc : b' * c = c * b' := (hc c hcN b' hb').symm
    apply mul_right_cancel (b := b')
    calc a' * c * b' = a' * (c * b') := by rw [mul_assoc]
      _ = a' * (b' * c) := by rw [hbc]
      _ = a' * b' * c := by rw [mul_assoc]
      _ = c * (a' * b') := h1
      _ = c * a' * b' := by rw [mul_assoc]
  have hb1 : b' = 1 := by
    apply hz₂ b' hb' fun c hcN => ?_
    have h2 := hp₂ c hcN
    rw [hy'] at h2
    have hac : a' * c = c * a' := hc a' ha' c hcN
    apply mul_left_cancel (a := a')
    calc a' * (b' * c) = a' * b' * c := by rw [mul_assoc]
      _ = c * (a' * b') := h2
      _ = c * a' * b' := by rw [mul_assoc]
      _ = a' * c * b' := by rw [hac]
      _ = a' * (c * b') := by rw [mul_assoc]
  have hyp : ((k₁ : X) * k₂ * x) ^ p = 1 := by rw [hy', ha1, hb1, mul_one]
  have hyN : (k₁ : X) * k₂ * x ∉ prodSub N₁ N₂ hc := by
    intro hy
    apply hxN
    have : x = ((k₁ : X) * k₂)⁻¹ * ((k₁ : X) * k₂ * x) := by group
    rw [this]
    exact (prodSub N₁ N₂ hc).mul_mem ((prodSub N₁ N₂ hc).inv_mem hnN) hy
  have hy1 : (k₁ : X) * k₂ * x ≠ 1 := fun h => hyN (h ▸ (prodSub N₁ N₂ hc).one_mem)
  exact ⟨_, orderOf_eq_prime hyp hy1, hy₁, hy₂, hyN⟩

end Lift

section Core

variable {X : Type*} [Group X]

variable {N₁ N₂ : Subgroup X} {hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a}

theorem exists_order_p_outside {p : ℕ} (hp : p.Prime)
    (hz₁ : ∀ a ∈ N₁, (∀ b ∈ N₁, a * b = b * a) → a = 1)
    (hz₂ : ∀ a ∈ N₂, (∀ b ∈ N₂, a * b = b * a) → a = 1)
    (hout₁ : OutPLifts p N₁) (hout₂ : OutPLifts p N₂) :
    ∀ (k : ℕ) (x : X), x ^ (p ^ k) = 1 → x ∈ Subgroup.normalizer (N₁ : Set X) →
      x ∈ Subgroup.normalizer (N₂ : Set X) → x ∉ prodSub N₁ N₂ hc →
      ∃ y : X, orderOf y = p ∧ y ∈ Subgroup.normalizer (N₁ : Set X) ∧
        y ∈ Subgroup.normalizer (N₂ : Set X) ∧ y ∉ prodSub N₁ N₂ hc := by
  intro k
  induction k with
  | zero =>
    intro x hx _ _ hxN
    exfalso
    apply hxN
    rw [pow_zero, pow_one] at hx
    rw [hx]
    exact (prodSub N₁ N₂ hc).one_mem
  | succ k ih =>
    intro x hx hn₁ hn₂ hxN
    by_cases hxp : x ^ p ∈ prodSub N₁ N₂ hc
    · exact lift_step hp hz₁ hz₂ hout₁ hout₂ hn₁ hn₂ hxN hxp
    · refine ih (x ^ p) ?_ (Subgroup.pow_mem _ hn₁ p) (Subgroup.pow_mem _ hn₂ p) hxp
      rw [← pow_mul, ← pow_succ']
      exact hx

variable [Finite X]

theorem mem_prodSub_of_pElement {p : ℕ} (hp : p.Prime)
    (hz₁ : ∀ a ∈ N₁, (∀ b ∈ N₁, a * b = b * a) → a = 1)
    (hz₂ : ∀ a ∈ N₂, (∀ b ∈ N₂, a * b = b * a) → a = 1)
    (hp₁ : p ∣ Nat.card N₁) (hp₂ : p ∣ Nat.card N₂)
    (hout₁ : OutPLifts p N₁) (hout₂ : OutPLifts p N₂)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2) {x : X} {k : ℕ} (hx : x ^ (p ^ k) = 1)
    (hn₁ : x ∈ Subgroup.normalizer (N₁ : Set X)) (hn₂ : x ∈ Subgroup.normalizer (N₂ : Set X)) :
    x ∈ prodSub N₁ N₂ hc := by
  by_contra hxN
  obtain ⟨z, hz, hzn₁, hzn₂, hzN⟩ := exists_order_p_outside hp hz₁ hz₂ hout₁ hout₂ k x hx hn₁ hn₂ hxN
  obtain ⟨u₁, hu₁N, hu₁o, hzu₁⟩ := exists_fixed_elt hp hp₁ hz hzn₁
  obtain ⟨u₂, hu₂N, hu₂o, hzu₂⟩ := exists_fixed_elt hp hp₂ hz hzn₂
  have hd : ∀ a ∈ N₁, a ∈ N₂ → a = 1 := fun a ha ha' => hz₁ a ha fun b hb => (hc b hb a ha').symm
  have h3 := three_le_pRank hp hc hd hz hu₁o hu₂o hu₁N hu₂N hzN hzu₁ hzu₂
  omega

end Core

end CFSG.QuasithinUnique.Vol2Native.L122A
