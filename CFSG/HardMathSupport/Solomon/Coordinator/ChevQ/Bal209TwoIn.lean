module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209Two
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6FourRank
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open scoped commutatorElement

namespace Bal209TwoInAux

section Lift

variable {Γ G : Type*} [Group Γ] [Group G]

theorem ker_comm {π : Γ →* G} (hker : π.ker ≤ Subgroup.center Γ) {z : Γ} (hz : π z = 1)
    (g : Γ) : g * z = z * g :=
  Subgroup.mem_center_iff.1 (hker (MonoidHom.mem_ker.2 hz)) g

theorem exists_lift_order_three (π : Γ →* G) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Γ) {x w : G} (hx3 : x ^ 3 = 1) (hw : w * x * w⁻¹ = x⁻¹) :
    ∃ y : Γ, π y = x ∧ y ^ 3 = 1 := by
  obtain ⟨y, hy⟩ := hπ x
  obtain ⟨v, hv⟩ := hπ w
  obtain ⟨a, ha⟩ : ∃ a : Γ, a = y ^ 3 := ⟨_, rfl⟩
  have haker : π a = 1 := by rw [ha, map_pow, hy, hx3]
  obtain ⟨z, hz⟩ : ∃ z : Γ, z = v * y * v⁻¹ * y := ⟨_, rfl⟩
  have hzker : π z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, hv, hy, hw]
    group
  have hac : ∀ g : Γ, g * a = a * g := ker_comm hker haker
  have hzc : ∀ g : Γ, g * z = z * g := ker_comm hker hzker
  have hvy : v * y * v⁻¹ = z * y⁻¹ := by
    rw [hz]; group
  have hcomm_zy : Commute z y⁻¹ := (hzc y⁻¹).symm
  have h1 : v * a * v⁻¹ = z ^ 3 * a⁻¹ := by
    have : v * a * v⁻¹ = (v * y * v⁻¹) ^ 3 := by
      rw [ha, conj_pow]
    rw [this, hvy, hcomm_zy.mul_pow, inv_pow, ha]
  have h2 : v * a * v⁻¹ = a := by
    rw [hac v, mul_inv_cancel_right]
  have h3 : a * a = z ^ 3 := by
    have : a = z ^ 3 * a⁻¹ := h2.symm.trans h1
    calc a * a = (z ^ 3 * a⁻¹) * a := by rw [← this]
      _ = z ^ 3 := by group
  obtain ⟨b, hb⟩ : ∃ b : Γ, b = z * a⁻¹ := ⟨_, rfl⟩
  have hbker : π b = 1 := by rw [hb, map_mul, map_inv, hzker, haker]; simp
  have hbc : ∀ g : Γ, g * b = b * g := ker_comm hker hbker
  refine ⟨y * b, ?_, ?_⟩
  · rw [map_mul, hy, hbker, mul_one]
  · have hcb : Commute y b := hbc y
    rw [hcb.mul_pow]
    have hb3 : b ^ 3 = a⁻¹ := by
      have hza : Commute z a⁻¹ := (hzc a⁻¹).symm
      rw [hb, hza.mul_pow, ← h3]
      group
    rw [hb3, ← ha, mul_inv_cancel]

theorem commutator_central_mul_left {z : Γ} (h : ∀ g, g * z = z * g) (a b : Γ) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have h1 : z * (a * b * a⁻¹) * z⁻¹ = a * b * a⁻¹ := by
    rw [← h (a * b * a⁻¹)]; group
  calc ⁅z * a, b⁆ = (z * (a * b * a⁻¹) * z⁻¹) * b⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅a, b⁆ := by rw [h1, commutatorElement_def]

theorem commutator_central_mul_right {z : Γ} (h : ∀ g, g * z = z * g) (a b : Γ) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have h1 : z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    rw [← h (a * b * a⁻¹ * b⁻¹)]; group
  have h2 : a * z = z * a := h a
  calc ⁅a, z * b⁆ = a * z * b * a⁻¹ * b⁻¹ * z⁻¹ := by
        rw [commutatorElement_def]; group
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by rw [h2]; group
    _ = ⁅a, b⁆ := by rw [h1, commutatorElement_def]

theorem commute_of_lift (π : Γ →* G) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Γ) {x y w : G} (hxy : Commute x y)
    (hw : w * x * w⁻¹ = x⁻¹) (hwy : w * y * w⁻¹ = y)
    {x' y' : Γ} (hx' : π x' = x) (hy' : π y' = y) (hx3 : x' ^ 3 = 1) : Commute x' y' := by
  obtain ⟨v, hv⟩ := hπ w
  obtain ⟨c, hc⟩ : ∃ c : Γ, c = ⁅x', y'⁆ := ⟨_, rfl⟩
  have hcker : π c = 1 := by
    rw [hc, map_commutatorElement, hx', hy']
    exact commutatorElement_eq_one_iff_mul_comm.2 hxy.eq
  have hcc : ∀ g : Γ, g * c = c * g := ker_comm hker hcker
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : Γ, z₁ = v * x' * v⁻¹ * x' := ⟨_, rfl⟩
  obtain ⟨z₂, hz₂⟩ : ∃ z₂ : Γ, z₂ = v * y' * v⁻¹ * y'⁻¹ := ⟨_, rfl⟩
  have hz₁ker : π z₁ = 1 := by
    rw [hz₁, map_mul, map_mul, map_mul, map_inv, hv, hx', hw]
    group
  have hz₂ker : π z₂ = 1 := by
    rw [hz₂, map_mul, map_mul, map_mul, map_inv, map_inv, hv, hy', hwy]
    group
  have hz₁c : ∀ g : Γ, g * z₁ = z₁ * g := ker_comm hker hz₁ker
  have hz₂c : ∀ g : Γ, g * z₂ = z₂ * g := ker_comm hker hz₂ker
  have e1 : v * x' * v⁻¹ = z₁ * x'⁻¹ := by rw [hz₁]; group
  have e2 : v * y' * v⁻¹ = z₂ * y' := by rw [hz₂]; group
  have e3 : v * c * v⁻¹ = c := by rw [hcc v, mul_inv_cancel_right]
  have e4 : v * c * v⁻¹ = ⁅x'⁻¹, y'⁆ := by
    have := map_commutatorElement (MulAut.conj v) x' y'
    rw [MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, e1, e2,
      commutator_central_mul_left hz₁c, commutator_central_mul_right hz₂c] at this
    rw [hc]
    exact this
  have e5 : ⁅x'⁻¹, y'⁆ = c⁻¹ := by
    have h1 : ⁅x'⁻¹, y'⁆ = x'⁻¹ * c⁻¹ * x' := by rw [hc, commutatorElement_def]; group
    have hci : x'⁻¹ * c⁻¹ = c⁻¹ * x'⁻¹ := (Commute.inv_right (hcc x'⁻¹) : Commute x'⁻¹ c⁻¹).eq
    rw [h1, hci]
    group
  have hc2 : c * c = 1 := by
    have : c = c⁻¹ := e3.symm.trans (e4.trans e5)
    calc c * c = c * c⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel c
  have hconj : ∀ n : ℕ, x' ^ n * y' * (x' ^ n)⁻¹ = c ^ n * y' := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h0 : x' * y' * x'⁻¹ = c * y' := by rw [hc, commutatorElement_def]; group
      calc x' ^ (n + 1) * y' * (x' ^ (n + 1))⁻¹
          = x' * (x' ^ n * y' * (x' ^ n)⁻¹) * x'⁻¹ := by rw [pow_succ']; group
        _ = x' * (c ^ n * y') * x'⁻¹ := by rw [ih]
        _ = c ^ n * (x' * y' * x'⁻¹) := by
            have hcn : x' * c ^ n = c ^ n * x' :=
              (Commute.pow_right (hcc x') n)
            calc x' * (c ^ n * y') * x'⁻¹ = (x' * c ^ n) * y' * x'⁻¹ := by group
              _ = (c ^ n * x') * y' * x'⁻¹ := by rw [hcn]
              _ = c ^ n * (x' * y' * x'⁻¹) := by group
        _ = c ^ (n + 1) * y' := by rw [h0, pow_succ, mul_assoc]
  have hc3 : c ^ 3 = 1 := by
    have h := hconj 3
    rw [hx3] at h
    simp only [inv_one, one_mul, mul_one] at h
    exact mul_right_cancel (a := c ^ 3) (b := y') (c := 1) (by rw [one_mul]; exact h.symm)
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; simp
  exact commutatorElement_eq_one_iff_mul_comm.1 (hc ▸ hc1)

open CFSG.Open in
theorem exists_lift_four {Γ : Type} {G : Type*} [Group Γ] [Group G] (π : Γ →* G)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Γ)
    {x₀ x₁ x₂ t w₀ w₁ w₂ n : G}
    (hx₀ : x₀ ^ 3 = 1) (hx₁ : x₁ ^ 3 = 1) (hx₂ : x₂ ^ 3 = 1) (ht : t ^ 3 = 1)
    (c01 : Commute x₀ x₁) (c02 : Commute x₀ x₂) (c12 : Commute x₁ x₂)
    (c0t : Commute x₀ t) (c1t : Commute x₁ t) (c2t : Commute x₂ t)
    (hw₀ : w₀ * x₀ * w₀⁻¹ = x₀⁻¹) (hw₀₁ : w₀ * x₁ * w₀⁻¹ = x₁) (hw₀₂ : w₀ * x₂ * w₀⁻¹ = x₂)
    (hw₀t : w₀ * t * w₀⁻¹ = t)
    (hw₁ : w₁ * x₁ * w₁⁻¹ = x₁⁻¹) (hw₁₂ : w₁ * x₂ * w₁⁻¹ = x₂) (hw₁t : w₁ * t * w₁⁻¹ = t)
    (hw₂ : w₂ * x₂ * w₂⁻¹ = x₂⁻¹) (hw₂t : w₂ * t * w₂⁻¹ = t)
    (hn : n * t * n⁻¹ = t⁻¹)
    (hind : ∀ a b c d : ℕ, x₀ ^ a * x₁ ^ b * x₂ ^ c * t ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d) :
    ∃ Q : Subgroup Γ, IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 4 ∧
      (∀ q ∈ Q, π q = 1 → q = 1) ∧
      ∀ q ∈ Q, ∃ a b c d : ℕ, π q = x₀ ^ a * x₁ ^ b * x₂ ^ c * t ^ d := by
  obtain ⟨y₀, hy₀, hy₀3⟩ := exists_lift_order_three π hπ hker hx₀ hw₀
  obtain ⟨y₁, hy₁, hy₁3⟩ := exists_lift_order_three π hπ hker hx₁ hw₁
  obtain ⟨y₂, hy₂, hy₂3⟩ := exists_lift_order_three π hπ hker hx₂ hw₂
  obtain ⟨s, hs, hs3⟩ := exists_lift_order_three π hπ hker ht hn
  have d01 : Commute y₀ y₁ := commute_of_lift π hπ hker c01 hw₀ hw₀₁ hy₀ hy₁ hy₀3
  have d02 : Commute y₀ y₂ := commute_of_lift π hπ hker c02 hw₀ hw₀₂ hy₀ hy₂ hy₀3
  have d12 : Commute y₁ y₂ := commute_of_lift π hπ hker c12 hw₁ hw₁₂ hy₁ hy₂ hy₁3
  have d0t : Commute y₀ s := commute_of_lift π hπ hker c0t hw₀ hw₀t hy₀ hs hy₀3
  have d1t : Commute y₁ s := commute_of_lift π hπ hker c1t hw₁ hw₁t hy₁ hs hy₁3
  have d2t : Commute y₂ s := commute_of_lift π hπ hker c2t hw₂ hw₂t hy₂ hs hy₂3
  have hind' : ∀ a b c d : ℕ, y₀ ^ a * y₁ ^ b * y₂ ^ c * s ^ d = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d := by
    intro a b c d h
    apply hind
    have := congrArg π h
    simpa only [map_mul, map_pow, map_one, hy₀, hy₁, hy₂, hs] using this
  obtain ⟨Q, hQel, hQcard, hQform⟩ := TwE6FourRankAux.four_range_facts y₀ y₁ y₂ s hy₀3 hy₁3 hy₂3
    hs3 d01 d02 (d0t) d12 d1t d2t hind'
  refine ⟨Q, hQel, hQcard, ?_, ?_⟩
  · intro q hq hπq
    obtain ⟨n₀, n₁, n₂, n₃, rfl⟩ := hQform q hq
    have hπ' : x₀ ^ n₀ * x₁ ^ n₁ * x₂ ^ n₂ * t ^ n₃ = 1 := by
      simpa only [map_mul, map_pow, hy₀, hy₁, hy₂, hs] using hπq
    obtain ⟨⟨k₀, rfl⟩, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, ⟨k₃, rfl⟩⟩ := hind _ _ _ _ hπ'
    simp only [pow_mul, hy₀3, hy₁3, hy₂3, hs3, one_pow, mul_one]
  · intro q hq
    obtain ⟨n₀, n₁, n₂, n₃, rfl⟩ := hQform q hq
    exact ⟨n₀, n₁, n₂, n₃, by simp only [map_mul, map_pow, hy₀, hy₁, hy₂, hs]⟩

theorem exists_two_group {Γ : Type*} {G : Type*} [Group Γ] [Finite Γ] [Group G] (π : Γ →* G)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Γ) {u : G} (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) (Q : Subgroup Γ) (hQ : ∀ q ∈ Q, Commute (π q) u) :
    ∃ U : Subgroup Γ, U ≠ ⊥ ∧ (∀ g ∈ U, ∃ k : ℕ, g ^ 2 ^ k = 1) ∧
      Q ≤ Subgroup.normalizer (U : Set Γ) := by
  obtain ⟨ũ, hũ⟩ := hπ u
  have key : ∀ g : Γ, π g ∈ Subgroup.zpowers u →
      ∃ (n : ℤ) (z : Γ), π z = 1 ∧ g = ũ ^ n * z := by
    intro g hg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨n, ũ ^ (-n) * g, ?_, by group⟩
    rw [map_mul, map_zpow, hũ, ← hn, zpow_neg, inv_mul_cancel]
  have hcomm : ∀ g h : Γ, π g ∈ Subgroup.zpowers u → π h ∈ Subgroup.zpowers u → Commute g h := by
    intro g h hg hh
    obtain ⟨n, z, hz, rfl⟩ := key g hg
    obtain ⟨m, z', hz', rfl⟩ := key h hh
    have h1 : Commute (ũ ^ n) (ũ ^ m) := Commute.zpow_zpow_self ũ n m
    have h2 : ∀ a : Γ, Commute a z := fun a => ker_comm hker hz a
    have h3 : ∀ a : Γ, Commute a z' := fun a => ker_comm hker hz' a
    exact Commute.mul_left (h1.mul_right (h3 _)) (h2 _).symm
  let U : Subgroup Γ :=
    { carrier := {g | π g ∈ Subgroup.zpowers u ∧ ∃ k : ℕ, g ^ 2 ^ k = 1}
      one_mem' := ⟨by rw [map_one]; exact Subgroup.one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro g h ⟨hg, k, hk⟩ ⟨hh, l, hl⟩
        refine ⟨by rw [map_mul]; exact Subgroup.mul_mem _ hg hh, k + l, ?_⟩
        rw [(hcomm g h hg hh).mul_pow]
        have e1 : g ^ 2 ^ (k + l) = 1 := by
          rw [pow_add, pow_mul, hk, one_pow]
        have e2 : h ^ 2 ^ (k + l) = 1 := by
          rw [add_comm, pow_add, pow_mul, hl, one_pow]
        rw [e1, e2, mul_one]
      inv_mem' := by
        rintro g ⟨hg, k, hk⟩
        refine ⟨by rw [map_inv]; exact Subgroup.inv_mem _ hg, k, ?_⟩
        rw [inv_pow, hk, inv_one] }
  have hmemU : ∀ g : Γ, g ∈ U ↔ π g ∈ Subgroup.zpowers u ∧ ∃ k : ℕ, g ^ 2 ^ k = 1 := fun g => Iff.rfl
  refine ⟨U, ?_, fun g hg => ((hmemU g).1 hg).2, ?_⟩
  ·
    obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card π.ker) Nat.card_pos.ne'
    have hsq : ũ ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, hũ, hu2]
    have hsq1 : (ũ ^ 2) ^ Nat.card π.ker = 1 := by
      have := pow_card_eq_one' (G := ↥π.ker) (x := ⟨ũ ^ 2, hsq⟩)
      exact congrArg Subtype.val this
    have hπg : π (ũ ^ m) = u := by
      obtain ⟨j, rfl⟩ := hm
      rw [map_pow, hũ, pow_succ, pow_mul, hu2, one_pow, one_mul]
    have hg : ũ ^ m ∈ U := by
      refine (hmemU _).2 ⟨by rw [hπg]; exact Subgroup.mem_zpowers u, a + 1, ?_⟩
      have : (ũ ^ m) ^ 2 ^ (a + 1) = (ũ ^ 2) ^ Nat.card π.ker := by
        rw [← pow_mul, ← pow_mul, hN]
        congr 1
        ring
      rw [this, hsq1]
    intro hbot
    have : ũ ^ m ∈ (⊥ : Subgroup Γ) := hbot ▸ hg
    rw [Subgroup.mem_bot] at this
    apply hu1
    rw [← hπg, this, map_one]
  · intro q hq
    rw [Subgroup.mem_normalizer_iff]
    have fwd : ∀ q ∈ Q, ∀ g : Γ, g ∈ U → q * g * q⁻¹ ∈ U := by
      intro q hq g hg
      obtain ⟨hg1, k, hk⟩ := (hmemU g).1 hg
      refine (hmemU _).2 ⟨?_, k, ?_⟩
      · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg1
        have hc : Commute (π q) (π g) := by rw [← hn]; exact (hQ q hq).zpow_right n
        rw [map_mul, map_mul, map_inv, hc.eq, mul_assoc, mul_inv_cancel, mul_one]
        exact hg1
      · rw [conj_pow, hk]; group
    intro g
    refine ⟨fwd q hq g, fun h => ?_⟩
    have := fwd q⁻¹ (Q.inv_mem hq) _ h
    simpa [mul_assoc] using this

end Lift

section LocalAbstract

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem innerOneBalanceThree_of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K')
    (h : InnerOneBalanceThree K') : InnerOneBalanceThree K := by
  intro d hdin hd3 hd1 H hH
  let ψ : MulAut K →* MulAut K' := (MulAut.congr e).toMonoidHom
  have hψ : Function.Injective ψ := (MulAut.congr e).injective
  have hinn : innerAut K' ≤ (innerAut K).map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    ext z
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  have hψd : ψ d ∈ innerAut K' := by
    obtain ⟨x, rfl⟩ := hdin
    refine ⟨e x, ?_⟩
    ext z
    simp [ψ, MulAut.congr_apply, MulAut.conj_apply]
  have hψd3 : ψ d ^ 3 = 1 := by rw [← map_pow, hd3, map_one]
  have hψd1 : ψ d ≠ 1 := fun h1 => hd1 (hψ (h1.trans (map_one ψ).symm))
  have h0 := h (ψ d) hψd hψd3 hψd1 (H.map ψ) (hinn.trans (Subgroup.map_mono hH))
  rw [← map_inf_centralizer_of_injective ψ hψ, ← map_glaPPrimeCoreOf_of_injective 3 ψ hψ] at h0
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h0

theorem pPrimeCore_le_center_of_quasisimple {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hq : CFSG.Open.IsQuasisimple Y) (hp : p.Prime) (hdvd : p ∣ Nat.card Y) :
    CFSG.pPrimeCore p Y ≤ Subgroup.center Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, hsimple⟩ := hq
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup Y, N = CFSG.pPrimeCore p Y := ⟨_, rfl⟩
  rw [← hNdef]
  haveI hNn : N.Normal := hNdef ▸ CFSG.pPrimeCore_normal
  haveI hmapn : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Y))) with hbot | htop
  · intro x hx
    have : QuotientGroup.mk' (Subgroup.center Y) x ∈ N.map (QuotientGroup.mk' (Subgroup.center Y)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · exfalso
    have hsplit : ∀ y : Y, ∃ z ∈ Subgroup.center Y, ∃ n ∈ N, y = z * n := by
      intro y
      have hy : QuotientGroup.mk' (Subgroup.center Y) y ∈
          N.map (QuotientGroup.mk' (Subgroup.center Y)) := by rw [htop]; trivial
      obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.1 hy
      have h1 : n⁻¹ * y ∈ Subgroup.center Y := QuotientGroup.eq.1 hny
      refine ⟨n⁻¹ * y, h1, n, hn, ?_⟩
      have := Subgroup.mem_center_iff.1 h1 n
      calc y = n * (n⁻¹ * y) := by group
        _ = (n⁻¹ * y) * n := this
    have hcomm : commutator Y ≤ N := by
      rw [commutator, Subgroup.commutator_le]
      intro y₁ _ y₂ _
      obtain ⟨z₁, hz₁, n₁, hn₁, rfl⟩ := hsplit y₁
      obtain ⟨z₂, hz₂, n₂, hn₂, rfl⟩ := hsplit y₂
      rw [commutator_central_mul_left (Subgroup.mem_center_iff.1 hz₁),
        commutator_central_mul_right (Subgroup.mem_center_iff.1 hz₂)]
      rw [commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    rw [hperf] at hcomm
    have hNtop : N = ⊤ := top_le_iff.1 hcomm
    have hcop : Nat.Coprime p (Nat.card N) := hNdef ▸ CFSG.pPrimeCore_coprime_card
    rw [hNtop, Subgroup.card_top] at hcop
    exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem center_quotient_eq_map {Y : Type*} [Group Y] (hperf : commutator Y = ⊤) {N : Subgroup Y}
    [N.Normal] (hN : N ≤ Subgroup.center Y) :
    Subgroup.center (Y ⧸ N) = (Subgroup.center Y).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · intro zb hzb
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zb
    refine ⟨z, ?_, rfl⟩
    have hconj : MulAut.conj z = 1 := by
      apply autCenterQuot_injective_of_perfect hperf
      rw [map_one]
      ext q
      induction q using QuotientGroup.induction_on with
      | H x =>
        rw [autCenterQuot_mk, MulAut.one_apply, MulAut.conj_apply]
        rw [eq_comm, QuotientGroup.eq]
        have h1 : (QuotientGroup.mk (z * x * z⁻¹) : Y ⧸ N) = (QuotientGroup.mk x : Y ⧸ N) := by
          have := Subgroup.mem_center_iff.1 hzb (QuotientGroup.mk x)
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          exact mul_inv_eq_iff_eq_mul.2 this.symm
        have h3 : x⁻¹ * (z * x * z⁻¹) ∈ N := QuotientGroup.eq.1 h1.symm
        exact hN h3
    show z ∈ Subgroup.center Y
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) hconj
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * z = (z * g * z⁻¹) * z := by rw [this]
      _ = z * g := by group
  · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _)

theorem isLocallyBalancedAbs_quotient_of_central {p k : ℕ} {Y : Type*} [Group Y]
    (hperf : commutator Y = ⊤) {N : Subgroup Y} [N.Normal] (hN : N ≤ Subgroup.center Y)
    (h : IsLocallyBalancedAbs p k (Y ⧸ Subgroup.center Y)) : IsLocallyBalancedAbs p k (Y ⧸ N) := by
  have hperf' : commutator (Y ⧸ N) = ⊤ := by
    have := congrArg (Subgroup.map (QuotientGroup.mk' N)) hperf
    rw [commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective N)] at this
    rw [commutator]
    exact this
  refine IsLocallyBalancedAbs.of_quotient_center hperf' ?_
  refine IsLocallyBalancedAbs.of_mulEquiv ?_ h
  exact (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map hperf hN)).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center Y) hN)

end LocalAbstract

section Conj

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {X : Type} [Group X]

theorem mem_centralizer_mul_iff {K : Subgroup X} {a z x : X}
    (hz : z ∈ Subgroup.centralizer (K : Set X)) (hx : x ∈ K) :
    x ∈ Subgroup.centralizer ({z * a} : Set X) ↔ x ∈ Subgroup.centralizer ({a} : Set X) := by
  have hzx : z * x = x * z := (Subgroup.mem_centralizer_iff.1 hz x hx).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : z * (x * a) = z * (a * x) := by
      calc z * (x * a) = (z * x) * a := by group
        _ = (x * z) * a := by rw [hzx]
        _ = x * (z * a) := by group
        _ = (z * a) * x := h
        _ = z * (a * x) := by group
    exact mul_left_cancel h1
  · intro h
    calc x * (z * a) = (x * z) * a := by group
      _ = (z * x) * a := by rw [hzx]
      _ = z * (x * a) := by group
      _ = z * (a * x) := by rw [h]
      _ = (z * a) * x := by group

theorem glaPComponent_conj_centralizer [Finite X] {K : Subgroup X} {a g : X}
    (hg : g ∈ Subgroup.normalizer (K : Set X))
    (hga : g * a * g⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X)) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) (GLBConj g J) := by
  have h := glaPComponent_gLBConj hJ g
  have hgK : ∀ x, x ∈ K ↔ g * x * g⁻¹ ∈ K := fun x => Subgroup.mem_normalizer_iff.1 hg x
  have hz'' : g⁻¹ * a * g * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g * k * g⁻¹ ∈ K := (hgK k).1 hk
    have hz : Commute (g * k * g⁻¹) (g * a * g⁻¹ * a⁻¹) :=
      Subgroup.mem_centralizer_iff.1 hga _ hk'
    have hzi := hz.inv_right.eq
    have e : g⁻¹ * a * g * a⁻¹ = g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g := by group
    rw [e]
    calc k * (g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g)
        = g⁻¹ * ((g * k * g⁻¹) * (g * a * g⁻¹ * a⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹ * a⁻¹)⁻¹ * (g * k * g⁻¹)) * g := by rw [hzi]
      _ = (g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g) * k := by group
  have hconj : ∀ x, g * x * g⁻¹ ∈ Subgroup.centralizer ({a} : Set X) ↔
      x ∈ Subgroup.centralizer ({g⁻¹ * a * g} : Set X) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * (g⁻¹ * a * g) = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
        _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h]
        _ = (g⁻¹ * a * g) * x := by group
    · intro h
      calc (g * x * g⁻¹) * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [h]
        _ = a * (g * x * g⁻¹) := by group
  have heq : GLBConj g (K ⊓ Subgroup.centralizer ({a} : Set X)) =
      K ⊓ Subgroup.centralizer ({a} : Set X) := by
    ext x
    rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, ← hgK x]
    constructor
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, ?_⟩
      have h1 := (hconj x).1 hxc
      have e : g⁻¹ * a * g = (g⁻¹ * a * g * a⁻¹) * a := by group
      rw [e] at h1
      exact (mem_centralizer_mul_iff hz'' hx).1 h1
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, (hconj x).2 ?_⟩
      have e : g⁻¹ * a * g = (g⁻¹ * a * g * a⁻¹) * a := by group
      rw [e]
      exact (mem_centralizer_mul_iff hz'' hx).2 hxc
  rwa [heq] at h

end Conj

section SL2Char2

open Matrix CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def wSL (h2 : (2 : F) = 0) : SL(2, F) :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two_of]; linear_combination (-1 : F) * h2⟩

theorem wSL_mul_self (h2 : (2 : F) = 0) : wSL h2 * wSL h2 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem wSL_mul_c3_mul_inv (h2 : (2 : F) = 0) :
    wSL h2 * c3 * (wSL h2)⁻¹ = (c3 : SL(2, F))⁻¹ := by
  have hw : (wSL h2)⁻¹ = wSL h2 := inv_eq_of_mul_eq_one_right (wSL_mul_self h2)
  have h3 : (c3 : SL(2, F))⁻¹ = c3 ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ' c3 2]; exact c3_pow_three)
  rw [hw, h3]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_c3_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, c3, Matrix.mul_apply, Fin.sum_univ_two]

theorem u1_ne_one : (u1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [u1] at this

theorem u1_mul_self (h2 : (2 : F) = 0) : (u1 : SL(2, F)) * u1 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u1, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h2

end SL2Char2

structure FourData (C : Type*) [Group C] where
  x₀ : C
  x₁ : C
  x₂ : C
  t : C
  w₀ : C
  w₁ : C
  w₂ : C
  n : C
  u : C
  hx₀ : x₀ ^ 3 = 1
  hx₁ : x₁ ^ 3 = 1
  hx₂ : x₂ ^ 3 = 1
  ht : t ^ 3 = 1
  c01 : Commute x₀ x₁
  c02 : Commute x₀ x₂
  c12 : Commute x₁ x₂
  c0t : Commute x₀ t
  c1t : Commute x₁ t
  c2t : Commute x₂ t
  hw₀ : w₀ * x₀ * w₀⁻¹ = x₀⁻¹
  hw₀₁ : w₀ * x₁ * w₀⁻¹ = x₁
  hw₀₂ : w₀ * x₂ * w₀⁻¹ = x₂
  hw₀t : w₀ * t * w₀⁻¹ = t
  hw₁ : w₁ * x₁ * w₁⁻¹ = x₁⁻¹
  hw₁₂ : w₁ * x₂ * w₁⁻¹ = x₂
  hw₁t : w₁ * t * w₁⁻¹ = t
  hw₂ : w₂ * x₂ * w₂⁻¹ = x₂⁻¹
  hw₂t : w₂ * t * w₂⁻¹ = t
  hn : n * t * n⁻¹ = t⁻¹
  hind : ∀ a b c d : ℕ, x₀ ^ a * x₁ ^ b * x₂ ^ c * t ^ d = 1 →
    3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d
  hu2 : u ^ 2 = 1
  hu1 : u ≠ 1
  cu₀ : Commute x₀ u
  cu₁ : Commute x₁ u
  cu₂ : Commute x₂ u
  cut : Commute t u

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

theorem WSL_mul_HSL_mul_inv {L : Type} [Field L] (w : Lˣ) :
    (WSL : SL2 L) * HSL w * (WSL : SL2 L)⁻¹ = (HSL w)⁻¹ := by
  have h1 : (HSL w)⁻¹ = HSL w⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [WSL, HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem torusAB_one_snd (σ : K →+* K) {u : Kˣ} (hu : u ∈ normOne σ) :
    torusAB σ u 1 = ((orbitH TwistTag.E6 K σ orb0 (orbUnit σ orb0 u
      (by rw [orb0_card]; exact sigma_sq_of_normOne σ hu)) : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) := by
  have hu2 : (σ ^ (TwistTag.E6.orbit orb0).card) (u : K) = u := by
    rw [orb0_card]; exact sigma_sq_of_normOne σ hu
  have h0 := orbitH_two σ orb0 orb0_card (orbUnit σ orb0 u hu2)
  rw [orb0_perm, orb0_min] at h0
  have hu0 : Units.map (orbitField TwistTag.E6 K σ orb0).subtype.toMonoidHom
      (orbUnit σ orb0 u hu2) = u := Units.ext rfl
  have hu1 : Units.map (σ.comp (orbitField TwistTag.E6 K σ orb0).subtype).toMonoidHom
      (orbUnit σ orb0 u hu2) = sU σ u := Units.ext rfl
  rw [hu0, hu1] at h0
  rw [torusAB_eq, h0]
  have h1 : sU σ (1 : Kˣ) = 1 := map_one _
  rw [h1, torusElt_one, torusElt_one, mul_one, mul_one]

theorem torusG_snd_one_ne_one (σ : K ≃+* K) {ω : Kˣ} (hω : ω ∈ normOne σ.toRingHom)
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    torusG σ.toRingHom (⟨ω, hω⟩, 1) ≠ 1 := by
  intro hp
  have h1 : torusAB σ.toRingHom ω 1 = 1 := congrArg Subtype.val hp
  have h2 : torusTuple σ.toRingHom ω 1 = 1 :=
    rootDiagUnit_injective (K := K) (τ := Tag.E6) (h1.trans rootDiagUnit_one.symm)
  obtain ⟨c00, c50, c20, c40, c02, c52, c22, c42⟩ := cartan_E6_values
  have e0 := congrFun h2 ⟨0, by decide⟩
  rw [torusTuple_eq σ.toRingHom ω 1] at e0
  simp only [Pi.mul_apply, e6TorParam, Pi.one_apply, c00, c50, c20, c40, c02, c52, c22, c42,
    zpow_zero, mul_one, zpow_neg, zpow_one, zpow_ofNat, pow_zero, pow_one] at e0
  rw [inv_one, mul_one] at e0
  apply hω1
  calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
    _ = 1 := by rw [hω3, e0]; simp

theorem nonempty_fourData [Finite K] (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) :
    Nonempty (FourData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  have h2K : (2 : K) = 0 := TwE6FourRankAux.two_eq_zero_of_natCard hK
  have h2F : (2 : ↥(RingHom.eqLocusField σ.toRingHom (RingHom.id K))) = 0 := by
    apply (Subfield.subtype (RingHom.eqLocusField σ.toRingHom (RingHom.id K))).injective
    rw [map_ofNat, map_zero]
    exact h2K
  obtain ⟨w, hw0, hw⟩ := TwE6FourRankAux.exists_sq_add_add_one hK
  let ω : Kˣ := Units.mk0 w hw0
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, ω]
    linear_combination (w - 1) * hw
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : w = 1 := congrArg Units.val h
    rw [h1] at hw
    have : (1 : K) = 0 := by linear_combination hw - h2K
    exact one_ne_zero this
  have hωn : ω ∈ normOne σ.toRingHom := by
    show sU σ.toRingHom ω = ω⁻¹
    apply Units.ext
    have h3 : w ^ 3 = 1 := by
      have := congrArg Units.val hω3
      simpa [ω] using this
    have hσw : σ w = w ^ 2 := hσ w
    rw [Units.val_inv_eq_inv_val]
    change σ w = w⁻¹
    rw [hσw]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h3)
  have hι : ∀ i, Function.Injective (frameHom σ.toRingHom i) := frameHom_injective σ.toRingHom
  have hc : ∀ i j, i ≠ j → ∀ A B, Commute (frameHom σ.toRingHom i A) (frameHom σ.toRingHom j B) :=
    fun i j hij A B => frameHom_commute σ.toRingHom hij A B
  have hroot := frameHom_mem_rootPair σ.toRingHom
  set t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := torusG σ.toRingHom (⟨ω, hωn⟩, 1) with ht
  have htc : ∀ i A, Commute t (frameHom σ.toRingHom i A) := fun i A =>
    torusG_commute_frame σ.toRingHom hroot (⟨ω, hωn⟩, 1) i A
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← map_pow]
    have : ((⟨ω, hωn⟩, 1) : ↥(normOne σ.toRingHom) × ↥(normOne σ.toRingHom)) ^ 3 = 1 := by
      refine Prod.ext ?_ ?_
      · show (⟨ω, hωn⟩ : ↥(normOne σ.toRingHom)) ^ 3 = 1
        exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hω3)
      · show (1 : ↥(normOne σ.toRingHom)) ^ 3 = 1
        exact one_pow 3
    rw [this, map_one]
  have ht1 : t ≠ 1 := torusG_snd_one_ne_one σ hωn hω3 hω1
  obtain ⟨n, hn⟩ : ∃ n : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), n * t * n⁻¹ = t⁻¹ := by
    have hu2 : (σ.toRingHom ^ (TwistTag.E6.orbit orb0).card) (ω : K) = ω := by
      rw [orb0_card]; exact sigma_sq_of_normOne σ.toRingHom hωn
    let ω' := orbUnit σ.toRingHom orb0 ω hu2
    have hnmem : orbitRankOneHom TwistTag.E6 K σ.toRingHom orb0 WSL ∈
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
      orbitRankOneHom_range_le σ.toRingHom orb0 ⟨WSL, rfl⟩
    refine ⟨⟨_, hnmem⟩, ?_⟩
    apply Subtype.ext
    have hts : ((t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) =
        orbitRankOneHom TwistTag.E6 K σ.toRingHom orb0 (HSL ω') := by
      rw [orbitRankOneHom_HSL]
      exact torusAB_one_snd σ.toRingHom hωn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hts, ← map_inv, ← map_inv, ← map_mul, ← map_mul, WSL_mul_HSL_mul_inv]
  have hx3 : ∀ i, (frameHom σ.toRingHom i c3) ^ 3 = 1 := fun i => by
    rw [← map_pow, c3_pow_three, map_one]
  have hcp : ∀ i j, i ≠ j →
      Commute (frameHom σ.toRingHom i c3) (frameHom σ.toRingHom j c3) :=
    fun i j hij => hc i j hij c3 c3
  have hw : ∀ i, frameHom σ.toRingHom i (wSL h2F) * frameHom σ.toRingHom i c3 *
      (frameHom σ.toRingHom i (wSL h2F))⁻¹ = (frameHom σ.toRingHom i c3)⁻¹ := fun i => by
    rw [← map_inv, ← map_mul, ← map_mul, wSL_mul_c3_mul_inv h2F, map_inv]
  have hwc : ∀ i j, i ≠ j → frameHom σ.toRingHom i (wSL h2F) * frameHom σ.toRingHom j c3 *
      (frameHom σ.toRingHom i (wSL h2F))⁻¹ = frameHom σ.toRingHom j c3 := fun i j hij =>
    mul_inv_eq_iff_eq_mul.2 (hc i j hij _ _).eq
  have hwt : ∀ i, frameHom σ.toRingHom i (wSL h2F) * t * (frameHom σ.toRingHom i (wSL h2F))⁻¹ = t :=
    fun i => mul_inv_eq_iff_eq_mul.2 (htc i _).symm.eq
  have hind : ∀ a b c d : ℕ, frameHom σ.toRingHom 0 c3 ^ a * frameHom σ.toRingHom 1 c3 ^ b *
      frameHom σ.toRingHom 2 c3 ^ c * t ^ d = 1 → 3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d := by
    intro a b c d h
    have hp : ∀ i j, i ≠ j → ∀ (m : ℕ) (B : SL(2, ↥(RingHom.eqLocusField σ.toRingHom
        (RingHom.id K)))), Commute (frameHom σ.toRingHom i c3 ^ m) (frameHom σ.toRingHom j B) :=
      fun i j hij m B => (hc i j hij c3 B).pow_left m
    have htp : ∀ (m : ℕ) i (B : SL(2, ↥(RingHom.eqLocusField σ.toRingHom (RingHom.id K)))),
        Commute (t ^ m) (frameHom σ.toRingHom i B) := fun m i B => (htc i B).pow_left m
    have hone : ∀ (i : Fin 4) (m : ℕ), 3 ∣ m → frameHom σ.toRingHom i c3 ^ m = 1 := by
      rintro i m ⟨k, rfl⟩
      rw [pow_mul, hx3 i, one_pow]
    have ha : 3 ∣ a := TwE6FourRankAux.exponent_eq_of_commute_u1 (hι 0)
      (y := (frameHom σ.toRingHom 1 c3 ^ b * frameHom σ.toRingHom 2 c3 ^ c * t ^ d)⁻¹)
      (fun B => Commute.inv_left (((hp 1 0 (by decide) b B).mul_left (hp 2 0 (by decide) c B)).mul_left
        (htp d 0 B)))
      (by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← h]; group)
    rw [hone 0 a ha, one_mul] at h
    have hb : 3 ∣ b := TwE6FourRankAux.exponent_eq_of_commute_u1 (hι 1)
      (y := (frameHom σ.toRingHom 2 c3 ^ c * t ^ d)⁻¹)
      (fun B => Commute.inv_left ((hp 2 1 (by decide) c B).mul_left (htp d 1 B)))
      (by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← h]; group)
    rw [hone 1 b hb, one_mul] at h
    have hc' : 3 ∣ c := TwE6FourRankAux.exponent_eq_of_commute_u1 (hι 2)
      (y := (t ^ d)⁻¹) (fun B => Commute.inv_left (htp d 2 B))
      (by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← h])
    rw [hone 2 c hc', one_mul] at h
    have hd : 3 ∣ d := by
      have := orderOf_dvd_of_pow_eq_one h
      rwa [orderOf_eq_prime ht3 ht1] at this
    exact ⟨ha, hb, hc', hd⟩
  exact ⟨{
    x₀ := frameHom σ.toRingHom 0 c3, x₁ := frameHom σ.toRingHom 1 c3,
    x₂ := frameHom σ.toRingHom 2 c3, t := t,
    w₀ := frameHom σ.toRingHom 0 (wSL h2F), w₁ := frameHom σ.toRingHom 1 (wSL h2F),
    w₂ := frameHom σ.toRingHom 2 (wSL h2F), n := n, u := frameHom σ.toRingHom 3 u1
    hx₀ := hx3 0, hx₁ := hx3 1, hx₂ := hx3 2, ht := ht3
    c01 := hcp 0 1 (by decide), c02 := hcp 0 2 (by decide), c12 := hcp 1 2 (by decide)
    c0t := (htc 0 c3).symm, c1t := (htc 1 c3).symm, c2t := (htc 2 c3).symm
    hw₀ := hw 0, hw₀₁ := hwc 0 1 (by decide), hw₀₂ := hwc 0 2 (by decide), hw₀t := hwt 0
    hw₁ := hw 1, hw₁₂ := hwc 1 2 (by decide), hw₁t := hwt 1
    hw₂ := hw 2, hw₂t := hwt 2
    hn := hn, hind := hind
    hu2 := by rw [sq, ← map_mul, u1_mul_self h2F, map_one]
    hu1 := fun h => u1_ne_one (hι 3 (h.trans (map_one _).symm))
    cu₀ := hc 0 3 (by decide) _ _, cu₁ := hc 1 3 (by decide) _ _, cu₂ := hc 2 3 (by decide) _ _
    cut := htc 3 u1 }⟩

end Model

end Bal209TwoInAux

open Bal209TwoInAux

section Parabolic

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem bal209TwoParabolic_holds : Bal209TwoParabolic := by
  intro X _ _ K hq hK
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hK
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    obtain ⟨D⟩ := nonempty_fourData hcard4 σ hσ2
    let eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom) :=
      e.trans eC
    let π : ↥K →* ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom) :=
      eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    have hπ : Function.Surjective π :=
      eK.surjective.comp (QuotientGroup.mk'_surjective _)
    have hπker : ∀ x : ↥K, π x = 1 ↔ x ∈ Subgroup.center ↥K := by
      intro x
      constructor
      · intro hx
        have : (QuotientGroup.mk' (Subgroup.center ↥K)) x = 1 :=
          eK.injective (by rw [map_one]; exact hx)
        exact (QuotientGroup.eq_one_iff x).1 this
      · intro hx
        have : (QuotientGroup.mk' (Subgroup.center ↥K)) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
        show eK ((QuotientGroup.mk' (Subgroup.center ↥K)) x) = 1
        rw [this, map_one]
    have hker : π.ker ≤ Subgroup.center ↥K := fun x hx => (hπker x).1 hx
    obtain ⟨Q', hQel, hQcard, hQker, hQform⟩ := exists_lift_four π hπ hker D.hx₀ D.hx₁ D.hx₂ D.ht
      D.c01 D.c02 D.c12 D.c0t D.c1t D.c2t D.hw₀ D.hw₀₁ D.hw₀₂ D.hw₀t D.hw₁ D.hw₁₂ D.hw₁t D.hw₂
      D.hw₂t D.hn D.hind
    have hQu : ∀ q ∈ Q', Commute (π q) D.u := by
      intro q hq
      obtain ⟨a, b, c, d, h⟩ := hQform q hq
      rw [h]
      exact (((D.cu₀.pow_left a).mul_left (D.cu₁.pow_left b)).mul_left
        (D.cu₂.pow_left c)).mul_left (D.cut.pow_left d)
    obtain ⟨U', hU'0, hU'2, hU'N⟩ := exists_two_group π hπ hker D.hu2 D.hu1 Q' hQu
    refine ⟨?_, U'.map K.subtype, Q'.map K.subtype, Subgroup.map_subtype_le U', ?_, ?_,
      Subgroup.map_subtype_le Q', ?_, ?_, ?_, ?_⟩
    ·
      have h1 : Nat.card Q' ∣ Nat.card ↥K := Subgroup.card_subgroup_dvd_card Q'
      rw [hQcard] at h1
      exact (dvd_pow_self 3 (by norm_num)).trans h1
    ·
      intro hbot
      apply hU'0
      rw [eq_bot_iff]
      intro g hg
      have : (g : X) ∈ U'.map K.subtype := Subgroup.mem_map_of_mem _ hg
      rw [hbot, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    ·
      rintro ⟨g, hg⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
      obtain ⟨k, hk⟩ := hU'2 g' hg'
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun y : ↥K => (y : X)) hk
      simpa using this
    · exact hQel.map K.subtype
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hQcard]
    · intro x hx
      obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hx
      exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem _ (hU'N hq'))
    ·
      rw [eq_bot_iff]
      rintro x ⟨hxQ, hxC⟩
      obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hxQ
      have hcen : q' ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC (g : X) g.2)
      have := hQker q' hq' ((hπker q').2 hcen)
      rw [Subgroup.mem_bot]
      simp [this]
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

end Parabolic

section Uniq

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  Bal209TwoInAux

@[expose] def Bal209TwoUniq : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) (a : X), CFSG.Open.IsQuasisimple ↥K →
    IsLieQuot ↥K Bal209TwoIndex → a ∈ Subgroup.normalizer (K : Set X) →
      a ^ 3 ∈ Subgroup.centralizer (K : Set X) → a ∉ Subgroup.centralizer (K : Set X) →
        ∀ J J' : Subgroup X, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J' → J = J'

end Uniq

section Local

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def Bal209TwoOuter : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), Bal209TwoIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ δ : MulAut S, δ ^ 3 = 1 → δ ∉ innerAut S →
      ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
        δ ∈ Subgroup.normalizer (H : Set (MulAut S)) →
          GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({δ} : Set (MulAut S))) = ⊥

set_option linter.unusedSectionVars false

theorem innerOneBalanceThree_of_bal209TwoIndex {S : Type} [Group S]
    (d : TauCeti.ValidLieTypeIndex) (hd : Bal209TwoIndex d.1)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : InnerOneBalanceThree S := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedE6 q =>
    have hq2 : q.p = 2 ∧ q.exponent = 1 := hd
    obtain ⟨K', hKf, σ, hcard, hσ, ⟨eC⟩⟩ :=
      CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    have hcard4 : Nat.card K' = 4 := by
      rw [hcard, hq2.1, hq2.2]; norm_num
    haveI : Finite K' := Nat.finite_of_card_ne_zero (by rw [hcard4]; norm_num)
    have hσ2 : ∀ c, σ c = c ^ 2 := fun c => by
      have := hσ c
      rwa [hq2.1, hq2.2, pow_one] at this
    exact innerOneBalanceThree_of_mulEquiv (e.trans eC)
      (SmallQ3.innerOneBalanceThree_twE6_two SmallQ3.twE6TwoFusion_holds SmallQ3.twE6TwoRigid_holds K' hcard4 σ hσ2)
  | _ => exact absurd hd (by simp [Bal209TwoIndex])

end Local

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
