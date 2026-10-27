module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

section Quotient

variable {G : Type*} [Group G] {Q : Type*} [Group Q]

theorem centralizer_quotient_cyclic [IsCyclic Q] {p : ℕ} {C D : Subgroup G} (hDC : D ≤ C)
    (hDZ : D ≤ centerOf C) (hDp : ∀ x ∈ D, x ^ p = 1) (ψ : G →* Q)
    (hker : ∀ x ∈ C, ψ x = 1 ↔ x ∈ D) :
    (∃ g ∈ C, ∀ x ∈ C, ∃ k : ℤ, g ^ k * x ∈ D) ∧ (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧
      D.relIndex C = Nat.card (C.map ψ) ∧
      ∀ Y : Subgroup G, Y ≤ C → Nat.Coprime p (Nat.card Y) →
        IsCyclic Y ∧ Function.Injective (ψ.comp Y.subtype) := by
  obtain ⟨⟨_, g, hgC, rfl⟩, hgen⟩ := IsCyclic.exists_generator (α := C.map ψ)
  have hcyc : ∀ x ∈ C, ∃ k : ℤ, g ^ k * x ∈ D := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨ψ x, x, hx, rfl⟩)
    refine ⟨-k, (hker _ (C.mul_mem (C.zpow_mem hgC _) hx)).1 ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at hk'
    rw [map_mul, map_zpow, ← hk', ← zpow_add, neg_add_cancel, zpow_zero]
  have hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := hcyc x hx
    obtain ⟨l, hl⟩ := hcyc y hy
    have hdc : ∀ d ∈ D, ∀ c ∈ C, c * d = d * c := fun d hd c hc =>
      (mem_center_map_subtype.1 (hDZ hd)).2 c hc
    obtain ⟨d, hd, rfl⟩ : ∃ d ∈ D, x = g ^ (-k) * d := ⟨_, hk, by group⟩
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ D, y = g ^ (-l) * e := ⟨_, hl, by group⟩
    have h1 : Commute d (g ^ (-l)) := (hdc d hd (g ^ (-l)) (C.zpow_mem hgC _)).symm
    have h2 : Commute (g ^ (-k)) e := hdc e he (g ^ (-k)) (C.zpow_mem hgC _)
    have h3 : Commute d e := (hdc d hd e (hDC he)).symm
    have h4 : Commute (g ^ (-k)) (g ^ (-l)) := (Commute.refl g).zpow_zpow _ _
    exact ((h4.mul_right h2).mul_left (h1.mul_right h3)).eq
  have hindex : D.relIndex C = Nat.card (C.map ψ) := by
    have hk : (ψ.comp C.subtype).ker = D.subgroupOf C := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
      exact hker x x.2
    rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]
  refine ⟨⟨g, hgC, hcyc⟩, hcomm, hindex, fun Y hYC hYp => ?_⟩
  have hinj : Function.Injective (ψ.comp Y.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyD : (y : G) ∈ D := (hker _ (hYC y.2)).1 hy
    have h1 := orderOf_dvd_of_pow_eq_one (hDp _ hyD)
    have h2 : orderOf (y : G) ∣ Nat.card Y := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard y
    have h3 := Nat.dvd_gcd h1 h2
    rw [hYp.gcd_eq_one, Nat.dvd_one, Subgroup.orderOf_coe, orderOf_eq_one_iff] at h3
    exact h3
  exact ⟨isCyclic_of_injective _ hinj, hinj⟩

end Quotient

theorem order_parity {p r f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ r ^ f + 1) :
    orderOf (r : ZMod p) ∣ 2 * f ∧ Even (orderOf (r : ZMod p)) ∧
      Odd (2 * f / orderOf (r : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hneg : (r : ZMod p) ^ f = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (r ^ f + 1) p).2 hdvd
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
  have h2f : orderOf (r : ZMod p) ∣ 2 * f := by
    rw [orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, hneg]
    ring
  have hnf : ¬ orderOf (r : ZMod p) ∣ f := fun h => by
    rw [orderOf_dvd_iff_pow_eq_one, hneg] at h
    exact ZMod.neg_one_ne_one h
  set d := orderOf (r : ZMod p)
  refine ⟨h2f, ?_, ?_⟩
  · by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    exact hnf ((Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.coprime_comm.1 ((Nat.coprime_two_left).2 hodd)) h2f))
  · obtain ⟨m, hm⟩ := h2f
    have hd0 : d ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hm
      exact hnf (by rw [show f = 0 by omega]; exact dvd_zero d)
    rw [hm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨m', rfl⟩ := hev
    exact hnf ⟨m', by linarith⟩

section Frobenius

variable {K : Type*} [Field K]

theorem pow_frobenius_apply {r : ℕ} {φ : K ≃+* K} (hφ : ∀ a, φ a = a ^ r) (k : ℕ) (a : K) :
    (φ ^ k) a = a ^ r ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [pow_succ φ k]
    change (φ ^ k) (φ a) = _
    rw [hφ, ih, ← pow_mul, pow_succ r k, mul_comm r (r ^ k)]

theorem mem_zpowers_of_fix [Finite K] {r p : ℕ} {φ : K ≃+* K} (hφ : ∀ a, φ a = a ^ r)
    (hφtop : Subgroup.zpowers φ = ⊤) (hr : 1 ≤ r) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hp : 1 ≤ p) {σ : K ≃+* K} (hσ : σ ζ = ζ) :
    σ ∈ Subgroup.zpowers (φ ^ orderOf (r : ZMod p)) := by
  have : Finite (K ≃+* K) := by
    have := Fintype.ofFinite K
    exact Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ h => RingEquiv.ext
      (congrFun h)
  have hσφ : σ ∈ Submonoid.powers φ := by
    rw [mem_powers_iff_mem_zpowers, hφtop]
    trivial
  obtain ⟨k, rfl⟩ := hσφ
  rw [pow_frobenius_apply hφ] at hσ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hrk : 1 ≤ r ^ k := Nat.one_le_pow _ _ (by omega)
  have h1 : ζ ^ (r ^ k - 1) = 1 := by
    have h2 : ζ ^ (r ^ k - 1) * ζ = 1 * ζ := by
      rw [← pow_succ, Nat.sub_add_cancel hrk, hσ, one_mul]
    exact mul_right_cancel₀ hζ0 h2
  have h3 : p ∣ r ^ k - 1 := (hζ.pow_eq_one_iff_dvd _).1 h1
  have h4 : (r : ZMod p) ^ k = 1 := by
    have h5 := (ZMod.natCast_eq_zero_iff (r ^ k - 1) p).2 h3
    rw [Nat.cast_sub hrk, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h5
    exact h5
  obtain ⟨m, rfl⟩ := orderOf_dvd_of_pow_eq_one h4
  change φ ^ (orderOf (r : ZMod p) * m) ∈ _
  rw [pow_mul]
  exact Subgroup.npow_mem_zpowers _ _

theorem card_zpowers_frobenius_pow {φ : K ≃+* K} {n d : ℕ} (hφ : orderOf φ = n) (hd : d ≠ 0)
    (hdn : d ∣ n) : Nat.card (Subgroup.zpowers (φ ^ d)) = n / d := by
  rw [Nat.card_zpowers, orderOf_pow_of_dvd hd (hφ ▸ hdn), hφ]

end Frobenius

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
