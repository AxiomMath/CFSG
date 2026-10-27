module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

@[expose] def IsWClosed {X : Type*} [Group X] (S A : Subgroup X) : Prop :=
  A ≤ S ∧ ∀ g : X, A.map (MulAut.conj g).toMonoidHom ≤ S → A.map (MulAut.conj g).toMonoidHom = A

variable {B : Type} [Group B] [Finite B] {K : Subgroup B} [K.Normal]

@[expose] noncomputable def innHom (K : Subgroup B) [K.Normal] :
    K →* (MulAut.conjNormal (H := K)).range :=
  ((MulAut.conjNormal (H := K)).comp K.subtype).codRestrict _ fun k => ⟨k, rfl⟩

theorem innHom_apply (k x : K) : ((innHom K k : MulAut K) x) = k * x * k⁻¹ := by
  apply Subtype.ext
  exact MulAut.conjNormal_apply (k : B) x

theorem innHom_injective (hZ : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1) :
    Function.Injective (innHom K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  apply hZ
  intro x
  have h := innHom_apply k x
  rw [MonoidHom.mem_ker.mp hk] at h
  calc k * x = (k * x * k⁻¹) * k := by group
    _ = x * k := by rw [← h]; rfl

theorem conj_eq_of_mem_zpowers {G : Type*} [Group G] {a t : G} (ha : orderOf a = 3) {m : ℕ}
    (ht : t ^ 3 ^ m = 1) (h : t * a * t⁻¹ ∈ zpowers a) : t * a * t⁻¹ = a := by
  classical
  have h3 : a ^ 3 = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha; omega
  rw [(orderOf_pos_iff.mp (by rw [ha]; norm_num)).mem_zpowers_iff_mem_range_orderOf, ha] at h
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨k, hk3, hk⟩ := h
  interval_cases k
  · exfalso
    apply ha1
    have : t * a * t⁻¹ = 1 := by rw [← hk, pow_zero]
    have := congrArg (fun x => t⁻¹ * x * t) this
    simpa [mul_assoc] using this
  · rw [← hk, pow_one]
  · exfalso
    set ψ := MulAut.conj t
    have hψ : ψ a = a ^ 2 := by rw [MulAut.conj_apply, ← hk]
    have hpow : ∀ n : ℕ, (ψ ^ n) a = a ^ (2 ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, map_pow, hψ, ← pow_mul, pow_succ']
    have h1 : (ψ ^ 3 ^ m) a = a := by
      rw [← map_pow, ht, map_one, MulAut.one_apply]
    rw [hpow, ← pow_mod_orderOf, ha] at h1
    obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
    have hmod : 2 ^ 3 ^ m % 3 = 2 := by
      rw [hj, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [hmod] at h1
    apply ha1
    have h2 : a * a = a * 1 := by rw [mul_one, ← pow_two, h1]
    exact mul_left_cancel h2

theorem inner_of_index_two {X : Type*} [Group X] [Finite X]
    (hZ : ∀ k : X, (∀ x : X, k * x = x * k) → k = 1)
    (hcard : Nat.card (MulAut X) = 2 * Nat.card X) (φ : MulAut X) {m : ℕ}
    (hm : φ ^ (2 * m + 1) = 1) : ∃ g : X, ∀ x : X, φ x = g * x * g⁻¹ := by
  set I := (MulAut.conj : X →* MulAut X).range
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    apply hZ
    intro x
    have h := congrArg (fun α : MulAut X => α x) (MonoidHom.mem_ker.mp hk)
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc k * x = (k * x * k⁻¹) * k := by group
      _ = x * k := by rw [h]
  have hI : Nat.card I = Nat.card X := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hidx : I.index = 2 := by
    have h := I.card_mul_index
    rw [hI, hcard] at h
    have hpos : 0 < Nat.card X := Nat.card_pos
    nlinarith
  have hsq : φ ^ (2 * m) ∈ I := by
    rw [pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.sq_mem_of_index_two hidx φ) m
  have hφ : φ ∈ I := by
    have h : φ = (φ ^ (2 * m))⁻¹ * φ ^ (2 * m + 1) := by group
    rw [h, hm, mul_one]
    exact I.inv_mem hsq
  obtain ⟨g, rfl⟩ := hφ
  exact ⟨g, fun x => MulAut.conj_apply g x⟩

theorem move_of_transitive
    (htr : ∀ (T : Sylow 3 K) (a b : K), a ∈ (T : Subgroup K) → b ∈ (T : Subgroup K) → a ≠ 1 →
      b ≠ 1 → ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * a * n⁻¹ = b)
    (h9 : ∀ T : Sylow 3 K, 3 < Nat.card (T : Subgroup K)) (T : Sylow 3 K) (a : K)
    (ha : a ∈ (T : Subgroup K)) (hoa : orderOf a = 3) :
    ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * a * n⁻¹ ∉ zpowers a := by
  obtain ⟨b, hbT, hba⟩ : ∃ b ∈ (T : Subgroup K), b ∉ zpowers a := by
    by_contra! h
    have hle := Subgroup.card_le_of_le (show (T : Subgroup K) ≤ zpowers a from h)
    rw [Nat.card_zpowers, hoa] at hle
    have := h9 T
    omega
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at hoa; omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  obtain ⟨n, hn, hnab⟩ := htr T a b ha hbT ha1 hb1
  exact ⟨n, hn, hnab ▸ hba⟩

theorem move_of_irred
    (hirr : ∀ (T : Sylow 3 K) (V : Subgroup K), V ≤ (T : Subgroup K) → V ≠ ⊥ →
      normalizer ((T : Subgroup K) : Set K) ≤ normalizer (V : Set K) → V = T)
    (h9 : ∀ T : Sylow 3 K, 3 < Nat.card (T : Subgroup K)) (T : Sylow 3 K) (a : K)
    (ha : a ∈ (T : Subgroup K)) (hoa : orderOf a = 3) :
    ∃ n ∈ normalizer ((T : Subgroup K) : Set K), n * a * n⁻¹ ∉ zpowers a := by
  by_contra! h
  have hconj : ∀ m ∈ normalizer ((T : Subgroup K) : Set K), ∀ x ∈ zpowers a,
      m * x * m⁻¹ ∈ zpowers a := by
    intro m hm x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : m * a ^ k * m⁻¹ = (m * a * m⁻¹) ^ k := by
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    rw [this]
    exact Subgroup.zpow_mem _ (h m hm) k
  have hN : normalizer ((T : Subgroup K) : Set K) ≤
      normalizer ((zpowers a : Subgroup K) : Set K) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj m hm x, fun hx => ?_⟩
    have := hconj m⁻¹ (Subgroup.inv_mem _ hm) _ hx
    simpa [mul_assoc] using this
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at hoa; omega
  have hV := hirr T (zpowers a) ((Subgroup.zpowers_le).mpr ha)
    (fun h => ha1 (by rw [← Subgroup.mem_bot, ← h]; exact Subgroup.mem_zpowers a)) hN
  have := h9 T
  rw [← hV, Nat.card_zpowers, hoa] at this
  omega

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
