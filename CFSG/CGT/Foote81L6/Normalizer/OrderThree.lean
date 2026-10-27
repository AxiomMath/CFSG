module

public import CFSG.Quasithin.Background.B19Block
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

private theorem odd_card_zpowers_of_pow_three {x : MulAut V} (hx3 : x ^ 3 = 1) :
    Odd (Nat.card (Subgroup.zpowers x)) := by
  rw [Nat.card_zpowers]
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h | h <;>
    rw [h] <;> decide

theorem commV_zpowers_inf_eq [Finite V] (hV : ∀ v : V, v * v = 1) {x : MulAut V}
    (hx3 : x ^ 3 = 1) : commV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) = ⊥ := by
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  obtain ⟨-, hinf⟩ := B1.coprime_decomp hV' (odd_card_zpowers_of_pow_three hx3) (M := ⊤)
    (fun _ _ _ _ => trivial)
  rw [top_inf_eq, ← commV_eq_commSub] at hinf
  rw [inf_comm]
  exact hinf

theorem commV_zpowers_sup_eq [Finite V] (hV : ∀ v : V, v * v = 1) {x : MulAut V}
    (hx3 : x ^ 3 = 1) : commV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers x) = ⊤ := by
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  obtain ⟨hsup, -⟩ := B1.coprime_decomp hV' (odd_card_zpowers_of_pow_three hx3) (M := ⊤)
    (fun _ _ _ _ => trivial)
  rw [top_inf_eq, ← commV_eq_commSub] at hsup
  rw [sup_comm]
  exact hsup

theorem apply_mem_commV_zpowers {x : MulAut V} {v : V}
    (hv : v ∈ commV (Subgroup.zpowers x)) : x v ∈ commV (Subgroup.zpowers x) := by
  rw [commV_eq_commSub] at hv ⊢
  refine B1.commSub_smul_mem (M := ⊤) (M' := ⊤) x (fun z hz => ?_)
    (fun _ _ => Subgroup.mem_top _) v hv
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [show x * x ^ n * x⁻¹ = x ^ n by group]
  exact Subgroup.zpow_mem_zpowers x n

theorem mem_commV_zpowers [Finite V] (hV : ∀ v : V, v * v = 1) {x : MulAut V}
    (hx3 : x ^ 3 = 1) (hcard : Nat.card (commV (Subgroup.zpowers x)) = 4) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers x)) (hw1 : w ≠ 1) :
    (∀ v ∈ commV (Subgroup.zpowers x), v = 1 ∨ v = w ∨ v = x w ∨ v = x (x w)) ∧
      x w ≠ w ∧ x (x w) ≠ w ∧ x (x w) ≠ x w ∧ x w ≠ 1 ∧ x (x w) ≠ 1 := by
  have hinf := commV_zpowers_inf_eq hV hx3
  have hx3' : ∀ v : V, x (x (x v)) = v := by
    intro v
    have := congrArg (fun f : MulAut V => f v) hx3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfix : ∀ v ∈ commV (Subgroup.zpowers x), x v = v → v = 1 := by
    intro v hv hxv
    have hvfix : v ∈ fixV (Subgroup.zpowers x) := fun z hz => B1.zpowers_fix hxv z hz
    have : v ∈ commV (Subgroup.zpowers x) ⊓ fixV (Subgroup.zpowers x) := ⟨hv, hvfix⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact this
  have hxw : x w ≠ w := fun h => hw1 (hfix w hw h)
  have hxxw : x (x w) ≠ w := fun h => hxw (by
    have := hx3' w
    rw [h] at this
    exact this)
  have hxxw' : x (x w) ≠ x w := fun h => hxw (x.injective h)
  have hxw1 : x w ≠ 1 := fun h => hw1 (by rwa [map_eq_one_iff _ x.injective] at h)
  have hxxw1 : x (x w) ≠ 1 := fun h => hxw1 (by rwa [map_eq_one_iff _ x.injective] at h)
  refine ⟨?_, hxw, hxxw, hxxw', hxw1, hxxw1⟩
  have hsub : ({1, w, x w, x (x w)} : Set V) ⊆ (commV (Subgroup.zpowers x) : Set V) := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact (commV _).one_mem
    · exact hw
    · exact apply_mem_commV_zpowers hw
    · exact apply_mem_commV_zpowers (apply_mem_commV_zpowers hw)
  have hnc : ({1, w, x w, x (x w)} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hxxw'.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxw.symm, hxxw.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hw1.symm, hxw1.symm, hxxw1.symm⟩
  have hcY : (commV (Subgroup.zpowers x) : Set V).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hnc, hcY])
  intro v hv
  have hv' : v ∈ ({1, w, x w, x (x w)} : Set V) := by
    rw [heq]
    exact hv
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hv'

theorem eq_mul_of_inverted_two [Finite V] (hV : ∀ v : V, v * v = 1) {t₀ t₁ : MulAut V}
    {b₀ b₁ : V} (h₀ : IsTransvectionWith t₀ b₀) (h₀1 : t₀ ≠ 1) (h₁ : IsTransvectionWith t₁ b₁)
    (h₁1 : t₁ ≠ 1) (hb : b₀ ≠ b₁) {x : MulAut V} {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1)
    (hx1 : x ≠ 1) (hx₀ : t₀ * x * t₀⁻¹ = x⁻¹) (hx₁ : t₁ * x * t₁⁻¹ = x⁻¹) :
    x b₀ = b₀ * b₁ ∨ x (x b₀) = b₀ * b₁ := by
  have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
  obtain ⟨hb₀, -, hcard, hx3⟩ := B1.inverted_by_transvection hV' h₀ h₀1 hr hxr hx1 hx₀
  obtain ⟨hb₁, -, -, -⟩ := B1.inverted_by_transvection hV' h₁ h₁1 hr hxr hx1 hx₁
  rw [← commV_eq_commSub] at hb₀ hb₁ hcard
  obtain ⟨hmem, -⟩ := mem_commV_zpowers hV hx3 hcard hb₀ h₀.1
  rcases hmem (b₀ * b₁) ((commV _).mul_mem hb₀ hb₁) with h | h | h | h
  · exfalso
    apply hb
    calc b₀ = b₀ * (b₀ * b₁) := by rw [h, mul_one]
      _ = b₁ := by rw [← mul_assoc, hV b₀, one_mul]
  · exfalso
    apply h₁.1
    calc b₁ = b₀⁻¹ * (b₀ * b₁) := by group
      _ = b₀⁻¹ * b₀ := by rw [h]
      _ = 1 := inv_mul_cancel b₀
  · exact Or.inl h.symm
  · exact Or.inr h.symm

variable {X : Type*} [Group X]

theorem exists_central_inverted_of_transvection [Finite V] [Finite X] (hV : ∀ v : V, v * v = 1)
    {ρ : X →* MulAut V} (hρ : Function.Injective ρ) {d : X} (hd : IsTransvection (ρ d))
    {K : Subgroup X} (hK : Odd (Nat.card K)) (hdK : ∀ k ∈ K, d * k * d⁻¹ ∈ K) :
    ∃ x ∈ K, x ^ 3 = 1 ∧ d * x * d⁻¹ = x⁻¹ ∧ (∀ k ∈ K, k * x = x * k) ∧
      ∀ y ∈ K, d * y * d⁻¹ = y⁻¹ → y ∈ Subgroup.zpowers x := by
  classical
  have hoddK : ∀ y ∈ K, Odd (orderOf y) := fun y hy =>
    hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hy)
  by_cases hc : ∀ k ∈ K, k * d = d * k
  · refine ⟨1, K.one_mem, one_pow 3, by group, fun k _ => by group, ?_⟩
    intro y hy hyd
    have hyy : y = y⁻¹ := by
      rw [← hyd, ← hc y hy, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [← hyy]
        _ = 1 := mul_inv_cancel y
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · rw [orderOf_eq_one_iff.mp h]
      exact Subgroup.one_mem _
    · have := hoddK y hy
      rw [h] at this
      exact absurd this (by decide)
  · push Not at hc
    obtain ⟨k₀, hk₀, hk₀d⟩ := hc
    obtain ⟨ht1, w, htw⟩ := hd
    have hV' : ∀ v : V, v ^ 2 = 1 := fun v => by rw [pow_two]; exact hV v
    set Φ : Subgroup (MulAut V) := K.map ρ with hΦ
    have hΦodd : Odd (Nat.card Φ) := by
      rw [hΦ, Subgroup.card_map_of_injective hρ]
      exact hK
    haveI : Group.IsSolvable Φ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hΦodd
    have htΦ : ∀ f ∈ Φ, ρ d * f * (ρ d)⁻¹ ∈ Φ := by
      rintro _ ⟨k, hk, rfl⟩
      exact ⟨d * k * d⁻¹, hdK k hk, by simp [map_mul, map_inv]⟩
    have hnt : ∃ f ∈ Φ, f * ρ d ≠ ρ d * f := by
      refine ⟨ρ k₀, ⟨k₀, hk₀, rfl⟩, fun h => hk₀d (hρ ?_)⟩
      rw [map_mul, map_mul]
      exact h
    obtain ⟨x', hB⟩ := B19.exists_tvBlock hV' hΦodd htw ht1 htΦ hnt
    obtain ⟨x, hx, rfl⟩ := hB.mem
    refine ⟨x, hx, hρ (by rw [map_pow, hB.x3, map_one]),
      hρ (by rw [map_mul, map_mul, map_inv, map_inv, hB.inv]),
      fun k hk => hρ (by rw [map_mul, map_mul]; exact hB.central (ρ k) ⟨k, hk, rfl⟩), ?_⟩
    intro y hy hyd
    have h1 : ρ y ∈ Subgroup.zpowers (ρ x) := hB.inverted (ρ y) ⟨y, hy, rfl⟩ (by
      rw [← map_inv, ← map_mul, ← map_mul, hyd, map_inv])
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, hρ (by rw [map_zpow, hn])⟩

end CFSG.CGT.Foote81L6.Normalizer
