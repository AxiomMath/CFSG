module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard

open Subgroup

variable {G : Type*} [Group G]

theorem conj_mem_zpowers_mul_self {s g c : G} (hg : g * s * g⁻¹ ∈ zpowers s)
    (hc : c ∈ zpowers (s * s)) : g * c * g⁻¹ ∈ zpowers (s * s) := by
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hg
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
  refine mem_zpowers_iff.mpr ⟨m * j, ?_⟩
  have h2 : g * (s * s) * g⁻¹ = (s * s) ^ m := by
    rw [(Commute.refl s).mul_zpow, hm]
    group
  rw [← conj_zpow, h2, zpow_mul]

theorem not_mem_zpowers_mul_self {s : G} {a : ℕ} (hs : orderOf s = 2 ^ a) (ha : 1 ≤ a) :
    s ∉ zpowers (s * s) := by
  intro h
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp h
  have h1 : s ^ (2 * j - 1) = 1 := by
    rw [zpow_sub_one, zpow_mul, zpow_two, hj, mul_inv_cancel]
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
  have h4 : (2 : ℤ) ∣ 2 * j - 1 := by
    refine dvd_trans ?_ h2
    rw [hs]
    push_cast
    exact dvd_pow_self 2 (by omega)
  omega

theorem mem_zpowers_mul_self_or {s b : G} (hb : b ∈ zpowers s) :
    b ∈ zpowers (s * s) ∨ b * s⁻¹ ∈ zpowers (s * s) := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hb
  rcases Int.even_or_odd m with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact Or.inl (mem_zpowers_iff.mpr ⟨r, by rw [(Commute.refl s).mul_zpow, zpow_add]⟩)
  · refine Or.inr (mem_zpowers_iff.mpr ⟨r, ?_⟩)
    rw [zpow_add_one, mul_inv_cancel_right, zpow_mul, zpow_two]

theorem mul_conj_inv_mem_zpowers_mul_self {s g : G} (hg : g * s * g⁻¹ ∈ zpowers s)
    (hg' : g⁻¹ * s * g⁻¹⁻¹ ∈ zpowers s) (hns : s ∉ zpowers (s * s)) :
    s * (g * s⁻¹ * g⁻¹) ∈ zpowers (s * s) := by
  have e : g * s⁻¹ * g⁻¹ = (g * s * g⁻¹)⁻¹ := by group
  rw [e]
  rcases mem_zpowers_mul_self_or hg with h | h
  · exfalso
    apply hns
    have h' := conj_mem_zpowers_mul_self hg' h
    have e' : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    rwa [e'] at h'
  · have e' : s * (g * s * g⁻¹)⁻¹ = (g * s * g⁻¹ * s⁻¹)⁻¹ := by group
    rw [e']
    exact inv_mem h

theorem exists_parity_character {X Kt U Sg : Subgroup G} {s : G} {a : ℕ}
    (hKtX : Kt ≤ X) (hUX : U ≤ X) (hSgX : Sg ≤ X) (hs : orderOf s = 2 ^ a) (ha : 1 ≤ a)
    (hSg : Sg = zpowers s) (hKt : ∀ h ∈ X, ∀ k ∈ Kt, h * k * h⁻¹ ∈ Kt)
    (hU : ∀ u ∈ U, u * s * u⁻¹ ∈ Sg)
    (hdec : ∀ h ∈ X, ∃ k ∈ Kt, ∃ b ∈ Sg, ∃ u ∈ U, h = k * b * u)
    (huniq : ∀ k ∈ Kt, ∀ b ∈ Sg, ∀ u ∈ U, k * b * u = 1 → b = 1) :
    ∃ φ : X →* Multiplicative (ZMod 2), (∀ y : X, (y : G) ∈ Kt → φ y = 1) ∧
      (∀ y : X, (y : G) ∈ U → φ y = 1) ∧
      (∀ y : X, (y : G) = s → φ y = Multiplicative.ofAdd 1) := by
  classical
  subst hSg
  have hsX : s ∈ X := hSgX (mem_zpowers s)
  have hTS : ∀ c ∈ zpowers (s * s), c ∈ zpowers s := fun c hc =>
    (zpowers_le.mpr (mul_mem (mem_zpowers s) (mem_zpowers s))) hc
  have hns : s ∉ zpowers (s * s) := not_mem_zpowers_mul_self hs ha
  have hUT : ∀ u ∈ U, ∀ c ∈ zpowers (s * s), u * c * u⁻¹ ∈ zpowers (s * s) :=
    fun u hu c hc => conj_mem_zpowers_mul_self (hU u hu) hc
  have hUs : ∀ u ∈ U, s * (u * s⁻¹ * u⁻¹) ∈ zpowers (s * s) := fun u hu =>
    mul_conj_inv_mem_zpowers_mul_self (hU u hu) (hU u⁻¹ (inv_mem hu)) hns
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, ∀ n, n ∈ N ↔
      ∃ k ∈ Kt, ∃ c ∈ zpowers (s * s), ∃ u ∈ U, n = k * c * u := by
    refine ⟨{ carrier := {n | ∃ k ∈ Kt, ∃ c ∈ zpowers (s * s), ∃ u ∈ U, n = k * c * u}
              mul_mem' := ?_
              one_mem' := ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
              inv_mem' := ?_ }, fun n => Iff.rfl⟩
    · rintro _ _ ⟨k, hk, c, hc, u, hu, rfl⟩ ⟨k', hk', c', hc', u', hu', rfl⟩
      refine ⟨k * c * u * k' * (k * c * u)⁻¹ * k, ?_, c * (u * c' * u⁻¹), ?_, u * u', ?_, ?_⟩
      · have hX : k * c * u ∈ X := mul_mem (mul_mem (hKtX hk) (hSgX (hTS c hc))) (hUX hu)
        exact mul_mem (hKt _ hX k' hk') hk
      · exact mul_mem hc (hUT u hu c' hc')
      · exact mul_mem hu hu'
      · group
    · rintro _ ⟨k, hk, c, hc, u, hu, rfl⟩
      refine ⟨(u⁻¹ * c⁻¹) * k⁻¹ * (u⁻¹ * c⁻¹)⁻¹, ?_, u⁻¹ * c⁻¹ * u⁻¹⁻¹, ?_, u⁻¹,
        inv_mem hu, ?_⟩
      · exact hKt _ (mul_mem (hUX (inv_mem hu)) (hSgX (hTS _ (inv_mem hc)))) _ (inv_mem hk)
      · exact hUT _ (inv_mem hu) _ (inv_mem hc)
      · group
  have hKtN : ∀ k ∈ Kt, k ∈ N := fun k hk =>
    (hN k).mpr ⟨k, hk, 1, one_mem _, 1, one_mem _, by simp⟩
  have hUN : ∀ u ∈ U, u ∈ N := fun u hu =>
    (hN u).mpr ⟨1, one_mem _, 1, one_mem _, u, hu, by simp⟩
  have hssN : s * s ∈ N := (hN _).mpr ⟨1, one_mem _, s * s, mem_zpowers _, 1, one_mem _, by simp⟩
  have hsN : s ∉ N := by
    intro h
    obtain ⟨k, hk, c, hc, u, hu, hsk⟩ := (hN s).mp h
    have hb : u * s⁻¹ * u⁻¹ ∈ zpowers s := by
      have e : u * s⁻¹ * u⁻¹ = (u * s * u⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (hU u hu)
    have h1 : k * (c * (u * s⁻¹ * u⁻¹)) * u = 1 := by
      calc k * (c * (u * s⁻¹ * u⁻¹)) * u = k * c * u * s⁻¹ := by group
        _ = 1 := by rw [← hsk, mul_inv_cancel]
    have h2 := huniq k hk _ (mul_mem (hTS c hc) hb) u hu h1
    have h3 : s = u⁻¹ * c * u⁻¹⁻¹ := by
      rw [eq_inv_of_mul_eq_one_left h2]
      group
    have h5 := hUT u⁻¹ (inv_mem hu) c hc
    rw [← h3] at h5
    exact hns h5
  have hsconj : ∀ n ∈ N, s * n * s⁻¹ ∈ N := by
    intro n hn
    obtain ⟨k, hk, c, hc, u, hu, rfl⟩ := (hN n).mp hn
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    have hcs : s * (s * s) ^ j = (s * s) ^ j * s :=
      (((Commute.refl s).mul_right (Commute.refl s)).zpow_right j).eq
    refine (hN _).mpr ⟨s * k * s⁻¹, hKt s hsX k hk, (s * s) ^ j * (s * (u * s⁻¹ * u⁻¹)),
      mul_mem hc (hUs u hu), u, hu, ?_⟩
    calc s * (k * (s * s) ^ j * u) * s⁻¹
        = s * k * s⁻¹ * (s * (s * s) ^ j) * (u * s⁻¹ * u⁻¹) * u := by group
      _ = s * k * s⁻¹ * ((s * s) ^ j * (s * (u * s⁻¹ * u⁻¹))) * u := by
        rw [hcs]
        group
  have hdich : ∀ x ∈ X, x ∈ N ∨ x * s⁻¹ ∈ N := by
    intro x hx
    obtain ⟨k, hk, b, hb, u, hu, rfl⟩ := hdec x hx
    rcases mem_zpowers_mul_self_or hb with hb' | hb'
    · exact Or.inl ((hN _).mpr ⟨k, hk, b, hb', u, hu, rfl⟩)
    · refine Or.inr ((hN _).mpr
        ⟨k, hk, b * s⁻¹ * (s * (u * s⁻¹ * u⁻¹)), mul_mem hb' (hUs u hu), u, hu, ?_⟩)
      group
  refine ⟨MonoidHom.mk' (fun x : X => if (x : G) ∈ N then 1 else Multiplicative.ofAdd 1) ?_,
    ?_, ?_, ?_⟩
  · intro x y
    simp only [Subgroup.coe_mul]
    by_cases hx : (x : G) ∈ N <;> by_cases hy : (y : G) ∈ N
    · rw [ite_eq_left (N.mul_mem hx hy), ite_eq_left hx, ite_eq_left hy, mul_one]
    · have hxy : (x : G) * y ∉ N := fun h => hy (by simpa using N.mul_mem (N.inv_mem hx) h)
      rw [ite_eq_right hxy, ite_eq_left hx, ite_eq_right hy, one_mul]
    · have hxy : (x : G) * y ∉ N := fun h => hx (by simpa using N.mul_mem h (N.inv_mem hy))
      rw [ite_eq_right hxy, ite_eq_right hx, ite_eq_left hy, mul_one]
    · have hx' := (hdich x x.2).resolve_left hx
      have hy' := (hdich y y.2).resolve_left hy
      have hxy : (x : G) * y ∈ N := by
        have h := N.mul_mem (N.mul_mem hx' (hsconj _ hy')) hssN
        have e : (x : G) * s⁻¹ * (s * (y * s⁻¹) * s⁻¹) * (s * s) = x * y := by group
        rwa [e] at h
      rw [ite_eq_left hxy, ite_eq_right hx, ite_eq_right hy]
      rfl
  · intro y hy
    simp only [MonoidHom.mk'_apply]
    rw [ite_eq_left (hKtN _ hy)]
  · intro y hy
    simp only [MonoidHom.mk'_apply]
    rw [ite_eq_left (hUN _ hy)]
  · intro y hy
    simp only [MonoidHom.mk'_apply]
    rw [hy, ite_eq_right hsN]

end CFSG.OddStandard
