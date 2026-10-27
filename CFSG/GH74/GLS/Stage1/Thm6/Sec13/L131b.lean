module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.InH

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_sup_zpowers_invol {N : Subgroup G} {x : G} (hx : x * x = 1)
    (hN : ∀ q ∈ N, x * q * x⁻¹ ∈ N) {g : G} :
    g ∈ N ⊔ zpowers x ↔ ∃ q ∈ N, g = q ∨ g = q * x := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ q ∈ N, g = q ∨ g = q * x}
        one_mem' := ⟨1, N.one_mem, Or.inl rfl⟩
        mul_mem' := by
          intro a b ha hb
          obtain ⟨u, hu, ha | ha⟩ := ha <;> obtain ⟨w, hw, hb | hb⟩ := hb <;> rw [ha, hb]
          · exact ⟨u * w, N.mul_mem hu hw, Or.inl rfl⟩
          · exact ⟨u * w, N.mul_mem hu hw, Or.inr (by rw [mul_assoc])⟩
          · refine ⟨u * (x * w * x⁻¹), N.mul_mem hu (hN w hw), Or.inr ?_⟩
            group
          · refine ⟨u * (x * w * x⁻¹), N.mul_mem hu (hN w hw), Or.inl ?_⟩
            calc u * x * (w * x) = u * (x * w * x) := by group
              _ = u * (x * w * x⁻¹) := by rw [hxi]
        inv_mem' := by
          intro a ha
          obtain ⟨u, hu, ha | ha⟩ := ha <;> rw [ha]
          · exact ⟨u⁻¹, N.inv_mem hu, Or.inl rfl⟩
          · refine ⟨x * u⁻¹ * x⁻¹, hN _ (N.inv_mem hu), Or.inr ?_⟩
            calc (u * x)⁻¹ = x⁻¹ * u⁻¹ := by group
              _ = x * u⁻¹ := by rw [hxi]
              _ = x * u⁻¹ * x⁻¹ * x := by group }
    have hle : N ⊔ zpowers x ≤ S := by
      refine sup_le (fun v hv => ⟨v, hv, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, N.one_mem, Or.inr (by simp)⟩
    exact hle hg
  · rintro ⟨q, hq, hg | hg⟩ <;> rw [hg]
    · exact Subgroup.mem_sup_left hq
    · exact (N ⊔ zpowers x).mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right (mem_zpowers x))

theorem card_sup_zpowers_invol {N : Subgroup G} {x : G} (hx : x * x = 1)
    (hN : ∀ q ∈ N, x * q * x⁻¹ ∈ N) (hxN : x ∉ N) :
    Nat.card ↥(N ⊔ zpowers x) = 2 * Nat.card N := by
  have hle : N ≤ N ⊔ zpowers x := le_sup_left
  have hrel : N.relIndex (N ⊔ zpowers x) = 2 := by
    have hdvd : N.relIndex (N ⊔ zpowers x) ∣ 2 := by
      rw [relIndex_dvd_two_iff]
      refine ⟨x, Subgroup.mem_sup_right (mem_zpowers x), ?_⟩
      intro b hb
      obtain ⟨q, hq, hb' | hb'⟩ := (mem_sup_zpowers_invol hx hN).1 hb
      · right; rw [hb']; exact hq
      · left
        have : q * x * x = q := by rw [mul_assoc, hx, mul_one]
        rw [hb', this]; exact hq
    have hne : N.relIndex (N ⊔ zpowers x) ≠ 1 := by
      intro h1
      rw [relIndex_eq_one] at h1
      exact hxN (h1 (Subgroup.mem_sup_right (mem_zpowers x)))
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have := relIndex_mul_card N (N ⊔ zpowers x)
  rw [inf_of_le_left hle, hrel] at this
  exact this.symm

namespace InH

variable {x : G} {T V H : Subgroup G} {f : G}

theorem x_not_mem_of_inf (h : Out12 G x T V) {N : Subgroup G} (hN : N ⊓ zpowers x = ⊥) :
    x ∉ N := by
  intro hx
  have : x ∈ N ⊓ zpowers x := ⟨hx, mem_zpowers x⟩
  rw [hN] at this
  exact h.x_ne ((Subgroup.mem_bot).1 this)

theorem card_H_of [Finite G] (h : Out12 G x T V) {H₀ : Subgroup G}
    (h1 : H₀ ⊓ zpowers x = ⊥) (h2 : H₀ ⊔ zpowers x = H) (h3 : ∀ g ∈ H, ∀ q ∈ H₀, g * q * g⁻¹ ∈ H₀)
    (hI : InH x V H f) : Nat.card H = 2 * Nat.card H₀ := by
  rw [← h2]
  apply card_sup_zpowers_invol h.x_sq
  · intro q hq
    exact h3 x (hI.x_mem) q hq
  · exact x_not_mem_of_inf h h1

theorem V_le_Hzero [Finite G] (h : Out12 G x T V) (hI : InH x V H f) : V ≤ Hzero H f := by
  obtain ⟨k, hk⟩ := hI.f3
  have hVn : ∀ v ∈ V, f * v * f⁻¹ ∈ V := fun v hv => (mem_normalizer_iff.1 hI.f_N v).1 hv
  have hnc : ∃ v ∈ V, f * v * f⁻¹ ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hI.f_C
    rw [mem_centralizer_iff]
    intro v hv
    have := hcon v hv
    calc v * f = (f * v * f⁻¹) * f := by rw [this]
      _ = f * v := by group
  have hfix := fix_free_four V f k hk hVn h.V_four.2 hnc
  let K : Subgroup G := ⁅zpowers f, V⁆
  have hKV : K ≤ V := by
    rw [commutator_le]
    intro g hg v hv
    obtain ⟨m, rfl⟩ := hg
    have hmv : ∀ m : ℤ, ∀ v ∈ V, f ^ m * v * (f ^ m)⁻¹ ∈ V := fun m v hv =>
      (mem_normalizer_iff.1 (zpow_mem hI.f_N m) v).1 hv
    have e : ⁅f ^ m, v⁆ = (f ^ m * v * (f ^ m)⁻¹) * v⁻¹ := by
      simp only [commutatorElement_def]
    rw [e]
    exact V.mul_mem (hmv m v hv) (V.inv_mem hv)
  have hKn : ∀ k ∈ K, f * k * f⁻¹ ∈ K := by
    have hVn' : f ∈ normalizer (V : Set G) := hI.f_N
    have := mem_normalizer_commutator hVn'
    intro k hk
    exact (mem_normalizer_iff.1 this k).1 hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := card_fix_modEq (p := 3) (K : Set G) f k hk hKn
  have hfixK : Nat.card {v : (K : Set G) // f * (v : G) * f⁻¹ = v} = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨1, K.one_mem⟩, by simp⟩, ?_⟩
    intro w
    apply Subtype.ext; apply Subtype.ext
    exact hfix w.1 (hKV w.1.2) w.2
  rw [hfixK] at hmod
  have hdvd : Nat.card K ∣ 4 := by
    rw [← h.V_four.2]
    exact Subgroup.card_dvd_of_le hKV
  have hcases : Nat.card K = 1 ∨ Nat.card K = 4 := by
    have hle4 : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hm : Nat.card K % 3 = 1 := by
      unfold Nat.ModEq at hmod; simpa using hmod
    interval_cases hK : Nat.card K <;> simp_all
  rcases hcases with h1 | h4
  · exfalso
    have hbot : K = ⊥ := by
      rw [Subgroup.eq_bot_iff_card, h1]
    apply hI.f_C
    rw [mem_centralizer_iff]
    intro v hv
    have := (commutator_eq_bot_iff_le_centralizer.1 hbot)
    have hf' : f ∈ centralizer (V : Set G) := this (mem_zpowers f)
    exact mem_centralizer_iff.1 hf' v hv
  · have hKeq : K = V := Subgroup.eq_of_le_of_card_ge hKV (by rw [h4, h.V_four.2])
    have hcm : ⁅V, zpowers f⁆ = K := by rw [commutator_comm]
    calc V = ⁅V, zpowers f⁆ := by rw [hcm, hKeq]
      _ ≤ ⁅H, zpowers f⁆ := Subgroup.commutator_mono (le_trans V_le_EV hI.E_le) le_rfl

end InH

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
