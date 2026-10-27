module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Claim1
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Models5

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

namespace InH

variable {G : Type} [Group G] [Finite G] {x : G} {T V H : Subgroup G} {f : G}

theorem comm_mem_of_central {H₀ V : Subgroup G} (hY : IsYGroup ↥H₀)
    (hna : ∃ a ∈ H₀, ∃ b ∈ H₀, a * b ≠ b * a) (hVH₀ : V ≤ H₀) (hV4 : Nat.card V = 4)
    (hVc : ∀ v ∈ V, ∀ c ∈ H₀, v * c = c * v) :
    Nat.card H₀ = 64 ∧ ∀ a ∈ H₀, ∀ b ∈ H₀, a * b * a⁻¹ * b⁻¹ ∈ V := by
  have hna' : ∃ a b : ↥H₀, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨h64, hcomm, hcen⟩ := IsYGroup.nonabelian_facts hY hna'
  refine ⟨h64, ?_⟩
  have hZ : Nat.card (Subgroup.center ↥H₀) ≤ 4 := by
    apply hcen
    intro z hz c
    exact ((Subgroup.mem_center_iff.1 hz) c).symm
  let V' : Subgroup ↥H₀ := V.subgroupOf H₀
  have hV'Z : V' ≤ Subgroup.center ↥H₀ := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact (hVc v hv c c.2).symm
  have hV'card : Nat.card V' = 4 := by
    rw [← hV4]; exact Nat.card_congr (subgroupOfEquivOfLe hVH₀).toEquiv
  have hZV' : V' = Subgroup.center ↥H₀ := Subgroup.eq_of_le_of_card_ge hV'Z (by omega)
  intro a ha b hb
  have hc : (⁅(⟨a, ha⟩ : ↥H₀), (⟨b, hb⟩ : ↥H₀)⁆ : ↥H₀) ∈ Subgroup.center ↥H₀ := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact (hcomm _ _ c).symm
  rw [← hZV'] at hc
  exact hc

theorem claim1 (h9 : IG_9_16) (h : Out12 G x T V) (hI : InH x V H f)
    (hiv1 : Hzero H f ⊓ zpowers x = ⊥) (hiv2 : Hzero H f ⊔ zpowers x = H)
    (hiv3 : ∀ g ∈ H, ∀ q ∈ Hzero H f, g * q * g⁻¹ ∈ Hzero H f) (hiv4 : IsYGroup ↥(Hzero H f))
    {g : G} (hgN : g ∈ normalizer (V : Set G)) (hgH : g ∈ normalizer (H : Set G)) :
    cj g (Hzero H f) = Hzero H f := by
  set H₀ := Hzero H f with hH₀
  have hxH₀ : x ∉ H₀ := x_not_mem_of_inf h hiv1
  have hcardH : Nat.card H = 2 * Nat.card H₀ := card_H_of h hiv1 hiv2 hiv3 hI
  have hVH₀ : V ≤ H₀ := V_le_Hzero h hI
  have hV4 : Nat.card V = 4 := h.V_four.2
  have hH₀H : H₀ ≤ H := hiv2 ▸ le_sup_left
  obtain ⟨n, hn1, hn⟩ := IsYGroup.card_pow4 hiv4
  have hgn : ∀ s : G, s ∈ H → g * s * g⁻¹ ∈ H := fun s hs => (mem_normalizer_iff.1 hgH s).1 hs
  by_cases hn1' : n = 1
  ·
    have hH₀V : H₀ = V := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hVH₀
      rw [hn, hn1', hV4]; norm_num
    ext s
    rw [mem_cj]
    have := (mem_normalizer_iff''.1 hgN s)
    rw [hH₀V]
    exact this.symm
  · have hn2 : 2 ≤ n := by omega
    have h16 : 16 ≤ Nat.card H₀ := by
      rw [hn]
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    by_contra hne
    set H₁ := cj g H₀ with hH₁
    have hH₁H : H₁ ≤ H := cj_le hgn hH₀H
    have hcard : Nat.card H₁ = Nat.card H₀ := card_cj g H₀
    have hne' : H₁ ≠ H₀ := hne
    have hx2 : x * x = 1 := h.x_sq
    have hxH : x ∈ H := hI.x_mem
    have hCx : Nat.card ↥(H ⊓ centralizer ({x} : Set G)) = 8 := by
      rw [InH.C_H_x h hI]; exact h.card_EV
    by_cases hab : ∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a
    ·
      have hle := claim1_core (N₀ := ⊥) h9 hx2 hxH hxH₀ hiv2 hiv3 bot_le
        (fun h' _ n hn' => by rw [Subgroup.mem_bot] at hn' ⊢; rw [hn']; group) hCx hH₁H hcard hne'
        (fun a ha b hb => by
          rw [Subgroup.mem_bot]
          rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, hab a ha b hb])
        (fun a ha b hb => by
          rw [Subgroup.mem_bot]
          obtain ⟨a₀, ha₀, rfl⟩ : ∃ a₀ ∈ H₀, a = g * a₀ * g⁻¹ := by
            refine ⟨g⁻¹ * a * g, (mem_cj.1 ha), by group⟩
          obtain ⟨b₀, hb₀, rfl⟩ : ∃ b₀ ∈ H₀, b = g * b₀ * g⁻¹ := by
            refine ⟨g⁻¹ * b * g, (mem_cj.1 hb), by group⟩
          have := hab a₀ ha₀ b₀ hb₀
          calc g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) * (g * a₀ * g⁻¹)⁻¹ * (g * b₀ * g⁻¹)⁻¹
              = g * (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) * g⁻¹ := by group
            _ = 1 := by
              rw [show a₀ * b₀ * a₀⁻¹ * b₀⁻¹ = 1 by rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, this]]
              group)
      simp at hle
      omega
    ·
      push Not at hab
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hab
      have hVc : ∀ v ∈ V, ∀ c ∈ H₀, v * c = c * v := fun v hv c hc =>
        mem_centralizer_iff.1 (hI.H_le (hH₀H hc)) v hv
      obtain ⟨h64, hcomm⟩ := comm_mem_of_central hiv4 ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ hVH₀ hV4 hVc
      have hVH : V ≤ H := hVH₀.trans hH₀H
      have hle := claim1_core (N₀ := V) h9 hx2 hxH hxH₀ hiv2 hiv3 hVH
        (fun h' hh' n hn' => by
          have := mem_centralizer_iff.1 (hI.H_le hh') n hn'
          rw [show h' * n * h'⁻¹ = n by rw [← this]; group]
          exact hn') hCx hH₁H hcard hne' hcomm
        (fun a ha b hb => by
          obtain ⟨a₀, ha₀, rfl⟩ : ∃ a₀ ∈ H₀, a = g * a₀ * g⁻¹ := ⟨g⁻¹ * a * g, mem_cj.1 ha, by group⟩
          obtain ⟨b₀, hb₀, rfl⟩ : ∃ b₀ ∈ H₀, b = g * b₀ * g⁻¹ := ⟨g⁻¹ * b * g, mem_cj.1 hb, by group⟩
          have hc := hcomm a₀ ha₀ b₀ hb₀
          have e : g * a₀ * g⁻¹ * (g * b₀ * g⁻¹) * (g * a₀ * g⁻¹)⁻¹ * (g * b₀ * g⁻¹)⁻¹ =
              g * (a₀ * b₀ * a₀⁻¹ * b₀⁻¹) * g⁻¹ := by group
          rw [e]
          exact (mem_normalizer_iff.1 hgN _).1 hc)
      rw [h64, hV4] at hle
      omega

end InH

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
