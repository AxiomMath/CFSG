module

public import CFSG.CGT.T75P.DecB
public import CFSG.CGT.T75I.CenCM
public import CFSG.CGT.T75P.Aut
public import CFSG.CGT.T75P.DecA
public import CFSG.CGT.T75P.Lift

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n : ℕ}

theorem mem_normD_of_mem_normIn (hc : Sec6Ctx T T₁ n 1) {ℓ : G} (hℓ : ℓ ∈ normIn T₁ T)
    (hℓ1 : ℓ ≠ 1) : ℓ ∈ classD T ∧ ℓ ∈ Subgroup.normalizer (T : Set G) ∧ ℓ ∉ T := by
  obtain ⟨s, hs⟩ := hc.hy.pair.conj
  have hℓT₁ : ℓ ∈ T₁ := (mem_normIn.1 hℓ).1
  refine ⟨mem_classD_of_mem_conjSubgroup (k := s) (hs ▸ hℓT₁) hℓ1, (mem_normIn.1 hℓ).2, fun hlT => ?_⟩
  have : ℓ ∈ T ⊓ T₁ := Subgroup.mem_inf.2 ⟨hlT, hℓT₁⟩
  rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
  exact hℓ1 this

theorem exists_ne_one_mem_normIn [Finite G] (hc : Sec6Ctx T T₁ n 1) :
    ∃ ℓ ∈ normIn T₁ T, ℓ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card (normIn T₁ T) = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    exact hcon l hl
  rw [hc.card_normIn_swap, hc.card_normIn] at h1
  have hn : 2 ≤ n := by
    have h4 := hc.hy.card
    rw [hc.hT] at h4
    by_contra hlt
    push Not at hlt
    interval_cases n <;> simp at h4
  have : (2 ^ 1) ^ (n - 1) ≠ 1 := by
    have : 1 ≤ n - 1 := by omega
    have h2 : 2 ≤ (2 ^ 1) ^ (n - 1) := by
      calc 2 = (2 ^ 1) ^ 1 := by norm_num
        _ ≤ (2 ^ 1) ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) this
    omega
  exact this h1

theorem exists_mul_mem_centralizer_hSub (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n 1)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n 1) {k : ℕ} (ch : TransvChain n k) {c : G}
    (hcC : c ∈ Subgroup.centralizer (T : Set G)) :
    ∃ t ∈ T, c * t ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
  classical
  have : Finite G := hc.finite
  obtain ⟨hTH, hHN, hHnorm⟩ := hSub_data T T₁
  have hHC := inf_centralizer_eq_of_natural hTH hHN hnat
  have hTab := hc.hy.pair.wc.1
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => elemAbelian_mul_comm hTab ha hb
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  have hnorm : (T.subgroupOf (hSub T (normIn T₁ T))).Normal := hN
  obtain ⟨ℓ, hℓ, hℓ1⟩ := exists_ne_one_mem_normIn hc
  obtain ⟨hℓD, hℓN, hℓT⟩ := mem_normD_of_mem_normIn hc hℓ hℓ1
  have hℓH : ℓ ∈ hSub T (normIn T₁ T) := le_hSub hℓ
  have hu₀ := isTransvection_of_mem_normIn h63 hc e φ hcompat hℓ hℓ1 hℓH
  have lifts : ∀ i, ∃ x ∈ classD T, ∃ hxH : x ∈ hSub T (normIn T₁ T),
      e (QuotientGroup.mk (⟨x, hxH⟩ : ↥(hSub T (normIn T₁ T)))) = ch.E i := fun i =>
    exists_lift_transvection_n e hℓD hℓH hu₀ (ch.isTrans i)
  choose x hxD hxH hxE using lifts
  have hxT : ∀ i, x i ∉ T := fun i hT => (ch.isTrans i).1 (by
    rw [← hxE i]
    have : (QuotientGroup.mk (⟨x i, hxH i⟩ : ↥(hSub T (normIn T₁ T))) :
        ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T))) = 1 :=
      (QuotientGroup.eq_one_iff (N := T.subgroupOf (hSub T (normIn T₁ T)))
        (⟨x i, hxH i⟩ : ↥(hSub T (normIn T₁ T)))).2 (Subgroup.mem_subgroupOf.2 hT)
    rw [this, map_one])
  have pw : ∀ i, ∃ s ∈ T, c * s ∈ Subgroup.centralizer ({x i} : Set G) := fun i =>
    exists_mul_mem_centralizer_single h62 h63 hc hHN hHnorm hHC hcC ⟨hxD i, hHN (hxH i)⟩ (hxT i)
      (hxH i)
  choose s hsT hsC using pw
  let a : Fin k → (Fin n → GaloisField 2 1) := fun i =>
    Multiplicative.toAdd (φ ⟨s i, hsT i⟩)
  let v₀ : Fin n → GaloisField 2 1 := fun j =>
    if h : ∃ i, ch.axis i = j then a h.choose j else 0
  have hv₀ : ∀ i, v₀ (ch.axis i) = a i (ch.axis i) := by
    intro i
    have h : ∃ i', ch.axis i' = ch.axis i := ⟨i, rfl⟩
    have hch : h.choose = i := ch.axis_inj h.choose_spec
    simp only [v₀, h, ↓reduceDIte]
    rw [hch]
  let t₀ : ↥T := φ.symm (Multiplicative.ofAdd v₀)
  have hφt₀ : φ t₀ = Multiplicative.ofAdd v₀ := φ.apply_symm_apply _
  have hcent : ∀ i, x i * ((s i)⁻¹ * (t₀ : G)) = ((s i)⁻¹ * (t₀ : G)) * x i := by
    intro i
    let τ : ↥T := (⟨s i, hsT i⟩ : ↥T)⁻¹ * t₀
    have hτ : (τ : G) = (s i)⁻¹ * (t₀ : G) := rfl
    have hmem : x i * (τ : G) * (x i)⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN (hxH i)) τ.2
    have hφτ : Multiplicative.toAdd (φ τ) = v₀ - a i := by
      show Multiplicative.toAdd (φ ((⟨s i, hsT i⟩ : ↥T)⁻¹ * t₀)) = _
      rw [map_mul, map_inv, hφt₀, toAdd_mul, toAdd_inv, toAdd_ofAdd]
      simp [a, sub_eq_add_neg, add_comm]
    have hcoord : Multiplicative.toAdd (φ τ) (ch.axis i) = 0 := by
      rw [hφτ]
      simp [hv₀ i]
    have hfix := ch.fixed_of i _ hcoord
    have h1 := hcompat ⟨x i, hxH i⟩ τ hmem
    rw [hxE i, hfix, ofAdd_toAdd] at h1
    have h2 : (⟨x i * (τ : G) * (x i)⁻¹, hmem⟩ : ↥T) = τ := φ.injective h1
    have h3 : x i * (τ : G) * (x i)⁻¹ = τ := congrArg Subtype.val h2
    rw [← hτ]
    calc x i * (τ : G) = x i * (τ : G) * (x i)⁻¹ * x i := by group
      _ = (τ : G) * x i := by rw [h3]
  let z : G := c * (t₀ : G)
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.centralizer (T : Set G)).mul_mem hcC ?_
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact hTc t ht _ t₀.2
  have hzT : ∀ t ∈ T, t * z = z * t := fun t ht =>
    (Subgroup.mem_centralizer_iff.1 hzC) t ht
  have hzx : ∀ i, x i * z = z * x i := by
    intro i
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hsC i)
    have h2 := hcent i
    calc x i * z = x i * (c * s i) * ((s i)⁻¹ * (t₀ : G)) := by simp only [z]; group
      _ = (c * s i) * x i * ((s i)⁻¹ * (t₀ : G)) := by rw [← h1]
      _ = (c * s i) * (x i * ((s i)⁻¹ * (t₀ : G))) := by group
      _ = (c * s i) * (((s i)⁻¹ * (t₀ : G)) * x i) := by rw [h2]
      _ = z * x i := by simp only [z]; group
  have hodd := odd_index_centralizer_of_chain e ch x hxH hxE hzT hzx
  obtain ⟨a', ha'T, ha'⟩ := CFSG.CGT.T75I.exists_fixed_of_odd_index (X := hSub T (normIn T₁ T))
    (A := T) (fun a ha => elemAbelian_mul_self hTab ha) hTc
    (fun y hy a ha => conj_mem_of_mem_normalizer (hHN hy) ha) (u := z)
    (fun y hy => by
      have hy' : y⁻¹ ∈ hSub T (normIn T₁ T) := (hSub T (normIn T₁ T)).inv_mem hy
      have := T.inv_mem (comm_mem_T hHN hHnorm hHC hy' hzC)
      have e1 : z⁻¹ * (y * z * y⁻¹) = (y⁻¹⁻¹ * z⁻¹ * y⁻¹ * z)⁻¹ := by group
      rw [e1]
      exact this)
    (S := (Subgroup.centralizer ({z} : Set G)).subgroupOf (hSub T (normIn T₁ T)))
    (fun s' hs' => by
      have h1 : (s' : G) * z = z * (s' : G) :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hs')
      calc (s' : G) * z * (s' : G)⁻¹ = z * (s' : G) * (s' : G)⁻¹ := by rw [h1]
        _ = z := by group)
    hodd
  refine ⟨(t₀ : G) * a', T.mul_mem t₀.2 ha'T, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := ha' y hy
  have h2 : y * (z * a') = (z * a') * y := by
    calc y * (z * a') = y * (z * a') * y⁻¹ * y := by group
      _ = (z * a') * y := by rw [h1]
  calc y * (c * ((t₀ : G) * a')) = y * (z * a') := by simp only [z]; group
    _ = (z * a') * y := h2
    _ = c * ((t₀ : G) * a') * y := by simp only [z]; group

end CFSG.CGT.T75P
