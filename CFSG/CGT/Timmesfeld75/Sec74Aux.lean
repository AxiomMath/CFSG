module

public import CFSG.CGT.Timmesfeld75.Sec74Swap
public import CFSG.CGT.Timmesfeld75.Sec74Fixed
public import CFSG.CGT.Timmesfeld75.Sec66Stmt
public import CFSG.CGT.Timmesfeld75.Sec7One

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.zalpha_facts (hc : Sec6Ctx T T₁ n m) {b α : G} (hb2 : b * b = 1)
    (hswap : conjSubgroup b T = T₁) (hα : α ∈ normIn T T₁) :
    α * (b * α * b) = (b * α * b) * α ∧ (α * (b * α * b)) * (α * (b * α * b)) = 1 ∧
      b * (α * (b * α * b)) * b = α * (b * α * b) := by
  have := hc.finite
  have hS3 := hc.sec3
  have hα' : b * α * b ∈ normIn T₁ T := mem_normIn_swap hb2 hswap hα
  have hcomm : α * (b * α * b) = (b * α * b) * α := hS3.cfg.comm_L_L₁ hα hα'
  have hα2 : α * α = 1 := elemAbelian_mul_self hc.hy.pair.wc.1 (normIn_le _ _ hα)
  have hα'2 : (b * α * b) * (b * α * b) = 1 :=
    elemAbelian_mul_self hS3.cfg.wc₁.1 (normIn_le _ _ hα')
  refine ⟨hcomm, ?_, ?_⟩
  · calc (α * (b * α * b)) * (α * (b * α * b))
        = α * ((b * α * b) * α) * (b * α * b) := by group
      _ = α * (α * (b * α * b)) * (b * α * b) := by rw [← hcomm]
      _ = (α * α) * ((b * α * b) * (b * α * b)) := by group
      _ = 1 := by rw [hα2, hα'2, one_mul]
  · calc b * (α * (b * α * b)) * b = b * α * b * α * (b * b) := by group
      _ = (b * α * b) * α := by rw [hb2, mul_one]
      _ = α * (b * α * b) := hcomm.symm

theorem Sec6Ctx.zalpha_ne_one (hc : Sec6Ctx T T₁ n m) {b α : G} (hb2 : b * b = 1)
    (hswap : conjSubgroup b T = T₁) (hα : α ∈ normIn T T₁) (hα1 : α ≠ 1) :
    α * (b * α * b) ≠ 1 := by
  have := hc.finite
  have hα' : b * α * b ∈ normIn T₁ T := mem_normIn_swap hb2 hswap hα
  intro h
  apply hα1
  have h1 : α = (b * α * b)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hT₁ : α ∈ T₁ := by
    rw [h1]
    exact T₁.inv_mem (normIn_le _ _ hα')
  have : α ∈ T ⊓ T₁ := ⟨normIn_le _ _ hα, hT₁⟩
  rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at this
  exact this

theorem Sec6Ctx.zalpha_inj (hc : Sec6Ctx T T₁ n m) {b α β : G} (hb2 : b * b = 1)
    (hswap : conjSubgroup b T = T₁) (hα : α ∈ normIn T T₁) (hβ : β ∈ normIn T T₁)
    (h : α * (b * α * b) = β * (b * β * b)) : α = β := by
  have := hc.finite
  have hα' : b * α * b ∈ normIn T₁ T := mem_normIn_swap hb2 hswap hα
  have hβ' : b * β * b ∈ normIn T₁ T := mem_normIn_swap hb2 hswap hβ
  have h1 : β⁻¹ * α = (b * β * b) * (b * α * b)⁻¹ := by
    calc β⁻¹ * α = β⁻¹ * (α * (b * α * b)) * (b * α * b)⁻¹ := by group
      _ = β⁻¹ * (β * (b * β * b)) * (b * α * b)⁻¹ := by rw [h]
      _ = (b * β * b) * (b * α * b)⁻¹ := by group
  have hT : β⁻¹ * α ∈ T := T.mul_mem (T.inv_mem (normIn_le _ _ hβ)) (normIn_le _ _ hα)
  have hT₁ : β⁻¹ * α ∈ T₁ := by
    rw [h1]
    exact T₁.mul_mem (normIn_le _ _ hβ') (T₁.inv_mem (normIn_le _ _ hα'))
  have : β⁻¹ * α ∈ T ⊓ T₁ := ⟨hT, hT₁⟩
  rw [hc.sec3.cfg.inf, Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this.symm

theorem Sec6Ctx.mul_zalpha (hc : Sec6Ctx T T₁ n m) {b α : G} (hb2 : b * b = 1)
    (hswap : conjSubgroup b T = T₁) (hα : α ∈ normIn T T₁) :
    b * (α * (b * α * b)) = α * b * α := by
  have := hc.finite
  obtain ⟨hcomm, -, -⟩ := hc.zalpha_facts hb2 hswap hα
  have hα2 : α * α = 1 := elemAbelian_mul_self hc.hy.pair.wc.1 (normIn_le _ _ hα)
  calc b * (α * (b * α * b)) = b * ((b * α * b) * α) := by rw [hcomm]
    _ = (b * b) * α * (b * α) := by group
    _ = α * (b * α) := by rw [hb2, one_mul]
    _ = α * b * α := by group

theorem Sec6Ctx.zalpha_mem_classD (h66 : Sec66) (hc : Sec6Ctx T T₁ n m) {b α : G}
    (hbD : b ∈ classD T) (hb2 : b * b = 1) (hswap : conjSubgroup b T = T₁)
    (hα : α ∈ normIn T T₁) (hα1 : α ≠ 1) : α * (b * α * b) ∈ classD T := by
  have := hc.finite
  obtain ⟨-, hzz, -⟩ := hc.zalpha_facts hb2 hswap hα
  have hz1 := hc.zalpha_ne_one hb2 hswap hα hα1
  have hsq : (α * b) ^ 2 = α * (b * α * b) := by
    rw [pow_two]
    group
  have hord : orderOf (α * b) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : ¬ (α * b) ^ 2 ^ 1 = 1 := by
      rw [pow_one, hsq]
      exact hz1
    have h4 : (α * b) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hsq, pow_two]
      exact hzz
    have := orderOf_eq_prime_pow h2 h4
    simpa using this
  have hαD : α ∈ classD T := mem_classD_of_mem (normIn_le _ _ hα) hα1
  have := h66 G T T₁ n m hc α hαD b hbD hord
  rwa [hsq] at this

theorem Sec6Ctx.sec74_aux (h66 : Sec66) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hA8 : ¬ (n = 4 ∧ m = 1)) (hn3 : 3 ≤ n) {a b : G} (ha : a ∈ T)
    (ha1 : a ≠ 1) (hbD : b ∈ classD T) (hb2 : b * b = 1) (hab : b * a * b ∈ normIn T₁ T) :
    ∃ g : G, b ∈ conjSubgroup g T ∧ a⁻¹ * b * a ∈ conjSubgroup g T := by
  have := hc.finite
  have := hc.hy.simple
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hTab := hP.wc.1
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hswap : conjSubgroup b T = T₁ := hc.conjSubgroup_swap ha ha1 hb2 (normIn_le _ _ hab)
  have hm1 : 1 ≤ m := by
    by_contra hm0
    have h0 : m = 0 := by omega
    have := hc.hy.card
    rw [hc.hT, h0, pow_zero, one_pow] at this
    omega
  have hT16 : Nat.card T ≠ 16 := by
    intro h16
    have h2 : 2 ^ (m * n) = 2 ^ 4 := by
      rw [pow_mul, ← hc.hT, h16]
      norm_num
    have hmn : m * n = 4 := Nat.pow_right_injective (le_refl 2) h2
    have h3 : m * 3 ≤ m * n := Nat.mul_le_mul_left m hn3
    rw [hmn] at h3
    have hm : m = 1 := by omega
    subst hm
    exact hA8 ⟨by omega, rfl⟩
  have haL : a ∈ normIn T T₁ := by
    have := mem_normIn_swap' hb2 hswap hab
    have e : b * (b * a * b) * b = a := by
      calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
        _ = a := by rw [hb2]; group
    rwa [e] at this
  obtain ⟨x₀, hx₀X, hx₀⟩ := hS3.conj
  have hconjD : ∀ x ∈ classD T, b * x * b ∈ classD T := fun x hx => by
    have := classD_conj_mul hx b
    rwa [hbi] at this
  have key : ∀ α ∈ normIn T T₁, α ≠ 1 → ∃ u ∈ T ⊔ T₁,
      α * (b * α * b) ∈ conjSubgroup u T ∧
        b ∈ Subgroup.normalizer ((conjSubgroup u T : Subgroup G) : Set G) := by
    intro α hα hα1
    have hα' : b * α * b ∈ normIn T₁ T := mem_normIn_swap hb2 hswap hα
    have hα'T₁ : b * α * b ∈ T₁ := normIn_le _ _ hα'
    have hα'ne : b * α * b ≠ 1 := by
      intro h
      apply hα1
      calc α = (b * b) * α * (b * b) := by rw [hb2]; group
        _ = b * (b * α * b) * b := by group
        _ = 1 := by rw [h, mul_one, hb2]
    have hα'T : b * α * b ∉ T := by
      intro hT
      have : b * α * b ∈ T ⊓ T₁ := ⟨hT, hα'T₁⟩
      rw [hS3.cfg.inf, Subgroup.mem_bot] at this
      exact hα'ne this
    have hαD : α ∈ classD T := mem_classD_of_mem (normIn_le _ _ hα) hα1
    have hα'D : b * α * b ∈ normD T := ⟨hconjD α hαD, (mem_normIn.1 hα').2⟩
    obtain ⟨hset1, -⟩ := hc.sec65 h62 h63 hα'D hα'T
    have hz := hc.zalpha_mem_classD h66 hbD hb2 hswap hα hα1
    obtain ⟨hcomm, -, hbz⟩ := hc.zalpha_facts hb2 hswap hα
    have hmem : α * (b * α * b) ∈ {y | y ∈ classD T ∧ ∃ t ∈ T, y = (b * α * b) * t} :=
      ⟨hz, α, normIn_le _ _ hα, hcomm⟩
    rw [hset1] at hmem
    obtain ⟨τ, hτT, hτ⟩ := hmem
    have hzU : α * (b * α * b) ∈ conjSubgroup (τ⁻¹ * x₀) T := by
      rw [mem_conjSubgroup]
      have e : (τ⁻¹ * x₀)⁻¹ * (α * (b * α * b)) * (τ⁻¹ * x₀) = x₀⁻¹ * (b * α * b) * x₀ := by
        rw [hτ]
        group
      rw [e]
      have : b * α * b ∈ conjSubgroup x₀ T := by
        rw [← hx₀]
        exact hα'T₁
      exact mem_conjSubgroup.1 this
    refine ⟨τ⁻¹ * x₀, (T ⊔ T₁).mul_mem ((T ⊔ T₁).inv_mem (Subgroup.mem_sup_left hτT)) hx₀X,
      hzU, ?_⟩
    have hbzc : b * (α * (b * α * b)) = (α * (b * α * b)) * b := by
      calc b * (α * (b * α * b)) = (b * (α * (b * α * b)) * b) * b := by
            calc b * (α * (b * α * b)) = b * (α * (b * α * b)) * (b * b) := by
                  rw [hb2, mul_one]
              _ = (b * (α * (b * α * b)) * b) * b := by group
        _ = (α * (b * α * b)) * b := by rw [hbz]
    exact (hP.wc.conj (τ⁻¹ * x₀)).centralizer_le_normalizer hzU
      (hc.zalpha_ne_one hb2 hswap hα hα1) (Subgroup.mem_centralizer_singleton_iff.2 hbzc)
  obtain ⟨u₀, hu₀X, hzU₀, hbN₀⟩ := key a haL ha1
  have hzU : ∀ α ∈ normIn T T₁, α * (b * α * b) ∈ conjSubgroup u₀ T := by
    intro α hα
    by_cases hα1 : α = 1
    · subst hα1
      have : (1 : G) * (b * 1 * b) = 1 := by rw [mul_one, hb2, one_mul]
      rw [this]
      exact (conjSubgroup u₀ T).one_mem
    · obtain ⟨u, hu, hzu, hbu⟩ := key α hα hα1
      have := hc.eq_of_normalized hbD hb2 hswap hT16 hu hu₀X hbu hbN₀
      rw [← this]
      exact hzu
  by_cases hbU : b ∈ conjSubgroup u₀ T
  · refine ⟨u₀, hbU, ?_⟩
    have hza := hzU a haL
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (elemAbelian_mul_self hTab ha)
    have e : a⁻¹ * b * a = (a * (b * a * b)) * b := by
      rw [hai]
      calc a * b * a = a * (b * a * (b * b)) := by rw [hb2, mul_one]; group
        _ = (a * (b * a * b)) * b := by group
    rw [e]
    exact (conjSubgroup u₀ T).mul_mem hza hbU
  · exfalso
    have hb₀D : u₀⁻¹ * b * u₀ ∈ classD T := classD_conj hbD u₀
    have hb₀N : u₀⁻¹ * b * u₀ ∈ Subgroup.normalizer (T : Set G) :=
      mem_normalizer_conjSubgroup_iff.1 hbN₀
    have hb₀T : u₀⁻¹ * b * u₀ ∉ T := fun h => hbU (mem_conjSubgroup.2 h)
    have hb₀ : u₀⁻¹ * b * u₀ ∈ normD T := ⟨hb₀D, hb₀N⟩
    have hset := hc.sec65 h62 h63 hb₀ hb₀T
    have hmemC : ∀ α ∈ normIn T T₁,
        u₀⁻¹ * (α * (b * α * b)) * u₀ ∈ commSub (u₀⁻¹ * b * u₀) T := by
      intro α hα
      by_cases hα1 : α = 1
      · subst hα1
        have : (1 : G) * (b * 1 * b) = 1 := by rw [mul_one, hb2, one_mul]
        rw [this]
        have e : u₀⁻¹ * (1 : G) * u₀ = 1 := by group
        rw [e]
        exact (commSub (u₀⁻¹ * b * u₀) T).one_mem
      · have hzT : u₀⁻¹ * (α * (b * α * b)) * u₀ ∈ T := mem_conjSubgroup.1 (hzU α hα)
        have hαD : α ∈ classD T := mem_classD_of_mem (normIn_le _ _ hα) hα1
        have hbz : (u₀⁻¹ * b * u₀) * (u₀⁻¹ * (α * (b * α * b)) * u₀) ∈ classD T := by
          have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right
            (elemAbelian_mul_self hTab (normIn_le _ _ hα))
          have h1' : α * b * α ∈ classD T := by
            have := classD_conj_mul hbD α
            rwa [hαi] at this
          have := classD_conj (x := α * b * α) h1' u₀
          rw [← hc.mul_zalpha hb2 hswap hα] at this
          have e : u₀⁻¹ * (b * (α * (b * α * b))) * u₀ =
              (u₀⁻¹ * b * u₀) * (u₀⁻¹ * (α * (b * α * b)) * u₀) := by group
          rwa [e] at this
        have hmem : (u₀⁻¹ * b * u₀) * (u₀⁻¹ * (α * (b * α * b)) * u₀) ∈
            {y | y ∈ classD T ∧ ∃ t ∈ T, y = (u₀⁻¹ * b * u₀) * t} :=
          ⟨hbz, _, hzT, rfl⟩
        rw [hset.1, hset.2] at hmem
        obtain ⟨c, hcc, hct⟩ := hmem
        have : u₀⁻¹ * (α * (b * α * b)) * u₀ = c := mul_left_cancel hct
        rw [this]
        exact hcc
    let f : ↥(normIn T T₁) → ↥(commSub (u₀⁻¹ * b * u₀) T) := fun α =>
      ⟨u₀⁻¹ * ((α : G) * (b * (α : G) * b)) * u₀, hmemC α α.2⟩
    have hf : Function.Injective f := by
      intro α β hαβ
      have h1' := congrArg Subtype.val hαβ
      have h2 : (α : G) * (b * (α : G) * b) = (β : G) * (b * (β : G) * b) := by
        have h3 : u₀⁻¹ * ((α : G) * (b * (α : G) * b)) * u₀ =
            u₀⁻¹ * ((β : G) * (b * (β : G) * b)) * u₀ := h1'
        simpa using h3
      exact Subtype.ext (hc.zalpha_inj hb2 hswap α.2 β.2 h2)
    have hle := Nat.card_le_card_of_injective f hf
    rw [hc.card_normIn, (hc.card_index_centralizer_eq h63 hA8 hb₀ hb₀T).2] at hle
    have hq2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    have hpow : (2 ^ m) ^ 2 ≤ (2 ^ m) ^ (n - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hsq : (2 ^ m) ^ 2 = 2 ^ m * 2 ^ m := by ring
    nlinarith

end CFSG.CGT.Timmesfeld75
