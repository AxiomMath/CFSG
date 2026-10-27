module

public import CFSG.LieType.ChevTwo.Defs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open CFSG.LieType.BorelTits

section Glue

theorem pCoreOf_inf_normal_le {Γ : Type} [Group Γ] [Finite Γ] (T : Subgroup Γ) [T.Normal]
    (C : Subgroup Γ) : pCoreOf 2 (C ⊓ T) ≤ pCoreOf 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 (C ⊓ T) ≤ C := (pCoreOf_le 2 (C ⊓ T)).trans inf_le_left
  refine le_pCoreOf 2 hle ?_ (pCoreOf_isPGroup 2 (C ⊓ T))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro c hc
  have hcCT : c ∈ Subgroup.normalizer ((C ⊓ T : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨hxC, hxT⟩
      exact ⟨mul_mem (mul_mem hc hxC) (inv_mem hc), ‹T.Normal›.conj_mem x hxT c⟩
    · rintro ⟨hxC, hxT⟩
      refine ⟨?_, ?_⟩
      · have := mul_mem (mul_mem (inv_mem hc) hxC) hc
        simpa [mul_assoc] using this
      · have := ‹T.Normal›.conj_mem _ hxT c⁻¹
        simpa [mul_assoc] using this
  exact normalizer_le_normalizer_pCoreOf 2 (C ⊓ T) hcCT

theorem conj_injective_of_center_eq_bot' {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have hmem : b⁻¹ * a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : a * x * a⁻¹ = b * x * b⁻¹ := by
      simpa using DFunLike.congr_fun hab x
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [hx]
      _ = b⁻¹ * a * x := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

theorem oppositeFixed_of_normal {Γ : Type} [Group Γ] [Finite Γ] (T : Subgroup Γ) [T.Normal]
    (hZ : Subgroup.center ↥T = ⊥)
    (hinner : ∀ α : MulAut ↥T, Odd (orderOf α) → α ∈ (MulAut.conj : ↥T →* MulAut ↥T).range)
    (hO2 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ S : Subgroup Γ, IsPGroup p S →
      pCoreOf 2 (Subgroup.centralizer (S : Set Γ)) = ⊥) :
    OppositeFixed ↥T := by
  intro p hp hp2 R hR Q hQ hQ2 hcore hne hRQ hC
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hRinn : R ≤ (MulAut.conj : ↥T →* MulAut ↥T).range := by
    intro α hα
    obtain ⟨k, hk⟩ := hR ⟨α, hα⟩
    have hk' : α ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
    exact hinner α (by rw [hi]; exact hpodd.pow)
  have hinj := conj_injective_of_center_eq_bot' hZ
  set R₁ : Subgroup ↥T := R.comap (MulAut.conj : ↥T →* MulAut ↥T) with hR₁
  have hR₁p : IsPGroup p R₁ := hR.comap_of_injective _ hinj
  set S : Subgroup Γ := R₁.map T.subtype with hS
  have hSp : IsPGroup p S := hR₁p.map _
  have hCeq : autCentralizer R = Subgroup.centralizer (R₁ : Set ↥T) := by
    ext x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx r hr
      have h1 : r * x * r⁻¹ = x := hx (MulAut.conj r) hr
      calc r * x = (r * x * r⁻¹) * r := by group
        _ = x * r := by rw [h1]
    · intro hx α hα
      obtain ⟨r, rfl⟩ := hRinn hα
      have h1 : r * x = x * r := hx r hα
      change r * x * r⁻¹ = x
      calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [h1]
        _ = x := by group
  set C₁ : Subgroup ↥T := autCentralizer R with hC₁
  set X : Subgroup ↥T := C₁ ⊓ Q with hX
  set X' : Subgroup Γ := X.map T.subtype with hX'
  set H : Subgroup Γ := Subgroup.centralizer (S : Set Γ) ⊓ T with hH
  have hC₁H : C₁.map T.subtype = H := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hCeq] at hx
      refine Subgroup.mem_inf.2 ⟨?_, x.2⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, hr, rfl⟩
      have := (Subgroup.mem_centralizer_iff.1 hx) r hr
      exact congrArg Subtype.val this
    · intro hg
      obtain ⟨hgC, hgT⟩ := Subgroup.mem_inf.1 hg
      have hmem : (⟨g, hgT⟩ : ↥T) ∈ Subgroup.centralizer (R₁ : Set ↥T) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have := (Subgroup.mem_centralizer_iff.1 hgC) (r : Γ) ⟨r, hr, rfl⟩
        exact Subtype.ext this
      refine ⟨⟨g, hgT⟩, ?_, rfl⟩
      change (⟨g, hgT⟩ : ↥T) ∈ C₁
      rw [hCeq]
      exact hmem
  have hX'H : X' ≤ H := by
    rw [← hC₁H]
    exact Subgroup.map_mono inf_le_left
  have hXp : IsPGroup 2 X := hQ2.to_le (inf_le_right : C₁ ⊓ Q ≤ Q)
  have hX'p : IsPGroup 2 X' := hXp.map T.subtype
  have hX'N : (X'.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX'H]
    intro c hc
    rw [← hC₁H] at hc
    obtain ⟨c₁, hc₁', rfl⟩ := hc
    have hc₁ : c₁ ∈ C₁ := hc₁'
    have hc₁Q : c₁ ∈ Subgroup.normalizer (Q : Set ↥T) := hC hc₁
    have hc₁C : c₁ ∈ Subgroup.normalizer (C₁ : Set ↥T) := Subgroup.le_normalizer hc₁
    have hc₁X : c₁ ∈ Subgroup.normalizer (X : Set ↥T) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 hc₁C y
      have h2 := Subgroup.mem_normalizer_iff.1 hc₁Q y
      simp only [hX, SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
      rw [h1, h2]
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨c₁ * x * c₁⁻¹, (Subgroup.mem_normalizer_iff.1 hc₁X x).1 hx, ?_⟩
      simp
    · rintro ⟨x, hx, hxy⟩
      refine ⟨c₁⁻¹ * x * c₁, ?_, ?_⟩
      · refine (Subgroup.mem_normalizer_iff.1 hc₁X (c₁⁻¹ * x * c₁)).2 ?_
        simpa [mul_assoc] using hx
      · simp only [map_mul, map_inv]
        change (T.subtype c₁)⁻¹ * T.subtype x * T.subtype c₁ = y
        rw [show T.subtype x = T.subtype c₁ * y * (T.subtype c₁)⁻¹ from hxy]
        group
  have hX'le : X' ≤ pCoreOf 2 H := le_pCoreOf 2 hX'H hX'N hX'p
  have hbot : pCoreOf 2 H = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hO2 p hp hp2 S hSp]
    exact pCoreOf_inf_normal_le T _
  have hX'bot : X' = ⊥ := le_bot_iff.1 (hbot ▸ hX'le)
  have hXbot : X = ⊥ := by
    rw [hX', Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at hX'bot
    exact hX'bot
  exact hXbot

end Glue

end CFSG.LieType.ChevTwo
