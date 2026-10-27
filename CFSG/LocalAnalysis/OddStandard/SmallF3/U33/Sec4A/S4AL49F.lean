module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL49A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma t_mem_S_of_center (h : Ctx t L S x₁ x₂ lam rho tau) : t ∈ S :=
  (h.center_ge (Subgroup.subset_closure
    (show t ∈ ({t, (x₁ * x₂) ^ 2} : Set G) from by simp))).1

private lemma t_commute_S_of_center (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ S) :
    t * g = g * t :=
  ((Subgroup.mem_centralizer_iff.mp
    (h.center_ge (Subgroup.subset_closure
      (show t ∈ ({t, (x₁ * x₂) ^ 2} : Set G) from by simp))).2) g hg).symm

private lemma zpowers_t_eq_one_or_t_of_center (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) : p = 1 ∨ p = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have ht : t * t = 1 := t_mul_self h.hyp
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, hm | hm⟩
  · left
    rw [← hk, hm, zpow_mul, ht2, one_zpow]
  · right
    rw [← hk, hm, zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

private lemma zpowers_t_commute_S_of_center (h : Ctx t L S x₁ x₂ lam rho tau) {p : G}
    (hp : p ∈ zpowers t) {g : G} (hg : g ∈ S) : p * g = g * p := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
  have hc : Commute t g := t_commute_S_of_center h hg
  rw [← hk]
  exact (hc.zpow_left k).eq

private lemma commute_E_zpowers_t_of_center (h : Ctx t L S x₁ x₂ lam rho tau)
    {E : Subgroup G} (hES : E ≤ S) : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a := by
  intro a ha b hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hta : Commute t a := t_commute_S_of_center h (hES ha)
  rw [← hk]
  exact (hta.symm.zpow_right k).eq

private lemma conj_mem_sup_zpowers_of_center (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮) (hE𝒮 : E ≤ 𝒮)
    (hEn : (E.subgroupOf 𝒮).Normal) (hES : E ≤ S) {Es : Subgroup G}
    (hEs : Es = E ⊔ zpowers t) (hcl : closure {t, (x₁ * x₂) ^ 2} ≤ Es)
    {β : G} (hβ : β ∈ ctxS1 S 𝒮) : ∀ x, x ∈ Es → β * x * β⁻¹ ∈ Es := by
  have hβN : β ∈ normalizer (S : Set G) := hβ.1
  have hβ𝒮 : β ∈ 𝒮 := hβ.2
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a :=
    commute_E_zpowers_t_of_center h hES
  have hcl' : closure {t, (x₁ * x₂) ^ 2} ≤ E ⊔ zpowers t := by
    rwa [hEs] at hcl
  intro x hx
  rw [hEs] at hx ⊢
  obtain ⟨e, he, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
  have hconjE : β * e * β⁻¹ ∈ E := by
    have he𝒮 : e ∈ 𝒮 := hE𝒮 he
    exact Subgroup.mem_subgroupOf.mp
      (hEn.conj_mem ⟨e, he𝒮⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨β, hβ𝒮⟩)
  have hconjt : β * p * β⁻¹ ∈ closure {t, (x₁ * x₂) ^ 2} := by
    rcases zpowers_t_eq_one_or_t_of_center h hp with h1 | h1
    · rw [h1]; simp
    · rw [h1]
      have htS : t ∈ S := t_mem_S_of_center h
      have hmemS : β * t * β⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hβN t).mp htS
      have hmemC : β * t * β⁻¹ ∈ centralizer (S : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hβinvN : β⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hβN
        have hs' : β⁻¹ * s * β ∈ S := by
          have := (Subgroup.mem_normalizer_iff.mp hβinvN s).mp hs
          simpa using this
        have hts : t * (β⁻¹ * s * β) = (β⁻¹ * s * β) * t :=
          t_commute_S_of_center h hs'
        calc s * (β * t * β⁻¹)
            = β * ((β⁻¹ * s * β) * t) * β⁻¹ := by group
          _ = β * (t * (β⁻¹ * s * β)) * β⁻¹ := by rw [← hts]
          _ = (β * t * β⁻¹) * s := by group
      have hmem : β * t * β⁻¹ ∈ S ⊓ centralizer (S : Set G) := ⟨hmemS, hmemC⟩
      rw [center_S_of h h43] at hmem
      exact hmem
  have h1 : β * e * β⁻¹ ∈ E ⊔ zpowers t := Subgroup.mem_sup_left hconjE
  have h2 : β * p * β⁻¹ ∈ E ⊔ zpowers t := hcl' hconjt
  rw [show β * (e * p) * β⁻¹ = (β * e * β⁻¹) * (β * p * β⁻¹) by group]
  exact Subgroup.mul_mem _ h1 h2

theorem false_of_E_le_S (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {𝒮 E : Subgroup G} (hS𝒮 : S ≤ 𝒮) (hE𝒮 : E ≤ 𝒮)
    (hEn : (E.subgroupOf 𝒮).Normal) (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEc : Nat.card E = 8) (htE : t ∉ E) (hES : E ≤ S)
    (hidx : S.relIndex (ctxS1 S 𝒮) = 2) {α : G} (hα : α ∈ ctxS1 S 𝒮)
    (hswap : ∀ x : G, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxYt t tau x₁ x₂) : False := by
  set Es : Subgroup G := E ⊔ zpowers t with hEs_def
  have hcomm : ∀ a ∈ E, ∀ b ∈ zpowers t, a * b = b * a :=
    commute_E_zpowers_t_of_center h hES
  have hinf : E ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rcases zpowers_t_eq_one_or_t_of_center h hx.2 with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx.1) htE
  have hcardEs : Nat.card Es = 16 := by
    rw [hEs_def, card_sup_of_commute hcomm hinf, hEc, Nat.card_zpowers, h.hyp.ord_t]
  have hEs_le_S : Es ≤ S := by
    rw [hEs_def]
    exact sup_le hES (Subgroup.zpowers_le.mpr (t_mem_S_of_center h))
  have hEs_ea : CFSG.Open.IsElemAbelian 2 Es := by
    rw [hEs_def]
    exact isElemAbelian_sup_zpowers h hES hEe
  have hEs16 : IsE16In S Es := ⟨hEs_le_S, hEs_ea, hcardEs⟩
  have hEsN : NormalIn Es S := by
    rw [hEs_def]
    refine ⟨sup_le hES (Subgroup.zpowers_le.mpr (t_mem_S_of_center h)), ?_⟩
    intro g hg x hx
    obtain ⟨e, he, p, hp, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hx
    have hconjE : g * e * g⁻¹ ∈ E := by
      have hg𝒮 : g ∈ 𝒮 := hS𝒮 hg
      have he𝒮 : e ∈ 𝒮 := hE𝒮 he
      exact Subgroup.mem_subgroupOf.mp
        (hEn.conj_mem ⟨e, he𝒮⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hg𝒮⟩)
    have hconjp : g * p * g⁻¹ = p := by
      rw [← zpowers_t_commute_S_of_center h hp hg, mul_assoc, mul_inv_cancel, mul_one]
    rw [show (g) * (e * p) * g⁻¹ = (g * e * g⁻¹) * (g * p * g⁻¹) by group, hconjp]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hconjE) (Subgroup.mem_sup_right hp)
  have hcl : closure {t, (x₁ * x₂) ^ 2} ≤ Es :=
    (lemma4_7a_of h h43 h44 Es hEs16).2.1
  have hαNormEs : ∀ x, x ∈ Es ↔ α * x * α⁻¹ ∈ Es := by
    intro x
    constructor
    · exact conj_mem_sup_zpowers_of_center h h43 hS𝒮 hE𝒮 hEn hES hEs_def hcl hα x
    · intro hx
      have hαinv : α⁻¹ ∈ ctxS1 S 𝒮 := (ctxS1 S 𝒮).inv_mem hα
      have h := conj_mem_sup_zpowers_of_center h h43 hS𝒮 hE𝒮 hEn hES hEs_def hcl hαinv
        (α * x * α⁻¹) hx
      have hx' : α⁻¹ * (α * x * α⁻¹) * (α⁻¹)⁻¹ = x := by group
      rwa [hx'] at h
  rcases lemma4_7b_of h h43 h44 Es hEs16 hEsN with hEsX | hEsY
  · have hEsEqX : Es = ctxX t tau x₁ x₂ := by
      rw [hEsX, ctxX]
      congr 1
      ext g
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have hαNormX : ∀ x, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxX t tau x₁ x₂ := by
      intro x
      have hx := hαNormEs x
      rwa [hEsEqX] at hx
    have hiff : ∀ u : G, u ∈ ctxX t tau x₁ x₂ ↔ u ∈ ctxYt t tau x₁ x₂ := by
      intro u
      have hxh := hswap (α⁻¹ * u * α)
      have hx' : α * (α⁻¹ * u * α) * α⁻¹ = u := by group
      rw [hx'] at hxh
      have hxn := hαNormX (α⁻¹ * u * α)
      rw [hx'] at hxn
      exact hxn.symm.trans hxh
    exact ctxX_ne_ctxYt h h44 (Subgroup.ext hiff)
  · have hEsEqY : Es = ctxYt t tau x₁ x₂ := by
      rw [hEsY, ctxYt]
    have hαNormY : ∀ x, x ∈ ctxYt t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxYt t tau x₁ x₂ := by
      intro x
      have hx := hαNormEs x
      rwa [hEsEqY] at hx
    have ha2S : α * α ∈ S := by
      have hK : (S.subgroupOf (ctxS1 S 𝒮)).index = 2 := hidx
      have hmem := Subgroup.mul_self_mem_of_index_two hK (⟨α, hα⟩ : ↥(ctxS1 S 𝒮))
      simpa using (Subgroup.mem_subgroupOf.mp hmem)
    have hNX := normalIn_ctxX h h43 h44
    have hα2NormX : ∀ u : G,
        u ∈ ctxX t tau x₁ x₂ ↔ (α * α) * u * (α * α)⁻¹ ∈ ctxX t tau x₁ x₂ := by
      intro u
      constructor
      · intro hu
        exact hNX.2 (α * α) ha2S u hu
      · intro hu
        have hmem := hNX.2 ((α * α)⁻¹) (S.inv_mem ha2S) ((α * α) * u * (α * α)⁻¹) hu
        have hx' : (α * α)⁻¹ * ((α * α) * u * (α * α)⁻¹) * ((α * α)⁻¹)⁻¹ = u := by group
        rwa [hx'] at hmem
    have hiff : ∀ u : G, u ∈ ctxX t tau x₁ x₂ ↔ u ∈ ctxYt t tau x₁ x₂ := by
      intro u
      let x : G := (α * α)⁻¹ * u * (α * α)
      have hYx : x ∈ ctxX t tau x₁ x₂ ↔
          α * (α * x * α⁻¹) * α⁻¹ ∈ ctxYt t tau x₁ x₂ :=
        (hswap x).trans (hαNormY (α * x * α⁻¹))
      have hXx : x ∈ ctxX t tau x₁ x₂ ↔
          (α * α) * x * (α * α)⁻¹ ∈ ctxX t tau x₁ x₂ := hα2NormX x
      have hxY : α * (α * x * α⁻¹) * α⁻¹ = u := by
        dsimp [x]; group
      have hxX : (α * α) * x * (α * α)⁻¹ = u := by
        dsimp [x]; group
      rw [hxY] at hYx
      rw [hxX] at hXx
      exact hXx.symm.trans hYx
    exact ctxX_ne_ctxYt h h44 (Subgroup.ext hiff)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
