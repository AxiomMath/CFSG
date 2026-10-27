module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OrdG
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ModelJ

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local

theorem two_mul_card_LBar2 {G : Type} [Group G] {z : G} {r₁ r₂ : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hprod : IsCentralProd L₁ L₂ (LBar z))
    (h₁ : HasSL2Model ↥L₁ (fun r => r = r₁)) (h₂ : HasSL2Model ↥L₂ (fun r => r = r₂)) :
    Nat.card ↥(LBar z) * 2 = (r₁ * (r₁ ^ 2 - 1)) * (r₂ * (r₂ ^ 2 - 1)) := by
  obtain ⟨hsup, hcomm, hinf⟩ := hprod
  have h := jm_card_sup_mul_card_inf L₁ L₂ hcomm
  rw [hsup, hinf, card_of_hasSL2Model h₁, card_of_hasSL2Model h₂] at h
  rw [h]

theorem card_S_g2 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hctx : Stage2Ctx G z Kind.g2 S)
    (h : G2Shape z S r₁ r₂ L₁ L₂) :
    Nat.card ↥S = 2 ^ ((r₁ * (r₁ ^ 2 - 1) * (r₂ * (r₂ ^ 2 - 1))).factorization 2) := by
  obtain ⟨-, -, -, hprod, hsl₁, hsl₂, -, -, -, hidx, -, -⟩ := h
  rw [card_S_eq_relIndex_mul z S, hidx, card_RC_eq_two_pow hctx.sylow]
  have h2 := two_mul_card_LBar2 hprod hsl₁ hsl₂
  have hpos : Nat.card ↥(LBar z) ≠ 0 := Nat.card_pos.ne'
  have hfac : (r₁ * (r₁ ^ 2 - 1) * (r₂ * (r₂ ^ 2 - 1))).factorization 2 =
      (Nat.card ↥(LBar z)).factorization 2 + 1 := by
    rw [← h2, Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
  rw [hfac, pow_succ]
  ring

theorem card_S_g2_diag {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hctx : Stage2Ctx G z Kind.g2 S)
    (h : G2Shape z S q q L₁ L₂) : Nat.card ↥S = 2 ^ nuQ q * 2 := by
  obtain ⟨-, -, -, hprod, hsl₁, hsl₂, -, -, -, hidx, -, -⟩ := h
  rw [card_S_eq_relIndex_mul z S, hidx, card_RC_eq_two_pow hctx.sylow, mul_comm]
  congr 1
  congr 1
  unfold nuQ
  have h2 := two_mul_card_LBar2 hprod hsl₁ hsl₂
  rw [← sq] at h2
  rw [← h2, Nat.mul_div_cancel _ (by norm_num)]

section Swap

variable {C : Type} [Group C]

theorem false_of_swap {L₁ L₂ T : Subgroup C} {r : ℕ}
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hnab : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a)
    (hPGL : InducedPGL2 L₁ T r) {s : C} (hsT : s ∈ T)
    (h12 : L₁.map (MulAut.conj s).toMonoidHom = L₂) (h21 : L₂.map (MulAut.conj s).toMonoidHom = L₁) :
    False := by
  obtain ⟨hN, -⟩ := hPGL
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hsM : s ∈ L₁ ⊔ T := Subgroup.mem_sup_right hsT
  have hbc : b ∈ L₂.map (MulAut.conj s).toMonoidHom := by rw [h21]; exact hb
  obtain ⟨ℓ, hℓ, hℓb⟩ := Subgroup.mem_map.1 hbc
  have hℓb' : s * ℓ * s⁻¹ = b := hℓb
  have hℓ' : ℓ ∈ L₁ ⊔ T := by
    have hℓ2 : ℓ ∈ L₁.map (MulAut.conj s).toMonoidHom := by rw [h12]; exact hℓ
    obtain ⟨m, hm, hmℓ⟩ := Subgroup.mem_map.1 hℓ2
    have hmℓ' : s * m * s⁻¹ = ℓ := hmℓ
    rw [← hmℓ']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hsM (Subgroup.mem_sup_left hm))
      (Subgroup.inv_mem _ hsM)
  have hℓC : ℓ ∈ centralizer (L₁ : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm h hh ℓ hℓ
  have hx : (⟨ℓ, hℓ'⟩ : ↥(L₁ ⊔ T)) ∈ (centralizer (L₁ : Set C)).subgroupOf (L₁ ⊔ T) := hℓC
  have hconj := hN.conj_mem _ hx ⟨s, hsM⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hconj
  have hc : ((⟨s, hsM⟩ * ⟨ℓ, hℓ'⟩ * ⟨s, hsM⟩⁻¹ : ↥(L₁ ⊔ T)) : C) = b := by
    rw [← hℓb']
    rfl
  rw [hc] at hconj
  exact hab (hconj a ha)

end Swap

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
