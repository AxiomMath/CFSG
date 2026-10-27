module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Cen
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Inst
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2YThree

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final

section Three

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem three_data (hsh : G2Shape z S r₁ 3 L₁ L₂) :
    WBar z ≤ L₂ ∧ Nat.card ↥(WBar z) = 8 ∧ (∀ x ∈ L₂, x ^ 4 = 1 → x ∈ WBar z) ∧
      generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ WBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, h3, -, -, -, -⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  obtain ⟨⟨eW⟩, hFR⟩ := h3 rfl
  have hc₁ : IsComponent L₁ :=
    L26.isComponent_of_sl2_pair hsup hcomm (LBar_normal z) hodd₁ (by omega) hm₁
  have hZ₁ : Nat.card (center ↥L₁) = 2 := (sl2_model_facts hodd₁ (by omega) hm₁).2.1
  have hcen₁ : ∀ a ∈ L₁, (∀ c ∈ L₁, c * a = a * c) → a ∈ L₂ := fun a ha hc =>
    central_mem_of_card_inf hcomm hZ₁ hcard ha hc
  have hFΦ : generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ L₂ := by
    rw [hFR, hsup]
    exact Subgroup.map_subtype_le _
  have hWn := L26.WBar_normal z
  have hWL₂ : WBar z ≤ L₂ :=
    L26.le_of_normal_twoGroup_of_two_comps hc₁.1 hcomm hcen₁ (L26.WBar_two_pow z)
      ((L26.WBar_le_generalizedFitting z).trans hFΦ)
  have hWcard : Nat.card ↥(WBar z) = 8 := by
    rw [Nat.card_congr eW.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hL₂card : Nat.card ↥L₂ = 24 := L26.card_eq_of_hasSL2Model_three hm₂
  have hW4 : ∀ x ∈ L₂, x ^ 4 = 1 → x ∈ WBar z := fun x hx h4 =>
    mem_of_twoElt_of_normal_card hWL₂ hL₂card hWcard hx ⟨2, by norm_num; exact h4⟩
  refine ⟨hWL₂, hWcard, hW4, ?_⟩
  rw [hFR]
  rintro _ ⟨x, hx, rfl⟩
  have hcl : ∀ y : ↥(LBar z), y ∈ Subgroup.closure {x : ↥(LBar z) | ∃ k : ℕ, x ^ (2 ^ k) = 1} →
      ((y : ↥(LBar z)) : CentralizerBar z) ∈ L₁ ⊔ WBar z := by
    intro y hy
    refine Subgroup.closure_induction (p := fun y _ => ((y : ↥(LBar z)) : CentralizerBar z) ∈ L₁ ⊔ WBar z)
      ?_ ?_ ?_ ?_ hy
    · intro x hx
      obtain ⟨k, hk⟩ := hx
      have hxL : (x : CentralizerBar z) ∈ L₁ ⊔ L₂ := by rw [hsup]; exact x.2
      obtain ⟨a, ha, b, hb, hab⟩ := L26.exists_mul_of_mem_sup_of_commute hcomm hxL
      have hk' : ((x : CentralizerBar z)) ^ (2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hcab : Commute a b := hcomm a ha b hb
      have hpow : a ^ (2 ^ k) * b ^ (2 ^ k) = 1 := by
        rw [← hcab.mul_pow, ← hab]
        exact hk'
      have hmemL₁ : b ^ (2 ^ k) ∈ L₁ := by
        have : b ^ (2 ^ k) = (a ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hpow
        rw [this]
        exact L₁.inv_mem (L₁.pow_mem ha _)
      have hmemI : b ^ (2 ^ k) ∈ L₁ ⊓ L₂ := ⟨hmemL₁, L₂.pow_mem hb _⟩
      have hsq : (b ^ (2 ^ k)) ^ 2 = 1 := by
        have h1 : orderOf (⟨b ^ (2 ^ k), hmemI⟩ : ↥(L₁ ⊓ L₂)) ∣ Nat.card ↥(L₁ ⊓ L₂) :=
          orderOf_dvd_natCard _
        rw [hcard] at h1
        have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
        exact congrArg Subtype.val h2
      have hb2 : ∃ j : ℕ, b ^ (2 ^ j) = 1 := by
        refine ⟨k + 1, ?_⟩
        rw [pow_succ, pow_mul]
        exact hsq
      have hbW : b ∈ WBar z := mem_of_twoElt_of_normal_card hWL₂ hL₂card hWcard hb hb2
      rw [hab]
      exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hbW)
    · exact one_mem _
    · intro x y _ _ hx hy
      exact mul_mem hx hy
    · intro x _ hx
      exact inv_mem hx
  exact hcl x hx

end Three


section Y

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem ykey_of_shape (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂)
    {t e : CentralizerBar z} (ht : t ∈ LBar z) (ht2 : t * t = 1) (htI : t ∉ L₁ ⊓ L₂)
    (he2 : e * e = 1) (het : e * t = t * e) (heI : e ∉ L₁ ⊓ L₂) (hetI : e * t ∉ L₁ ⊓ L₂)
    {Bb : Subgroup (CentralizerBar z)} (hBodd : Odd (Nat.card ↥Bb))
    (hBt : ∀ b ∈ Bb, b * t = t * b)
    (hBn : ∀ m : CentralizerBar z, m * t = t * m → ∀ b ∈ Bb, m * b * m⁻¹ ∈ Bb)
    (hBe : ∀ b ∈ Bb, e * b = b * e) : Bb = ⊥ := by
  have h3 := three_le_r₂ hsh
  have hsup := sup_eq hsh
  have htL : t ∈ L₁ ⊔ L₂ := by rw [hsup]; exact ht
  rcases Nat.lt_or_ge 3 r₂ with h | h
  · have hF : generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ L₂ := by
      obtain ⟨-, -, -, -, -, -, -, -, h4, -⟩ := hsh
      rw [(h4 h).2, hsup]
    exact ykey_big (factor₁ hctx hsh) (factor₂ hctx hsh h) hF htL ht2 htI he2 het heI hetI hBodd
      hBt hBn hBe
  · obtain rfl : r₂ = 3 := by omega
    obtain ⟨hWL, hWc, hW4, hF⟩ := three_data hsh
    exact ykey_three (factor₁ hctx hsh) (normal₂ hctx hsh) (L26.WBar_normal z) hWL hWc hW4 hF
      htL ht2 htI he2 het heI hetI hBodd hBt hBn hBe

end Y

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
