module

public import CFSG.GH74.GLS.Stage4.T2P56NegCore
public import CFSG.GH74.GLS.Stage4.T2NegWeyl
public import CFSG.GH74.GLS.Stage4.T2NegSing
public import CFSG.GH74.GLS.Stage4.T2NegConj
public import CFSG.GH74.GLS.Stage4.T2NegTransport
public import CFSG.GH74.GLS.Stage4.T2NegSwap

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage4.Hex CFSG.Assembly.LowTwoRank

@[expose] def Ch6T2TSingEq2Mod (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q : ℕ), IsTwoCentralG2TypeG2At G Gs q q →
      q ≠ 9 → (¬ ∃ n : ℕ, 3 ≤ n ∧ q = 3 ^ n) → q % 3 = 2 → q % 4 = r →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q q z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q q → Ch6TSing p q z K₁ K₂ ∨ Ch6TSing p q z K₂ K₁

theorem ch6T2TSingEq2_of_mods (h1 : Ch6T2TSingEq2Mod 1) (h3 : Ch6T2TSingEq2Mod 3) :
    Ch6T2TSingEq2 := by
  intro G _ _ hStd hr Gs _ q hAt h99 hn hq3 z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum
  have hodd := hSet.odd₁
  have h4 : q % 4 = 1 ∨ q % 4 = 3 := by obtain ⟨k, hk⟩ := hodd; omega
  rcases h4 with h | h
  · exact h1 G hStd hr Gs q hAt h99 hn hq3 h z K₁ K₂ F₁ F₂ t hSet hRem p hNum
  · exact h3 G hStd hr Gs q hAt h99 hn hq3 h z K₁ K₂ F₁ F₂ t hSet hRem p hNum

theorem ch6T2TSingEq2Mod_one_of_leaves (h3 : Ch6T2P51)
    (h4 : Ch6T2P52) (hCfg : Ch6T2NegCfgMod 1) (hL : SDWreathedLayer) (hL3 : LU.Local.L3Cover)
    (hR : IVK_4_1_R_U3) : Ch6T2TSingEq2Mod 1 := by
  intro G _ _ hStd hr Gs _ q hAt h99 hn hq3 hq4 z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨N₁, u₀, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
    h3 G Gs q q z K₁ K₂ F₁ F₂ t hSet hRem rfl
  obtain ⟨F, hF5⟩ := h4 G Gs q q z K₁ K₂ F₁ F₂ t hSet hRem N₁ u₀ hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have hnormK : ∀ c : G, c * z = z * c →
      (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) ∧ (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) :=
    fun c hc => t2Ctx_all_normK hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hc
  obtain ⟨u₁, H₁, w₁₁, w₂₁, cfg₀⟩ := hCfg G Gs q z K₁ K₂ F₁ F₂ t hSet hRem hq4
  obtain ⟨u, H, w₁, w₂, cfg, huS, hw₁S, hw₂S⟩ :=
    exists_cfg_in_sylow ctx.SC₁ hLoc.S_pGroup hLoc.S_sylow cfg₀
  have hCle : centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ ⊔ N₁.S ⊔ F := by
    have h := hF5.C_le
    change centralizer ({N₁.z} : Set G) ≤ N₁.K₁ ⊔ N₁.K₂ ⊔ N₁.S ⊔ F at h
    rwa [hz, hK₁, hK₂] at h
  have hFS : ∀ f ∈ F, ∀ s ∈ N₁.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N₁.S : Set G) := by
      have h := hF5.centS
      change centralizer (N₁.S : Set G) = Subgroup.zpowers N₁.z ⊔ F at h
      rw [h]
      exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hFodd : ∀ f ∈ F, Odd (orderOf f) := hF5.F_odd
  have hFK : F ⊓ (K₁ ⊔ K₂) = ⊥ := by
    have h := hF5.F_inter_K
    change F ⊓ (N₁.K₁ ⊔ N₁.K₂) = ⊥ at h
    rwa [hK₁, hK₂] at h
  obtain ⟨a, ha1, ha2, haN, ha3, hw₁a, -⟩ :=
    exists_a_neg hr hSet hRem ctx hCle hFodd hFS hFK cfg huS hw₁S hw₂S
  obtain ⟨y, hyH, hyz, hyord, hya⟩ := t5_singular_neg cfg (by omega) haN ha3 hw₁a
  have hyp : (orderOf y).Prime := hyord ▸ Nat.prime_three
  have hyodd : Odd (orderOf y) := hyord ▸ (by decide : Odd 3)
  have hp3 : p ≠ 3 := by
    rintro rfl
    obtain ⟨m, hm⟩ := hNum.q₁_pow
    have hm0 : m ≠ 0 := by
      rintro rfl
      have := hSet.five
      simp at hm
      omega
    have : 3 ∣ q := by rw [hm]; exact dvd_pow_self 3 hm0
    omega
  have hnp : ¬ p ∣ orderOf y := by
    rw [hyord]
    intro hp
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hNum.prime Nat.prime_three).1 hp)
  have hz2 : orderOf z = 2 := hSet.central.1
  have hzc₁ : ∀ x ∈ K₁, z * x = x * z := by
    intro x hx
    have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_left hx)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  have hzc₂ : ∀ x ∈ K₂, z * x = x * z := by
    intro x hx
    have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_right hx)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
  rcases hyH with hyH₁ | hyH₂
  · left
    obtain ⟨J, hJy, hKJ, hJ⟩ :=
      exists_J_core_neg_one hL hL3 hStd hSet hnormK hNum hq4 cfg ha1 ha2 hyH₁ hyp hyodd hya
    exact t5_tsing_of_J_neg hR hNum.prime hNum.p_ne_two hNum.q₂_pow hyH₁.2 hyz hnp hJy hKJ hJ hz2
      hSet.z_mem₂ hzc₂
  · right
    have hnormK' : ∀ c : G, c * z = z * c →
        (∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂) ∧ (∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁) :=
      fun c hc => (hnormK c hc).symm
    obtain ⟨J, hJy, hKJ, hJ⟩ :=
      exists_J_core_neg_one (K₁ := K₂) (K₂ := K₁) hL hL3 hStd (hSet.swap rfl) hnormK' hNum hq4
        cfg.swap ha1 ha2 hyH₂ hyp hyodd hya
    exact t5_tsing_of_J_neg hR hNum.prime hNum.p_ne_two hNum.q₂_pow hyH₂.2 hyz hnp hJy hKJ hJ hz2
      hSet.z_mem₁ hzc₁

end CFSG.GH74.GLS.Stage4.Rest
