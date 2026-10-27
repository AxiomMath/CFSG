module

public import CFSG.Quasithin.Recognition.Kleidman.BenderClose

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem top_of_conj_z [Finite G] [IsSimpleGroup G] {z : G}
    (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hsyl : ∃ S : Sylow 2 G, Nat.card (Subgroup.center (S : Subgroup G)) = 2)
    (hcomm : ∃ a : G, a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
      ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ a ∈ (S : Subgroup G))
    {M : Subgroup G} (hHM : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hconj : ∀ y ∈ M, y * y = 1 → y ≠ 1 → ∃ k ∈ M, k * z * k⁻¹ = y) : M = ⊤ := by
  classical
  by_contra hne
  set H := Subgroup.centralizer ({z} : Set G) with hH
  have hzsq : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hzM : z ∈ M := hHM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hzinv : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution z := ⟨hz1, hzsq⟩
  have hcent : ∀ y ∈ M, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution y →
      Subgroup.centralizer ({y} : Set G) ≤ M := by
    intro y hyM hy c hc
    obtain ⟨k, hkM, hk⟩ := hconj y hyM (by rw [← pow_two]; exact hy.2) hy.1
    have hc' : k⁻¹ * c * k ∈ H := by
      rw [hH, Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      calc k⁻¹ * c * k * z = k⁻¹ * (c * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * (c * y) * k := by rw [hk]
        _ = k⁻¹ * (y * c) * k := by rw [hc]
        _ = k⁻¹ * ((k * z * k⁻¹) * c) * k := by rw [hk]
        _ = z * (k⁻¹ * c * k) := by group
    have e : c = k * (k⁻¹ * c * k) * k⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem hkM (hHM hc')) (M.inv_mem hkM)
  have hfus : ∀ x ∈ M, ∀ y ∈ M, CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x → IsConj x y →
      ∃ k ∈ M, k * x * k⁻¹ = y := by
    intro x hxM y hyM hx hxy
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hx.2
    have hy2 : y * y = 1 := by
      rw [← hg]
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    have hy1 : y ≠ 1 := by
      rw [← hg]
      intro h1
      apply hx.1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨k₁, hk₁M, hk₁⟩ := hconj x hxM hx2 hx.1
    obtain ⟨k₂, hk₂M, hk₂⟩ := hconj y hyM hy2 hy1
    refine ⟨k₂ * k₁⁻¹, M.mul_mem hk₂M (M.inv_mem hk₁M), ?_⟩
    rw [← hk₁, ← hk₂]
    group
  have hSE := CFSG.Quasithin.isStronglyEmbedded_of_centralizer_le hne hzM hzinv hcent hfus
  have hF := CFSG.Quasithin.Kleidman.fusionStronglyEmbedded_of_isStronglyEmbedded hSE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG2 : Even (Nat.card G) := by
    have hzo : orderOf z = 2 := orderOf_eq_prime hzsq hz1
    exact even_iff_two_dvd.mpr (hzo ▸ orderOf_dvd_natCard z)
  rcases CFSG.Open.Open.bender_strongly_embedded G M hF with hcyc |
      ⟨M', N', hM', hN', hMN', -, hodd, hidx, hB⟩
  ·
    obtain ⟨a, ha2, ha1, haz, S, hzS, haS⟩ := hcomm
    refine CFSG.Quasithin.Kleidman.not_cyclic_or_quaternion (P := ↥(S : Subgroup G))
      (a := ⟨z, hzS⟩) (b := ⟨a, haS⟩) (Subtype.ext hz2) (Subtype.ext ha2) ?_ ?_ ?_ (hcyc S)
    · exact fun h1 => hz1 (congrArg Subtype.val h1)
    · exact fun h1 => ha1 (congrArg Subtype.val h1)
    · exact fun h1 => haz (congrArg Subtype.val h1).symm
  ·
    have hM'bot : M' = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M' with h1 | h1
      · exact h1
      · exfalso
        rw [h1, Subgroup.card_top] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) hG2
    have hN'top : N' = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h1 | h1
      · exfalso
        rw [h1, Subgroup.index_bot] at hidx
        exact (Nat.not_even_iff_odd.mpr hidx) hG2
      · exact h1
    subst hM'bot hN'top
    have e₀ : (↥(⊤ : Subgroup G) ⧸ (⊥ : Subgroup G).subgroupOf ⊤) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    obtain ⟨S, hS⟩ := hsyl
    have key : ∀ {B : Type} [Group B] (φ : G ≃* B) {q k : ℕ}, fusionBenderBorel B q k →
        4 ≤ q → False := by
      intro B _ φ q k hBB hq
      set Q := S.mapSurjective (f := φ.toMonoidHom) φ.surjective
      obtain ⟨-, -, -, hcard, -⟩ := hBB Q
      set ψ := Subgroup.equivMapOfInjective (S : Subgroup G) φ.toMonoidHom φ.injective
      have hmap := Subgroup.map_center_eq ψ
      have h2 : Nat.card (Subgroup.center ↥(Q : Subgroup B)) =
          Nat.card (Subgroup.center ↥((S : Subgroup G).map φ.toMonoidHom)) := rfl
      rw [h2, ← hmap, Subgroup.card_map_of_injective ψ.injective, hS] at hcard
      omega
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_psl2_borel f hf)
        (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_psu3_borel f hf)
        (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf)
    · exact key (e₀.symm.trans e) (CFSG.Open.Open.bender_suzuki_borel a ha)
        (by calc 4 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))

end CFSG.GH74.QTGen4.Ku

end
