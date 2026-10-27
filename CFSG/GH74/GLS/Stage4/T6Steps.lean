module

public import CFSG.GH74.GLS.Stage4.T6Fields
public import CFSG.GH74.GLS.Stage4.T2Omega1
public import CFSG.GH74.GLS.Stage4.T6Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped Pointwise commutatorElement

@[expose] def T6RleProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : T2N3 G) (u : G) (p : ℕ), T6Ctx N u p →
    ∀ (y : G) (R : Subgroup G), T6TSdata N p y R → R ≤ R₂ N p

@[expose] def T6SylProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (N : T2N3 G) (u : G) (p : ℕ), T6Ctx N u p →
    (∀ x ∈ N.H, x * x = 1 → x = 1 ∨ x = N.z ∨ x = u ∨ x = N.z * u) →
    ∀ (y : G) (R : Subgroup G), T6TSdata N p y R → R ≤ R₂ N p →
      ∀ P₀ : Subgroup G, P₀ ≤ N.F → IsPGroup p ↥P₀ → Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p →
        ∃ T : Sylow p G, (T : Subgroup G) = (R₂ N p ⊔ N.X₁) ⊔ P₀

theorem ch6T2Sec6'_of_leaves (h11b : IVK_11_1b_nat) (hB : T6RleProp)
    (hC : T6SylProp) : Ch6T2Sec6' := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u p hz hK₁ hK₂ hq₁ hq₂ hNum hTS
    hCoord h5
  have hctx := t6Ctx_of hSet hRem hz hK₁ hK₂ hq₁ hq₂ hNum hCoord h5
  obtain ⟨hw₀sq, hw₀H, -⟩ := t2Ctx_Y1 hSet hRem h5.loc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨hz2, hu2, -, hz1, hu1, hne⟩ := zu_facts hctx
  have hΩ : ∀ x ∈ N.H, x * x = 1 → x = 1 ∨ x = N.z ∨ x = u ∨ x = N.z * u :=
    t2_omega1_zu hr h5.loc.H_comm h5.loc.z_mem_H h5.loc.u_mem_H hz2 hu2 hz1 hu1 hne hw₀sq hw₀H
      h5.loc.w₀_inv
  subst hz hK₁ hK₂ hq₂
  obtain ⟨y, hyK, hyz, hyp, hR⟩ := hTS
  have hloc := h5.loc
  have hX₂K₂ : N.X₂ ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_left
  have hX₂p : IsPGroup p ↥N.X₂ := by
    obtain ⟨n, hn'⟩ := hctx.q₂_pow
    exact IsPGroup.of_card (n := n) (by rw [hloc.card_X₂, hn'])
  obtain ⟨R, hRp, hXR, hRC, hRcard, hRcen, hXcomm, hRcomm, hRinv, hRy⟩ :=
    hR N.X₂ hX₂K₂ hX₂p hloc.card_X₂
  have hTSd : T6TSdata N p y R :=
    ⟨hyK, hyz, hyp, hRp, hXR, hRC, hRcard, hRcen, hXcomm, hRcomm, hRinv, hRy⟩
  have hRle := hB G N u p hctx y R hTSd
  have : Fact p.Prime := ⟨hctx.prime⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥N.F) := inferInstance
  let P₀ : Subgroup G := (Q : Subgroup ↥N.F).map N.F.subtype
  have hP₀F : P₀ ≤ N.F := Subgroup.map_subtype_le _
  have hP₀p : IsPGroup p ↥P₀ := Q.isPGroup'.map _
  have hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p := by
    rw [Subgroup.card_map_of_injective N.F.subtype_injective, Sylow.card_eq_multiplicity]
  have hSyl := hC G N u p hctx hΩ y R hTSd hRle P₀ hP₀F hP₀p hP₀c
  exact ⟨P₀, R₂ N p ⊔ N.X₁, ch6S6_of_parts h11b hctx hTSd hRle P₀ hP₀F hP₀p hSyl⟩

end CFSG.GH74.GLS.Stage4.Rest.T6
