module

public import CFSG.GH74.GLS.Stage4.T2P71SylB
public import CFSG.GH74.GLS.IVK.Proofs2.NatModFinal
public import CFSG.GH74.GLS.Stage4.T2P71Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped Pointwise

theorem p71Sylow_proved : P71Sylow := by
  intro G _ _ Gs _ n N u hE hcard hnab
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hctx := hE.ctx
  obtain ⟨F₁, F₂, iF₁, iF₂, t, hSet, hRem⟩ := hE.setup
  obtain ⟨hw₀sq, hw₀H, -⟩ := t2Ctx_Y1 hSet hRem hE.sec5.loc rfl rfl rfl hE.q₁ hE.q₂
  obtain ⟨hz2, hu2, -, hz1, hu1, hne⟩ := T6.zu_facts hctx
  have hΩ : ∀ x ∈ N.H, x * x = 1 → x = 1 ∨ x = N.z ∨ x = u ∨ x = N.z * u :=
    t2_omega1_zu hE.rank hE.sec5.loc.H_comm hE.sec5.loc.z_mem_H hE.sec5.loc.u_mem_H hz2 hu2 hz1 hu1
      hne hw₀sq hw₀H hE.sec5.loc.w₀_inv
  have hm : N.q₁ = 3 ^ n := hE.q₁
  have hn : N.q₂ = 3 ^ n := hE.q₂
  have hMod := T6.t6Mod_of ivk_11_1b_nat hctx hm
  obtain ⟨Q⟩ : Nonempty (Sylow 3 ↥N.F) := inferInstance
  let P₀ : Subgroup G := (Q : Subgroup ↥N.F).map N.F.subtype
  have hP₀F : P₀ ≤ N.F := Subgroup.map_subtype_le _
  have hP₀p : IsPGroup 3 ↥P₀ := Q.isPGroup'.map _
  have hP₀c : Nat.card ↥P₀ = 3 ^ (Nat.card ↥N.F).factorization 3 := by
    rw [Subgroup.card_map_of_injective N.F.subtype_injective, Sylow.card_eq_multiplicity]
  obtain ⟨S, hS⟩ := T6.P71.Pst_sylow' hctx ⟨hcard⟩ hnab hΩ hMod hm hn hP₀F hP₀p hP₀c
  exact ⟨P₀, hP₀F, hP₀p, S, hS⟩

end CFSG.GH74.GLS.Stage4.Rest
