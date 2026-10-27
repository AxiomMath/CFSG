module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundBasic
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundMinusAux

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

theorem diagBoundMinus_holds : DiagBoundMinus := by
  intro V _ _ hV Y n hn hnat
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  obtain ⟨l, hl1, hlk⟩ := Diag.Bound.exists_unit_pow n (by omega)
  obtain ⟨y, hyθ⟩ : ∃ y : ↥Y, θ y = Diag.Bound.diagHom (Fq (2 * n)) l :=
    ⟨θ.symm _, θ.apply_symm_apply _⟩
  have hy1 : (y : MulAut V) ≠ 1 := by
    intro h
    have h1 : y = 1 := OneMemClass.coe_eq_one.mp h
    have h2 : Diag.Bound.diagHom (Fq (2 * n)) l = 1 := by rw [← hyθ, h1, map_one]
    apply hl1
    have h3 := Diag.Bound.diagHom_apply_zero_zero (Fq (2 * n)) l
    rw [h2] at h3
    exact Units.ext (by simpa using h3.symm)
  have hpow : (y : MulAut V) ^ (2 ^ n + 1) = 1 := by
    have h1 : y ^ (2 ^ n + 1) = 1 := by
      apply θ.injective
      rw [map_pow, hyθ, ← map_pow, hlk, map_one, map_one]
    have := congrArg (fun z : ↥Y => (z : MulAut V)) h1
    simpa using this
  have hodd : Odd (orderOf (y : MulAut V)) := by
    have hd : orderOf (y : MulAut V) ∣ 2 ^ n + 1 := orderOf_dvd_of_pow_eq_one hpow
    have hodd' : Odd (2 ^ n + 1) := by
      have : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact this.add_one
    exact Odd.of_dvd_nat hodd' hd
  refine ⟨(y : MulAut V), y.2, hy1, hodd, ?_⟩
  obtain ⟨u₀, hu₀⟩ := hβs (Multiplicative.ofAdd ⟨Diag.Bound.e11 n, Diag.Bound.e11_mem n⟩)
  have hyu : (y : MulAut V) (u₀ : V) ∈ commV Y := hinv y y.2 u₀ u₀.2
  have hyu₀ : (y : MulAut V) (u₀ : V) = u₀ := by
    have h := hβe y u₀ hyu
    rw [hyθ, hu₀, Diag.Bound.act_e11 n l hlk, ← hu₀] at h
    exact congrArg Subtype.val (hβinj h)
  have hu₀ne : (u₀ : V) ≠ 1 := by
    intro h
    have h1 : u₀ = 1 := Subtype.ext h
    rw [h1, map_one] at hu₀
    have h2 : Diag.Bound.e11 n = 0 := by
      have := congrArg (fun m : Multiplicative (hermSub n) =>
        ((Multiplicative.toAdd m : hermSub n) : Matrix (Fin 2) (Fin 2) (Fq (2 * n)))) hu₀
      simpa using this.symm
    exact Diag.Bound.e11_ne_zero n h2
  have hle : commV (Subgroup.zpowers (y : MulAut V)) ≤ commV Y :=
    Diag.Bound.commV_zpowers_le y.2
  have hinj := Diag.Bound.injective_comp_inclusion hV y.2 hodd (Z := ⊥) bot_le β hβk
  have hnot : ∀ r : ↥(commV (Subgroup.zpowers (y : MulAut V))),
      β (Subgroup.inclusion hle r) ≠ β u₀ := by
    intro r hr
    have h1 : Subgroup.inclusion hle r = u₀ := hβinj hr
    have h2 : (r : V) = (u₀ : V) := congrArg Subtype.val h1
    have h3 : (u₀ : V) ∈ commV (Subgroup.zpowers (y : MulAut V)) := h2 ▸ r.2
    exact hu₀ne (Diag.Bound.eq_one_of_mem_commV_zpowers_of_fixed hV hodd h3 hyu₀)
  have hlt : Nat.card ↥(commV (Subgroup.zpowers (y : MulAut V))) <
      Nat.card (Multiplicative (hermSub n)) := by
    by_contra hcon
    obtain ⟨r, hr⟩ := (hinj.bijective_of_nat_card_le (not_lt.mp hcon)).2 (β u₀)
    exact hnot r hr
  calc Nat.card ↥(commV (Subgroup.zpowers (y : MulAut V)))
      < Nat.card (Multiplicative (hermSub n)) := hlt
    _ = Nat.card (hermSub n) := Nat.card_congr Multiplicative.toAdd
    _ ≤ 2 ^ (4 * n) := Diag.Bound.card_hermSub_le n (by omega)

end CFSG.CGT.PushingUpLit.CGT6
