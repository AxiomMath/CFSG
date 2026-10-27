module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LUna
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LEig

import CFSG.LinearAlgebra.F2PlaneMaps

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Restrict

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {G : Type*} [Group G]

@[expose] def a6grpRes (ρ : G →* (V ≃ₗ[ZMod 2] V)) (U : Submodule (ZMod 2) V)
    (hU : ∀ g : G, Stable (ρ g) U) : G →* (U ≃ₗ[ZMod 2] U) where
  toFun g :=
    { toFun := fun u => ⟨ρ g u, hU g u u.2⟩
      map_add' := fun u v => Subtype.ext (map_add (ρ g) (u : V) (v : V))
      map_smul' := fun r u => Subtype.ext (map_smul (ρ g) r (u : V))
      invFun := fun u => ⟨ρ g⁻¹ u, hU g⁻¹ u u.2⟩
      left_inv := fun u => Subtype.ext (by
        show (ρ g⁻¹) ((ρ g) (u : V)) = (u : V)
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl)
      right_inv := fun u => Subtype.ext (by
        show (ρ g) ((ρ g⁻¹) (u : V)) = (u : V)
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl) }
  map_one' := by
    ext u
    show ρ 1 u = u
    rw [map_one]; rfl
  map_mul' := fun g h => by
    ext u
    show ρ (g * h) u = ρ g (ρ h u)
    rw [map_mul]; rfl

end Restrict

section Arith

theorem a6grp_two_pow_modEq {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] {g : U ≃ₗ[ZMod 2] U} {p : ℕ} [Fact p.Prime] (hg : g ^ p = 1)
    (hfix : ∀ u : U, g u = u → u = 0) : 2 ^ finrank (ZMod 2) U ≡ 1 [MOD p] := by
  classical
  haveI : Finite U := Module.finite_of_finite (ZMod 2)
  haveI : Fintype U := Fintype.ofFinite U
  let φ : Function.End U := MulAction.toEndHom (M := U ≃ₗ[ZMod 2] U) (α := U) g
  have hφ : φ ^ (p ^ 1) = 1 := by
    rw [pow_one, ← map_pow, hg, map_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := U) (f := φ) (p := p) (n := 1) hφ
  haveI : Unique (Function.fixedPoints φ) :=
    ⟨⟨⟨0, show φ 0 = 0 from map_zero g⟩⟩, fun y => Subtype.ext (hfix _ y.2)⟩
  have hU : Nat.card U = 2 ^ finrank (ZMod 2) U := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    simpa using this
  have h1 : Nat.card (Function.fixedPoints φ) = 1 := Nat.card_unique
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h1, hU] at hmod
  exact hmod

theorem a6grp_dim_six {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd1 : 1 ≤ d) (hd8 : d ≤ 8)
    (h1 : p ∣ d) (h2 : p ∣ 2 ^ d - 1) : d = 6 := by
  have hpd : p ≤ d := Nat.le_of_dvd (by omega) h1
  have hp1 : 2 ≤ p := hp.two_le
  have hp8 : p ≤ 8 := by omega
  interval_cases p <;> interval_cases d <;> first | omega | (exfalso; revert hp; decide) | skip

end Arith

section Main

theorem a6grp_perfect_map_one {G H : Type*} [Group G] [Group H] [Group.IsSolvable H]
    [Group.IsPerfect G] (f : G →* H) (g : G) : f g = 1 := by
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra h
    haveI : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have h1 : (⟨f g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {G : Type*} [Group G]

theorem a6grp_perfect_plane [Group.IsPerfect G] (ρ : G →* (V ≃ₗ[ZMod 2] V))
    (W : Submodule (ZMod 2) V) (hW : finrank (ZMod 2) W = 2) (hst : ∀ g : G, Stable (ρ g) W) :
    ∀ g : G, ∀ w ∈ W, ρ g w = w :=
  CFSG.LinearAlgebra.apply_eq_self_of_isPerfect (W := W) hW ρ hst

theorem a6grp_module_contra [Group.IsPerfect G] (ρ : G →* (V ≃ₗ[ZMod 2] V))
    (hinj : Function.Injective ρ) (hdim : finrank (ZMod 2) V = 8) {x : G}
    (hfix : ∀ v : V, ρ x v = v → v = 0) {a b c : G} (hc : c = b * a * b⁻¹ * a⁻¹)
    (hcc : ∀ j : G, j * c = c * j) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcp : orderOf c = p) :
    False := by
  haveI : Fact p.Prime := ⟨hp⟩
  set g : V ≃ₗ[ZMod 2] V := ρ c with hg
  have hgp : orderOf g = p := by rw [hg, orderOf_injective ρ hinj c, hcp]
  have hodd : Odd (orderOf g) := by rw [hgp]; exact hp.odd_of_ne_two hp2
  have hcompl := isCompl_fixSp_range_nu g hodd
  set U : Submodule (ZMod 2) V := LinearMap.range (nu g) with hU
  set W : Submodule (ZMod 2) V := fixSp g with hW
  have hcv : ∀ (j : G) (v : V), ρ j (g v) = g (ρ j v) := fun j v => by
    have h1 : ρ j * g = g * ρ j := by rw [hg, ← map_mul, ← map_mul, hcc j]
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h1
  have hstU : ∀ j : G, Stable (ρ j) U := by
    intro j u hu
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hu
    refine LinearMap.mem_range.mpr ⟨ρ j v, ?_⟩
    rw [← hv, nu_apply, nu_apply, map_sub, hcv]
  have hstW : ∀ j : G, Stable (ρ j) W := by
    intro j w hw
    have hw' : g w = w := by
      have h1 := LinearMap.mem_ker.mp hw
      rw [nu_apply, sub_eq_zero] at h1
      exact h1
    show nu g (ρ j w) = 0
    rw [nu_apply, ← hcv, hw', sub_self]
  have hU0 : 1 ≤ finrank (ZMod 2) U := by
    by_contra hlt
    have hbot : U = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    have hg1 : g = 1 := by
      ext v
      have h1 : nu g v ∈ U := LinearMap.mem_range.mpr ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot, nu_apply, sub_eq_zero] at h1
      simpa using h1
    have h2 : c = 1 := hinj (by rw [map_one]; exact hg1)
    rw [h2, orderOf_one] at hcp
    exact hp.one_lt.ne' hcp.symm
  let ρU := a6grpRes ρ U hstU
  have hfixU : ∀ u : U, ρU c u = u → u = 0 := by
    intro u hu
    have h1 : g (u : V) = u := congrArg Subtype.val hu
    have h2 : (u : V) ∈ W := by
      show nu g u = 0
      rw [nu_apply, h1, sub_self]
    have h4 : (u : V) ∈ W ⊓ U := ⟨h2, u.2⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at h4
    exact Subtype.ext h4
  have hcpow : c ^ p = 1 := by rw [← hcp]; exact pow_orderOf_eq_one c
  have hpowU : (ρU c) ^ p = 1 := by rw [← map_pow, hcpow, map_one]
  have hne1 : ρU c ≠ 1 := by
    intro h1
    obtain ⟨u, hu⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank (ZMod 2) U)
    exact hu (hfixU u (by rw [h1]; rfl))
  have hordU : orderOf (ρU c) = p := orderOf_eq_prime hpowU hne1
  have hcU : ρU c = ρU b * ρU a * (ρU b)⁻¹ * (ρU a)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hc]
  have hdvd : p ∣ finrank (ZMod 2) U :=
    eigen_dvd hp hp2 hcU hordU (by rw [← map_mul, ← map_mul, (hcc a).symm])
      (by rw [← map_mul, ← map_mul, (hcc b).symm]) hfixU
  have hmod := a6grp_two_pow_modEq hpowU hfixU
  have hd2 : p ∣ 2 ^ finrank (ZMod 2) U - 1 :=
    (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod.symm
  have hd8 : finrank (ZMod 2) U ≤ 8 := hdim ▸ Submodule.finrank_le U
  have hd6 := a6grp_dim_six hp hp2 hU0 hd8 hdvd hd2
  have hW2 : finrank (ZMod 2) W = 2 := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  have hall := a6grp_perfect_plane ρ W hW2 hstW
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (by omega : 0 < finrank (ZMod 2) W)
  exact hw (Subtype.ext (hfix w (hall x w w.2)))

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
