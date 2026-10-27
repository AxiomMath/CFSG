module

public import CFSG.LargeExtraspecial.S4Span

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_pow3_lift {θ : S.O} (hθ : θ ∈ S.Mbar) (hθ3 : θ ^ 3 = 1) :
    ∃ c : S.M, c ^ 3 = 1 ∧ S.ρ c = θ := by
  obtain ⟨c₀, rfl⟩ := MonoidHom.mem_range.mp hθ
  have h3 : ((c₀ ^ 3 : S.M) : G) ∈ S.QG := by
    rw [← S.ρ_eq_one_iff, map_pow, hθ3]
  have h4 := S.pow_four_eq_one h3
  refine ⟨c₀ ^ 4, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow, ← pow_mul, show 4 * 3 = 3 * 4 by norm_num, pow_mul]
    simpa using h4
  · rw [map_pow, show 4 = 1 + 3 by norm_num, pow_add, hθ3, mul_one, pow_one]

theorem apply_apply_apply_eq {θ : S.O} (hθ3 : θ ^ 3 = 1) (v : S.Qt) :
    (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v := by
  have h := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) hθ3
  simpa [pow_three, CFSG.LargeExtraspecial.S4.coe_mul_apply] using h

theorem sum_apply_eq_zero {θ : S.O} (hθ3 : θ ^ 3 = 1)
    (hfpf : ∀ v : S.Qt, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) (v : S.Qt) :
    v + (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v +
      (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = 0 := by
  apply hfpf
  rw [map_add, map_add, apply_apply_apply_eq hθ3]
  abel

theorem card_fiber_rho {τ : S.O} (hτ : τ ∈ S.Mbar) :
    Nat.card {m : S.M // S.ρ m = τ} = 2 ^ (1 + 2 * S.width) := by
  obtain ⟨m₀, hm₀⟩ := MonoidHom.mem_range.mp hτ
  rw [← S.card_Q_eq, ← S.card_QG_eq_card_Q]
  refine Nat.card_congr
    { toFun := fun m => ⟨((m₀⁻¹ * m.1 : S.M) : G), ?_⟩
      invFun := fun q => ⟨m₀ * ⟨q.1, S.QG_le_M q.2⟩, ?_⟩
      left_inv := fun m => ?_
      right_inv := fun q => ?_ }
  · rw [← S.ρ_eq_one_iff, map_mul, map_inv, hm₀, m.2, inv_mul_cancel]
  · rw [map_mul, hm₀, (S.ρ_eq_one_iff ⟨q.1, S.QG_le_M q.2⟩).mpr q.2, mul_one]
  · apply Subtype.ext
    show m₀ * (m₀⁻¹ * m.1) = m.1
    group
  · apply Subtype.ext
    simp

theorem exists_comm_lift {c : S.M} (hc3 : c ^ 3 = 1) {τ : S.O} (hτ : τ ∈ S.Mbar)
    (hcτ : S.ρ c * τ = τ * S.ρ c) : ∃ s : S.M, S.ρ s = τ ∧ c * s = s * c := by
  classical
  let X := {m : S.M // S.ρ m = τ}
  letI : Fintype X := Fintype.ofFinite X
  have hconj : ∀ m : S.M, S.ρ m = τ → S.ρ (c * m * c⁻¹) = τ := by
    intro m hm
    rw [map_mul, map_mul, map_inv, hm, hcτ, mul_inv_cancel_right]
  let f : Function.End X := fun m => ⟨c * m.1 * c⁻¹, hconj m.1 m.2⟩
  have hf3 : ∀ m : X, f (f (f m)) = m := by
    intro m
    apply Subtype.ext
    apply Subtype.ext
    have h3 : (c : G) * c * c = 1 := by
      have := congrArg (fun x : S.M => (x : G)) hc3
      simpa [pow_three, mul_assoc] using this
    change (c : G) * ((c : G) * ((c : G) * (m.1 : G) * (c : G)⁻¹) * (c : G)⁻¹) * (c : G)⁻¹ = m.1
    calc (c : G) * ((c : G) * ((c : G) * (m.1 : G) * (c : G)⁻¹) * (c : G)⁻¹) * (c : G)⁻¹
        = ((c : G) * c * c) * (m.1 : G) * ((c : G) * c * c)⁻¹ := by group
      _ = m.1 := by rw [h3]; group
  have hf : f ^ 3 ^ 1 = 1 := by
    funext m
    change f (f (f m)) = m
    exact hf3 m
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (α := X) (f := f) hf
  by_contra hno
  push Not at hno
  have hfix : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨m, hm⟩
    have hfm : f m = m := hm
    apply hno m.1 m.2
    have := congrArg (fun x : X => (x.1 : G)) hfm
    change (c : G) * (m.1 : G) * (c : G)⁻¹ = (m.1 : G) at this
    apply Subtype.ext
    calc (c : G) * (m.1 : G) = (c : G) * (m.1 : G) * (c : G)⁻¹ * (c : G) := by group
      _ = (m.1 : G) * (c : G) := by rw [this]
  rw [hfix] at hmod
  have hX : Fintype.card X = 2 ^ (1 + 2 * S.width) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fiber_rho hτ
  rw [hX] at hmod
  have h3 : 3 ∣ 2 ^ (1 + 2 * S.width) := (Nat.modEq_zero_iff_dvd).mp hmod
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem conj_eq_of_fixed {c s : S.M} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ v : S.Qt, (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) (hcs : c * s = s * c)
    {u : G} (hu : u ∈ S.QG)
    (hfix : (S.ρ s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) = S.cl u) :
    (s : G) * u * (s : G)⁻¹ = u := by
  have hcs' : (c : G) * s = s * c := congrArg (fun x : S.M => (x : G)) hcs
  have hsu : (s : G) * u * (s : G)⁻¹ ∈ S.QG := S.conj_mem_QG s.2 hu
  have hcl : S.cl ((s : G) * u * (s : G)⁻¹) = S.cl u := by
    rw [← S.ρ_cl s hu]
    exact hfix
  rcases (S.cl_eq_cl_iff hu hsu).mp hcl.symm with h | h
  · exact h
  · exfalso
    set u₂ : G := (c : G) * u * (c : G)⁻¹ with hu₂
    set u₃ : G := (c : G) * u₂ * (c : G)⁻¹ with hu₃
    have hu₂Q : u₂ ∈ S.QG := S.conj_mem_QG c.2 hu
    have hu₃Q : u₃ ∈ S.QG := S.conj_mem_QG c.2 hu₂Q
    have hzc : ∀ y : G, y ∈ S.M → y * S.z = S.z * y := fun y hy => S.z_comm hy
    have hsu₂ : (s : G) * u₂ * (s : G)⁻¹ = u₂ * S.z := by
      calc (s : G) * u₂ * (s : G)⁻¹
          = (c : G) * ((s : G) * u * (s : G)⁻¹) * (c : G)⁻¹ := by
            rw [hu₂]
            calc (s : G) * ((c : G) * u * (c : G)⁻¹) * (s : G)⁻¹
                = ((s : G) * c) * u * ((s : G) * c)⁻¹ := by group
              _ = ((c : G) * s) * u * ((c : G) * s)⁻¹ := by rw [hcs']
              _ = (c : G) * ((s : G) * u * (s : G)⁻¹) * (c : G)⁻¹ := by group
        _ = (c : G) * (u * S.z) * (c : G)⁻¹ := by rw [h]
        _ = u₂ * S.z := by
            have hcz := hzc c c.2
            calc (c : G) * (u * S.z) * (c : G)⁻¹ = (c : G) * u * (c : G)⁻¹ * ((c : G) * S.z * (c : G)⁻¹) := by
                  group
              _ = u₂ * S.z := by
                  rw [hcz, hu₂]
                  group
    have hsu₃ : (s : G) * u₃ * (s : G)⁻¹ = u₃ * S.z := by
      calc (s : G) * u₃ * (s : G)⁻¹
          = (c : G) * ((s : G) * u₂ * (s : G)⁻¹) * (c : G)⁻¹ := by
            rw [hu₃]
            calc (s : G) * ((c : G) * u₂ * (c : G)⁻¹) * (s : G)⁻¹
                = ((s : G) * c) * u₂ * ((s : G) * c)⁻¹ := by group
              _ = ((c : G) * s) * u₂ * ((c : G) * s)⁻¹ := by rw [hcs']
              _ = (c : G) * ((s : G) * u₂ * (s : G)⁻¹) * (c : G)⁻¹ := by group
        _ = (c : G) * (u₂ * S.z) * (c : G)⁻¹ := by rw [hsu₂]
        _ = u₃ * S.z := by
            have hcz := hzc c c.2
            calc (c : G) * (u₂ * S.z) * (c : G)⁻¹ = (c : G) * u₂ * (c : G)⁻¹ * ((c : G) * S.z * (c : G)⁻¹) := by
                  group
              _ = u₃ * S.z := by
                  rw [hcz, hu₃]
                  group
    set w : G := u * u₂ * u₃ with hw
    have hwQ : w ∈ S.QG := S.QG.mul_mem (S.QG.mul_mem hu hu₂Q) hu₃Q
    have hcl₂ : S.cl u₂ = (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) := (S.ρ_cl c hu).symm
    have hcl₃ : S.cl u₃ = (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u₂) := (S.ρ_cl c hu₂Q).symm
    have hclw : S.cl w = 0 := by
      rw [hw, S.cl_mul (S.QG.mul_mem hu hu₂Q) hu₃Q, S.cl_mul hu hu₂Q, hcl₃, hcl₂]
      exact sum_apply_eq_zero (θ := S.ρ c) (by rw [← map_pow, hc3, map_one]) hfpf _
    have hwz : w = 1 ∨ w = S.z := (S.cl_eq_zero_iff hwQ).mp hclw
    have hswc : (s : G) * w * (s : G)⁻¹ = w := by
      rcases hwz with h1 | h1
      · rw [h1]; group
      · rw [h1]
        have := S.z_comm s.2
        calc (s : G) * S.z * (s : G)⁻¹ = S.z * (s : G) * (s : G)⁻¹ := by rw [this]
          _ = S.z := by group
    have hsw : (s : G) * w * (s : G)⁻¹ = w * S.z := by
      calc (s : G) * w * (s : G)⁻¹
          = ((s : G) * u * (s : G)⁻¹) * ((s : G) * u₂ * (s : G)⁻¹) * ((s : G) * u₃ * (s : G)⁻¹) := by
            rw [hw]; group
        _ = (u * S.z) * (u₂ * S.z) * (u₃ * S.z) := by rw [h, hsu₂, hsu₃]
        _ = w * S.z := by
            have h1 : u₂ * S.z = S.z * u₂ := (S.z_comm_QG hu₂Q)
            have h2 : u₃ * S.z = S.z * u₃ := (S.z_comm_QG hu₃Q)
            have h3 : u * S.z = S.z * u := (S.z_comm_QG hu)
            have hzz : S.z * S.z = 1 := S.z_mul_z
            calc (u * S.z) * (u₂ * S.z) * (u₃ * S.z)
                = u * (S.z * u₂) * (S.z * (u₃ * S.z)) := by group
              _ = u * (u₂ * S.z) * (S.z * (u₃ * S.z)) := by rw [← h1]
              _ = u * u₂ * (S.z * S.z) * (u₃ * S.z) := by group
              _ = u * u₂ * u₃ * S.z := by rw [hzz]; group
              _ = w * S.z := by rw [hw]
    have hwz' : w * S.z = w := hsw.symm.trans hswc
    apply S.z_ne_one
    have := congrArg (fun x => w⁻¹ * x) hwz'
    simpa using this

theorem sq_eq_one_or_z_of_comm {c s : S.M} (hc3 : c ^ 3 = 1)
    (hfpf : ∀ v : S.Qt, (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0) (hcs : c * s = s * c)
    (hs2 : S.ρ s * S.ρ s = 1) : (s : G) * (s : G) = 1 ∨ (s : G) * (s : G) = S.z := by
  have hsq : ((s * s : S.M) : G) ∈ S.QG := (S.ρ_eq_one_iff _).mp (by rw [map_mul]; exact hs2)
  have hsq' : (s : G) * (s : G) ∈ S.QG := hsq
  have hcs' : (c : G) * s = s * c := congrArg (fun x : S.M => (x : G)) hcs
  have hfix : (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((s : G) * s)) = S.cl ((s : G) * s) := by
    rw [S.ρ_cl c hsq']
    congr 1
    calc (c : G) * ((s : G) * s) * (c : G)⁻¹ = ((c : G) * s) * s * (c : G)⁻¹ := by group
      _ = (s : G) * c * s * (c : G)⁻¹ := by rw [hcs']
      _ = (s : G) * ((c : G) * s) * (c : G)⁻¹ := by group
      _ = (s : G) * (s * c) * (c : G)⁻¹ := by rw [hcs']
      _ = (s : G) * s := by group
  exact (S.cl_eq_zero_iff hsq').mp (hfpf _ hfix)

theorem exists_conj_shift {s : S.M} {τ : S.O} (hs : S.ρ s = τ) (hττ : τ * τ = 1) {u q : G}
    (hu : u ∈ S.QG) (hq : q ∈ S.QG) :
    ∃ u' ∈ S.QG, q * ((s : G) * u) * q⁻¹ = (s : G) * u' ∧
      S.cl u' = S.cl u + ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) + S.cl q) := by
  have hsinv : (s : G)⁻¹ * q * (s : G) ∈ S.QG := by
    have := S.conj_mem_QG (S.M.inv_mem s.2) hq
    simpa using this
  have h1 : S.cl ((s : G)⁻¹ * q * (s : G)) = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) := by
    have h := S.ρ_cl s⁻¹ hq
    have hτ : S.ρ s⁻¹ = τ := by rw [map_inv, hs]; exact inv_eq_of_mul_eq_one_right hττ
    rw [hτ] at h
    rw [h]
    simp
  refine ⟨(s : G)⁻¹ * q * (s : G) * u * q⁻¹, ?_, by group, ?_⟩
  · exact S.QG.mul_mem (S.QG.mul_mem hsinv hu) (S.QG.inv_mem hq)
  · rw [S.cl_mul (S.QG.mul_mem hsinv hu) (S.QG.inv_mem hq), S.cl_mul hsinv hu, S.cl_inv hq, h1]
    abel

end CFSG.GF2Type.Smith1979.IdxFour
