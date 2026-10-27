module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Lift

variable {A : Type} [Group A] [Finite A] {J : Subgroup A} {Y : Type} [Group Y]

theorem exists_involution_section (ψ : ↥J →* Y) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center ↥J) {s : Y} (hs : orderOf s = 2) {G₀ : Type} [Group G₀]
    [Group.IsPerfect G₀] (ρ : G₀ →* Y) (hρ : Function.Injective ρ)
    (hcomm : ∀ g, s * ρ g = ρ g * s) :
    ∃ x : A, orderOf x = 2 ∧ IsSection G₀ ↥(centralizer ({x} : Set A)) := by
  classical
  obtain ⟨j, hj⟩ := hψ s
  let Dt : Subgroup ↥J := ρ.range.comap ψ
  have hcen : ∀ d : ↥Dt, j * (d : ↥J) * j⁻¹ * (d : ↥J)⁻¹ ∈ center ↥J := by
    intro d
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hj]
    obtain ⟨g, hg⟩ : ψ (d : ↥J) ∈ ρ.range := d.2
    rw [← hg, hcomm g]
    group
  let θ : ↥Dt →* ↥(center ↥J) :=
    { toFun := fun d => ⟨j * (d : ↥J) * j⁻¹ * (d : ↥J)⁻¹, hcen d⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro d e
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hcen e) (d : ↥J)
        calc j * ((d * e : ↥Dt) : ↥J) * j⁻¹ * ((d * e : ↥Dt) : ↥J)⁻¹ =
            (j * (d : ↥J) * j⁻¹ * (d : ↥J)⁻¹) *
              ((d : ↥J) * (j * (e : ↥J) * j⁻¹ * (e : ↥J)⁻¹) * (d : ↥J)⁻¹) := by
              simp only [Subgroup.coe_mul, mul_inv_rev]
              group
          _ = (j * (d : ↥J) * j⁻¹ * (d : ↥J)⁻¹) * (j * (e : ↥J) * j⁻¹ * (e : ↥J)⁻¹) := by
              rw [hc]
              group }
  have hθ : commutator ↥Dt ≤ θ.ker := Abelianization.commutator_subset_ker θ
  have hj2 : j ^ 2 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hj]
    exact (orderOf_dvd_iff_pow_eq_one.mp (by rw [hs]))
  have heven : Even (orderOf (j : ↥J)) := by
    by_contra hodd
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp hodd
    have h1 : j = (j ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf j + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have h2 : j ∈ ψ.ker := by
      rw [h1]
      exact pow_mem hj2 _
    rw [MonoidHom.mem_ker, hj] at h2
    have h3 : orderOf s = 1 := by rw [h2]; exact orderOf_one
    rw [hs] at h3
    omega
  set m := orderOf (j : ↥J) with hm
  obtain ⟨n, hn⟩ := heven
  have hn0 : 0 < n := by
    have : 0 < orderOf (j : ↥J) := orderOf_pos _
    omega
  let jA : A := (j : A)
  have hordA : orderOf jA = m := Subgroup.orderOf_coe j
  let x : A := jA ^ n
  have hx2 : orderOf x = 2 := by
    have h1 : Nat.gcd (n + n) n = n := Nat.gcd_eq_right ⟨2, by ring⟩
    rw [orderOf_pow' _ hn0.ne', hordA, hn, h1, ← two_mul, Nat.mul_div_cancel _ hn0]
  have hcomm_j : ∀ d ∈ commutator ↥Dt, Commute j (d : ↥J) := by
    intro d hd
    have h1 := hθ hd
    rw [MonoidHom.mem_ker] at h1
    have h2 := congrArg (fun z : ↥(center ↥J) => (z : ↥J)) h1
    simp only [θ, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h2
    exact commutatorElement_eq_one_iff_commute.mp (by rw [commutatorElement_def]; exact h2)
  let ψD : ↥Dt →* Y := ψ.comp Dt.subtype
  have hψDrange : ψD.range = ρ.range := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      exact d.2
    · intro hy
      obtain ⟨u, hu⟩ := hψ y
      exact ⟨⟨u, by rw [Subgroup.mem_comap, hu]; exact hy⟩, hu⟩
  have hρcomm : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    have : Group.IsPerfect ↥ρ.range := Group.IsPerfect.range ρ
    exact Subgroup.commutator_eq_self
  have hmapC : (commutator ↥Dt).map ψD = ρ.range := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hψDrange, hρcomm]
  let κ : ↥(commutator ↥Dt) →* G₀ :=
    (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp
      ((ψD.comp (commutator ↥Dt).subtype).codRestrict ρ.range (fun c => c.1.2))
  have hκ : Function.Surjective κ := by
    intro g
    have hg : ρ g ∈ (commutator ↥Dt).map ψD := by
      rw [hmapC]
      exact ⟨g, rfl⟩
    obtain ⟨c, hc, hcg⟩ := hg
    refine ⟨⟨c, hc⟩, ?_⟩
    show (MonoidHom.ofInjective hρ).symm _ = g
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hcg
  have hCsec : IsSection G₀ ↥(commutator ↥Dt) := by
    refine ⟨⊤, κ.comp (Subgroup.topEquiv (G := ↥(commutator ↥Dt))).toMonoidHom, ?_⟩
    exact hκ.comp (Subgroup.topEquiv (G := ↥(commutator ↥Dt))).surjective
  let ι : ↥Dt →* A := J.subtype.comp Dt.subtype
  have hι : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hVx : (commutator ↥Dt).map ι ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : Commute jA (ι d) := (hcomm_j d hd).map J.subtype
    exact ((h1.pow_left n).symm).eq
  have hVsec : IsSection G₀ ↥((commutator ↥Dt).map ι) :=
    IsSection.of_equiv ((commutator ↥Dt).equivMapOfInjective ι hι).symm hCsec
  exact ⟨x, hx2, IsSection.of_le_le hVx hVsec⟩

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
