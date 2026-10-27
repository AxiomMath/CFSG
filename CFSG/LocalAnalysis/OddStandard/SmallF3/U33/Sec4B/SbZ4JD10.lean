module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD9
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JD7

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {Q Y V V' B : Subgroup H} {ρ t τ l y z v₁ v₂ : H}

private theorem rho_conj_sq {G : Type*} [Group G] {r g : G} (h : r ^ 3 = 1) :
    r * (r * g * r⁻¹) * r⁻¹ = r⁻¹ * g * r := by
  have h2 : r * r = r⁻¹ := by
    have h3 : r * (r * r) = 1 := by
      rw [show r * (r * r) = r ^ 3 by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
        group]
      exact h
    exact eq_inv_of_mul_eq_one_right h3
  rw [show r * (r * g * r⁻¹) * r⁻¹ = (r * r) * g * (r * r)⁻¹ by group, h2, inv_inv]

namespace ZJData

variable (h : ZJData Q Y V V' B ρ t τ l y z v₁ v₂) include h

variable {Mh : Subgroup H} (hMh : IsZJMh y z v₁ v₂ Mh) include hMh

variable {Mc : Subgroup H} (hMc : IsZJMc ρ Q Mh Mc) include hMc

theorem zjNorm_mem_V {m : H} (hm : m ∈ Mc) :
    m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ) ∈ V := by
  set m' : H := ρ * m * ρ⁻¹ with hm'def
  set m'' : H := ρ⁻¹ * m * ρ with hm''def
  set n : H := m * m' * m'' with hndef
  have hmMh : m ∈ Mh := h.Mc_le_Mh hMh hMc hm
  have hnQ : n ∈ Q := by
    rw [hndef, hm'def, hm''def]
    simpa [zjNorm] using ((hMc m).mp hm).2
  have hnMc : n ∈ Mc := h.Q_le_Mc hMh hMc hnQ
  have hconj : ρ * n * ρ⁻¹ = m⁻¹ * n * m := by
    rw [hndef, hm'def, hm''def]
    have h1 : ρ * (m * (ρ * m * ρ⁻¹) * (ρ⁻¹ * m * ρ)) * ρ⁻¹
        = (ρ * m * ρ⁻¹) * (ρ * (ρ * m * ρ⁻¹) * ρ⁻¹)
          * (ρ * (ρ⁻¹ * m * ρ) * ρ⁻¹) := by group
    have h2 : ρ * (ρ * m * ρ⁻¹) * ρ⁻¹ = ρ⁻¹ * m * ρ := rho_conj_sq (g := m) h.rho_pow_three
    have h3 : ρ * (ρ⁻¹ * m * ρ) * ρ⁻¹ = m := by group
    rw [h1, h2, h3]
    group
  have hcomm : ρ * n * ρ⁻¹ * n⁻¹ ∈ V := by
    rw [hconj]
    have hmem := h.Mh_comm_Q hMh (Mh.inv_mem hmMh) hnQ
    simpa [mul_assoc] using hmem
  exact h.Mc_fpf_V hMh hMc hnMc hcomm

theorem Mc_comm_rho_eq_one {m : H} (hm : m ∈ Mc) :
    m * (ρ * m * ρ⁻¹) = (ρ * m * ρ⁻¹) * m := by
  set m' : H := ρ * m * ρ⁻¹ with hm'def
  set m'' : H := ρ⁻¹ * m * ρ with hm''def
  set n : H := m * m' * m'' with hndef
  have hmMh : m ∈ Mh := h.Mc_le_Mh hMh hMc hm
  have hm'Mc : m' ∈ Mc := by rw [hm'def]; exact h.Mc_conj_rho hMh hMc hm
  have hm''Mc : m'' ∈ Mc := by
    have h1 : m'' = ρ * m' * ρ⁻¹ := by
      rw [hm''def, hm'def]
      exact (rho_conj_sq (g := m) h.rho_pow_three).symm
    rw [h1]
    exact h.Mc_conj_rho hMh hMc hm'Mc
  have hm'Mh : m' ∈ Mh := h.Mc_le_Mh hMh hMc hm'Mc
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := fun x hx => h.Y_le_Q (hVY hx)
  have hnV : n ∈ V := by
    rw [hndef, hm'def, hm''def]
    exact h.zjNorm_mem_V hMh hMc hm
  have hcV : ⁅m, m'⁆ ∈ V := by
    rw [commutatorElement_def]
    exact h.Mc_comm_mem_V hMh hMc hm hm'Mc
  have hnm : n * m'⁻¹ * n⁻¹ = m'⁻¹ := by
    have h1 : m' * n * m'⁻¹ = n := h.Mh_cent_V hMh hm'Mh hnV
    have h2 : m' * n = n * m' := by
      calc m' * n = m' * n * m'⁻¹ * m' := by group
        _ = n * m' := by rw [h1]
    have hnm' : n * m'⁻¹ = m'⁻¹ * n := by
      calc n * m'⁻¹ = m'⁻¹ * (m' * n) * m'⁻¹ := by group
        _ = m'⁻¹ * (n * m') * m'⁻¹ := by rw [h2]
        _ = m'⁻¹ * n := by group
    rw [hnm']
    group
  have hm''eq : m'' = m'⁻¹ * m⁻¹ * n := by
    rw [hndef]
    group
  have hkey : ⁅m', m''⁆ = m⁻¹ * (n * m'⁻¹ * n⁻¹) * (m * m') := by
    rw [commutatorElement_def, hm''eq]
    group
  have hB : ⁅m', m''⁆ = ⁅m, m'⁆ := by
    rw [hkey, hnm]
    have hcm : m * m' = ⁅m, m'⁆ * (m' * m) := by
      rw [commutatorElement_def]
      group
    rw [hcm]
    have hc_m' : m'⁻¹ * ⁅m, m'⁆ * m' = ⁅m, m'⁆ := by
      have hh := h.Mh_cent_V hMh (Mh.inv_mem hm'Mh) hcV
      simpa using hh
    have hc_m : m⁻¹ * ⁅m, m'⁆ * m = ⁅m, m'⁆ := by
      have hh := h.Mh_cent_V hMh (Mh.inv_mem hmMh) hcV
      simpa using hh
    calc m⁻¹ * m'⁻¹ * (⁅m, m'⁆ * (m' * m))
        = m⁻¹ * (m'⁻¹ * ⁅m, m'⁆ * m') * m := by group
      _ = m⁻¹ * ⁅m, m'⁆ * m := by rw [hc_m']
      _ = ⁅m, m'⁆ := hc_m
  have hA : ρ * ⁅m, m'⁆ * ρ⁻¹ = ⁅m, m'⁆ := by
    rw [conjugate_commutatorElement (g₁ := m) (g₂ := m') (g₃ := ρ)]
    have hm''ρ : ρ * m' * ρ⁻¹ = m'' := by
      rw [hm'def, hm''def]
      exact rho_conj_sq (g := m) h.rho_pow_three
    rw [hm''ρ, ← hm'def]
    exact hB
  have hc1 : ⁅m, m'⁆ = 1 := h.rho_fpf_Q ⁅m, m'⁆ (hVQ hcV) hA
  exact commutatorElement_eq_one_iff_mul_comm.mp hc1

theorem card_ge_sixteen_of_rho_inv {U : Subgroup H} (hUQ : U ≤ Q) (hVU : V ≤ U)
    (hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U) {u : H} (hu : u ∈ U) (huV : u ∉ V) :
    16 ≤ Nat.card U := by
  have hVY : V ≤ Y := by rw [h.Y_eq]; exact le_sup_left
  have hVQ : V ≤ Q := fun x hx => h.Y_le_Q (hVY hx)
  have hcardQ : Nat.card Q = 2 ^ 6 := by rw [h.card_Q]; norm_num
  have hUdiv : Nat.card U ∣ 2 ^ 6 := by
    have hh := Subgroup.card_dvd_of_le hUQ
    rwa [hcardQ] at hh
  have huMc : u ∈ Mc := h.Q_le_Mc hMh hMc (hUQ hu)
  have h3 : 3 ≤ V.relIndex U := by
    by_contra hlt
    have hlt' : V.relIndex U < 3 := by omega
    haveI : V.IsFiniteRelIndex U :=
      Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
    have hne : V.relIndex U ≠ 0 := Subgroup.relIndex_ne_zero (H := V) (K := U)
    have hcases : V.relIndex U = 1 ∨ V.relIndex U = 2 := by omega
    rcases hcases with h1 | h2
    · exact huV ((Subgroup.relIndex_eq_one.mp h1) hu)
    · obtain ⟨a, haU, haxor⟩ :=
        (Subgroup.relIndex_eq_two_iff (H := V) (K := U)).mp h2
      have huaV : u * a ∈ V := by
        rcases haxor u hu with h | h
        · exact h.1
        · exact absurd h.1 huV
      let u' : H := ρ * u * ρ⁻¹
      have hu'U : u' ∈ U := hρU u hu
      have hu'V : u' ∉ V := by
        intro hV
        apply huV
        have key : ρ⁻¹ * u' * ρ = u := by
          rw [show u' = ρ * u * ρ⁻¹ by rfl]
          group
        have hmem : ρ⁻¹ * u' * ρ ∈ V := by
          simpa using h.normal_V ρ⁻¹ u' hV
        rwa [key] at hmem
      have hu'aV : u' * a ∈ V := by
        rcases haxor u' hu'U with h | h
        · exact h.1
        · exact absurd h.1 hu'V
      have hconjV : u⁻¹ * u' ∈ V := by
        have hmem : (u * a)⁻¹ * (u' * a) ∈ V := V.mul_mem (V.inv_mem huaV) hu'aV
        have hconj := h.normal_V a ((u * a)⁻¹ * (u' * a)) hmem
        have key : a * ((u * a)⁻¹ * (u' * a)) * a⁻¹ = u⁻¹ * u' := by group
        rwa [key] at hconj
      have hu'uV : u' * u⁻¹ ∈ V := by
        rw [h.Q_comm u' (hUQ hu'U) u⁻¹ (Q.inv_mem (hUQ hu))]
        exact hconjV
      have hfpf : ρ * u * ρ⁻¹ * u⁻¹ ∈ V := by
        rw [show ρ * u * ρ⁻¹ = u' from rfl]
        exact hu'uV
      exact huV (h.Mc_fpf_V hMh hMc huMc hfpf)
  have hUge12 : 12 ≤ Nat.card U := by
    have hrel := Subgroup.relIndex_mul_card (H := V) (K := U)
    rw [inf_of_le_left hVU, h.card_V] at hrel
    calc 12 = 3 * 4 := by norm_num
      _ ≤ V.relIndex U * 4 := Nat.mul_le_mul_right 4 h3
      _ = Nat.card U := hrel
  obtain ⟨i, hi6, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hUdiv
  have hi4 : 4 ≤ i := by
    by_contra hlt
    have hle : i ≤ 3 := by omega
    have hpow : 2 ^ i ≤ 2 ^ 3 :=
      pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) hle
    have hcardle : Nat.card U ≤ 8 := by
      rw [hi]
      norm_num at hpow ⊢
      exact hpow
    omega
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ i := pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by norm_num) hi4
    _ = Nat.card U := hi.symm

theorem eq_Cq_of_rho_inv (hb : ZJBound t) {U : Subgroup H}
    (hUC : U ≤ Q ⊓ centralizer ({t * τ} : Set H)) (hVU : V ≤ U)
    (hρU : ∀ u ∈ U, ρ * u * ρ⁻¹ ∈ U) {u : H} (hu : u ∈ U) (huV : u ∉ V) :
    U = Q ⊓ centralizer ({t * τ} : Set H) := by
  have hUQ : U ≤ Q := hUC.trans inf_le_left
  have h16 : 16 ≤ Nat.card U :=
    h.card_ge_sixteen_of_rho_inv hMh hMc hUQ hVU hρU hu huV
  refine Subgroup.eq_of_le_of_card_ge hUC ?_
  rw [card_Cq h hMh hMc hb]
  exact h16

end ZJData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
