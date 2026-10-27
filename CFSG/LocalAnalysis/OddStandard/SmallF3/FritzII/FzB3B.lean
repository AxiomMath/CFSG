module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

theorem fzbs_chi_mul (hS : FzbsStr t q tau lam rho u Z E X W R T) {r r' : G} (hr : r ∈ R)
    (hr' : r' ∈ R) :
    t * ((r * r') * t * (r * r')⁻¹) = (t * (r * t * r⁻¹)) * (t * (r' * t * r'⁻¹)) := by
  have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
  set c : G := t * (r' * t * r'⁻¹) with hc
  have hcZ : c ∈ Z := by rw [hc]; exact hS.R_t r' hr'
  have hrc : r * c * r⁻¹ = c := hS.R_Z r hr c hcZ
  have htc : t * c = r' * t * r'⁻¹ := by rw [hc, ← mul_assoc, htt, one_mul]
  calc t * ((r * r') * t * (r * r')⁻¹)
      = t * r * (r' * t * r'⁻¹) * r⁻¹ := by group
    _ = t * r * (t * c) * r⁻¹ := by rw [← htc]
    _ = t * r * t * c * r⁻¹ := by group
    _ = (t * r * t * r⁻¹) * (r * c * r⁻¹) := by group
    _ = (t * r * t * r⁻¹) * c := by rw [hrc]
    _ = (t * (r * t * r⁻¹)) * (t * (r' * t * r'⁻¹)) := by rw [hc]; group

theorem fzbs_chi_conj {g r : G} (hg : g * t * g⁻¹ = t) :
    t * ((g * r * g⁻¹) * t * (g * r * g⁻¹)⁻¹) = g * (t * (r * t * r⁻¹)) * g⁻¹ := by
  have hg' : g⁻¹ * t * g = t := by
    have h : g⁻¹ * (g * t * g⁻¹) * g = g⁻¹ * t * g := congrArg (fun x => g⁻¹ * x * g) hg
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h
    exact h.symm
  have hgt : g * t = t * g := by
    calc g * t = (g * t * g⁻¹) * g := by group
      _ = t * g := by rw [hg]
  calc t * ((g * r * g⁻¹) * t * (g * r * g⁻¹)⁻¹)
      = t * g * r * (g⁻¹ * t * g) * r⁻¹ * g⁻¹ := by group
    _ = t * g * r * t * r⁻¹ * g⁻¹ := by rw [hg']
    _ = g * t * r * t * r⁻¹ * g⁻¹ := by rw [← hgt]
    _ = g * (t * (r * t * r⁻¹)) * g⁻¹ := by group

theorem fzbs_chi_eq_one (hS : FzbsStr t q tau lam rho u Z E X W R T) {r : G} (hr : r ∈ R) :
    t * (r * t * r⁻¹) = 1 ↔ r ∈ W ∨ r * tau⁻¹ ∈ W := by
  have hwt : t ∈ W := hS.XW hS.t_mem
  constructor
  · intro h
    have h1 : r * t * r⁻¹ = t := by
      have h2 : r * t * r⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h2]
      exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hS.t_sq)
    exact hS.R_fix_t r hr h1
  · intro h
    rcases h with hrW | hrw
    · have hcomm : r * t = t * r := hS.W_comm r hrW t hwt
      have h1 : r * t * r⁻¹ = t := by rw [hcomm]; group
      rw [h1]
      simpa [pow_two] using hS.t_sq
    · have hcomm : (r * tau⁻¹) * t = t * (r * tau⁻¹) := hS.W_comm (r * tau⁻¹) hrw t hwt
      have h1 : r * t * r⁻¹ = t := by
        have hr_eq : r = (r * tau⁻¹) * tau := by group
        rw [hr_eq]
        calc ((r * tau⁻¹) * tau) * t * ((r * tau⁻¹) * tau)⁻¹
            = (r * tau⁻¹) * (tau * t * tau⁻¹) * (r * tau⁻¹)⁻¹ := by group
          _ = (r * tau⁻¹) * t * (r * tau⁻¹)⁻¹ := by rw [hS.tau_t]
          _ = t := by rw [hcomm]; group
      rw [h1]
      simpa [pow_two] using hS.t_sq

theorem fzbs_Z_orbit (hS : FzbsStr t q tau lam rho u Z E X W R T) {z y : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hy : y ∈ Z) :
    y = 1 ∨ y = z ∨ y = rho * z * rho⁻¹ ∨ y = rho ^ 2 * z * (rho ^ 2)⁻¹ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  set z1 : G := rho * z * rho⁻¹ with hz1def
  set z2 : G := rho ^ 2 * z * (rho ^ 2)⁻¹ with hz2def
  have hz1Z : z1 ∈ Z := by rw [hz1def]; exact hS.rho_Z z hz
  have hz2eq : z2 = rho * z1 * rho⁻¹ := by rw [hz2def, hz1def, pow_two]; group
  have hz2Z : z2 ∈ Z := by rw [hz2eq]; exact hS.rho_Z z1 hz1Z
  have hz1ne : z1 ≠ 1 := by
    intro h
    apply hz1
    calc z = rho⁻¹ * z1 * rho := by rw [hz1def]; group
      _ = 1 := by rw [h]; group
  have hz2ne : z2 ≠ 1 := by
    intro h
    apply hz1ne
    calc z1 = rho⁻¹ * z2 * rho := by rw [hz2eq]; group
      _ = 1 := by rw [h]; group
  have hz1nez : z1 ≠ z := by rw [hz1def]; exact hS.rho_Z_fpf z hz hz1
  have hz2nez1 : z2 ≠ z1 := by rw [hz2eq]; exact hS.rho_Z_fpf z1 hz1Z hz1ne
  have hz2nez : z2 ≠ z := by
    intro h
    have hA : rho * z2 * rho⁻¹ = z := by
      have h3 : rho * rho * rho = 1 := by rw [← pow_three']; exact hS.rho_cube
      calc rho * z2 * rho⁻¹
          = (rho * rho * rho) * z * (rho * rho * rho)⁻¹ := by rw [hz2def, pow_two]; group
        _ = z := by rw [h3]; group
    have hB : rho * z2 * rho⁻¹ = z1 := by rw [h, hz1def]
    exact hz1nez (hB.symm.trans hA)
  have hTcard : ({1, z, z1, z2} : Finset G).card = 4 :=
    Finset.card_eq_four.mpr
      ⟨1, z, z1, z2, (Ne.symm hz1), (Ne.symm hz1ne), (Ne.symm hz2ne),
        (Ne.symm hz1nez), (Ne.symm hz2nez), (Ne.symm hz2nez1), rfl⟩
  have hZcard : (Z : Set G).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hS.card_Z
  have hTsub : ({1, z, z1, z2} : Finset G) ⊆ (Z : Set G).toFinset := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Set.mem_toFinset]
    rcases ha with rfl | rfl | rfl | rfl
    · exact Z.one_mem
    · exact hz
    · exact hz1Z
    · exact hz2Z
  have hTZ : ({1, z, z1, z2} : Finset G) = (Z : Set G).toFinset :=
    Finset.eq_of_subset_of_card_le hTsub (by rw [hZcard, hTcard])
  have hyT : y ∈ ({1, z, z1, z2} : Finset G) := by
    rw [hTZ, Set.mem_toFinset]; exact hy
  simpa only [Finset.mem_insert, Finset.mem_singleton, hz1def, hz2def] using hyT

theorem fzbs_Z_norm (hS : FzbsStr t q tau lam rho u Z E X W R T) {z : G} (hz : z ∈ Z) :
    z * (rho * z * rho⁻¹) * (rho ^ 2 * z * (rho ^ 2)⁻¹) = 1 := by
  by_cases hz0 : z = 1
  · rw [hz0]; group
  · set z1 : G := rho * z * rho⁻¹ with hz1def
    set z2 : G := rho ^ 2 * z * (rho ^ 2)⁻¹ with hz2def
    have hz1Z : z1 ∈ Z := by rw [hz1def]; exact hS.rho_Z z hz
    have hz2eq : z2 = rho * z1 * rho⁻¹ := by rw [hz2def, hz1def, pow_two]; group
    have hz2Z : z2 ∈ Z := by rw [hz2eq]; exact hS.rho_Z z1 hz1Z
    have hz1ne : z1 ≠ 1 := by
      intro h
      apply hz0
      calc z = rho⁻¹ * z1 * rho := by rw [hz1def]; group
        _ = 1 := by rw [h]; group
    have hzz1Z : z * z1 ∈ Z := Z.mul_mem hz hz1Z
    have hzz1 : z * z1 = z2 := by
      rcases fzbs_Z_orbit hS hz hz0 hzz1Z with h | h | h | h
      · exfalso
        have hz1eq : z1 = z := by
          have h1 : z1 = z⁻¹ := eq_inv_of_mul_eq_one_right h
          rw [h1]
          exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hS.Z_sq z hz)
        exact hS.rho_Z_fpf z hz hz0 (by rw [← hz1def]; exact hz1eq)
      · exfalso
        have h1 : z1 = 1 := by
          have hh : z * z1 = z * 1 := by rw [h, mul_one]
          exact mul_left_cancel hh
        exact hz1ne h1
      · exfalso
        have h1 : z = 1 := by
          have hh : z * z1 = 1 * z1 := by rw [h, one_mul]
          exact mul_right_cancel hh
        exact hz0 h1
      · exact h.trans hz2def.symm
    rw [hzz1]
    simpa [pow_two] using hS.Z_sq z2 hz2Z

theorem fzbs_zpow_conj (hrho3 : rho ^ 3 = 1) {H : Subgroup G}
    (hH : ∀ h ∈ H, rho * h * rho⁻¹ ∈ H) {g : G} (hg : g ∈ zpowers rho) {h : G} (hh : h ∈ H) :
    g * h * g⁻¹ ∈ H := by
  have hrho : rho ∈ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hH x hx
    · intro hx
      have h1 : rho * (rho * x * rho⁻¹) * rho⁻¹ ∈ H := hH _ hx
      have h2 : rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈ H := hH _ h1
      have heq : rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹ = x := by
        have h3 : rho * rho * rho = 1 := by rw [← pow_three']; exact hrho3
        calc rho * (rho * (rho * x * rho⁻¹) * rho⁻¹) * rho⁻¹
            = (rho * rho * rho) * x * (rho * rho * rho)⁻¹ := by group
          _ = x := by rw [h3]; group
      rwa [heq] at h2
  have hle : zpowers rho ≤ Subgroup.normalizer (H : Set G) := Subgroup.zpowers_le.mpr hrho
  exact ((Subgroup.mem_set_normalizer_iff.mp (hle hg)) h).mp hh

theorem fzbs_rho_X_E (hS : FzbsStr t q tau lam rho u Z E X W R T) {g : G}
    (hg : g ∈ zpowers rho) {x : G} (hx : x ∈ X) : g * x * g⁻¹ * x⁻¹ ∈ E := by
  have hrho_c : rho ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    have h : (rho * t * rho⁻¹) * rho = t * rho := congrArg (fun x => x * rho) hS.rho_t
    rw [show (rho * t * rho⁻¹) * rho = rho * t by group] at h
    exact h.symm
  have hg_c : g ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.zpowers_le.mpr hrho_c) hg
  have hgt_comm : g * t = t * g :=
    ((Subgroup.mem_centralizer_iff.mp hg_c) t (Set.mem_singleton t)).symm
  have hgt' : g * t * g⁻¹ = t := by rw [hgt_comm]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hS.t_sq)
  have htt : t * t = 1 := by rw [← pow_two]; exact hS.t_sq
  have htw : t ∈ W := hS.XW hS.t_mem
  rcases hS.X_split x hx with hxE | htxE
  · exact E.mul_mem (fzbs_zpow_conj hS.rho_cube hS.rho_E hg hxE) (E.inv_mem hxE)
  · have key : ∀ e : G, e ∈ E → g * (t * e) * g⁻¹ * (t * e)⁻¹ ∈ E := by
      intro e he
      have hge : g * e * g⁻¹ ∈ E := fzbs_zpow_conj hS.rho_cube hS.rho_E hg he
      have hmW : g * e * g⁻¹ ∈ W := hS.EX.trans hS.XW hge
      have heW : e ∈ W := hS.EX.trans hS.XW he
      have hb1 : g * (t * e) * g⁻¹ = t * (g * e * g⁻¹) := by
        rw [show g * (t * e) * g⁻¹ = (g * t * g⁻¹) * (g * e * g⁻¹) by group, hgt']
      have hb2 : (t * e)⁻¹ = e⁻¹ * t := by rw [mul_inv_rev, htinv]
      rw [hb1, hb2]
      have hfinal : t * (g * e * g⁻¹) * (e⁻¹ * t) = (g * e * g⁻¹) * e⁻¹ := by
        have h1 := hS.W_comm t htw (g * e * g⁻¹) hmW
        have h2 := hS.W_comm t htw e⁻¹ (hS.EX.trans hS.XW (E.inv_mem he))
        calc t * (g * e * g⁻¹) * (e⁻¹ * t)
            = (t * (g * e * g⁻¹)) * (e⁻¹ * t) := by group
          _ = ((g * e * g⁻¹) * t) * (e⁻¹ * t) := by rw [h1]
          _ = ((g * e * g⁻¹) * t) * (t * e⁻¹) := by rw [← h2]
          _ = (g * e * g⁻¹) * (t * (t * e⁻¹)) := by group
          _ = (g * e * g⁻¹) * e⁻¹ := by rw [← mul_assoc t t e⁻¹, htt, one_mul]
      rw [hfinal]
      exact E.mul_mem hge (E.inv_mem he)
    have hx_eq : x = t * (t * x) := by rw [← mul_assoc, htt, one_mul]
    rw [hx_eq]
    exact key (t * x) htxE

end CFSG.OddStandard.SmallF3.FritzII
