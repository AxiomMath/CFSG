module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3H
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AHS29A

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

private lemma fzbs3i_mem_normalizer_of_conj_mem {H : Subgroup G} {g : G}
    (h : ∀ y ∈ H, g * y * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    show g * y * g⁻¹ ∈ H
    exact h y hy
  · exact le_of_eq (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective).symm

theorem fzbs_card_P (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (htP : t ∉ ⁅R, zpowers rho⁆) : Nat.card (⁅R, zpowers rho⁆ : Subgroup G) = 64 := by
  let P : Subgroup G := ⁅R, zpowers rho⁆
  have hE_le_P : E ≤ P := fzbs_E_le_P hS
  let chi : ↥P →* ↥Z :=
    { toFun := fun p =>
        ⟨t * ((p : G) * t * (p : G)⁻¹), hS.R_t _ (fzbs_P_le_R hS p.2)⟩
      map_one' := by
        apply Subtype.ext
        show t * ((1 : G) * t * (1 : G)⁻¹) = 1
        rw [one_mul, inv_one, mul_one]
        simpa only [← pow_two] using hS.t_sq
      map_mul' := by
        intro p p'
        apply Subtype.ext
        exact fzbs_chi_mul hS (fzbs_P_le_R hS p.2) (fzbs_P_le_R hS p'.2) }
  have hchi_val : ∀ p : ↥P, (chi p : G) = t * ((p : G) * t * (p : G)⁻¹) := by
    intro p
    simp only [chi]
    rfl
  have hker : chi.ker = E.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker]
    constructor
    · intro hp
      have hval : t * ((p : G) * t * (p : G)⁻¹) = 1 := by
        have h1 := congrArg Subtype.val hp
        rw [hchi_val p] at h1
        simpa using h1
      have hpt : (p : G) * t * (p : G)⁻¹ = t := by
        have h := congrArg (fun x => t * x) hval
        rwa [← mul_assoc, show t * t = 1 by simpa only [← pow_two] using hS.t_sq,
          one_mul, mul_one] at h
      exact Subgroup.mem_subgroupOf.mpr
        (fzbs_P_X hS htP (fzbs_P_ker hS p.2 hpt) p.2)
    · intro hp
      apply Subtype.ext
      rw [hchi_val p]
      have hpeE : (p : G) ∈ E := Subgroup.mem_subgroupOf.mp hp
      have hpW : (p : G) ∈ W := hS.XW (hS.EX hpeE)
      have hcomm : (p : G) * t = t * (p : G) := hS.W_comm _ hpW _ (hS.XW hS.t_mem)
      have hpt : (p : G) * t * (p : G)⁻¹ = t := by rw [hcomm]; group
      have ht2 : t * t = 1 := by simpa only [← pow_two] using hS.t_sq
      rw [hpt, ht2]
      rfl
  have hker_card : Nat.card chi.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le_P).toEquiv]
    exact hS.card_E
  have hsurj : Function.Surjective chi := by
    intro z
    obtain ⟨p, hp, hpt⟩ := fzbs_P_chi_surj hS z.2
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    rw [hchi_val ⟨p, hp⟩, hpt]
    have ht2 : t * t = 1 := by simpa only [← pow_two] using hS.t_sq
    rw [← mul_assoc, ht2, one_mul]
  have hrange_card : Nat.card chi.range = 4 := by
    rw [chi.range_eq_top_of_surjective hsurj, Subgroup.card_top]
    exact hS.card_Z
  have hcard := Subgroup.card_ker_mul_card_range chi
  rw [hker_card, hrange_card] at hcard
  change Nat.card P = 64
  rw [← hcard]

theorem fzbs_P_fpf (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (htP : t ∉ ⁅R, zpowers rho⁆) {p : G} (hp : p ∈ ⁅R, zpowers rho⁆)
    (hfix : rho * p * rho⁻¹ = p) : p = 1 := by
  have hpR : p ∈ R := fzbs_P_le_R hS hp
  have hchiZ : t * (p * t * p⁻¹) ∈ Z := hS.R_t p hpR
  have hchi_fix : rho * (t * (p * t * p⁻¹)) * rho⁻¹ = t * (p * t * p⁻¹) := by
    have hc := fzbs_chi_conj (g := rho) (r := p) hS.rho_t
    rw [hfix] at hc
    exact hc.symm
  have hchi1 : t * (p * t * p⁻¹) = 1 := by
    by_contra hne
    exact (hS.rho_Z_fpf _ hchiZ hne) hchi_fix
  have hpt : p * t * p⁻¹ = t := by
    have h := congrArg (fun x => t * x) hchi1
    rwa [← mul_assoc, show t * t = 1 by simpa only [← pow_two] using hS.t_sq,
      one_mul, mul_one] at h
  have hpX : p ∈ X := fzbs_P_ker hS hp hpt
  have hpE : p ∈ E := fzbs_P_X hS htP hpX hp
  have hpW : p ∈ W := hS.XW (hS.EX hpE)
  have hpq : p ∈ zpowers q := hS.rho_W_fix p hpW hfix
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpq
  have hq2t : q ^ (2 : ℤ) = t := by simpa using hS.q_sq
  have hq4 : q ^ (4 : ℤ) = 1 := by
    have h2 : q ^ (4 : ℤ) = (q ^ (2 : ℤ)) * (q ^ (2 : ℤ)) := by
      rw [← zpow_add]; norm_num
    rw [h2, hq2t]
    simpa only [← pow_two] using hS.t_sq
  have hmod : p = q ^ (k % 4) := by
    rw [← hk]
    exact zpow_eq_zpow_emod k hq4
  have hq_notin_X : q ∉ X := by
    intro hqX
    have hq2Z : q ^ 2 ∈ Z := (hS.X_iff q hS.q_mem).mp hqX
    rw [hS.q_sq] at hq2Z
    exact hS.t_notin_E (hS.ZE hq2Z)
  have hq_notin_E : q ∉ E := fun hqE => hq_notin_X (hS.EX hqE)
  have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by
    have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
    have h3 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
    omega
  rcases hr with h | h | h | h
  · rw [hmod, h]; simp
  · exfalso
    have hqE : q ∈ E := by rw [hmod, h] at hpE; simpa using hpE
    exact hq_notin_E hqE
  · exfalso
    have htE : t ∈ E := by
      rw [hmod, h] at hpE
      simpa [hq2t] using hpE
    exact hS.t_notin_E htE
  · exfalso
    have hq3 : q ^ (3 : ℤ) = q⁻¹ := by
      have h1 : q ^ (3 : ℤ) * q = 1 := by
        rw [← zpow_add_one, show (3 : ℤ) + 1 = 4 by norm_num, hq4]
      exact eq_inv_of_mul_eq_one_left h1
    have hqE : q ∈ E := by
      have hqinvE : q⁻¹ ∈ E := by
        rw [hmod, h] at hpE
        rwa [hq3] at hpE
      simpa using Subgroup.inv_mem E hqinvE
    exact hq_notin_E hqE

theorem fzbs_P_cent_t (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (htP : t ∉ ⁅R, zpowers rho⁆) : ⁅R, zpowers rho⁆ ⊓ centralizer ({t} : Set G) = E := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hconj : g * t * g⁻¹ = t := by rw [hgt]; group
    exact fzbs_P_X hS htP (fzbs_P_ker hS hgP hconj) hgP
  · intro e he
    refine Subgroup.mem_inf.mpr ⟨fzbs_E_le_P hS he, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have heW : e ∈ W := hS.XW (hS.EX he)
    exact hS.W_comm e heW t (hS.XW hS.t_mem)

theorem fzbs_P_nonab (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    ∃ a ∈ ⁅R, zpowers rho⁆, ∃ b ∈ ⁅R, zpowers rho⁆, a * b ≠ b * a := by
  have hu2Z : u ^ 2 ∈ Z := hS.E_sq u hS.u_mem
  obtain ⟨p, hpP, hpt⟩ := fzbs_P_chi_surj hS hu2Z
  set ap : G := q⁻¹ * (p * q * p⁻¹) with hapdef
  have hpR : p ∈ R := fzbs_P_le_R hS hpP
  have hapE : ap ∈ E := fzbs_P_aq hS hpP
  have hapP : ap ∈ ⁅R, zpowers rho⁆ := fzbs_E_le_P hS hapE
  have hap2 : ap ^ 2 = u ^ 2 := by
    have h := (fzbs_aq hS hpR).2
    rw [hpt, ← hapdef] at h
    rw [← mul_assoc, show t * t = 1 by simpa only [← pow_two] using hS.t_sq,
      one_mul] at h
    exact h
  have hp2W : p ^ 2 ∈ W := hS.R_sq p hpR
  have hcommq : p ^ 2 * q = q * p ^ 2 := hS.W_comm (p ^ 2) hp2W q hS.q_mem
  have hpq : p * (p * q * p⁻¹) * p⁻¹ = q := by
    have h1 : p * (p * q * p⁻¹) * p⁻¹ = p ^ 2 * q * (p ^ 2)⁻¹ := by
      rw [pow_two]; group
    rw [h1, hcommq]; group
  have hconj : p * ap * p⁻¹ = ap⁻¹ := by
    calc p * ap * p⁻¹
        = (p * q⁻¹ * p⁻¹) * (p * (p * q * p⁻¹) * p⁻¹) := by rw [hapdef]; group
      _ = (p * q * p⁻¹)⁻¹ * q := by rw [hpq]; group
      _ = ap⁻¹ := by rw [hapdef]; group
  refine ⟨p, hpP, ap, hapP, ?_⟩
  intro hcomm
  have hapeq : ap = ap⁻¹ := by rw [← hconj, hcomm]; group
  have hap1 : ap ^ 2 = 1 := by
    have h2 := congrArg (fun x => x * ap) hapeq
    rw [inv_mul_cancel] at h2
    rwa [pow_two]
  exact hS.u_sq_ne (by rw [← hap2, hap1])

theorem fzbs_P_iso (hS : FzbsStr t q tau lam rho u Z E X W R T)
    (htP : t ∉ ⁅R, zpowers rho⁆) : Nonempty (↥(⁅R, zpowers rho⁆ : Subgroup G) ≃* SylSL3_4) := by
  let P : Subgroup G := ⁅R, zpowers rho⁆
  have hcard : Nat.card P = 64 := fzbs_card_P hS htP
  have hnab : ¬ IsMulCommutative P := by
    intro hcomm
    obtain ⟨a, haP, b, hbP, hne⟩ := fzbs_P_nonab hS
    have h' := isMulCommutative_iff.mp hcomm ⟨a, haP⟩ ⟨b, hbP⟩
    exact hne (congrArg Subtype.val h')
  have hrho_norm : rho ∈ Subgroup.normalizer (P : Set G) :=
    fzbs3i_mem_normalizer_of_conj_mem (H := P) (g := rho) (fun y hy => fzbs_P_rho hS hy)
  have hlam_norm : lam ∈ Subgroup.normalizer (P : Set G) :=
    fzbs3i_mem_normalizer_of_conj_mem (H := P) (g := lam) (fun y hy => fzbs_P_lam hS hy)
  have hfpf : P ⊓ centralizer ({rho} : Set G) = ⊥ := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hg
      have hgr : g * rho = rho * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      have hfix : rho * g * rho⁻¹ = g := by rw [← hgr]; group
      rw [fzbs_P_fpf hS htP hgP hfix]
      exact Subgroup.mem_bot.mpr rfl
    · exact bot_le
  have hres := (CFSG.OddStandard.SmallF3.HarrisU33.S4A.hs29_transport
    (R := P) hcard hnab hrho_norm hlam_norm hS.rho_cube
    (by simpa only [← pow_two] using hS.lam_sq) hS.lam_rho hfpf).1
  change Nonempty (↥P ≃* SylSL3_4)
  exact hres

end CFSG.OddStandard.SmallF3.FritzII
