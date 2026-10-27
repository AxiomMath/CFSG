module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB3B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t q tau lam rho u : G} {Z E X W R T : Subgroup G}

theorem fzbs_P_le_R (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    ⁅R, zpowers rho⁆ ≤ R := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ R := fzbs_zpow_conj hS.rho_cube hS.rho_R hg₂ (R.inv_mem hg₁)
  rw [commutatorElement_def,
    show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) by group]
  exact R.mul_mem hg₁ h1

theorem fzbs_E_le_P (hS : FzbsStr t q tau lam rho u Z E X W R T) :
    E ≤ ⁅R, zpowers rho⁆ := by
  rw [← hS.E_rho]
  exact Subgroup.commutator_mono hS.WR le_rfl

theorem fzbs_P_R (hS : FzbsStr t q tau lam rho u Z E X W R T) {g p : G} (hg : g ∈ R)
    (hp : p ∈ ⁅R, zpowers rho⁆) : g * p * g⁻¹ ∈ ⁅R, zpowers rho⁆ := by
  have hn : g ∈ normalizer ((⁅R, zpowers rho⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left R (zpowers rho) hg
  exact (Subgroup.mem_normalizer_iff.mp hn p).mp hp

theorem fzbs_P_rho (hS : FzbsStr t q tau lam rho u Z E X W R T) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) : rho * p * rho⁻¹ ∈ ⁅R, zpowers rho⁆ := by
  have hn : rho ∈ normalizer ((⁅R, zpowers rho⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_right R (zpowers rho) (Subgroup.mem_zpowers rho)
  exact (Subgroup.mem_normalizer_iff.mp hn p).mp hp

theorem fzbs_P_lam (hS : FzbsStr t q tau lam rho u Z E X W R T) {p : G}
    (hp : p ∈ ⁅R, zpowers rho⁆) : lam * p * lam⁻¹ ∈ ⁅R, zpowers rho⁆ := by
  have hmap : (⁅R, zpowers rho⁆ : Subgroup G).map (MulAut.conj lam).toMonoidHom ≤
      ⁅R, zpowers rho⁆ := by
    rw [Subgroup.map_commutator]
    apply Subgroup.commutator_mono
    · rw [Subgroup.map_le_iff_le_comap]
      intro r hr
      exact hS.lam_R r hr
    · rw [MonoidHom.map_zpowers]
      have h1 : (MulAut.conj lam).toMonoidHom rho = rho⁻¹ := hS.lam_rho
      rw [h1, Subgroup.zpowers_inv]
  exact hmap (Subgroup.mem_map_of_mem _ hp)

theorem fzbs_P_T (hS : FzbsStr t q tau lam rho u Z E X W R T) {g p : G} (hg : g ∈ T)
    (hp : p ∈ ⁅R, zpowers rho⁆) : g * p * g⁻¹ ∈ ⁅R, zpowers rho⁆ := by
  rcases hS.T_cases g hg with hgR | hgR
  · exact fzbs_P_R hS hgR hp
  · have hll : lam * lam = 1 := by rw [← pow_two]; exact hS.lam_sq
    have h2 := fzbs_P_lam hS (fzbs_P_R hS hgR hp)
    have heq : g * p * g⁻¹ = lam * ((lam * g) * p * (lam * g)⁻¹) * lam⁻¹ := by
      calc g * p * g⁻¹ = (lam * lam) * (g * p * g⁻¹) * (lam * lam)⁻¹ := by rw [hll]; group
        _ = lam * ((lam * g) * p * (lam * g)⁻¹) * lam⁻¹ := by group
    rw [heq]
    exact h2

end CFSG.OddStandard.SmallF3.FritzII
