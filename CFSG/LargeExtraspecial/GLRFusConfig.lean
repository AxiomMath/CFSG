module

public import CFSG.LargeExtraspecial.GLRFusCard
public import CFSG.LargeExtraspecial.GLRConfig
public import CFSG.LargeExtraspecial.S12Main
public import CFSG.LargeExtraspecial.GLRFusMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G]

namespace Pair

variable {S : Setting G} {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem map_B_eq (h : Pair S X A B) {x : S.O} (hx : x ∈ X) :
    B.map ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B :=
  h.symm.map_A_eq hx

end Pair

theorem pair_of_residual {S : Setting G} {g : G} {t : S.O} (hR : S.S12GammaLResidual g t)
    (h5 : 5 ≤ S.width) {σ₀ : S.O} (hσ₀ : σ₀ ∈ S.Mbar) (hσ₀X : σ₀ ∉ S.Xbar12 g) :
    Pair S (S.Xbar12 g) (S.spanOrbitX12 g)
      ((S.spanOrbitX12 g).map ((σ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)) := by
  obtain ⟨-, -, -, -, ⟨φ⟩, hbr⟩ := hR
  rcases hbr with ⟨hdim, hq, -, hσ⟩ | ⟨hn4, -, -⟩
  swap
  · omega
  obtain ⟨hinf, hsup⟩ := hσ σ₀ hσ₀ hσ₀X
  refine ⟨hq, ?_, hinf, hsup, hdim, ?_, fun x hx v hv => Setting.apply_mem_spanOrbitX12 hx hv,
    ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup σ₀.2]
    exact hq u hu
  · rw [LinearEquiv.finrank_map_eq, hdim]
  · rintro x hx _ ⟨u, hu, rfl⟩
    have hx' : σ₀⁻¹ * x * σ₀⁻¹⁻¹ ∈ S.Xbar12 g :=
      (mem_normalizer_iff.mp (Setting.Mbar_le_normalizer_Xbar12 (S.Mbar.inv_mem hσ₀)) x).mp hx
    refine ⟨((σ₀⁻¹ * x * σ₀⁻¹⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u,
      Setting.apply_mem_spanOrbitX12 hx' hu, ?_⟩
    change ((σ₀ * (σ₀⁻¹ * x * σ₀⁻¹⁻¹) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = _
    rw [show σ₀ * (σ₀⁻¹ * x * σ₀⁻¹⁻¹) = x * σ₀ by group, Subgroup.coe_mul, LinearEquiv.mul_apply]
    rfl
  · rw [Nat.card_congr φ.toEquiv, card_SL_eq_card_GL]

theorem data_of_residual {S : Setting G} {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hR : S.S12GammaLResidual g t) (h5 : 5 ≤ S.width) {σ₀ : S.O}
    (hσ₀ : σ₀ ∈ S.Mbar) (hσ₀X : σ₀ ∉ S.Xbar12 g) :
    Data S (S.Xbar12 g) (S.spanOrbitX12 g)
      ((S.spanOrbitX12 g).map ((σ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)) g := by
  have hP := pair_of_residual hR h5 hσ₀ hσ₀X
  obtain ⟨-, hC1, -, hind, -, -⟩ := hR
  have hmap : ∀ σ ∈ S.Mbar, σ ∉ S.Xbar12 g → (S.spanOrbitX12 g).map
      ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
        (S.spanOrbitX12 g).map ((σ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    intro σ hσ hσX
    have hx : σ * σ₀⁻¹ ∈ S.Xbar12 g :=
      s12_mul_mem_of_relIndex_two hind hσ (S.Mbar.inv_mem hσ₀) hσX
        (fun h => hσ₀X (by simpa using (S.Xbar12 g).inv_mem h))
    have e : σ = (σ * σ₀⁻¹) * σ₀ := by group
    rw [e, Subgroup.coe_mul, LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans, Submodule.map_comp]
    exact hP.map_B_eq hx
  refine ⟨hP, by omega, Setting.Xbar12_le_Mbar, hind, hmap, haQ, hne, ?_, ?_,
    GLR.fusion hP h5 Setting.Xbar12_le_Mbar hind hmap⟩
  · have := Setting.orbit_mem_spanOrbitX12 (S := S) (S.Xbar12 g).one_mem
    exact this
  · obtain ⟨m, -, -, hm⟩ := hC1.model
    rcases hm with ⟨hL, hidx, hC⟩ | ⟨-, hL8, -⟩
    · obtain ⟨hnm, -⟩ := Setting.case1_finrank haQ hne (by omega) hL hidx hC
      rw [hL, hnm]
    · exfalso
      have h1 := S.card_Lbar_ge haQ hne
      rw [hL8] at h1
      have h2 : 2 ^ 4 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem nonempty_config {S : Setting G} {g : G} {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hR : S.S12GammaLResidual g t) (h5 : 5 ≤ S.width) :
    Nonempty (Config S) := by
  have hind := hR.2.2.2.1
  obtain ⟨σ₀, hσ₀, hσ₀X⟩ : ∃ σ ∈ S.Mbar, σ ∉ S.Xbar12 g := by
    by_contra hc
    push Not at hc
    have h1 : (S.Xbar12 g).relIndex S.Mbar = 1 := Subgroup.relIndex_eq_one.mpr hc
    omega
  have hD := data_of_residual haQ hne hR h5 hσ₀ hσ₀X
  have hP := hD.pair
  exact ⟨{
    Xbar := S.Xbar12 g
    At := S.spanOrbitX12 g
    Bt := (S.spanOrbitX12 g).map ((σ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)
    four_le_width := by omega
    Xbar_le := Setting.Xbar12_le_Mbar
    relIndex_Xbar := hind
    nonempty_equiv := hR.2.2.2.2.1
    finrank_At := hP.finrank_A
    finrank_Bt := hP.finrank_B
    q_At := hP.q_A
    q_Bt := hP.q_B
    inf_eq := hP.inf_eq
    sup_eq := hP.sup_eq
    apply_At := hP.apply_A
    apply_Bt := hP.apply_B
    map_At := hD.map_A
    transitive := fun v hv hv0 w hw hw0 => hP.exists_apply_eq_of_ne_zero hv hw hv0 hw0
    invariant := hP.invariant (by omega)
    conj_At := fun v hv hv0 => hD.conj_A hv hv0
    fusion := hD.fusion
    centralizer_A := hD.centralizer_eq
    normalizer_inf_M := hD.normalizer_inf_M
    card_normalizer := hD.card_normalizer }⟩

end CFSG.LargeExtraspecial.GLR
