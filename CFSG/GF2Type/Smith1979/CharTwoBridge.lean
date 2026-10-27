module

public import CFSG.GF2Type.Smith1979.IdxFourIdentE
public import CFSG.GF2Type.Smith1979.IdxFourBridge
public import CFSG.GF2Type.Smith1979.CharTwoTransport
public import Certificates.Kernel.SporSch.Co2M.ThirdBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module CFSG.LargeExtraspecial
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Dict

variable {G : Type} [Group G] [Finite G]

theorem map_tau_trans {S : Setting G} (φ : S.Qt ≃ₗ[ZMod 2] V12) (t : V12 ≃ₗ[ZMod 2] V12)
    (E : Subgroup S.Mbar) :
    (E.map S.Mbar.subtype).map (tau S (φ.trans t)) = conjSub (E.map (kappa S φ)) t := by
  ext y
  rw [mem_conjSub]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine ⟨e, he, ?_⟩
    rw [kappa_apply]
    show trEquiv φ ((e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = t⁻¹ * tau S (φ.trans t) (e : S.O) * t
    rw [tau_mul_tau_inv_eq, tau_apply]
    group
  · rintro ⟨e, he, hy⟩
    refine ⟨_, ⟨e, he, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, tau_mul_tau_inv_eq, tau_apply, ← kappa_apply, hy]
    group

theorem exists_isometry_map_layer_eq_E0 (S : Setting G) (hw : S.width = 6)
    (E : Subgroup S.Mbar) {θ : S.Mbar} (hθ3 : θ ^ 3 = 1) (hθ1 : θ ≠ 1)
    (hZ : (center E).map E.subtype = zpowers θ)
    (hmodel : CFSG.Open.StatedClassicalModel (E ⧸ center E) .PSU 4 3 1)
    (hE0card : Nat.card E0 = 9797760) :
    ∃ ψ : S.Qt ≃ₗ[ZMod 2] V12, (∀ v, q0 (ψ v) = S.q v) ∧ ThetaCompat ψ (θ : S.O) ∧
      (E.map S.Mbar.subtype).map (tau S ψ) = E0 := by
  classical
  have hfix := fixedPointFree_of_layer S hw E hθ3 hθ1 hZ hmodel
  have hθO3 : ((θ : S.O)) ^ 3 = 1 := by simpa using congrArg (fun x : S.Mbar => (x : S.O)) hθ3
  obtain ⟨φ₀, hq0, hθ0⟩ := exists_isometry_theta0_of_setting S hw hθO3 hfix
  have hθc : ThetaCompat φ₀ (θ : S.O) := Or.inl hθ0
  have hθE : θ ∈ E := by
    obtain ⟨c, -, hc⟩ := (hZ ▸ mem_zpowers θ : θ ∈ (center E).map E.subtype)
    exact hc ▸ c.2
  set θE : E := ⟨θ, hθE⟩ with hθEdef
  have hcen : center E = zpowers θE := by
    apply Subgroup.map_injective E.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have hθE3 : θE ^ 3 = 1 := Subtype.ext (by simpa using hθ3)
  have hθE1 : θE ≠ 1 := fun h => hθ1 (by simpa [hθEdef] using congrArg Subtype.val h)
  obtain ⟨π, hπ, hker, hcardE⟩ := layer_data hθE3 hθE1 hcen hmodel
  have hκ := kappa_injective S φ₀
  have hκθ : kappa S φ₀ θ = theta0e := LinearEquiv.ext fun v => by
    rw [kappa_apply, trEquiv_apply, hθ0, LinearEquiv.apply_symm_apply]
    rfl
  have hθEc : θE ∈ center E := by rw [hcen]; exact mem_zpowers θE
  have hθcen : ∀ e ∈ E, ((e : S.O)) * (θ : S.O) * (e : S.O)⁻¹ = θ := by
    intro e he
    have h : (⟨e, he⟩ : E) * θE = θE * ⟨e, he⟩ := Subgroup.mem_center_iff.mp hθEc ⟨e, he⟩
    have h' : ((⟨e, he⟩ : E) : S.Mbar) * θ = θ * ((⟨e, he⟩ : E) : S.Mbar) := by
      simpa [hθEdef] using congrArg Subtype.val h
    have h'' : (e : S.O) * (θ : S.O) = (θ : S.O) * (e : S.O) := by
      simpa using congrArg Subtype.val h'
    rw [h'', mul_inv_cancel_right]
  have hEg : E.map (kappa S φ₀) ≤ gammaU := by
    rintro _ ⟨e, he, rfl⟩
    have hcomm := hθcen e he
    refine mem_gammaU_of_conj (fun v => ?_) (conj_thetaU_tr hθc (Or.inl hcomm))
    rw [kappa_apply, trEquiv_apply, hq0,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (e : S.O).2, ← hq0,
      LinearEquiv.apply_symm_apply]
  have hEcard : Nat.card (E.map (kappa S φ₀)) = 9797760 := by
    rw [Subgroup.card_map_of_injective hκ, hcardE]
  obtain ⟨π', hπ', hk'⟩ := exists_proj_of_map hκ E π hπ hker
  have hZ' : (center (E.map (kappa S φ₀))).map (E.map (kappa S φ₀)).subtype =
      zpowers theta0e := by
    rw [center_map_map_subtype hκ, hZ, MonoidHom.map_zpowers, hκθ]
  obtain ⟨t, htg, ht⟩ := exists_conj_eq_E0 hEg hEcard π' hπ' hk' hZ' hE0card
  refine ⟨φ₀.trans t, fun v => ?_, ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, htg.1, hq0]
  · rcases htg.2 with h | h
    · exact Or.inl fun v => by rw [LinearEquiv.trans_apply, hθ0, h]; rfl
    · exact Or.inr fun v => by rw [LinearEquiv.trans_apply, hθ0, h]; rfl
  · rw [← ht]
    exact map_tau_trans φ₀ t E

end CFSG.GF2Type.Smith1979.IdxFour
