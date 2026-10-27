module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.CGT.PushingUpLit.BHS.SLCore

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Open CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin.G6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem exists_natIso {V X : Subgroup Γ} (hXV : X ≤ Subgroup.normalizer (V : Set Γ)) {S : Type*}
    [Group S] (φ : ↥X →* S) (hφs : Function.Surjective φ)
    (hφk : φ.ker = (X ⊓ Subgroup.centralizer (V : Set Γ)).subgroupOf X) :
    ∃ θ : ↥(autOn X V) ≃* S, ∀ g : ↥X, θ (actOnRange V X hXV g) = φ g := by
  have hρs := actOnRange_surjective V X hXV
  have hkerEq : (actOnRange V X hXV).ker = φ.ker := by rw [ker_actOnRange, hφk]
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)), fun g => ?_⟩
  show (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
    ((QuotientGroup.quotientMulEquivOfEq hkerEq)
      ((QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (actOnRange V X hXV g))) = φ g
  have : (QuotientGroup.quotientKerEquivOfSurjective _ hρs).symm (actOnRange V X hXV g) =
      (QuotientGroup.mk g : ↥X ⧸ (actOnRange V X hXV).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [this]
  rfl

theorem exists_faithful_data {W E : Subgroup Γ} {S M : Type*} [Group S] [Group M]
    {act : S → M → M} (hW : IsElemAbelian 2 W) (hEW : E ≤ Subgroup.normalizer (W : Set Γ))
    (hperf : ⁅E, W⁆ = W) (hnat : IsNatBy act E W) :
    ∃ (θ : ↥(autOn E W) ≃* S) (β : ↥W →* M), Function.Surjective β ∧
      (∀ w, β w = 1 → w ∈ fixOn hW E) ∧
      (∀ (x : ↥(autOn E W)) (w : ↥W), β ((x : MulAut ↥W) w) = act (θ x) (β w)) ∧
      commOn hW E = ⊤ := by
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  obtain ⟨θ, hθ⟩ := exists_natIso hEW φ hφs hφk
  have hρs := actOnRange_surjective W E hEW
  refine ⟨θ, ψ, hψs, fun w hw => ?_, fun x w => ?_, ?_⟩
  · rw [fixOn_eq hW hEW, Subgroup.mem_subgroupOf]
    have : w ∈ ψ.ker := hw
    rw [hψk, Subgroup.mem_subgroupOf] at this
    exact this.2
  · obtain ⟨g, rfl⟩ := hρs x
    have hcoe : (((actOnRange W E hEW g : MulAut ↥W)) w : ↥W) = actOn W E hEW g w := rfl
    have hw' : (g : Γ) * (w : Γ) * (g : Γ)⁻¹ ∈ W := by
      have := ((actOn W E hEW g w : ↥W)).2
      rwa [actOn_apply_coe] at this
    have key := hψe g w hw'
    rw [hθ g]
    have : ((actOnRange W E hEW g : MulAut ↥W)) w = ⟨(g : Γ) * w * (g : Γ)⁻¹, hw'⟩ :=
      Subtype.ext (actOn_apply_coe hEW g w)
    rw [this, key]
  · rw [commOn_eq hW hEW, hperf]
    exact Subgroup.subgroupOf_self W

theorem nonempty_slNatData {W E : Subgroup Γ} {n : ℕ} (hW : IsElemAbelian 2 W)
    (hEW : E ≤ Subgroup.normalizer (W : Set Γ)) (hperf : ⁅E, W⁆ = W) (hnat : IsNatSL E W n) :
    Nonempty (@SLNatData ↥W (commGroupOfElemAbelian hW) (autOn E W) (GaloisField 2 n) _) := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  obtain ⟨θ, β, hs, hkf, he, hc⟩ := exists_faithful_data hW hEW hperf (isNatSL_iff.mp hnat)
  exact ⟨{ θ := θ, β := β, surj := hs, ker_fix := hkf, equivar := he, comm_top := hc }⟩

theorem nonempty_altNatData {W E : Subgroup Γ} {n : ℕ} (hW : IsElemAbelian 2 W)
    (hEW : E ≤ Subgroup.normalizer (W : Set Γ)) (hperf : ⁅E, W⁆ = W) (hnat : IsNatAlt E W n) :
    Nonempty (@AltNatData ↥W (commGroupOfElemAbelian hW) (autOn E W) n) := by
  let _ : CommGroup ↥W := commGroupOfElemAbelian hW
  obtain ⟨θ, β, hs, hkf, he, hc⟩ := exists_faithful_data hW hEW hperf hnat
  exact ⟨{ θ := θ, β := β, surj := hs, ker_fix := hkf, equivar := he, comm_top := hc }⟩

end CFSG.CGT.PushingUpLit.BHS6
