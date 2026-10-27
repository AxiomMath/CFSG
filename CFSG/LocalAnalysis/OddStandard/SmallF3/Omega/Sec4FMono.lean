module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMonoModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMonoLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82FactMono_holds : Asc82FactMono := by
  intro G _ _ L P B φ hL hB μ i j hij hμ2 hμN hμ6 hact v hv hcomm hmono6
  have hr6 : (6 : ℕ) = 2 ∨ (6 : ℕ) = 4 ∨ (6 : ℕ) = 6 := Or.inr (Or.inr rfl)
  obtain ⟨e, fr, σ, hρ⟩ := sec4F_mono_frame hL hB
  obtain ⟨y, hy, hy6⟩ := (sec4I_inducesTypeSome_iff e hr6).mp hμ6
  have hL' : ∀ w, IsEvenVec w → φ w ∈ L := fun w hw => (hρ w hw).1
  have hrho : ∀ w (hw : IsEvenVec w) (hφ : φ w ∈ L),
      sec4IRho e ⟨φ w, hφ⟩ = sec4IPsi fr (permVec σ w) := by
    intro w hw hφ
    obtain ⟨_, h⟩ := hρ w hw
    exact h
  have hyconj : ∀ (x : G) (hx : x ∈ L) (hx' : μ * x * μ⁻¹ ∈ L),
      sec4IRho e ⟨μ * x * μ⁻¹, hx'⟩ = y * sec4IRho e ⟨x, hx⟩ * y⁻¹ := by
    intro x hx hx'
    rw [sec4IRho_apply, sec4IRho_apply]
    exact hy.2 ⟨x, hx⟩ ⟨μ * x * μ⁻¹, hx'⟩ rfl
  have hact' : ∀ w, IsEvenVec w →
      y * sec4IPsi fr w * y⁻¹ = sec4IPsi fr (permVec (Equiv.swap (σ i) (σ j)) w) := by
    intro w hw
    have hw₀ : IsEvenVec (permVec σ.symm w) := sec4I_isEvenVec_permVec σ.symm hw
    have hσw : permVec σ (permVec σ.symm w) = w := by
      funext k
      simp [permVec]
    have hs : IsEvenVec (permVec (Equiv.swap i j) (permVec σ.symm w)) :=
      sec4I_isEvenVec_permVec _ hw₀
    have h1 : μ * φ (permVec σ.symm w) * μ⁻¹ ∈ L := by
      rw [hact _ hw₀]
      exact hL' _ hs
    have h2 := hyconj (φ (permVec σ.symm w)) (hL' _ hw₀) h1
    rw [hrho _ hw₀ (hL' _ hw₀), hσw] at h2
    have h3 : sec4IRho e ⟨μ * φ (permVec σ.symm w) * μ⁻¹, h1⟩ =
        sec4IRho e ⟨φ (permVec (Equiv.swap i j) (permVec σ.symm w)), hL' _ hs⟩ := by
      congr 1
      exact Subtype.ext (hact _ hw₀)
    have h4 : permVec σ (permVec (Equiv.swap i j) (permVec σ.symm w)) =
        permVec (Equiv.swap (σ i) (σ j)) w := by
      funext k
      show w (σ (Equiv.swap i j (σ.symm k))) = w (Equiv.swap (σ i) (σ j) k)
      congr 1
      rw [Equiv.swap_apply_apply σ i j]
      rfl
    rw [← h2, h3, hrho _ hs (hL' _ hs), h4]
  have hφv : φ v ∈ L := hL' v hv
  have hA : Sec4IActs e (μ * φ v) (y * ((e (QuotientGroup.mk (⟨φ v, hφv⟩ : ↥L)) : Sec4IOmega) :
      ProjOrth Sec4IQ)) := hy.mul (Sec4IActs.of_mem e hφv)
  have hcomm' : y * sec4IPsi fr (permVec σ v) = sec4IPsi fr (permVec σ v) * y := by
    have hB' : Sec4IActs e (φ v * μ) (((e (QuotientGroup.mk (⟨φ v, hφv⟩ : ↥L)) : Sec4IOmega) :
        ProjOrth Sec4IQ) * y) := (Sec4IActs.of_mem e hφv).mul hy
    rw [hcomm] at hA
    have h := hA.unique hB'
    rw [← hrho v hv hφv, sec4IRho_apply]
    exact h
  have hyv : HasType (y * sec4IPsi fr (permVec σ v)) 6 1 := by
    obtain ⟨y', hy', hty'⟩ := (sec4I_inducesTypeSome_iff e hr6).mp hmono6
    rw [hy'.unique hA] at hty'
    rw [← hrho v hv hφv, sec4IRho_apply]
    exact hty'
  have hij' : σ i ≠ σ j := fun h => hij (σ.injective h)
  have hv' : IsEvenVec (permVec σ v) := sec4I_isEvenVec_permVec σ hv
  rcases sec4F_mono_model sec4IQ_nondegenerate fr hij' hy6 hact' hv' hcomm' hyv with h0 | h1
  · left
    funext k
    have h := congrFun h0 (σ k)
    simpa [permVec] using h
  · right
    funext k
    have h := congrFun h1 (σ k)
    simpa [permVec, Pi.single_apply, σ.injective.eq_iff] using h

end CFSG.OddStandard.SmallF3.Omega
