module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26E4B

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open scoped commutatorElement

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.exists_good_involution_E4_conj_of_ne_top (hLC : TightLambdaCommR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hΛp : tightCore Rd ⊔ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤)
    (hE : MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W) :
    ∃ t₁ : Y, (∃ g ∈ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
        g⁻¹ * t * g = t₁) ∧ t₁ * t₁ = 1 ∧ t₁ ≠ 1 ∧ t₁ ≠ t ∧ t * t₁ = t₁ * t ∧ z * t₁ = t₁ * z ∧
      (∀ x ∈ R, x * t₁ = t₁ * x) ∧ conjSub t₁ J = J ∧
      Subgroup.centralizer ({t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      Subgroup.centralizer ({t * t₁} : Set Y) ≤
        sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
      ∃ J₁ ∈ CoreAssembly.conjClass (tightCore Rd),
        J₁ ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ∧
          IsUniqueInvolution J₁ t₁ := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  have hN := tightSecNbrGenR_of_comm hLC
  have hΩ : HypOmegaGen Ω := hs.hyp
  have hcl := hΩ.conjInvariant
  have hK : K ∈ Ω := hs.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hKX := hs.not_le_omegaNbrGen_of_ne_top hN (ne_top_of_le_ne_top hΛp le_sup_right)
  set X : Subgroup Y := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_omegaNbrGen hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  obtain ⟨S₂, hRS₂, hTS₂, hS₂X⟩ := hs.exists_sylow_RT
  obtain ⟨g, hgX, hgS, hgne⟩ := hs.exists_zStar_conj_of_not_le hKX hE hRS₂ hTS₂ hS₂X
  have hgiX : g⁻¹ ∈ X := X.inv_mem hgX
  have ht1X : g⁻¹ * t * g ∈ X := X.mul_mem (X.mul_mem hgiX htX) hgX
  have hct : g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹ = t :=
    hs.sX_centralizes_t hE hRS₂ hTS₂ hKX hgS ht1X
  have htt1 : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t := by
    calc t * (g⁻¹ * t * g) = (g⁻¹ * t * g * t * (g⁻¹ * t * g)⁻¹) * (g⁻¹ * t * g) := by
          rw [hct]
      _ = g⁻¹ * t * g * t := by group
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hs.hR.1
  have hzR : z ∈ R := T3.mem_of_isPGroup hs.hz hs.hR.2.1 hRsyl.2.1 (by omega)
  have hS₂2 : IsPGroup 2 ↥(S₂ : Subgroup Y) := S₂.isPGroup'
  have hcommK : ∀ x ∈ R, x * (g⁻¹ * t * g) = g⁻¹ * t * g * x := fun x hx =>
    hs.commute_of_mem_two_subgroup_of_ne_top hLC hΛp hS₂2 (hs.hR.2.1 hx) ht1X (hRS₂ hx) hgS
  have ht1sq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [hs.ht.sq]; group
  have ht1ne : g⁻¹ * t * g ≠ 1 := by
    intro h1
    apply hs.ht.ne_one
    have := congrArg (fun y => g * y * g⁻¹) h1
    simpa [mul_assoc] using this
  have hgN : g ∈ sigmaNorm Ω K := omegaNbrGen_le_sigmaNorm hcl hK hgX
  have hCt := hs.centralizer_t_le_sigmaNorm
  have hC1 : Subgroup.centralizer ({g⁻¹ * t * g} : Set Y) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj ((sigmaNorm Ω K).inv_mem hgN) ?_
    have e : g⁻¹⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t := by group
    rw [e]
    exact hCt
  obtain ⟨y, hyX, hy⟩ := hs.exists_conj_mul_E4_of_not_le hKX hE hgX hgne htt1
  have hyN : y ∈ sigmaNorm Ω K := omegaNbrGen_le_sigmaNorm hcl hK hyX
  have hC2 : Subgroup.centralizer ({t * (g⁻¹ * t * g)} : Set Y) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hyN ?_
    have e : y⁻¹ * (t * (g⁻¹ * t * g)) * y = t := by rw [← hy]; group
    rw [e]
    exact hCt
  have hnJ : conjSub (g⁻¹ * t * g) J = J := hs.sX_normalizes_J hE hRS₂ hTS₂ hKX hgS ht1X
  have hb : IsUniqueInvolution (conjSub g⁻¹ J) (g⁻¹ * t * g) := by
    have := hs.ht.conj g⁻¹
    rwa [inv_inv] at this
  have hJ1X : conjSub g⁻¹ J ≤ X := by
    intro w hw
    have h1 : g * w * g⁻¹ ∈ J := by simpa using mem_conjSub_iff.mp hw
    have := X.mul_mem (X.mul_mem hgiX (hJX h1)) hgX
    simpa [mul_assoc] using this
  exact ⟨g⁻¹ * t * g, ⟨g, hgX, rfl⟩, ht1sq, ht1ne, hgne, htt1, hcommK z hzR, hcommK, hnJ, hC1,
    hC2, conjSub g⁻¹ J, hcl g⁻¹ J hJΩ, hJ1X, hb⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
