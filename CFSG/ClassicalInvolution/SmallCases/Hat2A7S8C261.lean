module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Defs
public import CFSG.ClassicalInvolution.Q3.Q3CLFrame
import CFSG.ClassicalInvolution.Q3.Q3CLFrame261
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274
import CFSG.ClassicalInvolution.Q3.Q3CLMirror

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

section

namespace Asc77

open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc in
theorem Std8.toFrame {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (hs : Std8 Ω K J S R T W z t) :
    Std8Frame Ω K J S R T W z t :=
  ⟨hs.stand.hyp, hs.stand.mem, hs.stand.trans, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT,
    hs.hW⟩

open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups
section Basic
variable {G : Type} [Group G]
end Basic
section Setup
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Setup
section Normalizer
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem s26_conjSub_mem_omegaNbr [Finite G] (hΩ : HypOmegaMod Ω) {K J' : Subgroup G} {b : G}
    (hb : conjSub b K = K) (hJ' : J' ∈ omegaNbr Ω K) : conjSub b J' ∈ omegaNbr Ω K :=
  Q3.Q3CL.Frame.s26_conjSub_mem_omegaNbr hΩ hb hJ'

theorem s26_conjSub_omegaNbrGen_le [Finite G] (hΩ : HypOmegaMod Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) ≤ omegaNbrGen Ω K :=
  Q3.Q3CL.Frame.s26_conjSub_omegaNbrGen_le hΩ hb

theorem s26_conjSub_omegaNbrGen [Finite G] (hΩ : HypOmegaMod Ω) {K : Subgroup G} {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K :=
  Q3.Q3CL.Frame.s26_conjSub_omegaNbrGen hΩ hb
end Normalizer
section Dichotomy
end Dichotomy
section Main
end Main
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Rep
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
end Rep
section Std
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem partIHyp_of_std8 (hs : Std8 Ω K J S R T W z t) : PartIHyp Ω :=
  ⟨hs.stand.hyp, hs.stand.cls, hs.stand.aEmpty⟩

theorem mem_DSet_of_le_sylow (hs : Std8 Ω K J S R T W z t) {X : Subgroup G}
    (hX : X ∈ RSet Ω) (hXS : X ≤ (S : Subgroup G)) : X ∈ DSet Ω W :=
  Q3.Q3CL.Frame.T8.mem_DSet_of_le_sylow hs.toFrame hX hXS

@[expose] noncomputable def stdRepK (hs : Std8 Ω K J S R T W z t) : Rep Ω W :=
  Hat2A7P1.T8.mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.stand.mem (mem_DSet_of_le_sylow hs hs.hR.1
      hs.hR.2.2)
    (Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.stand.hyp hs.stand.mem hs.hR.1 hs.hR.2.1)

@[expose] noncomputable def stdRepJ (hs : Std8 Ω K J S R T W z t) : Rep Ω W :=
  Hat2A7P1.T8.mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.hJ.1
    (mem_DSet_of_le_sylow hs hs.hT.1 hs.hT.2.2)
    (Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.stand.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1)

theorem le_centralizer_mul (hs : Std8 Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) :=
  Q3.Q3CL.Frame.T8.le_centralizer_mul hs.toFrame
end Std
section Klein
variable {Q : Type} [Group Q]
end Klein
section Dichotomy
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
end Dichotomy
section LayerTri
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end LayerTri
end T8
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_isSylow2In_of_le_sylow {M P Q : Subgroup G} (hP : IsSylow2In P M)
    (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G)) (hQS : Q ≤ (S : Subgroup G)) : P = Q :=
  Q3.Q3CL.Frame.T8R.eq_of_isSylow2In_of_le_sylow hP hQ hPS hQS

theorem R_ne_T (hs : Std8 Ω K J S R T W z t) : R ≠ T :=
  Q3.Q3CL.Frame.T8R.R_ne_T hs.toFrame

theorem eq_or_eq_of_mem_RSet_of_le (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {P : Subgroup G} (hP : P ∈ RSet Ω)
    (hPS : P ≤ (S : Subgroup G)) : P = R ∨ P = T :=
  Q3.Q3CL.Frame.T8R.eq_or_eq_of_mem_RSet_of_le hs.toFrame hX hP hPS

theorem fix_or_swap (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) :
    (conjSub s R = R ∧ conjSub s T = T) ∨ (conjSub s R = T ∧ conjSub s T = R) :=
  Q3.Q3CL.Frame.T8R.fix_or_swap hs.toFrame hX hsS

theorem conj_zt_of_mem_sylow (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {s : G}
    (hsS : s ∈ (S : Subgroup G)) : s * (z * t) * s⁻¹ = z * t :=
  Q3.Q3CL.Frame.T8R.conj_zt_of_mem_sylow hs.toFrame hX hsS

theorem exists_conj_of_le_of_eq_sup_oddCoreOf {X J₀ L : Subgroup G} (hΩ : HypOmegaMod Ω) (hJ₀ : J₀
    ∈ Ω) (hL : L ∈ Ω) (hJ₀X : J₀ ≤ X) (hLX : L ≤ X)
    (hX : X = J₀ ⊔ oddCoreOf X) : ∃ x ∈ X, conjSub x J₀ = L :=
  Q3.Q3CL.Frame.T8R.exists_conj_of_le_of_eq_sup_oddCoreOf hΩ hJ₀ hL hJ₀X hLX hX

theorem mul_inv_mem_oddCoreOf_of_mem_omegaNbr (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {L : Subgroup G}
    (hL : L ∈ omegaNbr Ω K) {y : G} (hy : IsUniqueInvolution L y) :
    y * t⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
  Q3.Q3CL.Frame.T8R.mul_inv_mem_oddCoreOf_of_mem_omegaNbr hs.toFrame hX hL hy

theorem conj_zt_mul_inv_mem_oddCoreOf (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {y : G}
    (hy : y ∈ Subgroup.centralizer ({z} : Set G)) :
    y * (z * t) * y⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
  Q3.Q3CL.Frame.T8R.conj_zt_mul_inv_mem_oddCoreOf hs.toFrame hX hy

theorem omegaNbrGen_conjSub (hΩ : HypOmegaMod Ω) {K : Subgroup G} (g : G) :
    omegaNbrGen Ω (conjSub g K) = conjSub g (omegaNbrGen Ω K) :=
  Q3.Q3CL.Frame.T8R.omegaNbrGen_conjSub hΩ g

theorem Std8.symm' (hs : Std8 Ω K J S R T W z t) : Std8 Ω J K S T R W t z := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  refine ⟨hs.stand.of_mem hs.hJ.1, ?_, hs.ht, ?_, hs.hz, hs.hT, hs.hR, hs.hW⟩
  · exact fun K' hK' => T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hs.hJ.1 K' hK'
  · exact Q3.Q3CL.T3.omegaNbr_symm (l6_2) hΩ hs.stand.mem hs.hJ.1 hs.hJ

theorem eq_sup_oddCoreOf_swap (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    omegaNbrGen Ω J = K ⊔ oddCoreOf (omegaNbrGen Ω J) :=
  Q3.Q3CL.Frame.T8R.eq_sup_oddCoreOf_swap hs.toFrame hX
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Odd
variable {G : Type} [Group G] [Finite G]
end Odd
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conj_zt_mul_inv_mem_of_conj (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n : G}
    (hn : conjSub n K = K ∨ conjSub n J = K) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
  Q3.Q3CL.Frame.T8R.conj_zt_mul_inv_mem_of_conj hs.toFrame hX hn
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Setup
variable {G : Type} [Group G] [Finite G]
end Setup
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) :=
  Q3.Q3CL.Frame.T8R.conj_zt_mul_inv_mem_of_orderFour hs.toFrame hX hV hxK hx4 hxc
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {G : Type} [Group G] [Finite G]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem frame_perm (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n' : G} {X : Subgroup G}
    (hXR : X ∈ RSet Ω) (hXS : X ≤ conjSub n' (S : Subgroup G)) :
    X = conjSub n' R ∨ X = conjSub n' T :=
  Q3.Q3CL.Frame.T8R.frame_perm hs.toFrame hX hXR hXS

theorem frame_conj_perm (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n' q : G}
    (hq : q ∈ conjSub n' (S : Subgroup G)) :
    (conjSub q (conjSub n' R) = conjSub n' R ∧ conjSub q (conjSub n' T) = conjSub n' T) ∨
      (conjSub q (conjSub n' R) = conjSub n' T ∧ conjSub q (conjSub n' T) = conjSub n' R) :=
  Q3.Q3CL.Frame.T8R.frame_conj_perm hs.toFrame hX hq

theorem eq_of_swap (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {g : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G))
    (hswap : conjSub (g⁻¹ * (z * t) * g) R = T) : g⁻¹ * (z * t) * g = z * t :=
  Q3.Q3CL.Frame.T8R.eq_of_swap hs.toFrame hX hV hb hswap
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {Γ : Type} [Group Γ]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem sylow_inf_omegaNbrGen (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    (S : Subgroup G) ⊓ omegaNbrGen Ω K = T :=
  Q3.Q3CL.Frame.T8R.sylow_inf_omegaNbrGen hs.toFrame hX

theorem not_mem_omegaNbr_of_four_le (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {M : Subgroup G} (hM : M ∈ Ω)
    (h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G))) (hMJ : M ≠ J) : M ∉ omegaNbr Ω K :=
  Q3.Q3CL.Frame.T8R.not_mem_omegaNbr_of_four_le hs.toFrame hX hM h4 hMJ

theorem extraTrans (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) : ExtraTrans Ω K J S z t := by
  intro M hM h4 hMK hMJ
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hcl := hΩ.conjInvariant
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hWS : W ≤ (S : Subgroup G) := hs.hW.2.1
  have hc := Hat2A7P1.T8.ctxOf hP hW
  obtain ⟨η, hηG, hWη⟩ := id hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS
  have hU : M ⊓ W ∈ η := by
    have := l6_11_proved G Ω hΩ S η hηG hηS M hM (by omega)
    rwa [← hWη] at this
  obtain ⟨S₀, hη, -⟩ := id hηG
  have hUU : M ⊓ W ∈ USet Ω := (hη.1 hU).1
  obtain ⟨RM, hRMD, hRMsyl⟩ := Q3.Q3CL.Thompson.exists_sylow_mem_DSet hΩ hW hWS hM hUU inf_le_left
    (inf_le_right.trans hWS)
  obtain ⟨ρK, hρK, hρKR⟩ : ∃ ρ : Rep Ω W, ρ.K = K ∧ ρ.R = R := ⟨T8.stdRepK hs, rfl, rfl⟩
  obtain ⟨ρJ, hρJ, -⟩ : ∃ ρ : Rep Ω W, ρ.K = J ∧ ρ.R = T := ⟨T8.stdRepJ hs, rfl, rfl⟩
  obtain ⟨ρM, hρM, -⟩ : ∃ ρ : Rep Ω W, ρ.K = M ∧ ρ.R = RM :=
    ⟨Hat2A7P1.T8.mkRep hP hW hM hRMD hRMsyl, rfl, rfl⟩
  obtain ⟨zM, hzM⟩ := hΩ.exists_uniqueInvolution hM
  have hMnK : M ∉ omegaNbr Ω K := not_mem_omegaNbr_of_four_le hs hX hM h4 hMJ
  have hMnJ : M ∉ omegaNbr Ω J :=
    not_mem_omegaNbr_of_four_le (Std8.symm' hs) (eq_sup_oddCoreOf_swap hs hX) hM h4 hMK
  have hKnM : K ∉ omegaNbr Ω M := fun h =>
    hMnK (Q3.Q3CL.T3.omegaNbr_symm (l6_2) hΩ hM hK h)
  have hJnM : J ∉ omegaNbr Ω M := fun h =>
    hMnJ (Q3.Q3CL.T3.omegaNbr_symm (l6_2) hΩ hM hJΩ h)
  have hzK : IsUniqueInvolution ρK.K z := by rw [hρK]; exact hs.hz
  have htJ : IsUniqueInvolution ρJ.K t := by rw [hρJ]; exact hs.ht
  have hzMρ : IsUniqueInvolution ρM.K zM := by rw [hρM]; exact hzM
  have hsz : ρM.r * z * ρM.r⁻¹ = zM * z :=
    hc.conj_involution ρM ρK (by rw [hρK, hρM]; exact hMK) (by rw [hρK, hρM]; exact hKnM) hzMρ hzK
  have hst : ρM.r * t * ρM.r⁻¹ = zM * t :=
    hc.conj_involution ρM ρJ (by rw [hρJ, hρM]; exact hMJ) (by rw [hρJ, hρM]; exact hJnM) hzMρ htJ
  have hzW : z ∈ W := (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρK.hK ρK.hR ρK.hRK hzK).2
  have hzMW : zM ∈ W := (Q3.Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW ρM.hK ρM.hR ρM.hRK hzMρ).2
  have hzzM : zM * z = z * zM := hc.comm_W zM hzMW z hzW
  have hrC : ρK.r ∈ Subgroup.centralizer ({z * t} : Set G) :=
    T8.le_centralizer_mul hs (hρKR ▸ ρK.hr)
  have hrN : ρK.r ∈ Subgroup.normalizer (W : Set G) := ρK.r_mem_normalizer
  have hsN : ρM.r ∈ Subgroup.normalizer (W : Set G) := ρM.r_mem_normalizer
  have hr2 : ρK.r * ρK.r ∈ W := Q3.Q3CL.Thompson.D_sq_mem hΩ hW ρK.hR ρK.hr
  have hs2 : ρM.r * ρM.r ∈ W := Q3.Q3CL.Thompson.D_sq_mem hΩ hW ρM.hR ρM.hr
  have hne : ρK.K ≠ ρM.K := by rw [hρK, hρM]; exact Ne.symm hMK
  have hnot : ρM.K ∉ omegaNbr Ω ρK.K := by rw [hρK, hρM]; exact hMnK
  have hcube : (piG W ρK.r * piG W ρM.r) ^ 3 = 1 := by
    rcases Hat2A7P1.thompsonCube hP W hW ρK.R ρK.hR ρM.R ρM.hR ρK.r ρK.hr ρM.r ρM.hr ρK.hrW ρM.hrW with
      h | h
    · exact absurd ((piG_comm_iff hrN hsN).mpr h) (hc.noncomm ρK ρM hne hnot)
    · exact (piG_cube_iff hrN hsN).mpr h
  obtain ⟨c, hcC, hcK⟩ := CFSG.ClassicalInvolution.Asc77.T8R.extraTrans_core hcl ρK ρM hzM.sq hsz hst hzzM hrC hr2 hs2 hcube
    (fun ρ' h => hc.K_eq_of_img_eq ρ' ρM h)
  exact ⟨c, hcC, Or.inl (by rw [← hρK, ← hρM]; exact hcK)⟩
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem zt_mem_sylow (hs : Std8 Ω K J S R T W z t) : z * t ∈ (S : Subgroup G) :=
  Q3.Q3CL.Frame.T8R.zt_mem_sylow hs.toFrame

theorem eq_of_centralizes (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t :=
  Q3.Q3CL.Frame.T8R.eq_of_centralizes hs.toFrame hX hV hb hxK hx4 hxc

theorem eq_of_centralizes_J (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV' : ExtraTrans Ω J K S t z)
    {g x : G} (hb : g⁻¹ * (z * t) * g ∈ (S : Subgroup G)) (hxJ : x ∈ J) (hx4 : orderOf x = 4)
    (hxc : x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x) :
    g⁻¹ * (z * t) * g = z * t :=
  Q3.Q3CL.Frame.T8R.eq_of_centralizes_J hs.toFrame hX hV' hb hxJ hx4 hxc

theorem exists_not_comm [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) :
    ∃ x y : G, x * y ≠ y * x :=
  Q3.Q3CL.Frame.T8R.exists_not_comm hs.toFrame

theorem false_of_hX [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    (hV' : ExtraTrans Ω J K S t z) (hO : OuterFusion K J S R T z t) : False :=
  Q3.Q3CL.Frame.T8R.false_of_hX hs.toFrame hX hV hV' hO
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R

@[expose] def OuterFusionAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K) →
        OuterFusion K J S R T z t

theorem c26_1_of_outer (h : OuterFusionAll) : C26_1 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc hX
  exact false_of_hX hs hX (extraTrans hs hX) (extraTrans (Std8.symm' hs)
    (eq_sup_oddCoreOf_swap hs hX)) (h G Ω K J S R T W z t hs hdisc hX)
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Pure
variable {G : Type} [Group G]
end Pure
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem Std8.conj (hs : Std8 Ω K J S R T W z t) (n : G) :
    Std8 Ω (conjSub n K) (conjSub n J) (conjSylow n S) (conjSub n R) (conjSub n T)
      (conjSub n W) (n * z * n⁻¹) (n * t * n⁻¹) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hcl := hΩ.conjInvariant
  have hmem : conjSub n K ∈ Ω := hcl n K hs.stand.mem
  refine ⟨hs.stand.conj n, ?_, hs.hz.conj n, omegaNbr_conj hcl hs.hJ n, hs.ht.conj n, ?_, ?_, ?_⟩
  · exact fun K' hK' => T8.noTwins_of_mem hcl hs.stand.trans hs.noTwins hmem K' hK'
  · obtain ⟨hR, hRK, hRS⟩ := hs.hR
    refine ⟨RSet.conj hcl hR n, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  · obtain ⟨hT, hTJ, hTS⟩ := hs.hT
    refine ⟨RSet.conj hcl hT n, conjSub_mono hTJ, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hTS
  · obtain ⟨hW, hWS, hWn⟩ := hs.hW
    refine ⟨WSet.conj hcl hW n, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs'
      rw [coe_conjSylow, mem_conjSub_iff] at hs'
      have := hWn _ hs'
      calc conjSub s (conjSub n W) = conjSub n (conjSub (n⁻¹ * s * n) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub n W := by rw [this]

theorem eq_sup_oddCoreOf_conj (hΩ : HypOmegaMod Ω)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (n : G) :
    omegaNbrGen Ω (conjSub n K) = conjSub n J ⊔ oddCoreOf (omegaNbrGen Ω (conjSub n K)) :=
  Q3.Q3CL.Frame.T8R.eq_sup_oddCoreOf_conj hΩ hX n
end Cert
end T8R
end Asc77

end

section

set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
    CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
namespace T8R
open CFSG.ClassicalInvolution.Asc77.T8R
section Cert
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_of_mem_conj_sylow (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) {n : G}
    (hzP : z ∈ conjSub n (S : Subgroup G)) (htP : t ∈ conjSub n (S : Subgroup G)) :
    n * (z * t) * n⁻¹ = z * t := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hs' := Std8.conj hs n
  have hX' := eq_sup_oddCoreOf_conj hΩ hX n
  have hV := extraTrans hs' hX'
  exact Q3.Q3CL.T8R.Loc.eq_of_mem_conj_sylow_of hs.toFrame hs'.toFrame (R_ne_T hs')
    (fix_or_swap hs' hX') (eq_of_swap hs' hX' hV) (eq_of_centralizes hs' hX' hV)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _, conj_zt_mul_inv_mem_oddCoreOf hs hX hy⟩)
    (fun hy => ⟨_, oddCoreOf_odd_natCard _,
      conj_zt_mul_inv_mem_oddCoreOf (Std8.symm' hs) (eq_sup_oddCoreOf_swap hs hX) hy⟩)
    (Hat2A7P1.l9_3 (T8.partIHyp_of_std8 hs)) hzP htP

theorem outerFusion (hs : Std8 Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) : OuterFusion K J S R T z t := by
  exact Q3.Q3CL.T8R.Loc.outerFusion_of hs.toFrame (conj_zt_of_mem_sylow hs hX)
    (eq_of_mem_conj_sylow hs hX)
end Cert

theorem outerFusionAll : OuterFusionAll := by
  intro G _ _ _ Ω K J S R T W z t hs _ hX
  exact outerFusion hs hX

theorem c26_1 : C26_1 := c26_1_of_outer (outerFusionAll)
end T8R
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8

namespace CFSG.ClassicalInvolution.Hat2A7S


theorem a7C26_1_proved : A7C26_1 :=
  Hat2A7S8.Asc77.a7C26_1_of_c26_1 Hat2A7S8.Asc77.T8R.c26_1

end CFSG.ClassicalInvolution.Hat2A7S
