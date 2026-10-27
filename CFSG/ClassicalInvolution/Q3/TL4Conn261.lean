module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.Q3CLFinal
import CFSG.ClassicalInvolution.Q3.Q3CLFrame261
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)
open CFSG.ClassicalInvolution.Asc77.T8R.Loc (Loc26)

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

section Loc

omit [Finite G] in
theorem eq_of_isSylow2In_of_le_sylow_gen {M P Q : Subgroup G} (hP : IsSylow2In P M)
    (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G)) (hQS : Q ≤ (S : Subgroup G)) : P = Q := by
  have h1 : M ⊓ (S : Subgroup G) = P :=
    hP.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hP.1 hPS)
  have h2 : M ⊓ (S : Subgroup G) = Q :=
    hQ.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hQ.1 hQS)
  exact h1.symm.trans h2

omit [Finite G] in
theorem omegaNbrGen_conjSub_gen (hcl : ConjInvariant Ω) (g : G) :
    omegaNbrGen Ω (conjSub g K) = conjSub g (omegaNbrGen Ω K) := by
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    have h1 : conjSub g⁻¹ M ∈ omegaNbr Ω K := by
      have := omegaNbr_conj hcl hM g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have := conjSub_mono (n := g) (le_omegaNbrGen h1)
    rwa [conjSub_conjSub_inv] at this
  · show (omegaNbrGen Ω K).map (MulAut.conj g).toMonoidHom ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M' hM' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_omegaNbrGen (omegaNbr_conj hcl hM' g)

theorem exists_conj_of_le_of_eq_sup_oddCoreOf_gen (hΩ : HypOmegaGen Ω) {X J₀ L : Subgroup G}
    (hJ₀ : J₀ ∈ Ω) (hL : L ∈ Ω) (hJ₀X : J₀ ≤ X) (hLX : L ≤ X) (hX : X = J₀ ⊔ oddCoreOf X) :
    ∃ x ∈ X, conjSub x J₀ = L :=
  Q3CL.Frame.T8R.exists_conj_of_le_of_eq_sup_oddCoreOf hΩ hJ₀ hL hJ₀X hLX hX

theorem loc26_of_eq_sup (hs : Std8Core Ω K J S R T W z t) (_h : TypeRFam r Ω)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    Loc26 Ω K J S R T z t (oddCoreOf (omegaNbrGen Ω K)) :=
  Q3CL.Frame.T8R.loc26_of_eq_sup hs.toFrame hX

theorem eq_sup_oddCoreOf_swap_gen (hs : Std8Core Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) :
    omegaNbrGen Ω J = K ⊔ oddCoreOf (omegaNbrGen Ω J) :=
  Q3CL.Frame.T8R.eq_sup_oddCoreOf_swap hs.toFrame hX

end Loc

section False

variable {Q Q' : Subgroup G}

theorem false_of_loc26_gen (hs : Std8Core Ω K J S R T W z t)
    (hodd : classicalInvolutionOddCore G = ⊥) (hZ : Subgroup.center G = ⊥)
    (hX : Loc26 Ω K J S R T z t Q) (hXs : Loc26 Ω J K S T R t z Q') : False := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hV := Q3CL.T8R.Loc.extraTrans hs hX hXs
  have hV' := Q3CL.T8R.Loc.extraTrans hs.symm' hXs hX
  have hO := Q3CL.T8R.Loc.outerFusion hs hX hXs
  have haa : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hzt : z ≠ t := by
    intro h'
    exact hs.hJ.2.1 (hs.noTwins J ⟨hs.hJ.1, z, hs.hz, h' ▸ hs.ht⟩)
  have ha1 : z * t ≠ 1 := fun h =>
    hzt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right hs.ht.sq))
  have hza : orderOf (z * t) = 2 := orderOf_eq_prime (by rw [pow_two]; exact haa) ha1
  have haS := Q3CL.T8R.Loc.zt_mem_sylow hs
  have hcS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := Q3CL.T8R.Loc.conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  have hzZ : (⟨z * t, haS⟩ : ↥(S : Subgroup G)) ∈ Subgroup.center ↥(S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hcS s s.2)
  have hnc : z * t ∉ Subgroup.center G := by
    rw [hZ, Subgroup.mem_bot]
    exact ha1
  obtain ⟨g₀, hg₀S, hg₀ne⟩ := CFSG.ClassicalInvolution.exists_conj_mem_sylow_ne hodd S
    ⟨z * t, haS⟩ hzZ (by rw [Subgroup.orderOf_mk]; exact hza) hnc
  set g : G := g₀⁻¹ with hg
  have hgS : g⁻¹ * (z * t) * g ∈ (S : Subgroup G) := by
    rw [hg, inv_inv]
    exact hg₀S
  have hgne : g⁻¹ * (z * t) * g ≠ z * t := by
    rw [hg, inv_inv]
    exact hg₀ne
  apply hgne
  rcases Q3CL.T8R.Loc.fix_or_swap hs hX hgS with ⟨hR, hT⟩ | ⟨hR, -⟩
  · by_cases hK : ∃ x ∈ K, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxK, hx4, hxc⟩ := hK
      exact Q3CL.T8R.Loc.eq_of_centralizes hs hX hV hgS hxK hx4 hxc
    by_cases hJ : ∃ x ∈ J, orderOf x = 4 ∧
        x * (g⁻¹ * (z * t) * g) = (g⁻¹ * (z * t) * g) * x
    · obtain ⟨x, hxJ, hx4, hxc⟩ := hJ
      exact Q3CL.T8R.Loc.eq_of_centralizes_J hs hXs hV' hgS hxJ hx4 hxc
    exact hO g hgS hR hT hK hJ
  · exact Q3CL.T8R.Loc.eq_of_swap hs hX hV hgS hR

end False

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.omegaNbrGen_ne_sup (hs : TightStd8R r n Rd Sd z J S R T W t) :
    omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠
      J ⊔ oddCoreOf (omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) := by
  intro hX
  have h := TightLargeHypR.typeRFam hs.large
  have hs0 := hs.toStd8Core
  exact false_of_loc26_gen hs0 hs.large.cls.2.2 hs.large.center (loc26_of_eq_sup hs0 h hX)
    (loc26_of_eq_sup hs0.symm' h (eq_sup_oddCoreOf_swap_gen hs0 hX))

theorem TightStd8R.top_not_mem_xFam (hs : TightStd8R r n Rd Sd z J S R T W t) :
    (⊤ : Subgroup (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))) ∉
      xFam (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set X := omegaNbrGen Ω (tightCore Rd) with hXdef
  have hΩ : HypOmegaGen Ω := hs.hyp
  rintro ⟨_, ⟨L, hL, hLX, rfl⟩, htop⟩
  have hXL : X = L ⊔ oddCoreOf X := by
    refine le_antisymm (fun x hx => ?_) (sup_le hLX (oddCoreOf_le_self X))
    have hxt : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨x, hx⟩ ∈
        (L.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlx⟩ := hxt
    have ho : l⁻¹ * ⟨x, hx⟩ ∈ classicalInvolutionOddCore ↥X := QuotientGroup.eq.mp hlx
    have e : x = (l : Y) * ((l⁻¹ * ⟨x, hx⟩ : ↥X) : Y) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) ⟨_, ho, rfl⟩
  obtain ⟨x, hxX, hxL⟩ := exists_conj_of_le_of_eq_sup_oddCoreOf_gen hΩ hL hs.hJ.1 hLX
    (le_omegaNbrGen hs.hJ) hXL
  have hxO : conjSub x (oddCoreOf X) = oddCoreOf X :=
    mem_normalizer_iff_conjSub_eq.mp
      (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer hxX))
  apply hs.omegaNbrGen_ne_sup
  calc X = conjSub x X := (conjSub_eq_self_of_mem hxX).symm
    _ = conjSub x (L ⊔ oddCoreOf X) := by rw [← hXL]
    _ = J ⊔ oddCoreOf X := by rw [Thompson.conjSub_sup, hxL, hxO]

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
