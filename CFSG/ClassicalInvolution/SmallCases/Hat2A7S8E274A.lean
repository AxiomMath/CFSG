module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8C261
public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Hat2A7S8

namespace Asc77

alias l6_9_proved := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.l6_9_proved

namespace T8

alias sylow_le_sigmaNorm := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.sylow_le_sigmaNorm
alias conjSub_mem_omegaNbr := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.conjSub_mem_omegaNbr

end T8

end Asc77

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Local
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_orderFour_centralizes_one_of_three (hΩ : HypOmegaMod Ω)
    {L : Subgroup G} (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {S₀ : Subgroup G}
    (hS₀ : IsPGroup 2 S₀) {d u : G} (hd : d ∈ S₀) (hu : u ∈ S₀) (hdL : conjSub d L = L)
    (huL : conjSub u L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧
      (x * d = d * x ∨ x * u = u * x ∨ x * (d * u) = (d * u) * x) :=
  Q3.Q3CL.Frame.T8.exists_orderFour_centralizes_one_of_three hΩ hL hb hS₀ hd hu hdL huL

theorem exists_orderFour_centralizes_mul_conj (hΩ : HypOmegaMod Ω) {M P : Subgroup G} {S : Sylow 2
    G} (hM : M ∈ Ω) (hP : P ∈ RSet Ω)
    (hPM : P ≤ M) (hPS : P ≤ (S : Subgroup G)) {m : G} (hm : IsUniqueInvolution M m) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbP : conjSub b P ≠ P) {L : Subgroup G} (hL : L ∈ Ω)
    (hb : IsUniqueInvolution L b)
    (hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (m * (b * m * b⁻¹)) = (m * (b * m * b⁻¹)) * x :=
  Q3.Q3CL.Frame.T8.exists_orderFour_centralizes_mul_conj hΩ hM hP hPM hPS hm hbS hbP hL hb hCb
end Local
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_dComp_of_four_le_card (hΩ : HypOmegaMod Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) {L : Subgroup G} (hL : L ∈ Ω)
    (hLS : 4 ≤ Nat.card ↥(L ⊓ (S : Subgroup G))) : L ∈ dComp Ω K :=
  Q3.Q3CL.Frame.T8.mem_dComp_of_four_le_card hΩ hcomp hK hnt hz hR hRK hRS hW hWS hL hLS

theorem exists_conj_mem_dComp (hΩ : HypOmegaMod Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) (hSH : (S : Subgroup G) ≤ H274 Ω K z) {L : Subgroup G}
    (hL : L ∈ Ω) {x : G} (hxL : x ∈ L) (hxo : orderOf x = 4) (hxH : x ∈ H274 Ω K z) :
    ∃ y ∈ H274 Ω K z, conjSub y L ∈ dComp Ω K :=
  Q3.Q3CL.Frame.T8.exists_conj_mem_dComp hΩ hcomp hK hnt hz hR hRK hRS hW hWS hSH hL hxL hxo hxH

theorem mem_H274_of_conj_mem_sylow {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g ∈ H274 Ω K z :=
  Q3.Q3CL.Frame.T8.mem_H274_of_conj_mem_sylow hs.toFrame hcomp hg

theorem mem_H274_of_conj_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ H274 Ω K z) : g ∈ H274 Ω K z :=
  Q3.Q3CL.Frame.T8.mem_H274_of_conj_mem_H274 hs.toFrame hcomp hg
end Main
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Coset
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem fixesUniqueCoset_z {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset z (H274 Ω K z) :=
  Q3.Q3CL.Frame.T8.fixesUniqueCoset_z hs.toFrame hcomp
end Coset
end T8
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Fuse
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem sylow_le_H274_of_mem {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S₂ : Sylow 2 G}
    {X M : Subgroup G} (hX : X ∈ RSet Ω) (hXS : X ≤ (S₂ : Subgroup G)) (hM : M ∈ Ω)
    (hXM : X ≤ M) {zM : G} (hzM : IsUniqueInvolution M zM) (hzH : zM ∈ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z :=
  Q3.Q3CL.Frame.T8.sylow_le_H274_of_mem hs.toFrame hcomp hX hXS hM hXM hzM hzH

theorem exists_mul_self_ne_one_of_mem_RSet (hΩ : HypOmegaMod Ω) {X : Subgroup G} (hX : X ∈ RSet Ω)
    : ∃ x ∈ X, x * x ≠ 1 :=
  Q3.Q3CL.Frame.T8.exists_mul_self_ne_one_of_mem_RSet hΩ hX

theorem sylow_le_H274_of_good_four {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S₂ : Sylow 2 G} {u v : G} (hu : u ∈ (S₂ : Subgroup G)) (hv : v ∈ (S₂ : Subgroup G))
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) (hgu : Subgroup.centralizer ({u} : Set G) ≤ H274 Ω K z)
    (hgv : Subgroup.centralizer ({v} : Set G) ≤ H274 Ω K z)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z :=
  Q3.Q3CL.Frame.T8.sylow_le_H274_of_good_four hs.toFrame hcomp hu hv hu1 hv1 huv hu2 hv2 hc hgu hgv
    hguv
end Fuse
end T8
end Asc77

end

end CFSG.ClassicalInvolution.Hat2A7S8
