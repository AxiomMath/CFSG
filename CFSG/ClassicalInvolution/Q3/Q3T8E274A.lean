module

public import CFSG.ClassicalInvolution.Q3.Q3T8P1Seven
public import CFSG.ClassicalInvolution.Q3.Q3T8Std8
public import CFSG.ClassicalInvolution.Q3.Q3T8BendEnd
public import CFSG.ClassicalInvolution.Q3.Q3CLFrame
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77

open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc in
theorem Std8.toFrame {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (hs : Std8 Ω K J S R T W z t) :
    Std8Frame Ω K J S R T W z t :=
  ⟨hs.stand.hyp, hs.stand.mem, hs.stand.trans, hs.noTwins, hs.hz, hs.hJ, hs.ht, hs.hR, hs.hT,
    hs.hW⟩

end Asc77

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
  Q3CL.Frame.T8.exists_orderFour_centralizes_one_of_three hΩ hL hb hS₀ hd hu hdL huL

theorem exists_orderFour_centralizes_mul_conj (hΩ : HypOmegaMod Ω) {M P : Subgroup G} {S : Sylow 2
    G} (hM : M ∈ Ω) (hP : P ∈ RSet Ω)
    (hPM : P ≤ M) (hPS : P ≤ (S : Subgroup G)) {m : G} (hm : IsUniqueInvolution M m) {b : G}
    (hbS : b ∈ (S : Subgroup G)) (hbP : conjSub b P ≠ P) {L : Subgroup G} (hL : L ∈ Ω)
    (hb : IsUniqueInvolution L b)
    (hCb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (m * (b * m * b⁻¹)) = (m * (b * m * b⁻¹)) * x :=
  Q3CL.Frame.T8.exists_orderFour_centralizes_mul_conj hΩ hM hP hPM hPS hm hbS hbP hL hb hCb
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
  Q3CL.Frame.T8.mem_dComp_of_four_le_card hΩ hcomp hK hnt hz hR hRK hRS hW hWS hL hLS

theorem exists_conj_mem_dComp (hΩ : HypOmegaMod Ω)
    {K : Subgroup G} (hcomp : dComp Ω K = dstarComp Ω K) (hK : K ∈ Ω)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z)
    {R : Subgroup G} (hR : R ∈ RSet Ω) (hRK : R ≤ K) {S : Sylow 2 G}
    (hRS : R ≤ (S : Subgroup G)) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hWS : W ≤ (S : Subgroup G)) (hSH : (S : Subgroup G) ≤ H274 Ω K z) {L : Subgroup G}
    (hL : L ∈ Ω) {x : G} (hxL : x ∈ L) (hxo : orderOf x = 4) (hxH : x ∈ H274 Ω K z) :
    ∃ y ∈ H274 Ω K z, conjSub y L ∈ dComp Ω K :=
  Q3CL.Frame.T8.exists_conj_mem_dComp hΩ hcomp hK hnt hz hR hRK hRS hW hWS hSH hL hxL hxo hxH

theorem mem_H274_of_conj_mem_sylow {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ (S : Subgroup G)) : g ∈ H274 Ω K z :=
  Q3CL.Frame.T8.mem_H274_of_conj_mem_sylow hs.toFrame hcomp hg

theorem mem_H274_of_conj_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g : G}
    (hg : g⁻¹ * z * g ∈ H274 Ω K z) : g ∈ H274 Ω K z :=
  Q3CL.Frame.T8.mem_H274_of_conj_mem_H274 hs.toFrame hcomp hg
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
section SixTwo
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem isConj_or_mem_omegaNbr {K : Subgroup G} (hs : AscStand Ω K)
    (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z : G} (hz : IsUniqueInvolution K z) {g : G}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Ω K :=
  Q3CL.Frame.T8.isConj_or_mem_omegaNbr hs.hyp hs.mem (hs.aEmpty K hs.mem) hnt hz hne hcomm
end SixTwo
section Coset
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem fixesUniqueCoset_z {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) :
    FixesUniqueCoset z (H274 Ω K z) :=
  Q3CL.Frame.T8.fixesUniqueCoset_z hs.toFrame hcomp
end Coset
end T8

@[expose] def C27_4a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → FixesUniqueCoset (z * t) (T8.H274 Ω K z)

theorem c27_4_of_steps (h2 : C27_2) (h4a : C27_4a) : C27_4 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hcomp : dComp Ω K = dstarComp Ω K := h2 G Ω K J S R T W z t hs hdisc
  by_contra hne
  have hH : T8.H274 Ω K z ≠ ⊤ := hne
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have h2' : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ T8.H274 Ω K z, (z * (g⁻¹ * z * g)) • c = c := by
    intro g hne' hcomm
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne' hcomm with hconj | hnbr
    · exact CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_isConj hconj h1
    · have hb : IsUniqueInvolution (conjSub g⁻¹ K) (g⁻¹ * z * g) := by
        have := hz.conj g⁻¹
        rwa [inv_inv] at this
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub g⁻¹ K) hnbr (g⁻¹ * z * g) hb
      exact h4a G Ω K (conjSub g⁻¹ K) S' R' T' W' z (g⁻¹ * z * g) hstd hdisc
  obtain ⟨z', hz'cl⟩ := hs.stand.modU.classical K hs.stand.mem
  have hz'z : z' = z := by
    rcases hz.unique z' hz'cl.mem hz'cl.mul_self with h | h
    · exact absurd h hz'cl.ne_one
    · exact h
  have hKm : Q3.IsClassicalMember3 K z := hz'z ▸ hz'cl.toQ3 (by norm_num)
  obtain ⟨x, -, y, -, hxy⟩ := hz'cl.exists_noncomm
  exact Q3T8.false_of_uniqueCoset_of_weakMember3 ⟨x, y, hxy⟩ hH hz2 h1 h2' hKm

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
  Q3CL.Frame.T8.sylow_le_H274_of_mem hs.toFrame hcomp hX hXS hM hXM hzM hzH

theorem exists_mul_self_ne_one_of_mem_RSet (hΩ : HypOmegaMod Ω) {X : Subgroup G} (hX : X ∈ RSet Ω)
    : ∃ x ∈ X, x * x ≠ 1 :=
  Q3CL.Frame.T8.exists_mul_self_ne_one_of_mem_RSet hΩ hX

theorem sylow_le_H274_of_good_four {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S₂ : Sylow 2 G} {u v : G} (hu : u ∈ (S₂ : Subgroup G)) (hv : v ∈ (S₂ : Subgroup G))
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) (hgu : Subgroup.centralizer ({u} : Set G) ≤ H274 Ω K z)
    (hgv : Subgroup.centralizer ({v} : Set G) ≤ H274 Ω K z)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ H274 Ω K z) :
    (S₂ : Subgroup G) ≤ H274 Ω K z :=
  Q3CL.Frame.T8.sylow_le_H274_of_good_four hs.toFrame hcomp hu hv hu1 hv1 huv hu2 hv2 hc hgu hgv
    hguv
end Fuse
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
section Mu
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem not_muIsoS3_of_std8 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) : ¬ MuIsoS3 Ω W := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hP : PartIHyp Ω := ⟨hΩ, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have c : Q3CL.Thompson.Ctx Ω W := ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hs.stand.aEmpty⟩
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hSN : ∀ s ∈ (S : Subgroup G), s ∈ Subgroup.normalizer (W : Set G) := fun s hs' =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 s hs')
  have hRD : R ∈ DSet Ω W := ⟨hRΩ, fun x hx => hSN x (hRS hx)⟩
  have hTD : T ∈ DSet Ω W := ⟨hTΩ, fun x hx => hSN x (hTS hx)⟩
  have hRsyl : IsSylow2In R K := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have hnot : ∀ {R' : Subgroup G}, R' ∈ DSet Ω W → ∃ r ∈ R', r ∉ W := by
    intro R' hR'
    by_contra h
    push Not at h
    have hle : R' ≤ W := h
    have h1 := Q3CL.Thompson.D_card hΩ hW hR'
    rw [inf_eq_left.mpr hle] at h1
    have h2 : 0 < Nat.card R' := Nat.card_pos
    omega
  obtain ⟨r, hr, hrW⟩ := hnot hRD
  obtain ⟨t', ht', htW⟩ := hnot hTD
  let ρ : Rep Ω W := ⟨K, R, r, hK, hRD, hRsyl, hr, hrW⟩
  let σ : Rep Ω W := ⟨J, T, t', hJΩ, hTD, hTsyl, ht', htW⟩
  let x : ↥(muGroup Ω W) :=
    ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hRD hr))⟩
  let y : ↥(muGroup Ω W) :=
    ⟨piG W t', piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hTD ht'))⟩
  have hx : x ∈ muDelta Ω W := ⟨R, hRD, r, hr, hrW, rfl⟩
  have hy : y ∈ muDelta Ω W := ⟨T, hTD, t', ht', htW, rfl⟩
  have hxy : x ≠ y := by
    intro h
    have h' : ρ.img = σ.img := congrArg Subtype.val h
    exact hs.hJ.2.1 (c.K_eq_of_img_eq ρ σ h').symm
  have hcomm : x * y = y * x := Subtype.ext (c.comm_of_omega ρ σ hs.hJ)
  rintro ⟨φ⟩
  have h1 := Thompson.muDelta_mul_self hΩ hW hx
  have h2 := Thompson.muDelta_mul_self hΩ hW hy
  refine perm3_not_comm_involutions (φ x) (φ y) (by rw [← map_mul, h1, map_one])
    (by rw [← map_mul, h2, map_one])
    (fun h => muDelta_ne_one hW hx (φ.injective (by rw [h, map_one])))
    (fun h => muDelta_ne_one hW hy (φ.injective (by rw [h, map_one])))
    (fun h => hxy (φ.injective h)) ?_
  rw [← map_mul, ← map_mul, hcomm]
end Mu
end T8
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
