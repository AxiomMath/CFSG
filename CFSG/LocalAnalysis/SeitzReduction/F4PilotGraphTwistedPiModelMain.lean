module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelSp4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelF4
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedDKernel

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.UnbalancedCatalog (descentField mem_descentField)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.ClassicalInvolution.Upgrade (irreducible_map)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear)

local instance f4PilotGraphTwistedPiModelMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section Partner

variable {k K : Type} [Field k] [Field K] {G M : Type*} [Group G] [Group M]

theorem exists_partner_of_mem_closure_two (φA : StatedSp 3 k →* G) (φD : StatedSp 3 K →* G)
    (FA : StatedSp 3 k →* M) (FD : StatedSp 3 K →* M)
    (hgen : ∀ s ∈ sp4Gens k, ∃ t, φD t = φA s ∧ FA s = FD t) {s : StatedSp 3 k}
    (hs : s ∈ closure (sp4Gens k)) : ∃ t, φD t = φA s ∧ FA s = FD t := by
  induction hs using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => exact ⟨1, by rw [map_one, map_one], by rw [map_one, map_one]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t, ht1, ht2⟩ := ha
    obtain ⟨u, hu1, hu2⟩ := hb
    exact ⟨t * u, by rw [map_mul, map_mul, ht1, hu1], by rw [map_mul, map_mul, ht2, hu2]⟩
  | inv a _ ha =>
    obtain ⟨t, ht1, ht2⟩ := ha
    exact ⟨t⁻¹, by rw [map_inv, map_inv, ht1], by rw [map_inv, map_inv, ht2]⟩

end Partner

theorem exists_ringEquiv_sq_eq_self {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ ε' : K ≃+* K, ∀ y : K, ε' y ^ 2 = y :=
  ⟨(frobeniusEquiv K 2).symm, fun y => frobeniusEquiv_symm_pow_p K 2 y⟩

section Pi


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
  {K : Type} [Field K] [Finite K] [CharP K 2] (ε : h.fixedField ≃+* K)
  {ω : F} (hω : h.barEquiv ω ≠ ω)

omit
  [Finite K] [CharP K 2] in
include hω in
theorem twFieldEquiv_d4MinusB_ne_zero : twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ≠ 0 :=
  (map_ne_zero _).2 (ne_zero_of_irreducible _ (d4Minus_irr (twBar_bar h) hω))

omit
  [Finite K] [CharP K 2] in
include hω in
theorem twMinus_irr : ∀ s : K, s ^ 2 + 1 * s + twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
    twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2 ≠ 0 := by
  have hb := twFieldEquiv_d4MinusB_ne_zero h ε hω
  have hirr' := irreducible_map (twFieldEquiv h ε) (d4Minus_irr (twBar_bar h) hω)
  intro s hs
  apply hirr' (twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) * s)
  have e : (twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) * s) ^ 2 +
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) *
        (twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) * s) +
      twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) =
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2 *
        (s ^ 2 + 1 * s + twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
          twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2) := by
    field_simp
  rw [e, hs, mul_zero]

@[expose] noncomputable def twPi :
    twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes →*
      StatedOmega (StatedQuadMinus 4 K 1 (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
        twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2)) :=
  (twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω)
    (twFieldEquiv_d4MinusB_ne_zero h ε hω)).toMonoidHom.comp
      (twCoverPi h.barEquiv (twBar_bar h) hω)

omit [Finite K] [CharP K 2] in
theorem twPi_apply (x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
    twPi h ε hω x = twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω)
      (twFieldEquiv_d4MinusB_ne_zero h ε hω) (twCoverPi h.barEquiv (twBar_bar h) hω x) :=
  rfl

omit [Finite K] [CharP K 2] in
theorem twPi_surjective : Function.Surjective (twPi h ε hω) :=
  (twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω)
    (twFieldEquiv_d4MinusB_ne_zero h ε hω)).surjective.comp
      (twCoverPi_surjective (twBar_bar h) hω)

omit [Finite K] [CharP K 2] in
theorem ker_twPi_le_center :
    (twPi h ε hω).ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) := by
  intro x hx
  have hx' : twCoverPi h.barEquiv (twBar_bar h) hω x = 1 :=
    (twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω)
      (twFieldEquiv_d4MinusB_ne_zero h ε hω)).injective (by rw [map_one]; exact hx)
  exact ker_twCoverPi_le_center (twBar_bar h) hω hx'

theorem twPi_bijective (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    Function.Bijective (twPi h ε hω) := by
  have hk4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have := finite_twLevi h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes
  obtain ⟨t₀, ht₀θ, ht₀⟩ := exists_barFixed_unit_sq_ne_one h hf
  have hθ : ∀ c, h.barEquiv.toRingHom (h.barEquiv.toRingHom c) = c := h.bar_bar
  have : Group.IsPerfect (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :=
    isPerfect_iff.mpr (commutator_twLevi_Y _ hθ ht₀θ ht₀)
  obtain ⟨s, hs⟩ := omegaMinus8_exists_section K hk4 (twMinus_irr h ε hω) _ (twPi h ε hω)
    (twPi_surjective h ε hω) (ker_twPi_le_center h ε hω)
  exact ⟨injective_of_section_of_perfect _ (ker_twPi_le_center h ε hω) s hs,
    twPi_surjective h ε hω⟩

omit [Finite K] in
theorem twPi_sigmaHat {x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes}
    (hxy : (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x) :
    twPi h ε hω y = omegaMinusBetaC K 1 (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2) (twPi h ε hω x) := by
  rw [twPi_apply, twPi_apply, twCoverPi_sigmaHat (twBar_bar h) hω (x := x) (y := y) hxy,
    twTransport_betaC]

theorem twPi_commute_diag_one_two (x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes)
    (hx : (x : fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {1, 2})
    {t : Fin 3 → Kˣ} (ht1 : t 1 = 1) (ht2 : t 2 = 1) :
    Commute (twPi h ε hω x) ⟨diagOmegaMinus K t, diagOmegaMinus_mem _ _ t⟩ := by
  rw [twPi_apply]
  refine commute_twTransport_diag _ _ _ (commute_twCoverPi_one_two (twBar_bar h) hω x hx ?_ ?_)
  · rw [ht1, map_one]
  · rw [ht2, map_one]

theorem twPi_commute_diag_zero (x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes)
    (hx : (x : fixedGroup F h.barEquiv.toRingHom) ∈ twLevi F h.barEquiv.toRingHom {0})
    {t : Fin 3 → Kˣ} (ht : t 0 = t 1) :
    Commute (twPi h ε hω x) ⟨diagOmegaMinus K t, diagOmegaMinus_mem _ _ t⟩ := by
  rw [twPi_apply]
  refine commute_twTransport_diag _ _ _ (commute_twCoverPi_zero (twBar_bar h) hω x hx ?_)
  rw [ht]

variable (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

@[expose] noncomputable def twTheta :
    StatedOmega (StatedQuadMinus 4 K 1 (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2)) ≃*
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes :=
  (MulEquiv.ofBijective (twPi h ε hω) (twPi_bijective h ε hω hK hf)).symm

theorem twTheta_twPi (y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
    twTheta h ε hω hK hf (twPi h ε hω y) = y :=
  (MulEquiv.ofBijective (twPi h ε hω) (twPi_bijective h ε hω hK hf)).symm_apply_apply y

theorem twTheta_symm_apply (x : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
    (twTheta h ε hω hK hf).symm x = twPi h ε hω x :=
  rfl

theorem twTheta_betaC (g : StatedOmega (StatedQuadMinus 4 K 1
    (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2))) :
    ((twTheta h ε hω hK hf (omegaMinusBetaC K 1 (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2) g) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) =
      sigmaHat h.barEquiv.toRingHom (twTheta h ε hω hK hf g) := by
  set Θ₀ := MulEquiv.ofBijective (twPi h ε hω) (twPi_bijective h ε hω hK hf) with hΘ₀
  have hy := twPi_sigmaHat h ε hω (x := Θ₀.symm g)
    (y := sigmaTwLevi AmalgamNeighbour.Y.nodes (Θ₀.symm g)) (coe_sigmaTwLevi _ _)
  have key : Θ₀.symm (omegaMinusBetaC K 1 (twFieldEquiv h ε (d4MinusC (twBar_bar h) ω) /
      twFieldEquiv h ε (d4MinusB (twBar_bar h) ω) ^ 2) g) =
      sigmaTwLevi AmalgamNeighbour.Y.nodes (Θ₀.symm g) := by
    rw [MulEquiv.symm_apply_eq]
    change omegaMinusBetaC K 1 _ g = twPi h ε hω (sigmaTwLevi _ (Θ₀.symm g))
    rw [hy]
    congr 1
    exact (Θ₀.apply_symm_apply g).symm
  show ((Θ₀.symm (omegaMinusBetaC K 1 _ g) :
    twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) : fixedGroup F h.barEquiv.toRingHom) =
      sigmaHat h.barEquiv.toRingHom (Θ₀.symm g)
  rw [key, coe_sigmaTwLevi]

end Pi

section Agree


variable {f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (h : UnitaryFieldData 2 f F)
  {K : Type} [Field K] [Finite K] [CharP K 2] (ε : h.fixedField ≃+* K)
  {ω : F} (hω : h.barEquiv ω ≠ ω) (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
  (ψ : K ≃+* K) (hψ : ∀ y : K, ψ y ^ 2 = y)

include hψ in
theorem twPi_partner_of_mem_sp4Gens {s : StatedSp 3 h.fixedField} (hs : s ∈ sp4Gens h.fixedField) :
    ∃ t : StatedSp 3 K,
      ((twTheta h ε hω hK hf (omegaMinusIota hK hf (twMinus_irr h ε hω) t) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) =
        ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) ∧
      (((c3LeviEquiv K (statedSpCongr ε 3 s) : C3Levi K) : adjointGroup .F4 K),
          graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 s) : C3Levi K)) =
        (graphAutF4 K (c3LeviEquiv K (statedSpCongr ψ 3 t) : C3Levi K),
          ((c3LeviEquiv K t : C3Levi K) : adjointGroup .F4 K)) := by
  have hmem := twParamEquiv_uEmbed6_mem_Y h hs
  have key := twTheta_twPi h ε hω hK hf ⟨_, hmem⟩
  have hΘ : ∀ t, omegaMinusIota hK hf (twMinus_irr h ε hω) t =
      twTransport (twFieldEquiv h ε) (d4MinusC (twBar_bar h) ω)
        (twFieldEquiv_d4MinusB_ne_zero h ε hω) (twCoverPi h.barEquiv (twBar_bar h) hω ⟨_, hmem⟩) →
      ((twTheta h ε hω hK hf (omegaMinusIota hK hf (twMinus_irr h ε hω) t) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) =
        ((twParamEquiv h (uEmbed6 h s) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
          fixedGroup F h.barEquiv.toRingHom) := by
    intro t ht
    rw [ht]
    exact congrArg Subtype.val key
  have hb := twFieldEquiv_d4MinusB_ne_zero h ε hω
  obtain ⟨c, rfl | rfl | rfl | rfl⟩ := hs
  · refine ⟨CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 2 1) (ε c ^ 2),
      hΘ _ (omegaMinusIota_partner_x_single_one h ε hω hb hK hf _ c hmem), ?_⟩
    rw [statedSpCongr_x, statedSpCongr_x, map_pow, hψ, c3LeviEquiv_x_single_one,
      c3LeviEquiv_x_single_two, c3LeviEquiv_x_single_two]
    exact Prod.ext (graphAutF4_pinnedX_single_one (ε c)).symm
      (graphAutF4_pinnedX_single_two (ε c))
  · refine ⟨CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 2 1) (ε c ^ 2),
      hΘ _ (omegaMinusIota_partner_x_neg_single_one h ε hω hb hK hf _ c hmem), ?_⟩
    rw [statedSpCongr_x, statedSpCongr_x, map_pow, hψ, c3LeviEquiv_x_neg_single_one,
      c3LeviEquiv_x_neg_single_two, c3LeviEquiv_x_neg_single_two]
    exact Prod.ext (graphAutF4_pinnedX_neg_single_one (ε c)).symm
      (graphAutF4_pinnedX_neg_single_two (ε c))
  · refine ⟨CFSG.LieType.Steinberg.Sp.x 3 K (Pi.single 1 1) (ε c),
      hΘ _ (omegaMinusIota_partner_x_single_two h ε hω hb hK hf _ c hmem), ?_⟩
    rw [statedSpCongr_x, statedSpCongr_x, c3LeviEquiv_x_single_two, c3LeviEquiv_x_single_one,
      c3LeviEquiv_x_single_one]
    exact Prod.ext ((graphAutF4_pinnedX_single_two (ψ (ε c))).trans (by rw [hψ])).symm
      (graphAutF4_pinnedX_single_one (ε c))
  · refine ⟨CFSG.LieType.Steinberg.Sp.x 3 K (-Pi.single 1 1) (ε c),
      hΘ _ (omegaMinusIota_partner_x_neg_single_two h ε hω hb hK hf _ c hmem), ?_⟩
    rw [statedSpCongr_x, statedSpCongr_x, c3LeviEquiv_x_neg_single_two,
      c3LeviEquiv_x_neg_single_one, c3LeviEquiv_x_neg_single_one]
    exact Prod.ext ((graphAutF4_pinnedX_neg_single_two (ψ (ε c))).trans (by rw [hψ])).symm
      (graphAutF4_pinnedX_neg_single_one (ε c))

include hψ in
theorem twPi_sp4_agree {sA : StatedSp 3 h.fixedField} {sD : StatedSp 3 K}
    (hsA : sp6ToSL6 sA ∈ blockSpecialLinear (K := h.fixedField) lin6BlockA)
    (hx : ((twTheta h ε hω hK hf (omegaMinusIota hK hf (twMinus_irr h ε hω) sD) :
      twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
        fixedGroup F h.barEquiv.toRingHom) =
      ((twParamEquiv h (uEmbed6 h sA) : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) :
        fixedGroup F h.barEquiv.toRingHom)) :
    (((c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K) : adjointGroup .F4 K),
        graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 sA) : C3Levi K)) =
      (graphAutF4 K (c3LeviEquiv K (statedSpCongr ψ 3 sD) : C3Levi K),
        ((c3LeviEquiv K sD : C3Levi K) : adjointGroup .F4 K)) := by
  obtain ⟨t, ht, hpair⟩ := exists_partner_of_mem_closure_two
    ((twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes).subtype.comp
      ((twParamEquiv h).toMonoidHom.comp (uEmbed6 h)))
    ((twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes).subtype.comp
      ((twTheta h ε hω hK hf).toMonoidHom.comp (omegaMinusIota hK hf (twMinus_irr h ε hω))))
    (((C3Levi K).subtype.comp
      ((c3LeviEquiv K).toMonoidHom.comp (statedSpCongr ε 3).toMonoidHom)).prod
      ((graphAutF4 K).toMonoidHom.comp ((C3Levi K).subtype.comp
        ((c3LeviEquiv K).toMonoidHom.comp (statedSpCongr ε 3).toMonoidHom))))
    (((graphAutF4 K).toMonoidHom.comp ((C3Levi K).subtype.comp
      ((c3LeviEquiv K).toMonoidHom.comp (statedSpCongr ψ 3).toMonoidHom))).prod
      ((C3Levi K).subtype.comp (c3LeviEquiv K).toMonoidHom))
    (fun _ hs => twPi_partner_of_mem_sp4Gens h ε hω hK hf ψ hψ hs)
    (mem_closure_sp4Gens_of_sp6ToSL6_mem hsA)
  have hinj : Function.Injective fun t : StatedSp 3 K =>
      ((twTheta h ε hω hK hf (omegaMinusIota hK hf (twMinus_irr h ε hω) t) :
        twLevi F h.barEquiv.toRingHom AmalgamNeighbour.Y.nodes) :
          fixedGroup F h.barEquiv.toRingHom) :=
    Subtype.val_injective.comp ((twTheta h ε hω hK hf).injective.comp
      (omegaMinusIota_injective hK hf _))
  have htD : t = sD := hinj (ht.trans hx.symm)
  subst htD
  exact hpair

end Agree

end CFSG.SeitzReduction.F4Pilot
