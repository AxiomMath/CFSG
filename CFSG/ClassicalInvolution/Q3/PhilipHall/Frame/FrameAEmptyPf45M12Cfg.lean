module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43Sigma
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Lift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Model

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Cfg

structure M12Std {T : Type} [Group T] (K : Subgroup T) (z : T) (J : Subgroup T) (zJ : T)
    (H : Subgroup T) : Prop extends FrameStd K z J zJ where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowM12 (⊤ : Subgroup ↥H)

structure M12Cfg {T : Type} [Group T] [Finite T] (K : Subgroup T) (z : T) (J : Subgroup T)
    (zJ : T) (H S : Subgroup T) : Prop extends FrameCfg K z J zJ S where
  hH : omegaGen (aStar (CoreAssembly.conjClass K) K) = H
  row : Thm3RowM12 (⊤ : Subgroup ↥H)
  ht : NativeSporadic.IsSporadic (SecQuot (firstFactor K)) .M12

end Cfg

section SecAux

private theorem m12_le_oddCore_of_odd {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (h : Odd (Nat.card N)) : N ≤ classicalInvolutionOddCore X :=
  le_sSup ⟨‹N.Normal›, h⟩

private theorem m12_odd_card_oddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (classicalInvolutionOddCore X)) :=
  CFSG.ComponentClassification.OddCore.odd_card X

private theorem m12_secQuot_equiv_of_sup {A X : Type} [Group A] [Group X] [Finite X]
    (ι : A →* X) (hι : Function.Injective ι) (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (hsup : ι.range ⊔ N = ⊤) :
    Nonempty ((A ⧸ classicalInvolutionOddCore A) ≃* (X ⧸ classicalInvolutionOddCore X)) := by
  haveI : Finite A := Finite.of_injective ι hι
  have hNO : N ≤ classicalInvolutionOddCore X := m12_le_oddCore_of_odd hN
  let ψ : A →* X ⧸ classicalInvolutionOddCore X :=
    (QuotientGroup.mk' (classicalInvolutionOddCore X)).comp ι
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ ι.range ⊔ N := by
      rw [hsup]
      exact Subgroup.mem_top x
    obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨a, rfl⟩ := hg
    refine ⟨a, ?_⟩
    show (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a) =
      (QuotientGroup.mk' (classicalInvolutionOddCore X)) (ι a * n)
    have h1 : (QuotientGroup.mk' (classicalInvolutionOddCore X)) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr (hNO hn)
    rw [map_mul, h1, mul_one]
  have hker : ψ.ker = classicalInvolutionOddCore A := by
    ext a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      have h1 : ι a ∈ classicalInvolutionOddCore X := (QuotientGroup.eq_one_iff _).mp ha
      have hPodd : Odd (Nat.card ((classicalInvolutionOddCore X).comap ι)) := by
        have e1 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) =
            Nat.card ((classicalInvolutionOddCore X).comap ι) :=
          Subgroup.card_map_of_injective hι
        have e2 : Nat.card (((classicalInvolutionOddCore X).comap ι).map ι) ∣
            Nat.card (classicalInvolutionOddCore X) :=
          Subgroup.card_dvd_of_le (Subgroup.map_comap_le ι _)
        rw [← e1]
        exact (m12_odd_card_oddCore X).of_dvd_nat e2
      exact m12_le_oddCore_of_odd hPodd h1
    · intro ha
      set B : Subgroup X := (classicalInvolutionOddCore A).map ι with hB
      have hBodd : Odd (Nat.card B) := by
        rw [hB, Subgroup.card_map_of_injective hι]
        exact m12_odd_card_oddCore A
      have hDodd : Odd (Nat.card (N ⊔ B : Subgroup X)) :=
        CFSG.ComponentClassification.OddCore.odd_card_sup N B hN hBodd
      have hconj : ∀ g ∈ ι.range, ∀ d ∈ N ⊔ B, g * d * g⁻¹ ∈ N ⊔ B := by
        intro g hg d hd
        obtain ⟨n', hn', b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hd
        obtain ⟨a₀, rfl⟩ := hg
        obtain ⟨b', hb', rfl⟩ := hb
        have e : ι a₀ * (n' * ι b') * (ι a₀)⁻¹ =
            (ι a₀ * n' * (ι a₀)⁻¹) * ι (a₀ * b' * a₀⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          group
        rw [e]
        exact (N ⊔ B).mul_mem (Subgroup.mem_sup_left (‹N.Normal›.conj_mem n' hn' _))
          (Subgroup.mem_sup_right ⟨a₀ * b' * a₀⁻¹,
            (inferInstance : (classicalInvolutionOddCore A).Normal).conj_mem b' hb' a₀, rfl⟩)
      have hDnormal : (N ⊔ B).Normal := by
        refine ⟨fun d hd x => ?_⟩
        have hx : x ∈ ι.range ⊔ N := by
          rw [hsup]
          exact Subgroup.mem_top x
        obtain ⟨g, hg, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
        have h1 : n * d * n⁻¹ ∈ N ⊔ B :=
          (N ⊔ B).mul_mem ((N ⊔ B).mul_mem (Subgroup.mem_sup_left hn) hd)
            ((N ⊔ B).inv_mem (Subgroup.mem_sup_left hn))
        have h2 := hconj g hg _ h1
        have e : g * n * d * (g * n)⁻¹ = g * (n * d * n⁻¹) * g⁻¹ := by group
        rw [e]
        exact h2
      have hDle : N ⊔ B ≤ classicalInvolutionOddCore X := m12_le_oddCore_of_odd hDodd
      exact (QuotientGroup.eq_one_iff _).mpr (hDle (Subgroup.mem_sup_right ⟨a, ha, rfl⟩))
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)⟩

end SecAux

section Exists

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H : Subgroup T}

theorem m12_ht_iso (hs : M12Std K z J zJ H) :
    NativeSporadic.IsSporadic (SecQuot (firstFactor K)) .M12 := by
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := hs.datum.hyp
  have hHle : H ≤ firstFactor K := by
    rw [← hs.hH]
    exact le_sup_left
  have hNle : oddCoreOf (sigmaGen K) ≤ firstFactor K := le_sup_right
  have hHtsup : H ⊔ oddCoreOf (sigmaGen K) = firstFactor K := by
    rw [← hs.hH]
    rfl
  have hHs : firstFactor K ≤ sigmaGen K := firstFactor_le_sigmaGen hΩ
  have hnorm : firstFactor K ≤ Subgroup.normalizer (oddCoreOf (sigmaGen K) : Set T) := fun x hx =>
    mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (hHs hx))
  haveI : ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hnorm
  have hodd : Odd (Nat.card ((oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv]
    exact oddCoreOf_odd_natCard _
  let ι : ↥(⊤ : Subgroup ↥H) →* ↥(firstFactor K) :=
    (Subgroup.inclusion hHle).comp (⊤ : Subgroup ↥H).subtype
  have hι : Function.Injective ι :=
    (Subgroup.inclusion_injective hHle).comp (⊤ : Subgroup ↥H).subtype_injective
  have hrange : ι.range = H.subgroupOf (firstFactor K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_top, Subgroup.inclusion_range]
  have hsup : ι.range ⊔ (oddCoreOf (sigmaGen K)).subgroupOf (firstFactor K) = ⊤ := by
    rw [hrange, ← Subgroup.subgroupOf_sup hHle hNle, hHtsup, Subgroup.subgroupOf_self]
  obtain ⟨e⟩ := m12_secQuot_equiv_of_sup ι hι _ hodd hsup
  obtain ⟨f⟩ := hs.row
  exact ⟨e.symm.trans f⟩

theorem m12_cfg_exists (hs : M12Std K z J zJ H) :
    ∃ S : Subgroup T, M12Cfg K z J zJ H S := by
  obtain ⟨S, cfg⟩ := frameCfg_exists hs.toFrameStd
  exact ⟨S, { toFrameCfg := cfg, hH := hs.hH, row := hs.row, ht := m12_ht_iso hs }⟩

end Exists

namespace M12Cfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {H S : Subgroup T}

theorem K_le_ht (_cfg : M12Cfg K z J zJ H S) : K ≤ firstFactor K :=
  (le_omegaGen (Relation.ReflTransGen.refl : K ∈ aStar (CoreAssembly.conjClass K) K)).trans
    le_sup_left

theorem z_mem_ht (cfg : M12Cfg K z J zJ H S) : z ∈ firstFactor K :=
  cfg.K_le_ht cfg.datum.unique.mem

theorem equiv (cfg : M12Cfg K z J zJ H S) :
    Nonempty (SecQuot (firstFactor K) ≃* NativeSporadic.M12) :=
  cfg.ht

theorem center_eq_bot
    (cfg : M12Cfg K z J zJ H S) : Subgroup.center (SecQuot (firstFactor K)) = ⊥ := by
  obtain ⟨e⟩ := cfg.equiv
  have h := center_map_equiv e
  rw [CFSG.Sporadic.Schreier.m12_center_eq_bot'] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem mul_mem_inner
    (cfg : M12Cfg K z J zJ H S)
    {φ ψ : MulAut (SecQuot (firstFactor K))} (hφ : φ ∉ inner (SecQuot (firstFactor K)))
    (hψ : ψ ∉ inner (SecQuot (firstFactor K))) : φ * ψ ∈ inner (SecQuot (firstFactor K)) := by
  obtain ⟨e⟩ := cfg.equiv
  set c := MulAut.congr e with hc
  have hmap := inner_map_congr e
  have key : ∀ α : MulAut (SecQuot (firstFactor K)),
      α ∈ inner (SecQuot (firstFactor K)) ↔ c α ∈ inner NativeSporadic.M12 := by
    intro α
    rw [← hmap]
    constructor
    · intro h
      exact Subgroup.mem_map_of_mem _ h
    · rintro ⟨β, hβ, hβα⟩
      have : β = α := c.injective hβα
      exact this ▸ hβ
  rw [key] at hφ hψ ⊢
  rw [map_mul]
  exact m12_mul_mem_inner _ _ hφ hψ

theorem involution_conj
    (cfg : M12Cfg K z J zJ H S) {u v : SecQuot (firstFactor K)}
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (h : (∃ k : SecQuot (firstFactor K), orderOf k = 4 ∧ k * k = u) ↔
      ∃ k : SecQuot (firstFactor K), orderOf k = 4 ∧ k * k = v) :
    ∃ x : SecQuot (firstFactor K), x * u * x⁻¹ = v := by
  obtain ⟨e⟩ := cfg.equiv
  have hsq : ∀ w : SecQuot (firstFactor K),
      (∃ k : SecQuot (firstFactor K), orderOf k = 4 ∧ k * k = w) ↔
        ∃ k : NativeSporadic.M12, orderOf k = 4 ∧ k * k = e w := by
    intro w
    constructor
    · rintro ⟨k, hk4, hkk⟩
      exact ⟨e k, by rw [MulEquiv.orderOf_eq]; exact hk4, by rw [← map_mul, hkk]⟩
    · rintro ⟨k, hk4, hkk⟩
      refine ⟨e.symm k, by rw [MulEquiv.orderOf_eq]; exact hk4, ?_⟩
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hkk]
  obtain ⟨x, hx⟩ := m12_involution_conj (e u) (e v) (by rw [← map_mul, hu2, map_one])
    (by rw [← map_mul, hv2, map_one]) (by rw [Ne, map_eq_one_iff e e.injective]; exact hu1)
    (by rw [Ne, map_eq_one_iff e e.injective]; exact hv1) ((hsq u).symm.trans (h.trans (hsq v)))
  refine ⟨e.symm x, ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hx]

theorem cent_of_inner
    (cfg : M12Cfg K z J zJ H S) {u : T} (hu2 : u * u = 1)
    (huN : u ∈ Subgroup.normalizer (firstFactor K : Set T))
    (hin : s26Act (firstFactor K) ⟨u, huN⟩ ∈ inner (SecQuot (firstFactor K))) :
    ∃ M' ∈ sigmaOf K, ∃ X' ∈ USet (CoreAssembly.conjClass K), X' ≤ M' ∧
      X' ≤ Subgroup.centralizer ({u} : Set T) := by
  obtain ⟨y, hy⟩ := hin
  have hyy : y * y = 1 := by
    have h1 : MulAut.conj (y * y) = 1 := by
      have hu1 : (⟨u, huN⟩ : ↥(Subgroup.normalizer (firstFactor K : Set T))) * ⟨u, huN⟩ = 1 :=
        Subtype.ext hu2
      rw [map_mul, hy, ← map_mul, hu1, map_one]
    have h2 : y * y ∈ Subgroup.center (SecQuot (firstFactor K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun φ : MulAut (SecQuot (firstFactor K)) => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * (y * y) = (y * y) * g * (y * y)⁻¹ * (y * y) := by rw [h3]
        _ = (y * y) * g := by group
    rw [cfg.center_eq_bot] at h2
    exact Subgroup.mem_bot.mp h2
  obtain ⟨R₀, hR₀, k, hk, hk4, -⟩ := exists_orderOf_four_of_datum cfg.datum
  have hkHt : k ∈ firstFactor K := cfg.K_le_ht (hR₀.1 hk)
  set kb : SecQuot (firstFactor K) := ((⟨k, hkHt⟩ : ↥(firstFactor K)) : SecQuot (firstFactor K))
    with hkb
  have hkb4 : orderOf kb = 4 := orderOf_mk_eq_four hkHt hk4
  obtain ⟨e⟩ := cfg.equiv
  obtain ⟨x₀, hx₀⟩ := m12_commute_conj_of_orderOf_four (e y) (e kb)
    (by rw [← map_mul, hyy, map_one]) (by rw [MulEquiv.orderOf_eq]; exact hkb4)
  have hcomm : y * (e.symm x₀ * kb * (e.symm x₀)⁻¹) = e.symm x₀ * kb * (e.symm x₀)⁻¹ * y := by
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hx₀
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm x₀)
  rw [← hx] at hcomm
  set w : ↥(firstFactor K) := x * ⟨k, hkHt⟩ * x⁻¹ with hw
  have huw : u * (w : T) * u⁻¹ ∈ firstFactor K :=
    (Subgroup.mem_normalizer_iff.mp huN (w : T)).mp w.2
  set w' : ↥(firstFactor K) := ⟨u * (w : T) * u⁻¹, huw⟩
  have hact : s26Act (firstFactor K) ⟨u, huN⟩ (w : SecQuot (firstFactor K)) =
      (w' : SecQuot (firstFactor K)) :=
    s26Act_mk (firstFactor K) ⟨u, huN⟩ w w' rfl
  have hwb : (w : SecQuot (firstFactor K)) =
      (x : SecQuot (firstFactor K)) * kb * (x : SecQuot (firstFactor K))⁻¹ := by
    rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have heq : (w' : SecQuot (firstFactor K)) = (w : SecQuot (firstFactor K)) := by
    rw [← hact, ← hy, MulAut.conj_apply, hwb, hcomm, mul_inv_cancel_right]
  have hc : (w' * w⁻¹ : ↥(firstFactor K)) ∈ classicalInvolutionOddCore ↥(firstFactor K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq,
      mul_inv_cancel]
  exact cfg.toFrameCfg.cent_of_mod_odd hu2 huN x.2 hR₀ hk hk4
    (mem_oddCoreOf_iff.mpr ⟨(w' * w⁻¹).2, hc⟩)

theorem mem_sigmaNorm_of_inner
    (cfg : M12Cfg K z J zJ H S) {u y : T} (hu : y⁻¹ * z * y = u)
    (huN : u ∈ Subgroup.normalizer (firstFactor K : Set T))
    (hin : s26Act (firstFactor K) ⟨u, huN⟩ ∈ inner (SecQuot (firstFactor K))) :
    y ∈ sigmaNorm K := by
  subst hu
  have hz2 : (y⁻¹ * z * y) * (y⁻¹ * z * y) = 1 := by
    calc (y⁻¹ * z * y) * (y⁻¹ * z * y) = y⁻¹ * (z * z) * y := by group
      _ = 1 := by rw [cfg.datum.unique.sq]; group
  obtain ⟨M', hM', X', hX', hX'M', hX'c⟩ := cfg.cent_of_inner hz2 huN hin
  exact cfg.toFrameCfg.mem_sigmaNorm_of_cent hM' hX' hX'M' hX'c

end M12Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
