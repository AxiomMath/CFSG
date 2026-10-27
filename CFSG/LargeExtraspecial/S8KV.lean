module

public import CFSG.LargeExtraspecial.S8ThreeB
public import CFSG.LargeExtraspecial.S8ThreeF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

theorem exists_pair_of_finrank_le_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {I : Submodule (ZMod 2) M} [FiniteDimensional (ZMod 2) I] (h : finrank (ZMod 2) I ≤ 2) :
    ∃ u₁ ∈ I, ∃ u₂ ∈ I, ∀ x ∈ I, ∃ a b : ZMod 2, a • u₁ + b • u₂ = x := by
  have : Module.Finite (ZMod 2) ↥(Submodule.span (ZMod 2) (I : Set M)) := by
    rw [Submodule.span_eq]
    infer_instance
  obtain ⟨f, hfI, hspan, -⟩ := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) (I : Set M)
  have hk : finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) ≤ 2 := by
    rwa [Submodule.span_eq]
  let u₁ : M :=
    if h0 : 0 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then f ⟨0, h0⟩ else 0
  let u₂ : M :=
    if h1 : 1 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then f ⟨1, h1⟩ else 0
  have hu₁ : u₁ ∈ I := by
    change (if h0 : 0 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then
      f ⟨0, h0⟩ else 0) ∈ I
    split_ifs
    · exact hfI _
    · exact I.zero_mem
  have hu₂ : u₂ ∈ I := by
    change (if h1 : 1 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then
      f ⟨1, h1⟩ else 0) ∈ I
    split_ifs
    · exact hfI _
    · exact I.zero_mem
  have hrange : Set.range f ⊆ {u₁, u₂} := by
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    have hj2 : j < 2 := lt_of_lt_of_le hj hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj2 with hj1 | rfl
    · have hj0 : j = 0 := by omega
      subst hj0
      left
      change f ⟨0, hj⟩ = if h0 : 0 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then
        f ⟨0, h0⟩ else 0
      split_ifs with h
      · rfl
      · exact absurd hj h
    · right
      change f ⟨1, hj⟩ = if h1 : 1 < finrank (ZMod 2) (Submodule.span (ZMod 2) (I : Set M)) then
        f ⟨1, h1⟩ else 0
      split_ifs with h
      · rfl
      · exact absurd hj h
  have hI : I ≤ Submodule.span (ZMod 2) {u₁, u₂} := by
    calc I = Submodule.span (ZMod 2) (I : Set M) := (Submodule.span_eq I).symm
      _ = Submodule.span (ZMod 2) (Set.range f) := hspan.symm
      _ ≤ Submodule.span (ZMod 2) {u₁, u₂} := Submodule.span_mono hrange
  exact ⟨u₁, hu₁, u₂, hu₂, fun x hx => Submodule.mem_span_pair.mp (hI hx)⟩

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem mem_Nbar_of_forall_apply_sub_mem (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t))
    {U : Submodule (ZMod 2) S.Qt} (hUW : U ≤ Wt S g t)
    (hU : ∀ r ∈ Rbar S g t, ∀ u ∈ U, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U)
    (hL : ¬ ∀ l ∈ S.Lbar g, ∀ u ∈ U, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t)
    {r : S.O} (hr : r ∈ Rbar S g t)
    (hrU : ∀ u ∈ U, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t) :
    r ∈ Nbar S g t := by
  have haQ := H.conj_mem
  have hs : IsSimpleGroup (RmodN S g t) := ((S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6).1
  let K : Subgroup (Rbar S g t) :=
    { carrier := {x | ∀ u ∈ U, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t}
      one_mem' := fun u _ => by
        change ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t
        rw [show ((1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u from rfl, sub_self]
        exact zero_mem _
      mul_mem' := fun {x y} hx hy u hu => by
        have hyu : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := hU _ y.2 u hu
        have e : (((x * y : Rbar S g t) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
            (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
              ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) +
            (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by
          rw [Subgroup.coe_mul, coe_mul_apply]
          abel
        rw [e]
        exact add_mem (hx _ hyu) (hy u hu)
      inv_mem' := fun {x} hx u hu => by
        have hxu : (((x : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U :=
          hU _ (inv_mem x.2) u hu
        have h1 : ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((((x : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) -
              (((x : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Vt S g t := hx _ hxu
        rw [apply_inv_apply_O] at h1
        have h2 := neg_mem h1
        rw [neg_sub] at h2
        change ((((x⁻¹ : Rbar S g t) : S.O)) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t
        rw [Subgroup.coe_inv]
        exact h2 }
  have hmemK : ∀ x : Rbar S g t, x ∈ K ↔
      ∀ u ∈ U, ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t := fun _ => Iff.rfl
  have hKn : ∀ x k : Rbar S g t, k ∈ K → x * k * x⁻¹ ∈ K := by
    intro x k hk
    rw [hmemK] at hk ⊢
    intro u hu
    have hxu : (((x : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U :=
      hU _ (inv_mem x.2) u hu
    have h1 := apply_mem_Vt_of_mem_Rbar haQ x.2 (hk _ hxu)
    rw [map_sub, apply_inv_apply_O] at h1
    have e : (((x * k * x⁻¹ : Rbar S g t) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u =
        ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((((x : S.O)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := rfl
    rw [e]
    exact h1
  set K' := K.map (resV haQ t) with hK'
  have hrange := range_resV haQ t
  have hK'R : K' ≤ RmodN S g t := hrange ▸ map_le_range _ _
  have hK'n : (K'.subgroupOf (RmodN S g t)).Normal := by
    refine ⟨fun z hz y => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨k, hk, hkz⟩ := hz
    have hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (resV haQ t).range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x * k * x⁻¹, hKn x k hk, ?_⟩
    simp only [map_mul, map_inv, hx, hkz, Subgroup.coe_mul, Subgroup.coe_inv]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.subgroupOf (RmodN S g t)) with
    hbot | htop
  ·
    have hrK : (⟨r, hr⟩ : Rbar S g t) ∈ K := hrU
    have hK'r : resV haQ t ⟨r, hr⟩ ∈ K' := Subgroup.mem_map_of_mem _ hrK
    have h1 : (⟨resV haQ t ⟨r, hr⟩, hK'R hK'r⟩ : RmodN S g t) ∈
        K'.subgroupOf (RmodN S g t) := mem_subgroupOf.mpr hK'r
    have h2 := (Subgroup.eq_bot_iff_forall _).mp hbot _ h1
    exact (resV_eq_one_iff haQ ⟨r, hr⟩).mp (congrArg Subtype.val h2)
  ·
    exfalso
    apply hL
    intro l hl u hu
    have hlR : l ∈ Rbar S g t := Lbar_le_Rbar ht hl
    have hmemR : resV haQ t ⟨l, hlR⟩ ∈ RmodN S g t := by
      rw [← hrange]
      exact ⟨_, rfl⟩
    have h1 := (Subgroup.eq_top_iff' _).mp htop ⟨_, hmemR⟩
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp (mem_subgroupOf.mp h1)
    have hkl2 : resV haQ t k = resV haQ t ⟨l, hlR⟩ := hkl
    have hn : ((k⁻¹ * ⟨l, hlR⟩ : Rbar S g t) : S.O) ∈ Nbar S g t :=
      (resV_eq_one_iff haQ _).mp (by rw [map_mul, map_inv, hkl2, inv_mul_cancel])
    have hkl' : ((⟨l, hlR⟩ : Rbar S g t) : S.O) =
        (k : S.O) * ((k⁻¹ * ⟨l, hlR⟩ : Rbar S g t) : S.O) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    have hnu := D.hN _ hn u (hUW hu)
    have hku := hk u hu
    have h2 := apply_mem_Vt_of_mem_Rbar haQ k.2 hnu
    change (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u ∈ Vt S g t
    have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u =
        ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((((k⁻¹ * ⟨l, hlR⟩ : Rbar S g t) : S.O) :
          S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) + (((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by
      have e1 : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) u = ((k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((((k⁻¹ * ⟨l, hlR⟩ : Rbar S g t) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := by
        rw [← coe_mul_apply, ← hkl']
      rw [e1, map_sub]
      abel
    rw [e]
    exact add_mem h2 hku

variable (S) in
@[expose] noncomputable def tauBil (τ : S.O) : LinearMap.BilinForm (ZMod 2) S.Qt :=
  CFSG.LargeExtraspecial.commForm S.q (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)

theorem tauBil_apply (τ : S.O) (x y : S.Qt) :
    tauBil S τ x y = polar S.q ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) y :=
  CFSG.LargeExtraspecial.commForm_apply _ x y

structure Bad3 (D : Std H C ht ht1 hVQ) (τ : S.O) : Prop where
  hCE : CentralExtInput.{u}
  hNo : NoA2 S g
  hΩ : OmegaCase H C ht ht1 hVQ
  hm3 : D.m = 3
  hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t
  hn : S.width ≠ 10
  hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t
  mem : τ ∈ conjCentM S t
  not_mem : τ ∉ Nbar S g t

namespace Bad3

variable {D : Std H C ht ht1 hVQ} {τ : S.O} (B : Bad3 D τ)
include B

theorem six_le : 6 ≤ finrank (ZMod 2) (Vt S g t) := by
  have := D.hdim
  have := B.hm3
  omega

theorem fix_Vt : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
  step1_fix_Vt B.hCE B.hNo B.hΩ D B.hA7 (Or.inl B.hm3) B.hsub
    (fun h => h.elim (fun h' => B.hn h'.2)
      (fun h' => absurd (h'.1.symm.trans B.hm3) (by norm_num))) τ B.mem

theorem τM : τ ∈ S.Mbar := B.mem.1

theorem τt : τ * t = t * τ := B.mem.2.1

theorem mul_self : τ * τ = 1 := by
  obtain ⟨-, -, x, -, rfl⟩ := B.mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
    _ = 1 := by rw [htt]; group

theorem not_flag : ¬ ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := by
  intro hfl
  have hτV := B.fix_Vt
  obtain ⟨-, hτt, x, hxM, hxτ⟩ := B.mem
  exact B.not_mem (mem_Nbar_of_flag B.hCE B.hNo B.hΩ D (by have := B.hm3; omega)
    (fun k hk => cl_mem_orbit_of_omegaCase B.hCE H B.hNo C B.hΩ B.six_le hk) B.hsub hxM hxτ
    hτt hτV hfl)

theorem U_le_Wt : (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t ≤
    Wt S g t := by
  refine sup_le ?_ (Vt_le_Wt H ht1)
  rintro _ ⟨w, hw, rfl⟩
  exact (Wt S g t).sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ B.τt hw) hw

theorem U_invariant : ∀ r ∈ Rbar S g t, ∀ u ∈ (Wt S g t).map
    ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t,
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ (Wt S g t).map
        ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t :=
  comm_sup_Vt_invariant D B.τM B.τt B.fix_Vt

theorem finrank_U : finrank (ZMod 2) (((Wt S g t).map
    ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t).map (Vt S g t).mkQ) = 4 := by
  have hτV := B.fix_Vt
  have hnf := B.not_flag
  obtain ⟨-, hτt, x, hxM, hxτ⟩ := B.mem
  exact (finrank_inf_of_three B.hCE B.hNo B.hΩ D B.hm3 hxM hxτ hτt hτV hnf).1

theorem finrank_U_inf : finrank (ZMod 2) ((((Wt S g t).map
    ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ⊔ Vt S g t) ⊓
      (S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t)).map (Vt S g t).mkQ) = 2 := by
  have h := (finrank_map_mkQ_of_invariant B.hCE B.hNo B.hΩ D le_sup_right B.U_le_Wt
    B.U_invariant).2.2
  rw [B.finrank_U] at h
  omega

theorem apply_mem_clSub_a {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  apply_mem_clSub_of_apply_cl_eq H.conj_mem H.conj_ne B.τM (B.fix_Vt _ (cl_a_mem_Vt ht)) hp

theorem apply_mem_clSub_b {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g))) :
    (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa ((D.h : G) * g)) :=
  apply_mem_clSub_of_apply_cl_eq (H.mul D.h).conj_mem (H.mul D.h).conj_ne B.τM
    (B.fix_Vt _ (cl_mem_Vt (mem_Lbar_of_pair H ht D.hh))) hp

theorem tauBil_symm (x y : S.Qt) : tauBil S τ x y = tauBil S τ y x := by
  have hττ := B.mul_self
  have h1 : ∀ a b : S.Qt, polar S.q ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) a) b =
      polar S.q a ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) b) := fun a b => by
    have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) b) = b := by
      rw [← coe_mul_apply, hττ]
      rfl
    conv_lhs => rw [← e]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup τ.2 _ _
  rw [tauBil_apply, tauBil_apply, polar_sub_left, polar_sub_left, h1 x y, polar_comm S.q x y,
    polar_comm S.q x]

theorem tauBil_apply_apply {r : S.O} (hr : r ∈ Rbar S g t) {x y : S.Qt}
    (hx : x ∈ Wt S g t) (hy : y ∈ Wt S g t) :
    tauBil S τ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y) =
      tauBil S τ x y := by
  obtain ⟨ν, hνdef⟩ : ∃ ν : S.O, ν = r⁻¹ * τ * r⁻¹⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  have hν : ν ∈ Nbar S g t := by
    rw [hνdef]
    exact comm_mem_Nbar_of_fix H B.τM B.τt B.fix_Vt (inv_mem hr)
  have hτx : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x ∈ Wt S g t :=
    apply_mem_Wt_of_commute H C ht ht1 hVQ B.τt hx
  have hc := D.hN ν hν _ hτx
  have h1 : τ * r = r * (ν * τ) := by rw [hνdef]; group
  have e : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) x) -
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) x = (r : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) + ((ν : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x) - (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) := by
    rw [← coe_mul_apply τ r, h1, coe_mul_apply, coe_mul_apply, map_add, map_sub, map_sub]
    abel
  rw [tauBil_apply, tauBil_apply, e,
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup r.2, polar_add_left,
    mem_Wt.mp hy _ hc, add_zero]

theorem tauBil_comm_symm {l : S.O} (hl : l ∈ S.Lbar g) {z₁ z₂ : S.Qt} (hz₁ : z₁ ∈ Wt S g t)
    (hz₂ : z₂ ∈ Wt S g t) :
    tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ - z₁) z₂ =
      tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₂ - z₂) z₁ := by
  have hinv := B.tauBil_apply_apply (Lbar_le_Rbar ht hl) hz₁ hz₂
  have hδ₁ := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hz₁ hl
  have hδ₂ := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hz₂ hl
  set δ₁ := (l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ - z₁ with hδ₁def
  set δ₂ := (l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₂ - z₂ with hδ₂def
  have h00 : tauBil S τ δ₁ δ₂ = 0 := by
    rw [tauBil_apply]
    exact polar_eq_zero_of_mem_clSub H.conj_ne (sub_mem (B.apply_mem_clSub_a hδ₁) hδ₁) hδ₂
  have e₁ : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₁ = z₁ + δ₁ := by rw [hδ₁def]; abel
  have e₂ : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) z₂ = z₂ + δ₂ := by rw [hδ₂def]; abel
  rw [e₁, e₂] at hinv
  simp only [map_add, LinearMap.add_apply, h00, add_zero] at hinv
  have h2 : tauBil S τ δ₁ z₂ + tauBil S τ z₁ δ₂ = 0 := by linear_combination hinv
  rw [zmod2_eq_of_add_eq_zero h2, B.tauBil_symm z₁ δ₂]

theorem tauBil_comm_mul {l l' : S.O} (hl : l ∈ S.Lbar g) (hl' : l' ∈ S.Lbar g) {z : S.Qt}
    (hz : z ∈ Wt S g t) (y : S.Qt) :
    tauBil S τ (((l * l' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) y =
      tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) y +
        tauBil S τ ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) y := by
  have hδ := apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) H.conj_mem hz hl'
  have hv : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) -
      ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) ∈ Vt S g t :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt ht)
      (Lbar_apply_sub_mem_span' H.conj_mem hδ hl)
  have e : ((l * l' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z =
      ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) -
        ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z)) + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) +
          ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) := by
    rw [coe_mul_apply, map_sub]
    abel
  have h0 : tauBil S τ ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z) -
      ((l' : S.Qt ≃ₗ[ZMod 2] S.Qt) z - z)) y = 0 := by
    rw [tauBil_apply, B.fix_Vt _ hv, sub_self, polar_zero_left]
  rw [e]
  simp only [map_add, LinearMap.add_apply, h0, zero_add]

end Bad3

end CFSG.LargeExtraspecial.S8
