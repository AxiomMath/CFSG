module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGEichlerDef
import Mathlib.LinearAlgebra.Center

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {B : LinearMap.BilinForm (ZMod 3) V} {ρ : V →ₗ[ZMod 3] V}

@[expose] def FGEichlerComm (B : LinearMap.BilinForm (ZMod 3) V) (ρ : V →ₗ[ZMod 3] V)
    (c : V →ₗ[ZMod 3] V) : Prop :=
  ∀ u w : V, B u w = 0 → ((ρ u = u ∧ ρ w = -w) ∨ (ρ u = -u ∧ ρ w = w)) →
    ∀ x, c (fgEichler B u w x) = fgEichler B u w (c x)

theorem fg_exists_pair_ne (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y) {w : V}
    (hw : w ∈ fgMinus ρ) (hw0 : w ≠ 0) : ∃ y ∈ fgPlus ρ, B w y ≠ 0 := by
  have hcompl := fg_isCompl_plus_minus (ρ := ρ) hρ2
  have hex : ∃ z, B w z ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (hB.1 w h)
  obtain ⟨z, hz⟩ := hex
  have hzmem : z ∈ fgPlus ρ ⊔ fgMinus ρ := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzmem
  refine ⟨a, ha, ?_⟩
  rw [← hab, map_add, fg_minus_isotropic hρB hw hb, add_zero] at hz
  exact hz

theorem fg_exists_orth_pair (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {u x : V} (hu : u ∈ fgPlus ρ) (hx : x ∈ fgPlus ρ) :
    ∃ w ∈ fgMinus ρ, w ≠ 0 ∧ B u w = 0 ∧ B x w = 0 := by
  have hfm : Module.finrank (ZMod 3) (fgMinus ρ) = 3 :=
    (fg_finrank_plus_minus hB hsymm hρ2 hρB hdim).2
  let f : fgMinus ρ →ₗ[ZMod 3] ZMod 3 × ZMod 3 :=
    ((B u).comp (fgMinus ρ).subtype).prod ((B x).comp (fgMinus ρ).subtype)
  have hfin : Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) <
      Module.finrank (ZMod 3) (fgMinus ρ) := by
    rw [hfm, Module.finrank_prod, Module.finrank_self]
    norm_num
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfin
  obtain ⟨w, hw, hw0⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  have hw1 : B u (w : V) = 0 := by
    have h := congrArg Prod.fst (LinearMap.mem_ker.mp hw)
    simpa [f] using h
  have hw2 : B x (w : V) = 0 := by
    have h := congrArg Prod.snd (LinearMap.mem_ker.mp hw)
    simpa [f] using h
  refine ⟨w, w.2, ?_, hw1, hw2⟩
  intro h
  exact hw0 (Subtype.ext h)

private lemma fg_mem_plus_of_forall (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    {z : V} (hz : ∀ y ∈ fgPlus ρ, B z y = 0) : z ∈ fgPlus ρ := by
  have hcompl := fg_isCompl_plus_minus (ρ := ρ) hρ2
  have hzmem : z ∈ fgPlus ρ ⊔ fgMinus ρ := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzmem
  have hb0 : b = 0 := by
    by_contra hbne
    obtain ⟨y, hy, hBy⟩ := fg_exists_pair_ne hB hsymm hρ2 hρB hb hbne
    have hzy : B b y = 0 := by
      have h0 : B z y = 0 := hz y hy
      rw [← hab, map_add, LinearMap.add_apply, fg_plus_isotropic hρB ha hy, zero_add] at h0
      exact h0
    exact hBy hzy
  rw [hb0, add_zero] at hab
  rw [← hab]
  exact ha

private lemma fg_exists_plus_orth (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {w : V} (hw : w ∈ fgMinus ρ) :
    ∃ u ∈ fgPlus ρ, u ≠ 0 ∧ B u w = 0 := by
  have hfp : Module.finrank (ZMod 3) (fgPlus ρ) = 3 :=
    (fg_finrank_plus_minus hB hsymm hρ2 hρB hdim).1
  let f : fgPlus ρ →ₗ[ZMod 3] ZMod 3 := (B.flip w).comp (fgPlus ρ).subtype
  have hfin : Module.finrank (ZMod 3) (ZMod 3) < Module.finrank (ZMod 3) (fgPlus ρ) := by
    rw [hfp, Module.finrank_self]
    norm_num
  have hker : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfin
  obtain ⟨u, hu, hu0⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
  refine ⟨u, u.2, ?_, ?_⟩
  · intro h
    exact hu0 (Subtype.ext h)
  · have h : f u = 0 := LinearMap.mem_ker.mp hu
    simpa [f] using h

private lemma fg_exists_minus_pair_ne (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    {u : V} (hu : u ∈ fgPlus ρ) (hu0 : u ≠ 0) : ∃ x ∈ fgMinus ρ, B u x ≠ 0 := by
  have hcompl := fg_isCompl_plus_minus (ρ := ρ) hρ2
  have hex : ∃ z, B u z ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hB.1 u h)
  obtain ⟨z, hz⟩ := hex
  have hzmem : z ∈ fgPlus ρ ⊔ fgMinus ρ := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hzmem
  refine ⟨b, hb, ?_⟩
  rw [← hab, map_add, fg_plus_isotropic hρB hu ha, zero_add] at hz
  exact hz

private lemma fg_block_eq (hsymm : ∀ x y, B x y = B y x)
    (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c)
    {u x y w : V} (hu : u ∈ fgPlus ρ) (hx : x ∈ fgPlus ρ) (hy : y ∈ fgPlus ρ)
    (hw : w ∈ fgMinus ρ) (huw : B u w = 0) :
    B w y * B (c x) u + B w x * B (c u) y + B w x * B w y * B (c u) u = 0 := by
  have huu : B u u = 0 := fg_plus_isotropic hρB hu hu
  have hww : B w w = 0 := fg_minus_isotropic hρB hw hw
  have hcomm := hc u w huw (Or.inl ⟨mem_fgPlus.mp hu, mem_fgMinus.mp hw⟩) x
  have hkey : B (c (fgEichler B u w x)) (fgEichler B u w y) = B (c x) y := by
    rw [hcomm, fg_eichler_isom hsymm huu hww huw (c x) y]
  have htx : fgEichler B u w x = x + B w x • u := by
    rw [fgEichler_apply, fg_plus_isotropic hρB hu hx, zero_smul, sub_zero]
  have hty : fgEichler B u w y = y + B w y • u := by
    rw [fgEichler_apply, fg_plus_isotropic hρB hu hy, zero_smul, sub_zero]
  have hL : B (c (fgEichler B u w x)) (fgEichler B u w y)
      = B (c x) y + (B w y * B (c x) u + B w x * B (c u) y
          + B w x * B w y * B (c u) u) := by
    rw [htx, hty, map_add, map_smul]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hEq : B (c x) y + (B w y * B (c x) u + B w x * B (c u) y
      + B w x * B w y * B (c u) u) = B (c x) y := by
    rw [← hL, hkey]
  linear_combination hEq

theorem fg_block (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c) :
    ∀ x ∈ fgPlus ρ, c x ∈ fgPlus ρ := by
  have step1 : ∀ u ∈ fgPlus ρ, B (c u) u = 0 := by
    intro u hu
    obtain ⟨w, hw, hw0, huw, _⟩ := fg_exists_orth_pair hB hsymm hρ2 hρB hdim hu hu
    obtain ⟨x, hx, hwx⟩ := fg_exists_pair_ne hB hsymm hρ2 hρB hw hw0
    have hEq := fg_block_eq hsymm hρB hc hu hx hu hw huw
    have hwu : B w u = 0 := by rw [hsymm w u, huw]
    simp [hwu] at hEq
    exact hEq.resolve_left hwx
  have step2 : ∀ u ∈ fgPlus ρ, ∀ y ∈ fgPlus ρ, B (c u) y = 0 := by
    intro u hu y hy
    obtain ⟨w, hw, hw0, huw, hyw⟩ := fg_exists_orth_pair hB hsymm hρ2 hρB hdim hu hy
    obtain ⟨x, hx, hwx⟩ := fg_exists_pair_ne hB hsymm hρ2 hρB hw hw0
    have hEq := fg_block_eq hsymm hρB hc hu hx hy hw huw
    have hwy : B w y = 0 := by rw [hsymm w y, hyw]
    simp [hwy] at hEq
    exact hEq.resolve_left hwx
  intro x hx
  apply fg_mem_plus_of_forall hB hsymm hρ2 hρB
  intro y hy
  exact step2 x hx y hy

private lemma fg_scalar_minus_eigen (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c)
    (hpres : ∀ x ∈ fgMinus ρ, c x ∈ fgMinus ρ) {w : V} (hw : w ∈ fgMinus ρ) :
    ∃ κ : ZMod 3, c w = κ • w := by
  obtain ⟨u, hu, hu0, huw⟩ := fg_exists_plus_orth hB hsymm hρ2 hρB hdim hw
  obtain ⟨x, hx, hux⟩ := fg_exists_minus_pair_ne hB hsymm hρ2 hρB hu hu0
  have hcomm := hc u w huw (Or.inl ⟨mem_fgPlus.mp hu, mem_fgMinus.mp hw⟩) x
  have hwx : B w x = 0 := fg_minus_isotropic hρB hw hx
  have hwcx : B w (c x) = 0 := fg_minus_isotropic hρB hw (hpres x hx)
  have htx : fgEichler B u w x = x - B u x • w := by
    rw [fgEichler_apply, hwx, zero_smul, add_zero]
  have htcx : fgEichler B u w (c x) = c x - B u (c x) • w := by
    rw [fgEichler_apply, hwcx, zero_smul, add_zero]
  have hEq : c x - B u x • c w = c x - B u (c x) • w := by
    have h := hcomm
    rw [htx, htcx, map_sub, map_smul] at h
    exact h
  have hEq2 : B u x • c w = B u (c x) • w := sub_right_inj.mp hEq
  have hcw : c w = (B u x)⁻¹ • (B u (c x) • w) := by
    rw [← hEq2, smul_smul, inv_mul_cancel₀ hux, one_smul]
  refine ⟨(B u x)⁻¹ * B u (c x), ?_⟩
  rw [hcw, smul_smul]

theorem fg_scalar_minus (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c)
    (hpres : ∀ x ∈ fgMinus ρ, c x ∈ fgMinus ρ) :
    ∃ β : ZMod 3, ∀ x ∈ fgMinus ρ, c x = β • x := by
  let f : fgMinus ρ →ₗ[ZMod 3] fgMinus ρ := c.restrict hpres
  have hf : ∀ v : fgMinus ρ, ∃ κ : ZMod 3, f v = κ • v := by
    intro v
    obtain ⟨κ, hκ⟩ := fg_scalar_minus_eigen hB hsymm hρ2 hρB hdim hc hpres v.2
    exact ⟨κ, Subtype.ext (by simpa [f] using hκ)⟩
  have hli : ∀ v : fgMinus ρ, ¬ LinearIndependent (ZMod 3) ![v, f v] := by
    intro v
    obtain ⟨κ, hκ⟩ := hf v
    intro h
    have hrel : (-κ) • v + (1 : ZMod 3) • f v = 0 := by
      rw [hκ]
      simp
    have h0 := (LinearIndependent.pair_iff.mp h) (-κ) 1 hrel
    exact one_ne_zero h0.2
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (R := ZMod 3) (V := fgMinus ρ) (f := f) hli
  refine ⟨a, ?_⟩
  intro x hx
  have hx' : c x = a • x := by
    have h := congrArg (fun g : fgMinus ρ →ₗ[ZMod 3] fgMinus ρ => (g ⟨x, hx⟩ : V)) ha
    simpa [f] using h
  exact hx'

private lemma fgPlus_neg : fgPlus (-ρ) = fgMinus ρ := by
  unfold fgPlus fgMinus
  have h : -ρ - LinearMap.id = -(ρ + LinearMap.id) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.id_apply]
    abel
  rw [h, LinearMap.ker_neg]

private lemma fgMinus_neg : fgMinus (-ρ) = fgPlus ρ := by
  unfold fgMinus fgPlus
  have h : -ρ + LinearMap.id = -(ρ - LinearMap.id) := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.sub_apply,
      LinearMap.id_apply]
    abel
  rw [h, LinearMap.ker_neg]

private lemma fgEichlerComm_neg {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c) :
    FGEichlerComm B (-ρ) c := by
  intro u w huw h
  rcases h with ⟨hu, hw⟩ | ⟨hu, hw⟩
  · exact hc u w huw (Or.inr ⟨neg_eq_iff_eq_neg.mp hu, neg_inj.mp hw⟩)
  · exact hc u w huw (Or.inl ⟨neg_inj.mp hu, neg_eq_iff_eq_neg.mp hw⟩)

theorem fg_commutant_eichler (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x)
    (hρ2 : ∀ v, ρ (ρ v) = v) (hρB : ∀ x y, B (ρ x) (ρ y) = -B x y)
    (hdim : Module.finrank (ZMod 3) V = 6) {c : V →ₗ[ZMod 3] V} (hc : FGEichlerComm B ρ c) :
    ∃ α β : ZMod 3, ∀ v, c v = α • v + β • ρ v := by
  have hρ2' : ∀ v, (-ρ) ((-ρ) v) = v := by intro v; simpa using hρ2 v
  have hρB' : ∀ x y, B ((-ρ) x) ((-ρ) y) = -B x y := by intro x y; simpa using hρB x y
  have hc' : FGEichlerComm B (-ρ) c := fgEichlerComm_neg hc
  have hblock : ∀ x ∈ fgPlus ρ, c x ∈ fgPlus ρ := fg_block hB hsymm hρ2 hρB hdim hc
  have hblock' : ∀ x ∈ fgPlus (-ρ), c x ∈ fgPlus (-ρ) :=
    fg_block hB hsymm hρ2' hρB' hdim hc'
  have hpresMinus : ∀ x ∈ fgMinus ρ, c x ∈ fgMinus ρ := by
    intro x hx
    rw [← fgPlus_neg] at hx ⊢
    exact hblock' x hx
  have hpresPlus : ∀ x ∈ fgMinus (-ρ), c x ∈ fgMinus (-ρ) := by
    intro x hx
    rw [fgMinus_neg] at hx ⊢
    exact hblock x hx
  obtain ⟨β, hβ⟩ := fg_scalar_minus hB hsymm hρ2 hρB hdim hc hpresMinus
  obtain ⟨α, hα'⟩ := fg_scalar_minus hB hsymm hρ2' hρB' hdim hc' hpresPlus
  have hα : ∀ x ∈ fgPlus ρ, c x = α • x := by
    intro x hx
    exact hα' x (by rw [fgMinus_neg]; exact hx)
  refine ⟨-α - β, β - α, ?_⟩
  intro v
  have hplus : -(v + ρ v) ∈ fgPlus ρ := by
    rw [mem_fgPlus, map_neg, map_add, hρ2 v]
    abel
  have hminus : (-v + ρ v) ∈ fgMinus ρ := by
    rw [mem_fgMinus, map_add, map_neg, hρ2 v]
    abel
  have hv : v = -(v + ρ v) + (-v + ρ v) := by
    have h2 : (-2 : ZMod 3) = 1 := by decide
    rw [show -(v + ρ v) + (-v + ρ v) = (-2 : ZMod 3) • v by module, h2, one_smul]
  calc c v = c (-(v + ρ v) + (-v + ρ v)) := congrArg c hv
    _ = c (-(v + ρ v)) + c (-v + ρ v) := by rw [map_add]
    _ = α • (-(v + ρ v)) + β • (-v + ρ v) := by rw [hα _ hplus, hβ _ hminus]
    _ = (-α - β) • v + (β - α) • ρ v := by module

end CFSG.OddStandard.SmallF3.Omega
