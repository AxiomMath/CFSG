module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
import CFSG.LinearAlgebra.MapRangeFixedVector
import CFSG.LieType.AlgebraicGroups.ZariskiClosureFrobenius
import CFSG.LieType.AlgebraicGroups.AdditiveCoordinateSurjective
import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
import TauCeti.RepresentationTheory.Unipotent.PowerOrder
import Mathlib.LinearAlgebra.Basis.VectorSpace

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]
  (p : ℕ) [Fact p.Prime] [CharP k p]


omit [IsAlgClosed k] in
private lemma exists_fixed_of_ker_finite {W : Subgroup (ModGL τ k)} {e : ℕ}
    (he : 1 ≤ e)
    (fW : W →* W) (hfW : ∀ u : W, ((fW u : W) : ModGL τ k) = entrywiseFrobGL τ k p e u)
    {ψ : W → k} (hψ1 : ψ 1 = 0) (hψmul : ∀ u v : W, ψ (u * v) = ψ u + ψ v)
    (hψF : ∀ u : W, ψ (fW u) = ψ u ^ p ^ e)
    (hψsurj : ∀ t : k, ∃ u : W, ψ u = t)
    (K : Subgroup (ModGL τ k)) (hKle : K ≤ W)
    (hKmem : ∀ u : W, (u : ModGL τ k) ∈ K ↔ ψ u = 0)
    [Finite ↥K] :
    ∃ u : W, u ≠ 1 ∧ entrywiseFrobGL τ k p e (u : ModGL τ k) = (u : ModGL τ k) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite ↥K
  let φ : W → W := fun u => u⁻¹ * fW u
  let S : Set W := {u | (φ u : ModGL τ k) ∈ K}
  have hp0 : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hψneg : ∀ u : W, ψ u⁻¹ = -ψ u := by
    intro u
    have h := hψmul u u⁻¹
    rw [mul_inv_cancel, hψ1] at h
    linear_combination -h
  have hφψ : ∀ u : W, ψ (φ u) = ψ (fW u) - ψ u := by
    intro u
    have h : ψ (φ u) = ψ u⁻¹ + ψ (fW u) := hψmul u⁻¹ (fW u)
    rw [h, hψneg]
    ring
  have hFixFin : ({u : W | fW u = u} : Set W).Finite := by
    have hfin : {g : ModGL τ k | entrywiseFrobGL τ k p e g = g}.Finite :=
      finite_setOf_entrywiseFrobGL_eq (τ := τ) (k := k) (p := p) he
    have : Finite ↥{g : ModGL τ k | entrywiseFrobGL τ k p e g = g} := hfin
    refine Finite.of_injective
      (fun u : ↥{u : W | fW u = u} =>
        (⟨(u.1 : ModGL τ k), ?_⟩ : ↥{g : ModGL τ k | entrywiseFrobGL τ k p e g = g})) ?_
    · have h := congrArg (fun x : W => (x : ModGL τ k)) u.2
      rw [hfW] at h
      exact h
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥{g : ModGL τ k | entrywiseFrobGL τ k p e g = g} =>
        (x : ModGL τ k)) hab
  have : Fintype ↥{u : W | fW u = u} := hFixFin.fintype
  let r : ↥K → W := fun c =>
    if h : ∃ u : ↥S, ((φ u.1 : W) : ModGL τ k) = (c : ModGL τ k) then (h.choose.1 : W) else 1
  have hr : ∀ (c : ↥K) (u : ↥S), ((φ u.1 : W) : ModGL τ k) = (c : ModGL τ k) →
      ((φ (r c) : W) : ModGL τ k) = (c : ModGL τ k) := by
    intro c u hu
    have h : ∃ u : ↥S, ((φ u.1 : W) : ModGL τ k) = (c : ModGL τ k) := ⟨u, hu⟩
    have hrc : r c = (h.choose.1 : W) := by
      simp only [r, dif_pos h]
    rw [hrc]
    exact h.choose_spec
  let κW : ↥K → W := fun c => ⟨(c : ModGL τ k), hKle c.2⟩
  have hκWcoe : ∀ c : ↥K, ((κW c : W) : ModGL τ k) = (c : ModGL τ k) := fun c => rfl
  have hκWinj : Function.Injective κW := by
    intro c c' h
    apply Subtype.ext
    have h' := congrArg (fun x : W => (x : ModGL τ k)) h
    simpa only [hκWcoe] using h'
  have hψκ : ∀ c : ↥K, ψ (κW c) = 0 := by
    intro c
    apply (hKmem (κW c)).mp
    rw [hκWcoe]
    exact c.2
  have hκS : ∀ c : ↥K, κW c ∈ S := by
    intro c
    show (φ (κW c) : ModGL τ k) ∈ K
    rw [hKmem, hφψ, hψF, hψκ, zero_pow hp0, sub_self]
  obtain ⟨s₁, hs₁⟩ := hψsurj 1
  have hs₁S : s₁ ∈ S := by
    show (φ s₁ : ModGL τ k) ∈ K
    rw [hKmem, hφψ, hψF, hs₁, one_pow, sub_self]
  have hκsS : ∀ c : ↥K, κW c * s₁ ∈ S := by
    intro c
    show (φ (κW c * s₁) : ModGL τ k) ∈ K
    rw [hKmem]
    have hφκ : ψ (φ (κW c)) = 0 := (hKmem (φ (κW c))).mp (hκS c)
    have h1 : φ (κW c * s₁) = s₁⁻¹ * φ (κW c) * fW s₁ := by
      have e1 : φ (κW c * s₁) = (κW c * s₁)⁻¹ * fW (κW c * s₁) := rfl
      have e2 : φ (κW c) = (κW c)⁻¹ * fW (κW c) := rfl
      rw [e1, e2, map_mul, mul_inv_rev]
      group
    rw [h1, hψmul, hψmul, hψneg, hφκ, hψF, hs₁, one_pow]
    ring
  let toK : ↥S → ↥K := fun u => ⟨(φ u.1 : ModGL τ k), u.2⟩
  have htoK : ∀ u : ↥S, ((toK u : ↥K) : ModGL τ k) = (φ u.1 : ModGL τ k) := fun u => rfl
  let toFix : ↥S → ↥{u : W | fW u = u} := fun u =>
    ⟨r (toK u) * u.1⁻¹, by
      show fW (r (toK u) * u.1⁻¹) = r (toK u) * u.1⁻¹
      have hrW : φ (r (toK u)) = φ u.1 := by
        apply Subtype.ext
        rw [htoK u]
        exact hr (toK u) u rfl
      have h2 : (r (toK u))⁻¹ * fW (r (toK u)) = u.1⁻¹ * fW u.1 := by
        simpa only [φ] using hrW
      have h1 : fW (r (toK u)) = r (toK u) * (u.1⁻¹ * fW u.1) := by
        calc fW (r (toK u)) = r (toK u) * ((r (toK u))⁻¹ * fW (r (toK u))) := by group
          _ = r (toK u) * (u.1⁻¹ * fW u.1) := by rw [h2]
      rw [map_mul, map_inv, h1]
      group⟩
  have htoFix : ∀ u : ↥S, ((toFix u : ↥{u : W | fW u = u}) : W) = r (toK u) * u.1⁻¹ :=
    fun u => rfl
  have inj1 : Function.Injective (fun u : ↥S => (toK u, toFix u)) := by
    intro u u' h
    have h1 : toK u = toK u' := congrArg Prod.fst h
    have h2' : toFix u = toFix u' := congrArg Prod.snd h
    have h2 : ((toFix u : ↥{u : W | fW u = u}) : W) = ((toFix u' : ↥{u : W | fW u = u}) : W) :=
      congrArg Subtype.val h2'
    rw [htoFix, htoFix] at h2
    have h3 : r (toK u) = r (toK u') := congrArg r h1
    rw [h3] at h2
    have h4 : u.1⁻¹ = u'.1⁻¹ := mul_left_cancel h2
    exact Subtype.ext (inv_injective h4)
  have inj2 : Function.Injective (fun x : ↥K × Bool =>
      if x.2 then (⟨κW x.1 * s₁, hκsS x.1⟩ : ↥S) else (⟨κW x.1, hκS x.1⟩ : ↥S)) := by
    rintro ⟨c, b⟩ ⟨c', b'⟩ h
    cases b <;> cases b' <;> simp only [Bool.false_eq_true, if_true, if_false] at h
    · have h1 : κW c = κW c' := Subtype.ext_iff.mp h
      rw [hκWinj h1]
    · exfalso
      have h1 : κW c = κW c' * s₁ := Subtype.ext_iff.mp h
      have hψ : ψ (κW c) = ψ (κW c' * s₁) := by rw [h1]
      have h2 : ψ (κW c') = 0 := hψκ c'
      have h3 : ψ (κW c' * s₁) = 1 := by rw [hψmul, h2, hs₁, zero_add]
      rw [hψκ c, h3] at hψ
      exact zero_ne_one hψ
    · exfalso
      have h1 : κW c * s₁ = κW c' := Subtype.ext_iff.mp h
      have hψ : ψ (κW c * s₁) = ψ (κW c') := by rw [h1]
      have h3 : ψ (κW c * s₁) = 1 := by rw [hψmul, hψκ c, hs₁, zero_add]
      rw [h3, hψκ c'] at hψ
      exact one_ne_zero hψ
    · have h1 : κW c * s₁ = κW c' * s₁ := Subtype.ext_iff.mp h
      have h2 : κW c = κW c' := mul_right_cancel h1
      rw [hκWinj h2]
  have : Fintype ↥S := Fintype.ofInjective _ inj1
  have hle1 : Fintype.card ↥S ≤ Fintype.card (↥K × ↥{u : W | fW u = u}) :=
    Fintype.card_le_of_injective _ inj1
  have hle2 : Fintype.card (↥K × Bool) ≤ Fintype.card ↥S :=
    Fintype.card_le_of_injective _ inj2
  have hmain : Fintype.card (↥K × Bool) ≤ Fintype.card (↥K × ↥{u : W | fW u = u}) :=
    le_trans hle2 hle1
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool] at hmain
  have hKpos : 0 < Fintype.card ↥K := Fintype.card_pos_iff.mpr ⟨⟨1, K.one_mem⟩⟩
  have hFix2 : 2 ≤ Fintype.card ↥{u : W | fW u = u} :=
    Nat.le_of_mul_le_mul_left hmain hKpos
  obtain ⟨u, hu⟩ := Fintype.exists_ne_of_one_lt_card
    (by omega : 1 < Fintype.card ↥{u : W | fW u = u})
    (⟨1, map_one fW⟩ : ↥{u : W | fW u = u})
  refine ⟨u.1, ?_, ?_⟩
  · intro h
    exact hu (Subtype.ext h)
  · have h := congrArg (fun x : W => (x : ModGL τ k)) u.2
    rwa [hfW] at h

private lemma exists_fixed_of_dense {W : Subgroup (ModGL τ k)} {N e : ℕ}
    (he : 1 ≤ e)
    (hWcl : IsPointClosed k (transportPoints (modGLPoint τ k) (W : Set (ModGL τ k))))
    (hWirr : IsPointIrreducible k (transportPoints (modGLPoint τ k) (W : Set (ModGL τ k))))
    (hWstab : ∀ g ∈ W, entrywiseFrobGL τ k p e g ∈ W)
    (hWexp : ∀ u ∈ W, u ^ p ^ N = 1) (hWne : W ≠ ⊥)
    (hdense : ∀ C : Set (ModGL τ k),
      IsPointClosed k (transportPoints (modGLPoint τ k) C) →
      (entrywiseFrobGL τ k p e '' (W : Set (ModGL τ k))) ⊆ C →
      (W : Set (ModGL τ k)) ⊆ C)
    (ih' : ∀ Z : Subgroup (ModGL τ k),
      IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))) →
      (Z : Set (ModGL τ k)) ⊂ (W : Set (ModGL τ k)) →
      IsPointIrreducible k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))) →
      (∀ g ∈ Z, entrywiseFrobGL τ k p e g ∈ Z) →
      (∀ u ∈ Z, u ^ p ^ N = 1) → Z ≠ ⊥ →
      ∃ u ∈ Z, u ≠ 1 ∧ entrywiseFrobGL τ k p e u = u) :
    ∃ u ∈ W, u ≠ 1 ∧ entrywiseFrobGL τ k p e u = u := by
  classical
  let F : ModGL τ k →* ModGL τ k := entrywiseFrobGL τ k p e
  let σ : k →+* k := iterateFrobenius k p e
  let V := RootModule τ k
  let σv : V → V := fun x => Finsupp.mapRange σ σ.map_zero x
  have hp0 : p ^ e ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hFσcoe (u : ModGL τ k) :
      ((entrywiseFrobGL τ k p e u : ModGL τ k) : Module.End k V)
        = entrywise (iterateFrobenius k p e) (u : Module.End k V) := rfl
  have hFσ : ∀ (u : ModGL τ k), u ∈ W → ∀ x : V,
      ((F u : ModGL τ k) : Module.End k V) (σv x)
        = σv ((u : Module.End k V) x) := by
    intro u _hu x
    rw [show ((F u : ModGL τ k) : Module.End k V) = entrywise σ (u : Module.End k V) from
      hFσcoe u]
    exact entrywise_apply_mapRange σ (u : Module.End k V) x
  let VU : Submodule k V := ⨅ u : W, LinearMap.ker (((u : ModGL τ k) : Module.End k V) - 1)
  have memVU : ∀ {x : V}, x ∈ VU ↔ ∀ u : W, ((u : ModGL τ k) : Module.End k V) x = x := by
    intro x
    simp only [VU, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hVUproper : VU ≠ ⊤ := by
    intro htop
    apply hWne
    refine le_bot_iff.mp ?_
    intro g hg
    have hunit : (⟨g, hg⟩ : W) = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro x
      have hx : x ∈ VU := by rw [htop]; exact Submodule.mem_top
      simpa using memVU.mp hx (⟨g, hg⟩ : W)
    simpa using congrArg Subtype.val hunit
  have hσsub : ∀ a b : V, σv (a - b) = σv a - σv b := by
    intro a b
    ext c
    show σ ((a - b) c) = σ (a c) - σ (b c)
    rw [Finsupp.sub_apply, map_sub]
  have hVUstable : ∀ x ∈ VU, σv x ∈ VU := by
    intro x hx
    have hset : {g : ModGL τ k | ((g : Module.End k V)) (σv x) = σv x} =
        ⋂ a : Label τ, {g : ModGL τ k | (((g : Module.End k V)) (σv x)) a = (σv x) a} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finsupp.ext_iff]
    have hclosed : IsPointClosed k (transportPoints (modGLPoint τ k)
        {g : ModGL τ k | ((g : Module.End k V)) (σv x) = σv x}) := by
      rw [hset]
      exact isPointClosed_iInter fun a =>
        isPointClosed_setOf_apply_apply_eq (σv x) a ((σv x) a)
    have hFW : F '' (W : Set (ModGL τ k)) ⊆
        {g : ModGL τ k | ((g : Module.End k V)) (σv x) = σv x} := by
      rintro _ ⟨u, hu, rfl⟩
      have hux : (u : Module.End k V) x = x := (memVU (x := x)).mp hx ⟨u, hu⟩
      show ((F u : ModGL τ k) : Module.End k V) (σv x) = σv x
      rw [hFσ u hu x, hux]
    exact memVU.mpr fun u => hdense _ hclosed hFW u.2
  have : Nontrivial (V ⧸ VU) := Submodule.Quotient.nontrivial_iff.mpr hVUproper
  have hVUcomap : ∀ u : W, VU ≤ VU.comap (((u : ModGL τ k) : Module.End k V)) := by
    intro u x hx
    rw [Submodule.mem_comap]
    rw [show (((u : ModGL τ k) : Module.End k V)) x = x from (memVU (x := x)).mp hx u]
    exact hx
  let ρ : Representation k W (V ⧸ VU) :=
    { toFun := fun u => Submodule.mapQ (p := VU) (q := VU) (((u : ModGL τ k) : Module.End k V))
        (hVUcomap u)
      map_one' := Submodule.mapQ_id (p := VU)
      map_mul' := by
        intro u v
        have h := Submodule.mapQ_comp (p := VU) (p₂ := VU) (p₃ := VU)
          (f := (((v : W) : ModGL τ k) : Module.End k V))
          (g := (((u : W) : ModGL τ k) : Module.End k V)) (hVUcomap v) (hVUcomap u)
        exact h }
  have hρ : ∀ u : W, ∃ n : ℕ, ρ u ^ p ^ n = 1 := by
    intro u
    refine ⟨N, ?_⟩
    have hu : u ^ p ^ N = 1 := by
      apply Subtype.ext
      show (u : ModGL τ k) ^ p ^ N = 1
      exact hWexp u u.2
    have h1 : ρ (u ^ p ^ N) = 1 := by rw [hu, map_one]
    rwa [map_pow] at h1
  obtain ⟨q, hqne, hqfix⟩ :=
    Representation.exists_common_fixed_vector_of_forall_pow_expChar_pow_eq_one (p := p) ρ hρ
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective VU q
  let W₂ : Submodule k V :=
    ⨅ u : W, Submodule.comap ((((u : ModGL τ k) : Module.End k V)) - 1) VU
  have memW₂ : ∀ {x : V}, x ∈ W₂ ↔
      ∀ u : W, ((u : ModGL τ k) : Module.End k V) x - x ∈ VU := by
    intro x
    simp only [W₂, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.sub_apply,
      Module.End.one_apply]
  have hmkQ : ∀ {x : V}, (Submodule.mkQ VU) x = 0 ↔ x ∈ VU := by
    intro x
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hwW₂ : w ∈ W₂ := by
    refine memW₂.mpr fun u => ?_
    have h1 : (Submodule.mkQ VU) ((((u : ModGL τ k) : Module.End k V)) w) =
        (Submodule.mkQ VU) w := by
      have h2 : ρ u q = q := hqfix u
      rw [← hw] at h2
      rw [show (ρ u) (Submodule.mkQ VU w) =
        Submodule.mkQ VU (((u : ModGL τ k) : Module.End k V) w) from rfl] at h2
      exact h2
    have h3 : (Submodule.mkQ VU) ((((u : ModGL τ k) : Module.End k V)) w - w) = 0 := by
      rw [map_sub, h1, sub_self]
    exact hmkQ.mp h3
  have hwNotVU : w ∉ VU := by
    intro hwmem
    apply hqne
    rw [← hw]
    exact hmkQ.mpr hwmem
  have hW₂notle : ¬ W₂ ≤ VU := fun hle => hwNotVU (hle hwW₂)
  obtain ⟨Vc, hVc⟩ := Submodule.exists_isCompl (p := VU)
  let P : V →ₗ[k] V := VU.projection Vc hVc
  have hPmem : ∀ y : V, P y ∈ VU := fun y => Submodule.projection_apply_mem hVc y
  have hPid : ∀ y : V, y ∈ VU → P y = y := fun y hy =>
    Submodule.projection_apply_of_mem_left hVc hy
  have hPiff : ∀ y : V, y ∈ VU ↔ P y = y := fun y =>
    ⟨hPid y, fun h => h ▸ hPmem y⟩
  let Pa : Label τ → V →ₗ[k] k := fun a => (Finsupp.lapply a) ∘ₗ (P - LinearMap.id)
  have hPa : ∀ (a : Label τ) (y : V), Pa a y = (P y - y) a := fun a y => rfl
  have hVUiff : ∀ y : V, y ∈ VU ↔ ∀ a : Label τ, Pa a y = 0 := by
    intro y
    rw [hPiff]
    constructor
    · intro h a
      rw [hPa, h, sub_self]
      rfl
    · intro h
      refine sub_eq_zero.mp ?_
      ext a
      simpa [hPa] using h a
  have hW₂closed : ∀ x : V, IsPointClosed k (transportPoints (modGLPoint τ k)
      {g : ModGL τ k | (((g : Module.End k V)) - 1) (σv x) ∈ VU}) := by
    intro x
    have hset : {g : ModGL τ k | (((g : Module.End k V)) - 1) (σv x) ∈ VU} =
        ⋂ a : Label τ, {g : ModGL τ k |
          Pa a (((g : Module.End k V)) (σv x)) = Pa a (σv x)} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [hVUiff]
      refine forall_congr' fun a => ?_
      rw [show (((g : Module.End k V)) - 1) (σv x) = ((g : Module.End k V)) (σv x) - σv x from by
        rw [LinearMap.sub_apply, Module.End.one_apply], map_sub, sub_eq_zero]
    rw [hset]
    exact isPointClosed_iInter fun a =>
      isPointClosed_setOf_linearMap_apply_eq (Pa a) (σv x) (Pa a (σv x))
  have hW₂stable : ∀ x ∈ W₂, σv x ∈ W₂ := by
    intro x hx
    refine memW₂.mpr fun u => ?_
    have hFW : F '' (W : Set (ModGL τ k)) ⊆
        {g : ModGL τ k | (((g : Module.End k V)) - 1) (σv x) ∈ VU} := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : ((F (u : ModGL τ k) : ModGL τ k) : Module.End k V) (σv x) - σv x
          = σv ((((u : ModGL τ k) : Module.End k V)) x - x) := by
        rw [hFσ u hu x, ← hσsub]
      show ((F (u : ModGL τ k) : ModGL τ k) : Module.End k V) (σv x) - σv x ∈ VU
      rw [h1]
      exact hVUstable _ (memW₂.mp hx ⟨u, hu⟩)
    exact hdense _ (hW₂closed x) hFW u.2
  obtain ⟨v, hvW₂, hvnotVU, hvfix⟩ :=
    CFSG.LinearAlgebra.exists_mapRange_fixed_mem_not_mem (σ := Label τ) (φ := σ)
      (W := W₂) (W' := VU) hW₂stable hW₂notle
  have hvne : ∃ u : W, (((u : ModGL τ k) : Module.End k V)) v ≠ v := by
    by_contra h
    apply hvnotVU
    refine memVU.mpr fun u => ?_
    by_contra hcon
    exact h ⟨u, hcon⟩
  obtain ⟨u₀, hu₀⟩ := hvne
  have hcoord : ∃ a : Label τ, ((((u₀ : ModGL τ k) : Module.End k V)) v) a ≠ v a := by
    by_contra h
    push Not at h
    exact hu₀ (Finsupp.ext h)
  obtain ⟨a, ha⟩ := hcoord
  let ψ : W → k := fun u => ((((u : ModGL τ k) : Module.End k V)) v) a - v a
  let Ψ : ModGL τ k → k := fun g => ((((g : ModGL τ k) : Module.End k V)) v) a - v a
  have hψmul : ∀ u u' : W, ψ (u * u') = ψ u + ψ u' := by
    intro u u'
    have h1 : (((u * u' : W) : ModGL τ k) : Module.End k V) v - v =
        ((((u : W) : ModGL τ k) : Module.End k V))
            (((((u' : W) : ModGL τ k) : Module.End k V)) v - v)
          + (((((u : W) : ModGL τ k) : Module.End k V)) v - v) := by
      show ((((u : W) : ModGL τ k) : Module.End k V))
            (((((u' : W) : ModGL τ k) : Module.End k V)) v) - v = _
      rw [map_sub]
      abel
    have h2 : ((((u : W) : ModGL τ k) : Module.End k V))
        (((((u' : W) : ModGL τ k) : Module.End k V)) v - v)
        = (((((u' : W) : ModGL τ k) : Module.End k V)) v - v) :=
      (memVU.mp (memW₂.mp hvW₂ u')) u
    show ((((u * u' : W) : ModGL τ k) : Module.End k V)) v a - v a = _
    have hgoal : ((((u * u' : W) : ModGL τ k) : Module.End k V)) v a - v a =
        ((((((u * u' : W) : ModGL τ k) : Module.End k V)) v - v)) a := by simp
    rw [hgoal, h1, h2]
    simp only [Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have hψ1 : ψ 1 = 0 := by
    show ((((1 : W) : ModGL τ k) : Module.End k V)) v a - v a = 0
    simp
  let fW : W →* W := (F.comp W.subtype).codRestrict W fun x => hWstab x.1 x.2
  have hfW : ∀ u : W, ((fW u : W) : ModGL τ k) = entrywiseFrobGL τ k p e u := fun u => rfl
  have hψF : ∀ u : W, ψ (fW u) = ψ u ^ p ^ e := by
    intro u
    have h1 : ((((fW u : W) : ModGL τ k) : Module.End k V)) v =
        σv (((((u : W) : ModGL τ k) : Module.End k V)) v) := by
      have h := hFσ (u : ModGL τ k) u.2 v
      rw [show σv v = v from hvfix] at h
      exact h
    have h2 : σv ((((((u : W) : ModGL τ k) : Module.End k V)) v)) a
        = ((((((u : W) : ModGL τ k) : Module.End k V)) v a)) ^ p ^ e := rfl
    have h3 : v a ^ p ^ e = v a := congrArg (fun z : V => z a) hvfix
    have hfresh : (((((((u : W) : ModGL τ k) : Module.End k V)) v a - v a)) + v a) ^ p ^ e
        = (((((((u : W) : ModGL τ k) : Module.End k V)) v a - v a))) ^ p ^ e + v a ^ p ^ e :=
      add_pow_expChar_pow _ _ p e
    rw [sub_add_cancel, h3] at hfresh
    show ((((fW u : W) : ModGL τ k) : Module.End k V)) v a - v a = _
    rw [h1, h2, hfresh]
    ring
  have hΨmul : ∀ g ∈ W, ∀ h ∈ W, Ψ (g * h) = Ψ g + Ψ h := by
    intro g hg h' hh
    have hh' := hψmul ⟨g, hg⟩ ⟨h', hh⟩
    have e : (⟨g, hg⟩ * ⟨h', hh⟩ : W) = ⟨g * h', W.mul_mem hg hh⟩ := rfl
    rw [e] at hh'
    exact hh'
  have hΨone : Ψ 1 = 0 := hψ1
  have hΨinv : ∀ g ∈ W, Ψ g⁻¹ = -Ψ g := by
    intro g hg
    have h := hΨmul g hg g⁻¹ (W.inv_mem hg)
    rw [mul_inv_cancel, hΨone] at h
    linear_combination -h
  let K : Subgroup (ModGL τ k) :=
    { carrier := {g | g ∈ W ∧ Ψ g = 0}
      mul_mem' := by
        rintro g h ⟨hgW, hg0⟩ ⟨hhW, hh0⟩
        exact ⟨W.mul_mem hgW hhW, by rw [hΨmul g hgW h hhW, hg0, hh0, add_zero]⟩
      one_mem' := ⟨W.one_mem, hΨone⟩
      inv_mem' := by
        rintro g ⟨hgW, hg0⟩
        exact ⟨W.inv_mem hgW, by rw [hΨinv g hgW, hg0, neg_zero]⟩ }
  have hKle : K ≤ W := fun g hg => hg.1
  have hKmem : ∀ u : W, (u : ModGL τ k) ∈ K ↔ ψ u = 0 := by
    intro u
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨u.2, h⟩
  have hKstab : ∀ g ∈ K, F g ∈ K := by
    rintro g ⟨hgW, hg0⟩
    refine ⟨hWstab g hgW, ?_⟩
    have h := hψF ⟨g, hgW⟩
    show Ψ (F g) = 0
    rw [show Ψ (F g) = ψ (fW ⟨g, hgW⟩) from rfl, h,
      show ψ ⟨g, hgW⟩ = 0 from hg0, zero_pow hp0]
  have hKcl : IsPointClosed k (transportPoints (modGLPoint τ k) (K : Set (ModGL τ k))) := by
    have hset : (K : Set (ModGL τ k)) = (W : Set (ModGL τ k)) ∩
        {g : ModGL τ k | ((((g : ModGL τ k) : Module.End k V)) v) a = v a} := by
      ext g
      constructor
      · rintro ⟨hgW, hg0⟩
        exact ⟨hgW, sub_eq_zero.mp hg0⟩
      · rintro ⟨hgW, hge⟩
        exact ⟨hgW, sub_eq_zero.mpr hge⟩
    rw [hset]
    exact isPointClosed_inter hWcl (isPointClosed_setOf_apply_apply_eq v a (v a))
  have hKproper : ∃ u ∈ W, u ∉ K := by
    refine ⟨u₀.1, u₀.2, fun hcon => ?_⟩
    exact ha (sub_eq_zero.mp hcon.2)
  have hψsurj : ∀ t : k, ∃ u : W, ψ u = t := by
    have hadd : ∀ u ∈ W, ∀ u' ∈ W,
        (((u * u' : ModGL τ k) : Module.End k V)) v a - v a =
          (((u : ModGL τ k) : Module.End k V)) v a - v a +
            ((((u' : ModGL τ k) : Module.End k V)) v a - v a) := by
      intro u hu u' hu'
      have h := hψmul ⟨u, hu⟩ ⟨u', hu'⟩
      have e : (⟨u, hu⟩ * ⟨u', hu'⟩ : W) = ⟨u * u', W.mul_mem hu hu'⟩ := rfl
      rw [e] at h
      exact h
    intro t
    obtain ⟨u, huW, hu⟩ :=
      surjective_coordinate_of_additive hWcl hWirr v a hadd ⟨u₀.1, u₀.2, ha⟩ t
    exact ⟨⟨u, huW⟩, hu⟩
  by_cases hKfin : Finite ↥K
  · have : Finite ↥K := hKfin
    obtain ⟨u, hune, hfix⟩ :=
      exists_fixed_of_ker_finite (p := p) (e := e) he fW hfW
        hψ1 hψmul hψF hψsurj K hKle hKmem
    exact ⟨u.1, u.2, fun h => hune (Subtype.ext h), hfix⟩
  · have hKzne : closedIdentityComponent K ≠ ⊥ := by
      intro hbot
      apply hKfin
      have : ((closedIdentityComponent K).subgroupOf K).FiniteIndex := inferInstance
      have hfin : Finite ↥((closedIdentityComponent K).subgroupOf K) := by
        rw [hbot, Subgroup.bot_subgroupOf]
        refine Finite.of_injective (fun _ : ↥(⊥ : Subgroup ↥K) => (0 : Fin 1))
          (fun a b _ => ?_)
        apply Subtype.ext
        rw [Subgroup.mem_bot.mp a.2, Subgroup.mem_bot.mp b.2]
      exact (Subgroup.finite_iff_finite_and_finiteIndex
        (H := (closedIdentityComponent K).subgroupOf K)).mpr ⟨hfin, inferInstance⟩
    have hKzcl : IsPointClosed k
        (transportPoints (modGLPoint τ k) ((closedIdentityComponent K) : Set (ModGL τ k))) :=
      isPointClosed_closedIdentityComponent hKcl
    have hKzirr : IsPointIrreducible k
        (transportPoints (modGLPoint τ k) ((closedIdentityComponent K) : Set (ModGL τ k))) :=
      isPointIrreducible_closedIdentityComponent K
    have hKzstab : ∀ g ∈ closedIdentityComponent K, F g ∈ closedIdentityComponent K := by
      intro g hg
      have hS : ∀ g ∈ K, frobTwistGL τ k p e (1 : ModGL τ k) g ∈ K := by
        intro g hg
        simpa only [frobTwistGL_apply, one_mul, inv_one, mul_one] using hKstab g hg
      have h := frobTwistGL_mem_closedIdentityComponent (p := p) e (1 : ModGL τ k) hS hg
      simpa only [frobTwistGL_apply, one_mul, inv_one, mul_one] using h
    have hKzexp : ∀ u ∈ closedIdentityComponent K, u ^ p ^ N = 1 := fun u hu =>
      hWexp u (hKle (closedIdentityComponent_le K hu))
    have hKzlt : ((closedIdentityComponent K) : Set (ModGL τ k)) ⊂ (W : Set (ModGL τ k)) := by
      refine ⟨fun g hg => hKle (closedIdentityComponent_le K hg), ?_⟩
      obtain ⟨u, huW, huK⟩ := hKproper
      intro hsub
      exact huK (closedIdentityComponent_le K (hsub huW))
    obtain ⟨u, hu, hune, hfix⟩ :=
      ih' (closedIdentityComponent K) hKzcl hKzlt hKzirr hKzstab hKzexp hKzne
    exact ⟨u, hKle (closedIdentityComponent_le K hu), hune, hfix⟩

theorem exists_ne_one_entrywiseFrobGL_eq_self_of_unipotent {U : Subgroup (ModGL τ k)}
    (hUc : IsPointClosed k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k))))
    (hUi : IsPointIrreducible k (transportPoints (modGLPoint τ k) (U : Set (ModGL τ k))))
    {e : ℕ} (he : 1 ≤ e) (hS : ∀ g ∈ U, entrywiseFrobGL τ k p e g ∈ U)
    {N : ℕ} (hUp : ∀ u ∈ U, u ^ p ^ N = 1) (hU1 : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ entrywiseFrobGL τ k p e u = u := by
  classical
  have key : ∀ S : {S : Set (ModGL τ k) // IsPointClosed k (transportPoints (modGLPoint τ k) S)},
      ∀ (W : Subgroup (ModGL τ k)), (W : Set (ModGL τ k)) = S.1 →
      IsPointIrreducible k (transportPoints (modGLPoint τ k) (W : Set (ModGL τ k))) →
      (∀ g ∈ W, entrywiseFrobGL τ k p e g ∈ W) →
      (∀ u ∈ W, u ^ p ^ N = 1) → W ≠ ⊥ →
      ∃ u ∈ W, u ≠ 1 ∧ entrywiseFrobGL τ k p e u = u := by
    intro S
    induction S using (wellFounded_ssubset_isPointClosed (τ := τ) (k := k)).induction with
    | h S ih =>
      intro W hWS hWirr hWstab hWexp hWne
      let F : ModGL τ k →* ModGL τ k := entrywiseFrobGL τ k p e
      have hWc : IsPointClosed k (transportPoints (modGLPoint τ k) (W : Set (ModGL τ k))) := by
        rw [hWS]
        exact S.2
      have ih' : ∀ Z : Subgroup (ModGL τ k),
          IsPointClosed k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))) →
          (Z : Set (ModGL τ k)) ⊂ (W : Set (ModGL τ k)) →
          IsPointIrreducible k (transportPoints (modGLPoint τ k) (Z : Set (ModGL τ k))) →
          (∀ g ∈ Z, entrywiseFrobGL τ k p e g ∈ Z) →
          (∀ u ∈ Z, u ^ p ^ N = 1) → Z ≠ ⊥ →
          ∃ u ∈ Z, u ≠ 1 ∧ entrywiseFrobGL τ k p e u = u := by
        intro Z hZc hZlt hZi hZs hZe hZn
        exact ih ⟨Z, hZc⟩ (by rw [← hWS]; exact hZlt) Z rfl hZi hZs hZe hZn
      obtain ⟨W₀, hW'le, hW₀cl, hW₀min, hW₀irr⟩ :=
        exists_isPointClosed_subgroup_closure (W.map F)
      have hW'coe : (W.map F : Set (ModGL τ k)) = F '' (W : Set (ModGL τ k)) :=
        Subgroup.coe_map F W
      have hW₀le : W₀ ≤ W := by
        refine hW₀min W hWc ?_
        rw [hW'coe]
        rintro _ ⟨u, hu, rfl⟩
        exact hWstab u hu
      have hW'ne : W.map F ≠ ⊥ := fun hbot =>
        hWne ((Subgroup.map_eq_bot_iff_of_injective W
          (entrywiseFrobGL_injective (τ := τ) (k := k) (p := p) e)).mp hbot)
      have hW₀ne : W₀ ≠ ⊥ := fun hbot => hW'ne (le_bot_iff.mp (hbot ▸ hW'le))
      have hW₀irr' : IsPointIrreducible k
          (transportPoints (modGLPoint τ k) (W₀ : Set (ModGL τ k))) :=
        hW₀irr (by
          rw [hW'coe]
          exact isPointIrreducible_image_entrywiseFrobGL (p := p) e hWirr)
      have hW₀stab : ∀ g ∈ W₀, F g ∈ W₀ := by
        intro g hg
        have hpre : IsPointClosed k
            (transportPoints (modGLPoint τ k) (F ⁻¹' (W₀ : Set (ModGL τ k)))) :=
          isPointClosed_preimage_entrywiseFrobGL (p := p) e hW₀cl
        have hsub : (W.map F : Set (ModGL τ k)) ⊆ F ⁻¹' (W₀ : Set (ModGL τ k)) := by
          rw [hW'coe]
          rintro _ ⟨u, hu, rfl⟩
          exact hW'le ⟨F u, hWstab u hu, rfl⟩
        exact hW₀min _ hpre hsub hg
      have hW₀exp : ∀ u ∈ W₀, u ^ p ^ N = 1 := fun u hu => hWexp u (hW₀le hu)
      by_cases hproper : (W₀ : Set (ModGL τ k)) ⊂ (W : Set (ModGL τ k))
      · obtain ⟨u, hu, hune, hfix⟩ :=
          ih' W₀ hW₀cl hproper hW₀irr' hW₀stab hW₀exp hW₀ne
        exact ⟨u, hW₀le hu, hune, hfix⟩
      · have hW₀eq : (W₀ : Set (ModGL τ k)) = (W : Set (ModGL τ k)) := by
          refine Set.Subset.antisymm hW₀le ?_
          by_contra hcon
          exact hproper ⟨hW₀le, hcon⟩
        have hdense : ∀ C : Set (ModGL τ k),
            IsPointClosed k (transportPoints (modGLPoint τ k) C) →
            (entrywiseFrobGL τ k p e '' (W : Set (ModGL τ k))) ⊆ C →
            (W : Set (ModGL τ k)) ⊆ C := by
          intro C hC hsub
          have hsub' : (W.map F : Set (ModGL τ k)) ⊆ C := by
            rw [hW'coe]
            exact hsub
          exact hW₀eq ▸ hW₀min C hC hsub'
        exact exists_fixed_of_dense (p := p) (N := N) (e := e) he hWc hWirr hWstab hWexp
          hWne hdense ih'
  exact key ⟨U, hUc⟩ U rfl hUi hS hUp hU1

end CFSG.LieType.AlgebraicGroups
