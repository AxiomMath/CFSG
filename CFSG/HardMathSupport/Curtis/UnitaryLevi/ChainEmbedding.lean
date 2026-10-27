module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainFaithful
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem finrank_orthogonalBilin_eq [FiniteDimensional K V] (hσ : Function.Surjective σ)
    {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.SeparatingLeft) (P : Submodule K V) :
    finrank K (P.orthogonalBilin B) = finrank K V - finrank K P := by
  let b := Module.finBasis K P
  let Φ : V →ₗ[K] (Fin (finrank K P) → K) := LinearMap.pi fun i => B (b i : V)
  have hker : LinearMap.ker Φ = P.orthogonalBilin B := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_orthogonalBilin]
    constructor
    · intro h w hw
      have hw' : w = ∑ i, b.repr ⟨w, hw⟩ i • (b i : V) := by
        have := congrArg Subtype.val (b.sum_repr ⟨w, hw⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      rw [hw', map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi : B (b i : V) v = 0 := congrFun h i
      rw [map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
    · intro h
      ext i
      exact h _ (b i).2
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.dualMap_injective_iff, ← LinearMap.ker_eq_bot]
    refine LinearMap.ker_eq_bot'.2 fun f hf => ?_
    have hf' : ∀ v, f (Φ v) = 0 := fun v => LinearMap.congr_fun hf v
    choose d hd using fun i => hσ (f (Pi.single i 1))
    have hw : B (∑ i, d i • (b i : V)) = 0 := by
      ext v
      rw [map_sum, LinearMap.sum_apply, LinearMap.zero_apply]
      have := hf' v
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at this
      simp only [map_smulₛₗ, LinearMap.smul_apply, hd]
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (fun j => if i = j then (1 : K) else 0) = Pi.single i 1 := by
        ext j; simp [Pi.single_apply, eq_comm]
      simp [Φ, this, smul_eq_mul, mul_comm]
    have h0 : ∑ i, d i • (b i : V) = 0 := hB _ fun y => by rw [hw]; rfl
    have h0' : ∑ i, d i • b i = 0 := by
      apply Subtype.ext
      simpa using h0
    have hd0 : ∀ i, d i = 0 := fun i =>
      (Fintype.linearIndependent_iff.1 b.linearIndependent) d h0' i
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply, LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (fun j => if i = j then (1 : K) else 0) = Pi.single i 1 := by
      ext j; simp [Pi.single_apply, eq_comm]
    rw [this, ← hd i, hd0 i, map_zero, smul_zero]
  have := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun, hker] at this
  omega


abbrev perpQuot (B : V →ₛₗ[σ] V →ₗ[K] K) (P : Submodule K V) : Type _ :=
  ↥(P.orthogonalBilin B) ⧸ P.comap (P.orthogonalBilin B).subtype

theorem finrank_perpQuot_eq [FiniteDimensional K V] (hσ : Function.Surjective σ)
    {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.SeparatingLeft) (P : Submodule K V)
    (hP : P ≤ P.orthogonalBilin B) :
    finrank K (perpQuot B P) = finrank K V - 2 * finrank K P := by
  have h1 : finrank K (perpQuot B P) + finrank K (P.comap (P.orthogonalBilin B).subtype) =
      finrank K (P.orthogonalBilin B) :=
    Submodule.finrank_quotient_add_finrank (P.comap (P.orthogonalBilin B).subtype)
  have h2 : finrank K (P.comap (P.orthogonalBilin B).subtype) = finrank K P :=
    (Submodule.comapSubtypeEquivOfLe hP).finrank_eq
  have h3 := finrank_orthogonalBilin_eq hσ hB P
  omega

theorem coe_inv_apply_apply (g : LinearMap.GeneralLinearGroup K V) (v : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) ((g : Module.End K V) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
  rfl

theorem coe_apply_inv_apply (g : LinearMap.GeneralLinearGroup K V) (v : V) :
    (g : Module.End K V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) = v := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
  rfl

@[expose] def isoStab (B : V →ₛₗ[σ] V →ₗ[K] K) (P : Submodule K V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | (∀ v w, B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w) ∧
    ∀ v, (g : Module.End K V) v ∈ P ↔ v ∈ P}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · simp only [Units.val_mul, Module.End.mul_apply]
      rw [hg1, hh1]
    · simp only [Units.val_mul, Module.End.mul_apply]
      rw [hg2, hh2]
  one_mem' := by
    refine ⟨fun v w => ?_, fun v => ?_⟩ <;> simp
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v w => ?_, fun v => ?_⟩
    · have := hg1 (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
        (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w)
      rw [coe_apply_inv_apply, coe_apply_inv_apply] at this
      exact this.symm
    · rw [← hg2, coe_apply_inv_apply]

theorem mem_isoStab_iso {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ isoStab B P) (v w : V) :
    B ((g : Module.End K V) v) ((g : Module.End K V) w) = B v w := hg.1 v w

theorem mem_isoStab_mem {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ isoStab B P) (v : V) :
    (g : Module.End K V) v ∈ P ↔ v ∈ P := hg.2 v

theorem apply_mem_orthogonalBilin {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V}
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ isoStab B P) {v : V}
    (hv : v ∈ P.orthogonalBilin B) : (g : Module.End K V) v ∈ P.orthogonalBilin B := by
  rw [Submodule.mem_orthogonalBilin] at hv ⊢
  intro w hw
  have h1 : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w ∈ P := by
    rw [← mem_isoStab_mem hg, coe_apply_inv_apply]
    exact hw
  have := mem_isoStab_iso hg (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w) v
  rw [coe_apply_inv_apply] at this
  rw [this]
  exact hv _ h1

@[expose] def perpRestrict {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V}
    (g : isoStab B P) : P.orthogonalBilin B →ₗ[K] P.orthogonalBilin B :=
  LinearMap.restrict ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
    fun _ hv => apply_mem_orthogonalBilin g.2 hv

@[expose] def perpEnd {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V}
    (g : isoStab B P) : Module.End K (perpQuot B P) :=
  Submodule.mapQ _ _ (perpRestrict g) fun x hx => by
    simpa [perpRestrict, mem_isoStab_mem g.2] using hx

theorem perpEnd_mk {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V} (g : isoStab B P)
    (x y : P.orthogonalBilin B)
    (hxy : (y : V) = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) x) :
    perpEnd g (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  have : y = perpRestrict g x := Subtype.ext hxy
  rw [this]
  rfl

@[expose] noncomputable def perpGL (B : V →ₛₗ[σ] V →ₗ[K] K) (P : Submodule K V) :
    isoStab B P →* LinearMap.GeneralLinearGroup K (perpQuot B P) :=
  MonoidHom.toHomUnits
    { toFun := perpEnd
      map_one' := by
        refine LinearMap.ext fun q => ?_
        induction q using Submodule.Quotient.induction_on with
        | _ x => exact perpEnd_mk 1 x x (by simp)
      map_mul' := by
        intro g h
        refine LinearMap.ext fun q => ?_
        induction q using Submodule.Quotient.induction_on with
        | _ x =>
          rw [Module.End.mul_apply]
          have h1 := perpEnd_mk h x (perpRestrict h x) rfl
          rw [h1]
          have h2 := perpEnd_mk g (perpRestrict h x) (perpRestrict g (perpRestrict h x)) rfl
          rw [h2]
          exact (perpEnd_mk (g * h) x _ (by simp [perpRestrict])).symm }

theorem perpGL_mk {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Submodule K V} (g : isoStab B P)
    (x y : P.orthogonalBilin B)
    (hxy : (y : V) = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) x) :
    ((perpGL B P g : LinearMap.GeneralLinearGroup K (perpQuot B P)) :
      Module.End K (perpQuot B P)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk y :=
  perpEnd_mk g x y hxy


structure ChainStabData (B : V →ₛₗ[σ] V →ₗ[K] K) (s : ℕ) (W : ℕ → Submodule K V)
    (U : Subgroup (LinearMap.GeneralLinearGroup K V)) : Prop where
  iso : ∀ u ∈ U, ∀ v w, B ((u : Module.End K V) v) ((u : Module.End K V) w) = B v w
  three : ∀ u ∈ U, ∃ k : ℕ, u ^ 3 ^ k = 1
  stab : ∀ u ∈ U, ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j, (u : Module.End K V) v ∈ W j
  scal : ∀ u ∈ U, ∀ j, 1 ≤ j → j ≤ s →
    ∃ c : K, ∀ v ∈ W j, (u : Module.End K V) v - c • v ∈ W (j - 1)

theorem scalar_unique {g : Module.End K V} {X Y : Submodule K V} (hlt : Y < X) {c c' : K}
    (hc : ∀ v ∈ X, g v - c • v ∈ Y) (hc' : ∀ v ∈ X, g v - c' • v ∈ Y) : c = c' := by
  by_contra hne
  obtain ⟨v, hvX, hvY⟩ := IsConcreteLE.exists_of_lt hlt
  have h1 : (c' - c) • v ∈ Y := by
    have := Y.sub_mem (hc v hvX) (hc' v hvX)
    rwa [sub_sub_sub_cancel_left, ← sub_smul] at this
  apply hvY
  have := Y.smul_mem (c' - c)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hne)), one_smul] at this

namespace ChainStabData

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
  {U : Subgroup (LinearMap.GeneralLinearGroup K V)}

theorem stab_of_le (h : ChainStabData B s W U) (hW0 : W 0 = ⊥) {u : LinearMap.GeneralLinearGroup K V}
    (hu : u ∈ U) {j : ℕ} (hj : j ≤ s) {v : V} (hv : v ∈ W j) :
    (u : Module.End K V) v ∈ W j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [hW0, Submodule.mem_bot] at hv
    simp [hv, hW0]
  · exact h.stab u hu j hj0 hj v hv

theorem mem_isoStab (h : ChainStabData B s W U) (hs : 1 ≤ s) {u : LinearMap.GeneralLinearGroup K V}
    (hu : u ∈ U) : u ∈ isoStab B (W s) := by
  refine ⟨h.iso u hu, fun v => ⟨fun hv => ?_, h.stab u hu s hs le_rfl v⟩⟩
  have := h.stab u⁻¹ (U.inv_mem hu) s hs le_rfl _ hv
  rwa [coe_inv_apply_apply] at this

theorem le_isoStab (h : ChainStabData B s W U) (hs : 1 ≤ s) : U ≤ isoStab B (W s) :=
  fun _ hu => h.mem_isoStab hs hu

noncomputable def scalOf (h : ChainStabData B s W U) (u : U) (i : Fin s) : K :=
  Classical.choose (h.scal u u.2 (i.1 + 1) (by omega) i.2)

theorem scalOf_spec (h : ChainStabData B s W U) (u : U) (i : Fin s) :
    ∀ v ∈ W (i.1 + 1), ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
      h.scalOf u i • v ∈ W i.1 := by
  intro v hv
  have := Classical.choose_spec (h.scal u u.2 (i.1 + 1) (by omega) i.2) v hv
  simpa [scalOf] using this

variable (hW0 : W 0 = ⊥) (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j)
include hlt

theorem eq_scalOf (h : ChainStabData B s W U) (u : U) (i : Fin s) {c : K}
    (hc : ∀ v ∈ W (i.1 + 1),
      ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - c • v ∈ W i.1) :
    h.scalOf u i = c :=
  scalar_unique (g := ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V))
    (by simpa using hlt (i.1 + 1) (by omega) i.2) (h.scalOf_spec u i) hc

include hW0

theorem scalOf_mul (h : ChainStabData B s W U) (u u' : U) (i : Fin s) :
    h.scalOf (u * u') i = h.scalOf u i * h.scalOf u' i := by
  refine h.eq_scalOf hlt _ _ fun v hv => ?_
  have h1 := h.scalOf_spec u' i v hv
  have h2 := h.scalOf_spec u i v hv
  have h3 := h.stab_of_le hW0 u.2 (le_of_lt i.2) h1
  have h4 := (W i.1).add_mem h3 ((W i.1).smul_mem (h.scalOf u' i) h2)
  convert h4 using 1
  rw [mul_comm (h.scalOf u i)]
  simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, map_sub, map_smul, smul_sub,
    mul_smul]
  abel

omit hW0 in
theorem scalOf_one (h : ChainStabData B s W U) (i : Fin s) : h.scalOf 1 i = 1 :=
  h.eq_scalOf hlt _ _ fun v _ => by simp

noncomputable def scalHom (h : ChainStabData B s W U) (i : Fin s) : U →* K where
  toFun u := h.scalOf u i
  map_one' := h.scalOf_one hlt i
  map_mul' u u' := h.scalOf_mul hW0 hlt u u' i

noncomputable def chainHom (h : ChainStabData B s W U) (hs : 1 ≤ s) :
    U →* (Fin s → Kˣ) × LinearMap.GeneralLinearGroup K (perpQuot B (W s)) :=
  (MonoidHom.pi fun i => MonoidHom.toHomUnits (h.scalHom hW0 hlt i)).prod
    ((perpGL B (W s)).comp (Subgroup.inclusion (h.le_isoStab hs)))

theorem chainHom_fst_spec (h : ChainStabData B s W U) (hs : 1 ≤ s) (u : U) (i : Fin s) :
    ∀ v ∈ W (i.1 + 1), ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
      (((h.chainHom hW0 hlt hs u).1 i : Kˣ) : K) • v ∈ W i.1 :=
  h.scalOf_spec u i

theorem chainHom_snd_spec (h : ChainStabData B s W U) (hs : 1 ≤ s) (u : U)
    (x y : (W s).orthogonalBilin B)
    (hxy : (y : V) = ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) x) :
    ((h.chainHom hW0 hlt hs u).2 : Module.End K (perpQuot B (W s)))
      (Submodule.Quotient.mk x) = Submodule.Quotient.mk y :=
  perpGL_mk (Subgroup.inclusion (h.le_isoStab hs) u) x y hxy

omit hlt hW0 in
theorem eq_one_of_forall [CharP K 2] (h : ChainStabData B s W U) (hW0 : W 0 = ⊥) (hs : 1 ≤ s)
    (u : U) (hP : ∀ j, 1 ≤ j → j ≤ s → ∀ v ∈ W j,
      ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - v ∈ W (j - 1))
    (hM : ∀ v, (∀ w ∈ W s, B w v = 0) →
      ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v - v ∈ W s) : u = 1 := by
  obtain ⟨k, hk⟩ := h.three u u.2
  have := eq_one_of_trivial_on_pieces (B := B) s W hW0 (u : LinearMap.GeneralLinearGroup K V)
    (h.iso u u.2) (fun j hj1 hjs v hv => h.stab u u.2 j hj1 hjs v hv) hP hM hk hs
  exact Subtype.ext this

theorem chainHom_injective [CharP K 2] (h : ChainStabData B s W U) (hs : 1 ≤ s) :
    Function.Injective (h.chainHom hW0 hlt hs) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 := Prod.ext_iff.1 hu
  refine h.eq_one_of_forall hW0 hs u ?_ ?_
  · intro j hj1 hjs v hv
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, j = i + 1 := ⟨j - 1, by omega⟩
    have := h.chainHom_fst_spec hW0 hlt hs u ⟨i, by omega⟩ v hv
    have e : (h.chainHom hW0 hlt hs u).1 ⟨i, by omega⟩ = 1 := by
      have := congrFun h1.1 ⟨i, by omega⟩
      simpa using this
    rw [e] at this
    simpa using this
  · intro v hv
    have e : (h.chainHom hW0 hlt hs u).2 = 1 := h1.2
    have hu' := h.chainHom_snd_spec hW0 hlt hs u ⟨v, hv⟩
      ⟨((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v, ?_⟩ rfl
    · rw [e] at hu'
      have := (Submodule.Quotient.eq _).1 hu'.symm
      simpa using this
    · exact apply_mem_orthogonalBilin (h.mem_isoStab hs u.2) hv

end ChainStabData


theorem exists_injective_hom_chain [CharP K 2] {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ}
    {W : ℕ → Submodule K V} (hW0 : W 0 = ⊥) (hs : 1 ≤ s)
    (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j)
    {U : Subgroup (LinearMap.GeneralLinearGroup K V)} (h : ChainStabData B s W U) :
    ∃ θ : U →* (Fin s → Kˣ) × LinearMap.GeneralLinearGroup K (perpQuot B (W s)),
      Function.Injective θ ∧
      (∀ (u : U) (i : Fin s), ∀ v ∈ W (i.1 + 1),
        ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
          (((θ u).1 i : Kˣ) : K) • v ∈ W i.1) ∧
      (∀ (u : U) (x y : (W s).orthogonalBilin B),
        (y : V) = ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) x →
        ((θ u).2 : Module.End K (perpQuot B (W s))) (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y) :=
  ⟨h.chainHom hW0 hlt hs, h.chainHom_injective hW0 hlt hs, h.chainHom_fst_spec hW0 hlt hs,
    h.chainHom_snd_spec hW0 hlt hs⟩

theorem card_generalLinearGroup_eq (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N] [Module K N]
    [Module.Finite K N] {m : ℕ} (hN : finrank K N = m) :
    Nat.card (LinearMap.GeneralLinearGroup K N) = ∏ i : Fin m, (4 ^ m - 4 ^ i.1) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let b := Module.finBasisOfFinrankEq K N hN
  have := Matrix.card_GL_field (𝔽 := K) m
  rw [hq] at this
  rw [← this]
  exact (Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv).symm

theorem card_generalLinearGroup_zero (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N]
    [Module K N] [Module.Finite K N] (hN : finrank K N = 0) :
    Nat.card (LinearMap.GeneralLinearGroup K N) = 1 := by
  rw [card_generalLinearGroup_eq hK hN]
  simp

theorem card_generalLinearGroup_one (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N]
    [Module K N] [Module.Finite K N] (hN : finrank K N = 1) :
    Nat.card (LinearMap.GeneralLinearGroup K N) = 3 := by
  rw [card_generalLinearGroup_eq hK hN]
  simp

theorem card_generalLinearGroup_two (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N]
    [Module K N] [Module.Finite K N] (hN : finrank K N = 2) :
    Nat.card (LinearMap.GeneralLinearGroup K N) = 180 := by
  rw [card_generalLinearGroup_eq hK hN]
  simp [Fin.prod_univ_two]

theorem le_of_pow_three_dvd {n c m : ℕ}
    (hc : c = 1 ∧ m = 0 ∨ c = 3 ∧ m = 1 ∨ c = 180 ∧ m = 2) (h : 3 ^ n ∣ c) : n ≤ m := by
  by_contra hnm
  have h3 : 3 ^ (m + 1) ∣ c := (pow_dvd_pow 3 (by omega)).trans h
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert h3 <;> decide

theorem three_subgroup_generalLinearGroup (hK : Nat.card K = 4) {N : Type*} [AddCommGroup N]
    [Module K N] [Module.Finite K N] {m : ℕ} (hN : finrank K N = m) (hm : m ≤ 2)
    (H : Subgroup (LinearMap.GeneralLinearGroup K N))
    (hH : ∀ g ∈ H, ∃ k : ℕ, g ^ 3 ^ k = 1) :
    Nat.card H ∣ 3 ^ m ∧ ∀ a b : H, a * b = b * a := by
  have hcard : Nat.card (LinearMap.GeneralLinearGroup K N) = 1 ∧ m = 0 ∨
      Nat.card (LinearMap.GeneralLinearGroup K N) = 3 ∧ m = 1 ∨
      Nat.card (LinearMap.GeneralLinearGroup K N) = 180 ∧ m = 2 := by
    interval_cases m
    · exact Or.inl ⟨card_generalLinearGroup_zero hK hN, rfl⟩
    · exact Or.inr (Or.inl ⟨card_generalLinearGroup_one hK hN, rfl⟩)
    · exact Or.inr (Or.inr ⟨card_generalLinearGroup_two hK hN, rfl⟩)
  have : Finite (LinearMap.GeneralLinearGroup K N) :=
    Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 H := fun g => by
    obtain ⟨k, hk⟩ := hH g g.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : 3 ^ n ∣ Nat.card (LinearMap.GeneralLinearGroup K N) :=
    hn ▸ Subgroup.card_subgroup_dvd_card H
  have hnm : n ≤ m := le_of_pow_three_dvd hcard hdvd
  refine ⟨hn ▸ pow_dvd_pow 3 hnm, ?_⟩
  have hn2 : n ≤ 2 := le_trans hnm hm
  interval_cases n
  · have h1 : Nat.card H = 1 := by simpa using hn
    have := (Nat.card_eq_one_iff_unique.1 h1).1
    exact fun a b => Subsingleton.elim _ _
  · have : IsCyclic H := isCyclic_of_prime_card (p := 3) (by simpa using hn)
    exact fun a b => (IsCyclic.isMulCommutative (α := H)).is_comm.comm a b
  · exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hn).is_comm.comm a b


namespace ChainStabData

variable {B : V →ₛₗ[σ] V →ₗ[K] K} {s : ℕ} {W : ℕ → Submodule K V}
  {U : Subgroup (LinearMap.GeneralLinearGroup K V)}
  (hW0 : W 0 = ⊥) (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j) (hs : 1 ≤ s)
include hW0 hlt hs

noncomputable def chainImage (h : ChainStabData B s W U) :
    Subgroup (LinearMap.GeneralLinearGroup K (perpQuot B (W s))) :=
  ((MonoidHom.snd _ _).comp (h.chainHom hW0 hlt hs)).range

theorem chainImage_three (h : ChainStabData B s W U) :
    ∀ g ∈ h.chainImage hW0 hlt hs, ∃ k : ℕ, g ^ 3 ^ k = 1 := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨k, hk⟩ := h.three u u.2
  refine ⟨k, ?_⟩
  have : u ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  have h2 : (h.chainHom hW0 hlt hs) (u ^ 3 ^ k) = 1 := by rw [this, map_one]
  rw [map_pow] at h2
  have := congrArg Prod.snd h2
  simpa using this

theorem mul_comm_of_finrank_le [CharP K 2] [FiniteDimensional K V] (h : ChainStabData B s W U)
    (hK : Nat.card K = 4) (hm : finrank K (perpQuot B (W s)) ≤ 2) (u u' : U) :
    u * u' = u' * u := by
  have hH := (three_subgroup_generalLinearGroup hK rfl hm _
    (h.chainImage_three hW0 hlt hs)).2
  apply h.chainHom_injective hW0 hlt hs
  rw [map_mul, map_mul]
  refine Prod.ext (mul_comm _ _) ?_
  exact congrArg Subtype.val (hH ⟨_, ⟨u, rfl⟩⟩ ⟨_, ⟨u', rfl⟩⟩)

theorem isMulCommutative_of_finrank_le [CharP K 2] [FiniteDimensional K V]
    (h : ChainStabData B s W U) (hK : Nat.card K = 4)
    (hm : finrank K (perpQuot B (W s)) ≤ 2) : IsMulCommutative U :=
  ⟨⟨h.mul_comm_of_finrank_le hW0 hlt hs hK hm⟩⟩

theorem card_dvd_of_finrank [CharP K 2] [FiniteDimensional K V] (h : ChainStabData B s W U)
    (hK : Nat.card K = 4) {m : ℕ} (hN : finrank K (perpQuot B (W s)) = m) (hm : m ≤ 2) :
    Nat.card U ∣ 3 ^ (s + m) := by
  have hH := three_subgroup_generalLinearGroup hK hN hm _ (h.chainImage_three hW0 hlt hs)
  let H := h.chainImage hW0 hlt hs
  let θ' : U →* (Fin s → Kˣ) × H :=
    (MonoidHom.fst _ _ |>.comp (h.chainHom hW0 hlt hs)).prod
      (((MonoidHom.snd _ _).comp (h.chainHom hW0 hlt hs)).codRestrict H fun u => ⟨u, rfl⟩)
  have hinj : Function.Injective θ' := fun u u' hu => by
    apply h.chainHom_injective hW0 hlt hs
    exact Prod.ext (Prod.ext_iff.1 hu).1 (congrArg Subtype.val (Prod.ext_iff.1 hu).2)
  have h1 := Subgroup.card_dvd_of_injective θ' hinj
  have hKu : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hK]
  have hA : Nat.card (Fin s → Kˣ) = 3 ^ s := by
    rw [Nat.card_pi]
    simp [hKu]
  rw [Nat.card_prod, hA] at h1
  rw [pow_add]
  exact h1.trans (mul_dvd_mul_left _ hH.1)

end ChainStabData

end CFSG.HardMathSupport.Curtis.UnitaryLevi
