module

public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators
public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

noncomputable abbrev ox₁
    (s : K) : ModGL TwistTag.D4.tag K :=
  (trialityX₁ K σ.toRingHom s : ModGL TwistTag.D4.tag K)

noncomputable abbrev ox₂
    (b : trialityFixedField K σ.toRingHom) : ModGL TwistTag.D4.tag K :=
  (trialityX₂ K σ.toRingHom b : ModGL TwistTag.D4.tag K)

noncomputable abbrev ox₃
    (s : K) : ModGL TwistTag.D4.tag K :=
  (trialityX₃ K σ.toRingHom s : ModGL TwistTag.D4.tag K)

noncomputable abbrev ox₄
    (s : K) : ModGL TwistTag.D4.tag K :=
  (trialityX₄ K σ.toRingHom s : ModGL TwistTag.D4.tag K)

noncomputable abbrev ox₅
    (b : trialityFixedField K σ.toRingHom) : ModGL TwistTag.D4.tag K :=
  (trialityX₅ K σ.toRingHom b : ModGL TwistTag.D4.tag K)

noncomputable abbrev ox₆
    (b : trialityFixedField K σ.toRingHom) : ModGL TwistTag.D4.tag K :=
  (trialityX₆ K σ.toRingHom b : ModGL TwistTag.D4.tag K)

end Defs

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

theorem add_of_hom' {H : Type*} [Group H] {P A : Subgroup H} {M : Type*} [AddCommGroup M]
    (f : Multiplicative M →* P) (X : M → A)
    (hf : ∀ c : M, ((f (Multiplicative.ofAdd c) : P) : H) = (X c : H)) :
    ∀ c d : M, X (c + d) = X c * X d := by
  intro c d
  apply Subtype.ext
  have h1 := hf (c + d)
  rw [ofAdd_add, map_mul, Subgroup.coe_mul, hf c, hf d] at h1
  exact h1.symm

include hσ3 in
theorem ox_data
    :
    ((∀ c d : K, trialityX₁ K τ₀ (c + d) = trialityX₁ K τ₀ c * trialityX₁ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₂ K τ₀ (c + d) = trialityX₂ K τ₀ c *
        trialityX₂ K τ₀ d) ∧
      (∀ c d : K, trialityX₃ K τ₀ (c + d) = trialityX₃ K τ₀ c * trialityX₃ K τ₀ d) ∧
      (∀ c d : K, trialityX₄ K τ₀ (c + d) = trialityX₄ K τ₀ c * trialityX₄ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₅ K τ₀ (c + d) = trialityX₅ K τ₀ c *
        trialityX₅ K τ₀ d) ∧
      (∀ c d : trialityFixedField K τ₀, trialityX₆ K τ₀ (c + d) = trialityX₆ K τ₀ c *
        trialityX₆ K τ₀ d)) ∧
    ((∀ c : K, ox₁ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, ox₂ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : K, ox₃ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : K, ox₄ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, ox₅ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) ∧
      (∀ c : trialityFixedField K τ₀, ox₆ σ c ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀)) ∧
    ((Function.Injective (trialityX₁ K τ₀)) ∧ (Function.Injective (trialityX₂ K τ₀)) ∧
      (Function.Injective (trialityX₃ K τ₀)) ∧ (Function.Injective (trialityX₄ K τ₀)) ∧
      (Function.Injective (trialityX₅ K τ₀)) ∧ (Function.Injective (trialityX₆ K τ₀))) := by
  obtain ⟨⟨f₁, hf₁i, hf₁⟩, ⟨f₂, hf₂i, hf₂⟩, ⟨f₃, hf₃i, hf₃⟩, ⟨f₄, hf₄i, hf₄⟩,
    ⟨f₅, hf₅i, hf₅⟩, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  have mP : ∀ {M : Type} [AddCommGroup M] (f : Multiplicative M →* ↥(graphFixedPosUnipotent
      TwistTag.D4 K τ₀)) (X : M → adjointGroup TwistTag.D4.tag K),
      (∀ c : M, ((f (Multiplicative.ofAdd c) : graphFixedPosUnipotent TwistTag.D4 K τ₀) : GL) =
        (X c : GL)) → ∀ c, (X c : GL) ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀ :=
    fun f X hf c => by rw [← hf c]; exact (f (Multiplicative.ofAdd c)).2
  have inj : ∀ {M : Type} [AddCommGroup M] (f : Multiplicative M →* ↥(graphFixedPosUnipotent
      TwistTag.D4 K τ₀)) (X : M → adjointGroup TwistTag.D4.tag K),
      Function.Injective f →
      (∀ c : M, ((f (Multiplicative.ofAdd c) : graphFixedPosUnipotent TwistTag.D4 K τ₀) : GL) =
        (X c : GL)) → Function.Injective X := by
    intro M _ f X hi hf c d h
    have h1 : f (Multiplicative.ofAdd c) = f (Multiplicative.ofAdd d) := by
      apply Subtype.ext
      rw [hf c, hf d, h]
    exact Multiplicative.ofAdd.injective (hi h1)
  exact ⟨⟨add_of_hom' f₁ (trialityX₁ K τ₀) hf₁, add_of_hom' f₂ (trialityX₂ K τ₀) hf₂,
    add_of_hom' f₃ (trialityX₃ K τ₀) hf₃, add_of_hom' f₄ (trialityX₄ K τ₀) hf₄,
    add_of_hom' f₅ (trialityX₅ K τ₀) hf₅, add_of_hom' f₆ (trialityX₆ K τ₀) hf₆⟩,
    ⟨mP f₁ (trialityX₁ K τ₀) hf₁, mP f₂ (trialityX₂ K τ₀) hf₂, mP f₃ (trialityX₃ K τ₀) hf₃,
      mP f₄ (trialityX₄ K τ₀) hf₄, mP f₅ (trialityX₅ K τ₀) hf₅, mP f₆ (trialityX₆ K τ₀) hf₆⟩,
    ⟨inj f₁ (trialityX₁ K τ₀) hf₁i hf₁, inj f₂ (trialityX₂ K τ₀) hf₂i hf₂,
      inj f₃ (trialityX₃ K τ₀) hf₃i hf₃, inj f₄ (trialityX₄ K τ₀) hf₄i hf₄,
      inj f₅ (trialityX₅ K τ₀) hf₅i hf₅, inj f₆ (trialityX₆ K τ₀) hf₆i hf₆⟩⟩

end Coordinates

section Torus

variable {K : Type} [Field K]

theorem rootChar_d4 (c₀ c₁ c₂ c₃ : Kˣ) (n₀ n₁ n₂ n₃ : ℤ) :
    rootChar (d4Tuple c₀ c₁ c₂ c₃) ![n₀, n₁, n₂, n₃] =
      c₀ ^ n₀ * c₁ ^ n₁ * c₂ ^ n₂ * c₃ ^ n₃ := by
  change ∏ i : Fin 4, (![c₀, c₁, c₂, c₃] i) ^ (![n₀, n₁, n₂, n₃] i) = _
  simp [Fin.prod_univ_four]

theorem conj_trialityOrbitProd
    (l : Fin TwistTag.D4.tag.rank → Kˣ)
    {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hr : ∀ h : ℕ, IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ h) α))
    (σ' : K →+* K) (s : K)
    (h1 : ((rootChar l (permLattice TwistTag.D4.perm α) : Kˣ) : K) =
      σ' ((rootChar l α : Kˣ) : K))
    (h2 : ((rootChar l (permLattice (TwistTag.D4.perm ^ 2) α) : Kˣ) : K) =
      σ' (σ' ((rootChar l α : Kˣ) : K))) :
    rootDiagUnit TwistTag.D4.tag l * (trialityOrbitProd K σ' α s : ModGL TwistTag.D4.tag K) *
        (rootDiagUnit TwistTag.D4.tag l)⁻¹ =
      (trialityOrbitProd K σ' α (((rootChar l α : Kˣ) : K) * s) :
        ModGL TwistTag.D4.tag K) := by
  have e1 : (TwistTag.D4.perm ^ 1) = TwistTag.D4.perm := pow_one _
  have r0 : IsRoot TwistTag.D4.tag α := hr 0
  have r1 := hr 1
  have r2 := hr 2
  rw [e1] at r1
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd]
  have conj3 : ∀ x y z : ModGL TwistTag.D4.tag K, ∀ d : ModGL TwistTag.D4.tag K,
      d * (x * y * z) * d⁻¹ = (d * x * d⁻¹) * (d * y * d⁻¹) * (d * z * d⁻¹) := by
    intro x y z d; group
  rw [conj3, rootDiagUnit_conj_pinnedX l r0, rootDiagUnit_conj_pinnedX l r1,
    rootDiagUnit_conj_pinnedX l r2, h1, h2]
  simp only [map_mul]

structure TwistFixed (σ : K ≃+* K) (c₀ c₁ c₂ c₃ : Kˣ) : Prop where
  h0 : σ (c₀ : K) = c₁
  h1 : σ (c₁ : K) = c₃
  h3 : σ (c₃ : K) = c₀
  h2 : σ (c₂ : K) = c₂

theorem perm_r0 : permLattice TwistTag.D4.perm (trialityRoot 0) = ![0, 1, 0, 0] :=
  List.ofFn_injective (by decide +kernel)

theorem perm2_r0 : permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 0) = ![0, 0, 0, 1] :=
  List.ofFn_injective (by decide +kernel)

theorem perm_r2 : permLattice TwistTag.D4.perm (trialityRoot 2) = ![0, 1, 1, 0] :=
  List.ofFn_injective (by decide +kernel)

theorem perm2_r2 : permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 2) = ![0, 0, 1, 1] :=
  List.ofFn_injective (by decide +kernel)

theorem perm_r3 : permLattice TwistTag.D4.perm (trialityRoot 3) = ![1, 0, 1, 1] :=
  List.ofFn_injective (by decide +kernel)

theorem perm2_r3 : permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3) = ![1, 1, 1, 0] :=
  List.ofFn_injective (by decide +kernel)

section Instances

variable {σ : K ≃+* K} {c₀ c₁ c₂ c₃ : Kˣ}

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K
local notation "dd" => rootDiagUnit TwistTag.D4.tag (d4Tuple c₀ c₁ c₂ c₃)

theorem torus_ox₁
    (hF : TwistFixed σ c₀ c₁ c₂ c₃) (s : K) :
    dd * ox₁ σ s * dd⁻¹ = ox₁ σ ((c₀ : K) * s) := by
  have hr0 : trialityRoot 0 = ![1, 0, 0, 0] := rfl
  have := conj_trialityOrbitProd (K := K) (d4Tuple c₀ c₁ c₂ c₃) (α := trialityRoot 0)
    (fun h => (isRoot_trialityRoot 0 h).1) τ₀ s ?_ ?_
  · rw [hr0, rootChar_d4] at this
    simpa [ox₁, trialityX₁, hr0] using this
  · rw [perm_r0, hr0, rootChar_d4, rootChar_d4]; simp [hF.h0]
  · rw [perm2_r0, hr0, rootChar_d4, rootChar_d4]; simp [hF.h0, hF.h1]

theorem torus_ox₃
    (hF : TwistFixed σ c₀ c₁ c₂ c₃) (s : K) :
    dd * ox₃ σ s * dd⁻¹ = ox₃ σ ((c₀ : K) * c₂ * s) := by
  have hr0 : trialityRoot 2 = ![1, 0, 1, 0] := rfl
  have := conj_trialityOrbitProd (K := K) (d4Tuple c₀ c₁ c₂ c₃) (α := trialityRoot 2)
    (fun h => (isRoot_trialityRoot 2 h).1) τ₀ s ?_ ?_
  · rw [hr0, rootChar_d4] at this
    simpa [ox₃, trialityX₃, hr0] using this
  · rw [perm_r2, hr0, rootChar_d4, rootChar_d4]; simp [hF.h0, hF.h2]
  · rw [perm2_r2, hr0, rootChar_d4, rootChar_d4]; simp [hF.h0, hF.h1, hF.h2]; ring

theorem torus_ox₄
    (hF : TwistFixed σ c₀ c₁ c₂ c₃) (s : K) :
    dd * ox₄ σ s * dd⁻¹ = ox₄ σ ((c₁ : K) * c₂ * c₃ * s) := by
  have hr0 : trialityRoot 3 = ![0, 1, 1, 1] := rfl
  have := conj_trialityOrbitProd (K := K) (d4Tuple c₀ c₁ c₂ c₃) (α := trialityRoot 3)
    (fun h => (isRoot_trialityRoot 3 h).1) τ₀ s ?_ ?_
  · rw [hr0, rootChar_d4] at this
    simpa [ox₄, trialityX₄, hr0] using this
  · rw [perm_r3, hr0, rootChar_d4, rootChar_d4]; simp [hF.h1, hF.h2, hF.h3]; ring
  · rw [perm2_r3, hr0, rootChar_d4, rootChar_d4]; simp [hF.h0, hF.h1, hF.h2, hF.h3]; ring

theorem torus_ox₅
    (hF : TwistFixed σ c₀ c₁ c₂ c₃) (b : trialityFixedField K τ₀) :
    dd * ox₅ σ b * dd⁻¹ =
      ox₅ σ ⟨((c₀ : K) * c₁ * c₂ * c₃) * b, by
        have hb : σ (b : K) = b := b.2
        change σ (((c₀ : K) * c₁ * c₂ * c₃) * b) = ((c₀ : K) * c₁ * c₂ * c₃) * b
        rw [map_mul, map_mul, map_mul, map_mul, hF.h0, hF.h1, hF.h2, hF.h3, hb]
        ring⟩ := by
  have hr0 : trialityRoot 4 = ![1, 1, 1, 1] := rfl
  have := rootDiagUnit_conj_pinnedX (K := K) (d4Tuple c₀ c₁ c₂ c₃)
    (α := trialityRoot 4) (isRoot_trialityRoot 4 0).1 (b : K)
  rw [hr0, rootChar_d4] at this
  simpa [ox₅, trialityX₅, hr0] using this

theorem torus_ox₆
    (hF : TwistFixed σ c₀ c₁ c₂ c₃) (b : trialityFixedField K τ₀) :
    dd * ox₆ σ b * dd⁻¹ =
      ox₆ σ ⟨((c₀ : K) * c₁ * c₂ ^ 2 * c₃) * b, by
        have hb : σ (b : K) = b := b.2
        change σ (((c₀ : K) * c₁ * (c₂ : K) ^ 2 * c₃) * b) =
          ((c₀ : K) * c₁ * (c₂ : K) ^ 2 * c₃) * b
        rw [map_mul, map_mul, map_mul, map_mul, map_pow, hF.h0, hF.h1, hF.h2, hF.h3, hb]
        ring⟩ := by
  have hr0 : trialityRoot 5 = ![1, 1, 2, 1] := rfl
  have := rootDiagUnit_conj_pinnedX (K := K) (d4Tuple c₀ c₁ c₂ c₃)
    (α := trialityRoot 5) (isRoot_trialityRoot 5 0).1 (b : K)
  rw [hr0, rootChar_d4] at this
  simpa [ox₆, trialityX₆, hr0] using this

end Instances

end Torus

section TorusHom

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))
local notation "τ₀" => σ.toRingHom

theorem twistFixed_torus (hσ3 : σ.toRingHom ^ 3 = 1) (a : Kˣ)
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    TwistFixed σ (a ^ 2 * (trialityFixedUnit K σ b)⁻¹) (σu a ^ 2 * (trialityFixedUnit K σ b)⁻¹)
      ((a * σu a * σu (σu a))⁻¹ * trialityFixedUnit K σ b ^ 2)
      (σu (σu a) ^ 2 * (trialityFixedUnit K σ b)⁻¹) := by
  have h3 : σ (σ (σ (a : K))) = a := by
    have := congrArg (fun f : K →+* K => f (a : K)) hσ3
    simpa using this
  have hb : σ ((trialityFixedUnit K σ b : Kˣ) : K) = (trialityFixedUnit K σ b : Kˣ) :=
    sigma_trialityFixedUnit b
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow,
      map_inv₀, hb]
    rfl
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow,
      map_inv₀, hb]
    rfl
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow,
      map_inv₀, hb]
    change σ (σ (σ (a : K))) ^ 2 * _ = _
    rw [h3]
  · simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_mul, map_pow,
      map_inv₀, hb]
    change (σ (a : K) * σ (σ (a : K)) * σ (σ (σ (a : K))))⁻¹ * _ =
      (a * σ (a : K) * σ (σ (a : K)))⁻¹ * _
    rw [h3]
    congr 2
    ring

theorem torusHom_eq
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (a, b) = rootDiagUnit TwistTag.D4.tag
      (d4Tuple (a ^ 2 * (trialityFixedUnit K σ b)⁻¹) (σu a ^ 2 * (trialityFixedUnit K σ b)⁻¹)
        ((a * σu a * σu (σu a))⁻¹ * trialityFixedUnit K σ b ^ 2)
        (σu (σu a) ^ 2 * (trialityFixedUnit K σ b)⁻¹)) :=
  trialityOuter_mul_middle_eq a b

theorem ne_zero_coe_unit (b : (trialityFixedField K σ.toRingHom)ˣ) :
    ((b : trialityFixedField K σ.toRingHom) : K) ≠ 0 := fun h =>
  b.ne_zero (Subtype.ext (by simpa using h))

theorem torus_b_ox₁
    (hσ3 : σ.toRingHom ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ) (s : K) :
    trialityTorusHom σ (1, b) * ox₁ σ s * (trialityTorusHom σ (1, b))⁻¹ =
      ox₁ σ ((((b : trialityFixedField K τ₀) : K))⁻¹ * s) := by
  rw [torusHom_eq, torus_ox₁ (twistFixed_torus σ hσ3 1 b)]
  have hw : (((1 : Kˣ) ^ 2 * (trialityFixedUnit K σ b)⁻¹ : Kˣ) : K) =
      (((b : trialityFixedField K τ₀) : K))⁻¹ := by
    simp only [one_pow, one_mul, Units.val_inv_eq_inv_val]
    rfl
  rw [hw]

theorem torus_b_ox₃
    (hσ3 : σ.toRingHom ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ) (s : K) :
    trialityTorusHom σ (1, b) * ox₃ σ s * (trialityTorusHom σ (1, b))⁻¹ =
      ox₃ σ (((b : trialityFixedField K τ₀) : K) * s) := by
  rw [torusHom_eq, torus_ox₃ (twistFixed_torus σ hσ3 1 b)]
  have hw : (((1 : Kˣ) ^ 2 * (trialityFixedUnit K σ b)⁻¹ : Kˣ) : K) *
      ((((1 : Kˣ) * σu 1 * σu (σu 1))⁻¹ * trialityFixedUnit K σ b ^ 2 : Kˣ) : K) =
      ((b : trialityFixedField K τ₀) : K) := by
    have hb := ne_zero_coe_unit σ b
    simp only [map_one, one_pow, one_mul, mul_one, inv_one, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    change ((((b : trialityFixedField K τ₀) : K))⁻¹) *
      ((((b : trialityFixedField K τ₀) : K)) ^ 2) = _
    field_simp
  rw [hw]

theorem torus_b_ox₅
    (hσ3 : σ.toRingHom ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ)
    (e : trialityFixedField K τ₀) :
    trialityTorusHom σ (1, b) * ox₅ σ e * (trialityTorusHom σ (1, b))⁻¹ =
      ox₅ σ (((b⁻¹ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * e) := by
  rw [torusHom_eq, torus_ox₅ (twistFixed_torus σ hσ3 1 b)]
  congr 1
  apply Subtype.ext
  have hb := ne_zero_coe_unit σ b
  simp only [map_one, one_pow, one_mul, mul_one, inv_one, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val]
  change ((((b : trialityFixedField K τ₀) : K))⁻¹ * (((b : trialityFixedField K τ₀) : K))⁻¹ *
      ((((b : trialityFixedField K τ₀) : K)) ^ 2) * (((b : trialityFixedField K τ₀) : K))⁻¹) *
      (e : K) = _
  push_cast
  field_simp

theorem torus_b_ox₆
    (hσ3 : σ.toRingHom ^ 3 = 1) (b : (trialityFixedField K σ.toRingHom)ˣ)
    (e : trialityFixedField K τ₀) :
    trialityTorusHom σ (1, b) * ox₆ σ e * (trialityTorusHom σ (1, b))⁻¹ =
      ox₆ σ (((b : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * e) := by
  rw [torusHom_eq, torus_ox₆ (twistFixed_torus σ hσ3 1 b)]
  congr 1
  apply Subtype.ext
  have hb := ne_zero_coe_unit σ b
  simp only [map_one, one_pow, one_mul, mul_one, inv_one, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val]
  change ((((b : trialityFixedField K τ₀) : K))⁻¹ * (((b : trialityFixedField K τ₀) : K))⁻¹ *
      ((((b : trialityFixedField K τ₀) : K)) ^ 2) ^ 2 * (((b : trialityFixedField K τ₀) : K))⁻¹) *
      (e : K) = _
  push_cast
  field_simp

theorem torus_a_ox₃
    (hσ3 : σ.toRingHom ^ 3 = 1) (a : Kˣ) (s : K) :
    trialityTorusHom σ (a, 1) * ox₃ σ s * (trialityTorusHom σ (a, 1))⁻¹ =
      ox₃ σ (((a : K) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹) * s) := by
  rw [torusHom_eq, torus_ox₃ (twistFixed_torus σ hσ3 a 1)]
  have hw : ((a ^ 2 * (trialityFixedUnit K σ 1)⁻¹ : Kˣ) : K) *
      ((((a * σu a * σu (σu a))⁻¹ * trialityFixedUnit K σ 1 ^ 2 : Kˣ) : K)) =
      (a : K) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ := by
    simp only [map_one, one_pow, mul_one, inv_one, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [hw]

theorem torus_a_ox₄
    (hσ3 : σ.toRingHom ^ 3 = 1) (a : Kˣ) (s : K) :
    trialityTorusHom σ (a, 1) * ox₄ σ s * (trialityTorusHom σ (a, 1))⁻¹ =
      ox₄ σ ((σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹) * s) := by
  rw [torusHom_eq, torus_ox₄ (twistFixed_torus σ hσ3 a 1)]
  have hw : (((σu a ^ 2 * (trialityFixedUnit K σ 1)⁻¹ : Kˣ) : K)) *
      ((((a * σu a * σu (σu a))⁻¹ * trialityFixedUnit K σ 1 ^ 2 : Kˣ) : K)) *
      ((σu (σu a) ^ 2 * (trialityFixedUnit K σ 1)⁻¹ : Kˣ) : K) =
      σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ := by
    simp only [map_one, one_pow, mul_one, inv_one, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_pow_eq_pow_val]
    change σ (a : K) ^ 2 * ((a * σ (a : K) * σ (σ (a : K)))⁻¹) * σ (σ (a : K)) ^ 2 = _
    ring
  rw [hw]

end TorusHom

section Relations

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

omit [CharP K 2] in
theorem commute_coe {x y : adjointGroup TwistTag.D4.tag K} (h : Commute x y) :
    Commute (x : ModGL TwistTag.D4.tag K) (y : ModGL TwistTag.D4.tag K) :=
  h.map (adjointGroup TwistTag.D4.tag K).subtype

include hσ3 in
theorem rel14
    (s t : K) :
    ⁅ox₁ σ s, ox₄ σ t⁆ = ox₅ σ (trialityTrace K τ₀ hσ3 (s * t)) :=
  (coe_commutatorElement_adjoint (trialityX₁ K τ₀ s) (trialityX₄ K τ₀ t)).symm.trans
    (congrArg Subtype.val ((even_triality_trace_commutators K τ₀ hσ3).1 s t))

include hσ3 in
theorem rel34
    (s t : K) :
    ⁅ox₃ σ s, ox₄ σ t⁆ = ox₆ σ (trialityTrace K τ₀ hσ3 (s * t)) :=
  (coe_commutatorElement_adjoint (trialityX₃ K τ₀ s) (trialityX₄ K τ₀ t)).symm.trans
    (congrArg Subtype.val ((even_triality_trace_commutators K τ₀ hσ3).2.1 s t))

include hσ3 in
theorem rel25
    (b e : trialityFixedField K τ₀) :
    ⁅ox₂ σ b, ox₅ σ e⁆ = ox₆ σ (b * e) :=
  (coe_commutatorElement_adjoint (trialityX₂ K τ₀ b) (trialityX₅ K τ₀ e)).symm.trans
    (congrArg Subtype.val ((even_triality_trace_commutators K τ₀ hσ3).2.2.1 b e))

include hσ3 in
theorem comm15
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₁ σ a) (ox₅ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.1 a b)

include hσ3 in
theorem comm16
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₁ σ a) (ox₆ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.1 a b)

include hσ3 in
theorem comm23
    (a : trialityFixedField K τ₀) (b : K) : Commute (ox₂ σ a) (ox₃ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.1 a b)

include hσ3 in
theorem comm24
    (a : trialityFixedField K τ₀) (b : K) : Commute (ox₂ σ a) (ox₄ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm26
    (a b : trialityFixedField K τ₀) : Commute (ox₂ σ a) (ox₆ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm35
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₃ σ a) (ox₅ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm36
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₃ σ a) (ox₆ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm45
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₄ σ a) (ox₅ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm46
    (a : K) (b : trialityFixedField K τ₀) : Commute (ox₄ σ a) (ox₆ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem comm56
    (a b : trialityFixedField K τ₀) : Commute (ox₅ σ a) (ox₆ σ b) :=
  commute_coe ((even_triality_trace_commutators K τ₀ hσ3).2.2.2.2.2.2.2.2.2.2.2.2.1 a b)

include hσ3 in
theorem trace_nondeg
    (s : K) (hs : ∀ t : K, trialityTrace K τ₀ hσ3 (s * t) = 0) : s = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, htr, hnd⟩ :=
    even_triality_trace_commutators K τ₀ hσ3
  exact hnd.1 s fun t => (htr s t).trans (hs t)

include hσ3 in
theorem trace_nondeg'
    (t : K) (ht : ∀ s : K, trialityTrace K τ₀ hσ3 (s * t) = 0) : t = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, htr, hnd⟩ :=
    even_triality_trace_commutators K τ₀ hσ3
  exact hnd.2 t fun s => (htr s t).trans (ht s)

include hσ3 in
theorem trace_fixed (e : trialityFixedField K τ₀) : trialityTrace K τ₀ hσ3 (e : K) = e := by
  apply Subtype.ext
  have he : σ (e : K) = e := e.2
  change (e : K) + σ (e : K) + σ (σ (e : K)) = e
  rw [he, he]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (e : K) * h2

end Relations

section NormalForm

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem coord_exists
    {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) :
    ∃ (a : K) (b : trialityFixedField K τ₀) (c d : K) (e f : trialityFixedField K τ₀),
      g = ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f := by
  obtain ⟨-, -, -, -, -, -, hbij, -, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨⟨a, b, c, d, e, f⟩, -, hzN⟩ := hbij.2.2 hg
  exact ⟨a, b, c, d, e, f, by rw [← hzN]; simp [ox₁, ox₂, ox₃, ox₄, ox₅, ox₆]⟩

include hσ3 in
theorem coord_unique
    {a a' : K} {b b' : trialityFixedField K τ₀} {c c' d d' : K}
    {e e' f f' : trialityFixedField K τ₀}
    (h : ox₁ σ a * ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
      ox₁ σ a' * ox₂ σ b' * ox₃ σ c' * ox₄ σ d' * ox₅ σ e' * ox₆ σ f') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
  obtain ⟨-, -, -, -, -, -, hbij, -, -⟩ := even_triality_positive_orbit_parametrization K σ hσ3
  have := hbij.2.1 (Set.mem_univ (a, b, c, d, e, f)) (Set.mem_univ (a', b', c', d', e', f'))
    (by simpa [ox₁, ox₂, ox₃, ox₄, ox₅, ox₆] using h)
  simpa only [Prod.mk.injEq] using this

end NormalForm

section Weyl

variable {K : Type} [Field K] [CharP K 2] (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom

theorem canonicalRep_conj_charTwo'
    {τ : Tag} (w : WeylGroup τ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (x : K) :
    canonicalRep (coxeterSystem τ) K w * pinnedX τ K α x * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
      pinnedX τ K (w • α) x := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w hα
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h3 : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  rw [h, hε1, one_mul]

theorem weyl_x5_x2
    (b : trialityFixedField K τ₀) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) *
        ox₅ σ b *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))⁻¹ =
      ox₂ σ b := by
  let a₀ : Fin TwistTag.D4.foldedTag.rank := ⟨0, by decide⟩
  have hroot5 : IsRoot TwistTag.D4.tag (trialityRoot 4) := (isRoot_trialityRoot 4 0).1
  have hr0 : TwistTag.D4.orbitReflection a₀ • trialityRoot 4 = trialityRoot 1 := by
    have hw : TwistTag.D4.orbitWord a₀ =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  have := canonicalRep_conj_charTwo' (K := K) (TwistTag.D4.orbitReflection a₀) hroot5 (b : K)
  rw [hr0] at this
  exact this

end Weyl

section Comm12

section Abstract

variable {G : Type*} [Group G]

theorem comm_expand {A Y0 Y1 Y3 M0 M1 M3 N01 N03 N13 P H : G}
    (hA0 : ⁅A, Y0⁆ = M0) (hA1 : ⁅A, Y1⁆ = M1) (hA3 : ⁅A, Y3⁆ = M3)
    (h01 : ⁅Y0, M1⁆ = N01) (h13 : ⁅Y1, M3⁆ = N13) (h03 : ⁅Y0, M3⁆ = N03)
    (hP : ⁅Y0, N13⁆ = P) (hH : ⁅N01, M3⁆ = H)
    (c1 : Commute N01 M1) (c2 : Commute M3 N03) (c3 : Commute M3 N13) (c4 : Commute M3 P)
    (cH3 : Commute H M3) (cH01 : Commute H N01) (cHP : Commute H P) (cH13 : Commute H N13)
    (cH03 : Commute H N03) (c0113 : Commute N01 N13)
    (c0103 : Commute N01 N03) (cP13 : Commute P N13) (cP03 : Commute P N03) :
    ⁅A, Y0 * Y1 * Y3⁆ = M0 * M1 * M3 * (N13 * N03 * N01) * P * H := by
  have rA0 : A * Y0 * A⁻¹ = M0 * Y0 := by rw [← hA0, commutatorElement_def]; group
  have rA1 : A * Y1 * A⁻¹ = M1 * Y1 := by rw [← hA1, commutatorElement_def]; group
  have rA3 : A * Y3 * A⁻¹ = M3 * Y3 := by rw [← hA3, commutatorElement_def]; group
  have r01 : Y0 * M1 * Y0⁻¹ = N01 * M1 := by rw [← h01, commutatorElement_def]; group
  have r13 : Y1 * M3 * Y1⁻¹ = N13 * M3 := by rw [← h13, commutatorElement_def]; group
  have r03 : Y0 * M3 * Y0⁻¹ = N03 * M3 := by rw [← h03, commutatorElement_def]; group
  have rP : Y0 * N13 * Y0⁻¹ = P * N13 := by rw [← hP, commutatorElement_def]; group
  have rH : ∀ w : G, N01 * (M3 * w) = H * (M3 * (N01 * w)) := fun w => by
    rw [← hH, commutatorElement_def]; group
  have s1 : ⁅A, Y0 * Y1 * Y3⁆ =
      (A * Y0 * A⁻¹) * (A * Y1 * A⁻¹) * (A * Y3 * A⁻¹) * (Y3⁻¹ * Y1⁻¹ * Y0⁻¹) := by
    rw [commutatorElement_def]; group
  rw [s1, rA0, rA1, rA3]
  have s2 : M0 * Y0 * (M1 * Y1) * (M3 * Y3) * (Y3⁻¹ * Y1⁻¹ * Y0⁻¹) =
      M0 * Y0 * M1 * (Y1 * M3 * Y1⁻¹) * Y0⁻¹ := by group
  rw [s2, r13]
  have s3 : M0 * Y0 * M1 * (N13 * M3) * Y0⁻¹ =
      M0 * ((Y0 * M1 * Y0⁻¹) * (Y0 * N13 * Y0⁻¹) * (Y0 * M3 * Y0⁻¹)) := by group
  rw [s3, r01, rP, r03]
  simp only [mul_assoc]
  rw [c1.left_comm, ← c2.eq, c3.symm.left_comm, c4.symm.left_comm, rH, cH3.left_comm,
    cH01.left_comm, cHP.left_comm, cH13.left_comm, cH03.eq, cP13.left_comm, cP03.left_comm,
    c0113.left_comm, c0103.left_comm]

end Abstract

section Roots

@[expose] def d4C : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 0]

@[expose] def d4E0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 0, 0]

@[expose] def d4E1 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 0, 0]

@[expose] def d4E3 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 0, 1]

@[expose] def d4M0 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 0]

@[expose] def d4M1 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 0]

@[expose] def d4M3 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 0, 1, 1]

@[expose] def d4N01 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 0]

@[expose] def d4N03 : Fin TwistTag.D4.tag.rank → ℤ := ![1, 0, 1, 1]

@[expose] def d4N13 : Fin TwistTag.D4.tag.rank → ℤ := ![0, 1, 1, 1]

@[expose] def d4P : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 1, 1]

@[expose] def d4H : Fin TwistTag.D4.tag.rank → ℤ := ![1, 1, 2, 1]

end Roots

section D4

variable {K : Type} [Field K] [CharP K 2]

local notation "Xr" => pinnedX TwistTag.D4.tag K

theorem comm_root
    (β : K) :
    ⁅Xr d4C β, Xr d4E0 1 * Xr d4E1 1 * Xr d4E3 1⁆ =
      Xr d4M0 β * Xr d4M1 β * Xr d4M3 β * (Xr d4N13 β * Xr d4N03 β * Xr d4N01 β) * Xr d4P β *
        Xr d4H (β * β) := by
  have hs : ∀ {α γ δ : Fin TwistTag.D4.tag.rank → ℤ}, d4SumB α γ δ = true → ∀ s t : K,
      ⁅Xr α s, Xr γ t⁆ = Xr δ (s * t) := fun h s t => commutator_of_d4SumB h s t
  have hc : ∀ {α γ : Fin TwistTag.D4.tag.rank → ℤ}, d4CommB α γ = true → ∀ s t : K,
      Commute (Xr α s) (Xr γ t) := fun h s t => commute_of_d4CommB h s t
  refine comm_expand (A := Xr d4C β) (Y0 := Xr d4E0 1) (Y1 := Xr d4E1 1) (Y3 := Xr d4E3 1)
    (M0 := Xr d4M0 β) (M1 := Xr d4M1 β) (M3 := Xr d4M3 β) (N01 := Xr d4N01 β)
    (N03 := Xr d4N03 β) (N13 := Xr d4N13 β) (P := Xr d4P β) (H := Xr d4H (β * β))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := hs (α := d4C) (γ := d4E0) (δ := d4M0) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := d4C) (γ := d4E1) (δ := d4M1) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := d4C) (γ := d4E3) (δ := d4M3) (by decide +kernel) β 1
    rwa [mul_one] at this
  · have := hs (α := d4E0) (γ := d4M1) (δ := d4N01) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := d4E1) (γ := d4M3) (δ := d4N13) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := d4E0) (γ := d4M3) (δ := d4N03) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · have := hs (α := d4E0) (γ := d4N13) (δ := d4P) (by decide +kernel) 1 β
    rwa [one_mul] at this
  · exact hs (α := d4N01) (γ := d4M3) (δ := d4H) (by decide +kernel) β β
  · exact hc (α := d4N01) (γ := d4M1) (by decide +kernel) β β
  · exact hc (α := d4M3) (γ := d4N03) (by decide +kernel) β β
  · exact hc (α := d4M3) (γ := d4N13) (by decide +kernel) β β
  · exact hc (α := d4M3) (γ := d4P) (by decide +kernel) β β
  · exact hc (α := d4H) (γ := d4M3) (by decide +kernel) (β * β) β
  · exact hc (α := d4H) (γ := d4N01) (by decide +kernel) (β * β) β
  · exact hc (α := d4H) (γ := d4P) (by decide +kernel) (β * β) β
  · exact hc (α := d4H) (γ := d4N13) (by decide +kernel) (β * β) β
  · exact hc (α := d4H) (γ := d4N03) (by decide +kernel) (β * β) β
  · exact hc (α := d4N01) (γ := d4N13) (by decide +kernel) β β
  · exact hc (α := d4N01) (γ := d4N03) (by decide +kernel) β β
  · exact hc (α := d4P) (γ := d4N13) (by decide +kernel) β β
  · exact hc (α := d4P) (γ := d4N03) (by decide +kernel) β β

variable (σ : K ≃+* K)

local notation "τ₀" => σ.toRingHom

omit [CharP K 2] in
theorem coe_ox₁_one :
    ox₁ σ 1 = pinnedX TwistTag.D4.tag K d4E0 1 * pinnedX TwistTag.D4.tag K d4E1 1 *
      pinnedX TwistTag.D4.tag K d4E3 1 := by
  have h0 : trialityRoot 0 = d4E0 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4E0 = d4E1 := List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4E0 = d4E3 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₁, trialityX₁, coe_trialityOrbitProd, h0, h1, h2, map_one, map_one]

omit [CharP K 2] in
theorem coe_ox₃
    (β : K) (hβ : τ₀ β = β) :
    ox₃ σ β = pinnedX TwistTag.D4.tag K d4M0 β * pinnedX TwistTag.D4.tag K d4M1 β *
      pinnedX TwistTag.D4.tag K d4M3 β := by
  have h0 : trialityRoot 2 = d4M0 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4M0 = d4M1 := List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4M0 = d4M3 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₃, trialityX₃, coe_trialityOrbitProd, h0, h1, h2, hβ, hβ]

omit [CharP K 2] in
theorem coe_ox₄
    (β : K) (hβ : τ₀ β = β) :
    ox₄ σ β = pinnedX TwistTag.D4.tag K d4N13 β * pinnedX TwistTag.D4.tag K d4N03 β *
      pinnedX TwistTag.D4.tag K d4N01 β := by
  have h0 : trialityRoot 3 = d4N13 := List.ofFn_injective (by decide +kernel)
  have h1 : permLattice TwistTag.D4.perm d4N13 = d4N03 := List.ofFn_injective (by decide +kernel)
  have h2 : permLattice (TwistTag.D4.perm ^ 2) d4N13 = d4N01 :=
    List.ofFn_injective (by decide +kernel)
  rw [ox₄, trialityX₄, coe_trialityOrbitProd, h0, h1, h2, hβ, hβ]

omit [CharP K 2] in
theorem trialityRoot_one' : trialityRoot 1 = d4C := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem trialityRoot_four' : trialityRoot 4 = d4P := List.ofFn_injective (by decide +kernel)

omit [CharP K 2] in
theorem trialityRoot_five' : trialityRoot 5 = d4H := List.ofFn_injective (by decide +kernel)

theorem ox₂_comm_ox₁
    (β : trialityFixedField K τ₀) :
    ⁅ox₂ σ β, ox₁ σ 1⁆ = ox₃ σ (β : K) * ox₄ σ (β : K) * ox₅ σ β * ox₆ σ (β * β) := by
  have hβ : τ₀ (β : K) = (β : K) := β.2
  rw [coe_ox₁_one, coe_ox₃ σ _ hβ, coe_ox₄ σ _ hβ]
  have e2 : ox₂ σ β = pinnedX TwistTag.D4.tag K d4C (β : K) := by
    rw [← trialityRoot_one']; rfl
  have e5 : ox₅ σ β = pinnedX TwistTag.D4.tag K d4P (β : K) := by
    rw [← trialityRoot_four']; rfl
  have e6 : ox₆ σ (β * β) = pinnedX TwistTag.D4.tag K d4H ((β : K) * (β : K)) := by
    rw [← trialityRoot_five']; rfl
  rw [e2, e5, e6]
  exact comm_root (β : K)

end D4

end Comm12

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
