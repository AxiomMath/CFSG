module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.EvenTrialityParameterData
public import CFSG.LieType.Chevalley.GraphFixedOrbitParametrization

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

section Data

variable (K) (σ : K ≃+* K)

@[expose] def trialityOuterTorus
    (a : Kˣ) : ModGL TwistTag.D4.tag K :=
  ((List.range 3).map fun j => torusElt TwistTag.D4.tag K
    ((TwistTag.D4.perm ^ j) ⟨0, by decide⟩) (Units.map (σ.toRingHom ^ j).toMonoidHom a)).prod

@[expose] def trialityFixedUnit : (trialityFixedField K σ.toRingHom)ˣ →* Kˣ :=
  Units.map (trialityFixedField K σ.toRingHom).subtype.toMonoidHom

@[expose] def trialityMiddleTorus
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    ModGL TwistTag.D4.tag K :=
  torusElt TwistTag.D4.tag K ⟨2, by decide⟩ (trialityFixedUnit K σ b)

@[expose] def trialityOuterRep
    : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨0, by decide⟩)

@[expose] def trialityMiddleRep
    : ModGL TwistTag.D4.tag K :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection ⟨1, by decide⟩)

end Data

variable {σ : K ≃+* K}

theorem ringEquiv_pow_three_apply (σ : K ≃+* K) (c : K) : (σ ^ 3) c = σ (σ (σ c)) :=
  rfl

theorem norm_mem_trialityFixedField (hσ : σ ^ 3 = 1) (a : K) :
    a * σ a * σ (σ a) ∈ trialityFixedField K σ.toRingHom := by
  have h3 : σ (σ (σ a)) = a := by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  rw [mem_trialityFixedField]
  change σ (a * σ a * σ (σ a)) = a * σ a * σ (σ a)
  rw [map_mul, map_mul, h3]
  ring

variable (σ) in
@[expose] def trialityNorm (hσ : σ ^ 3 = 1) : Kˣ →* (trialityFixedField K σ.toRingHom)ˣ where
  toFun a := Units.mk0 ⟨(a : K) * σ a * σ (σ a), norm_mem_trialityFixedField hσ a⟩ fun h => by
    have h' := congrArg Subtype.val h
    simp only [ZeroMemClass.coe_zero] at h'
    have ha := a.ne_zero
    have h1 := (map_ne_zero σ).2 ha
    have h2 := (map_ne_zero σ).2 h1
    exact mul_ne_zero (mul_ne_zero ha h1) h2 h'
  map_one' := Units.ext (Subtype.ext (by simp))
  map_mul' a b := Units.ext (Subtype.ext (by
    simp only [Units.val_mk0, Units.val_mul, map_mul, Subfield.coe_mul]
    ring))

theorem coe_trialityNorm (hσ : σ ^ 3 = 1) (a : Kˣ) :
    ((trialityFixedUnit K σ (trialityNorm σ hσ a) : Kˣ) : K) = a * σ a * σ (σ a) :=
  rfl

theorem coe_trialityFixedUnit (b : (trialityFixedField K σ.toRingHom)ˣ) :
    ((trialityFixedUnit K σ b : Kˣ) : K) = ((b : trialityFixedField K σ.toRingHom) : K) :=
  rfl

theorem sigma_trialityFixedUnit (b : (trialityFixedField K σ.toRingHom)ˣ) :
    σ ((trialityFixedUnit K σ b : Kˣ) : K) = (trialityFixedUnit K σ b : Kˣ) :=
  (mem_trialityFixedField).1 (b : trialityFixedField K σ.toRingHom).2

@[expose] def d4Tuple (x₀ x₁ x₂ x₃ : Kˣ) : Fin TwistTag.D4.tag.rank → Kˣ :=
  ![x₀, x₁, x₂, x₃]

local notation "vec4" x₀:max x₁:max x₂:max x₃:max => d4Tuple x₀ x₁ x₂ x₃

theorem vec4_mul (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Kˣ) :
    vec4 a₀ a₁ a₂ a₃ * vec4 b₀ b₁ b₂ b₃ = vec4 (a₀ * b₀) (a₁ * b₁) (a₂ * b₂) (a₃ * b₃) := by
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem vec4_eq {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Kˣ} (h₀ : a₀ = b₀) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂)
    (h₃ : a₃ = b₃) : vec4 a₀ a₁ a₂ a₃ = vec4 b₀ b₁ b₂ b₃ := by
  rw [h₀, h₁, h₂, h₃]

theorem eq_of_vec4_eq {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Kˣ}
    (h : vec4 a₀ a₁ a₂ a₃ = vec4 b₀ b₁ b₂ b₃) : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  have h₀ := congrFun h ⟨0, by decide⟩
  have h₁ := congrFun h ⟨1, by decide⟩
  have h₂ := congrFun h ⟨2, by decide⟩
  have h₃ := congrFun h ⟨3, by decide⟩
  exact ⟨h₀, h₁, h₂, h₃⟩

theorem vec4_eta (c : Fin TwistTag.D4.tag.rank → Kˣ) :
    c = vec4 (c ⟨0, by decide⟩) (c ⟨1, by decide⟩) (c ⟨2, by decide⟩) (c ⟨3, by decide⟩) := by
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem torusElt_D4_zero (u : Kˣ) :
    torusElt TwistTag.D4.tag K ⟨0, by decide⟩ u = rootDiagUnit TwistTag.D4.tag
      (vec4 (u ^ (2 : ℤ)) (u ^ (0 : ℤ)) (u ^ (-1 : ℤ)) (u ^ (0 : ℤ))) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem torusElt_D4_one (u : Kˣ) :
    torusElt TwistTag.D4.tag K ⟨1, by decide⟩ u = rootDiagUnit TwistTag.D4.tag
      (vec4 (u ^ (0 : ℤ)) (u ^ (2 : ℤ)) (u ^ (-1 : ℤ)) (u ^ (0 : ℤ))) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem torusElt_D4_two (u : Kˣ) :
    torusElt TwistTag.D4.tag K ⟨2, by decide⟩ u = rootDiagUnit TwistTag.D4.tag
      (vec4 (u ^ (-1 : ℤ)) (u ^ (-1 : ℤ)) (u ^ (2 : ℤ)) (u ^ (-1 : ℤ))) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem torusElt_D4_three (u : Kˣ) :
    torusElt TwistTag.D4.tag K ⟨3, by decide⟩ u = rootDiagUnit TwistTag.D4.tag
      (vec4 (u ^ (0 : ℤ)) (u ^ (0 : ℤ)) (u ^ (-1 : ℤ)) (u ^ (2 : ℤ))) := by
  rw [torusElt_eq_rootDiagUnit]
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem weylElt_conj_D4_zero
    (c₀ c₁ c₂ c₃ : Kˣ) :
    weylElt TwistTag.D4.tag K ⟨0, by decide⟩ 1 *
        rootDiagUnit TwistTag.D4.tag (vec4 c₀ c₁ c₂ c₃) *
        (weylElt TwistTag.D4.tag K ⟨0, by decide⟩ 1)⁻¹ = rootDiagUnit TwistTag.D4.tag
      (vec4 (c₀ * c₀ ^ (-2 : ℤ)) (c₁ * c₀ ^ (0 : ℤ)) (c₂ * c₀ ^ (1 : ℤ)) (c₃ * c₀ ^ (0 : ℤ))) := by
  refine (weylElt_conj_rootDiagUnit (τ := TwistTag.D4.tag) (K := K) (vec4 c₀ c₁ c₂ c₃)
    ⟨0, by decide⟩).trans ?_
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem weylElt_conj_D4_one
    (c₀ c₁ c₂ c₃ : Kˣ) :
    weylElt TwistTag.D4.tag K ⟨1, by decide⟩ 1 *
        rootDiagUnit TwistTag.D4.tag (vec4 c₀ c₁ c₂ c₃) *
        (weylElt TwistTag.D4.tag K ⟨1, by decide⟩ 1)⁻¹ = rootDiagUnit TwistTag.D4.tag
      (vec4 (c₀ * c₁ ^ (0 : ℤ)) (c₁ * c₁ ^ (-2 : ℤ)) (c₂ * c₁ ^ (1 : ℤ)) (c₃ * c₁ ^ (0 : ℤ))) := by
  refine (weylElt_conj_rootDiagUnit (τ := TwistTag.D4.tag) (K := K) (vec4 c₀ c₁ c₂ c₃)
    ⟨1, by decide⟩).trans ?_
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem weylElt_conj_D4_two
    (c₀ c₁ c₂ c₃ : Kˣ) :
    weylElt TwistTag.D4.tag K ⟨2, by decide⟩ 1 *
        rootDiagUnit TwistTag.D4.tag (vec4 c₀ c₁ c₂ c₃) *
        (weylElt TwistTag.D4.tag K ⟨2, by decide⟩ 1)⁻¹ = rootDiagUnit TwistTag.D4.tag
      (vec4 (c₀ * c₂ ^ (1 : ℤ)) (c₁ * c₂ ^ (1 : ℤ)) (c₂ * c₂ ^ (-2 : ℤ)) (c₃ * c₂ ^ (1 : ℤ))) := by
  refine (weylElt_conj_rootDiagUnit (τ := TwistTag.D4.tag) (K := K) (vec4 c₀ c₁ c₂ c₃)
    ⟨2, by decide⟩).trans ?_
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem weylElt_conj_D4_three
    (c₀ c₁ c₂ c₃ : Kˣ) :
    weylElt TwistTag.D4.tag K ⟨3, by decide⟩ 1 *
        rootDiagUnit TwistTag.D4.tag (vec4 c₀ c₁ c₂ c₃) *
        (weylElt TwistTag.D4.tag K ⟨3, by decide⟩ 1)⁻¹ = rootDiagUnit TwistTag.D4.tag
      (vec4 (c₀ * c₃ ^ (0 : ℤ)) (c₁ * c₃ ^ (0 : ℤ)) (c₂ * c₃ ^ (1 : ℤ)) (c₃ * c₃ ^ (-2 : ℤ))) := by
  refine (weylElt_conj_rootDiagUnit (τ := TwistTag.D4.tag) (K := K) (vec4 c₀ c₁ c₂ c₃)
    ⟨3, by decide⟩).trans ?_
  congr 1
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

local notation "σu" => Units.map (RingHom.toMonoidHom (RingEquiv.toRingHom σ))

macro "unit_arith" : tactic => `(tactic| (
  refine Units.ext ?_
  try simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
    Units.val_pow_eq_pow_val, Units.val_one, zpow_neg, zpow_one, zpow_zero, zpow_ofNat,
    map_inv, map_mul, map_one, map_pow, Prod.fst_mul, Prod.snd_mul, Prod.fst_one,
    Prod.snd_one]
  try field_simp
  try ring))

theorem trialityOuterTorus_eq (a : Kˣ) :
    trialityOuterTorus K σ a = torusElt TwistTag.D4.tag K ⟨0, by decide⟩ a *
      torusElt TwistTag.D4.tag K ⟨1, by decide⟩ (σu a) *
      torusElt TwistTag.D4.tag K ⟨3, by decide⟩ (σu (σu a)) := by
  have e1 : (TwistTag.D4.perm ^ 1) ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have e2 : (TwistTag.D4.perm ^ 2) ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
  have e0 : (TwistTag.D4.perm ^ 0) ⟨0, by decide⟩ = ⟨0, by decide⟩ := rfl
  have u0 : Units.map (σ.toRingHom ^ 0).toMonoidHom a = a := Units.ext (by simp)
  have u1 : Units.map (σ.toRingHom ^ 1).toMonoidHom a = σu a := Units.ext (by simp)
  have u2 : Units.map (σ.toRingHom ^ 2).toMonoidHom a = σu (σu a) :=
    Units.ext (by simp [pow_two])
  simp only [trialityOuterTorus, List.range_succ, List.range_zero, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, e0, e1, e2, u0, u1, u2]

theorem trialityOuterTorus_eq_rootDiagUnit
    (a : Kˣ) :
    trialityOuterTorus K σ a = rootDiagUnit TwistTag.D4.tag
      (vec4 (a ^ 2) (σu a ^ 2) (a * σu a * σu (σu a))⁻¹ (σu (σu a) ^ 2)) := by
  rw [trialityOuterTorus_eq, torusElt_D4_zero, torusElt_D4_one, torusElt_D4_three,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul, vec4_mul, vec4_mul]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem trialityMiddleTorus_eq_rootDiagUnit
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ b = rootDiagUnit TwistTag.D4.tag
      (vec4 (trialityFixedUnit K σ b)⁻¹ (trialityFixedUnit K σ b)⁻¹
        (trialityFixedUnit K σ b ^ 2) (trialityFixedUnit K σ b)⁻¹) := by
  rw [trialityMiddleTorus, torusElt_D4_two]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem coe_units_map_sigma (x : Kˣ) : ((σu x : Kˣ) : K) = σ (x : K) :=
  rfl

theorem trialityFixedUnit_inv (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityFixedUnit K σ b⁻¹ = (trialityFixedUnit K σ b)⁻¹ :=
  map_inv _ b

theorem units_map_trialityFixedUnit (b : (trialityFixedField K σ.toRingHom)ˣ) :
    σu (trialityFixedUnit K σ b) = trialityFixedUnit K σ b :=
  Units.ext (sigma_trialityFixedUnit b)

theorem trialityFixedUnit_norm (hσ : σ ^ 3 = 1) (a : Kˣ) :
    trialityFixedUnit K σ (trialityNorm σ hσ a) = a * σu a * σu (σu a) :=
  Units.ext rfl

theorem units_map_three (hσ : σ ^ 3 = 1) (a : Kˣ) : σu (σu (σu a)) = a :=
  Units.ext (by
    change σ (σ (σ (a : K))) = a
    rw [← ringEquiv_pow_three_apply, hσ]
    rfl)

variable (K) in
theorem trialityOuterRep_eq
    : trialityOuterRep K =
    weylElt TwistTag.D4.tag K ⟨0, by decide⟩ 1 *
      (weylElt TwistTag.D4.tag K ⟨1, by decide⟩ 1 *
        weylElt TwistTag.D4.tag K ⟨3, by decide⟩ 1) := by
  have hw : TwistTag.D4.orbitWord ⟨0, by decide⟩ =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
  rw [trialityOuterRep, canonicalRep_orbitReflection, hw]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

variable (K) in
theorem trialityMiddleRep_eq :
    trialityMiddleRep K = weylElt TwistTag.D4.tag K ⟨2, by decide⟩ 1 := by
  have hw : TwistTag.D4.orbitWord ⟨1, by decide⟩ = [⟨2, by decide⟩] := by decide
  rw [trialityMiddleRep, canonicalRep_orbitReflection, hw]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

theorem conj_mul_mul_eq_nested {G : Type*} [Group G] (x y z g : G) :
    x * (y * z) * g * (x * (y * z))⁻¹ = x * (y * (z * g * z⁻¹) * y⁻¹) * x⁻¹ := by
  group

theorem trialityOuterRep_conj_outer
    (a : Kˣ) :
    trialityOuterRep K * trialityOuterTorus K σ a * (trialityOuterRep K)⁻¹ =
      trialityOuterTorus K σ a⁻¹ := by
  rw [trialityOuterRep_eq, conj_mul_mul_eq_nested, trialityOuterTorus_eq_rootDiagUnit,
    weylElt_conj_D4_three, weylElt_conj_D4_one, weylElt_conj_D4_zero,
    trialityOuterTorus_eq_rootDiagUnit]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem trialityMiddleRep_conj_middle
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleRep K * trialityMiddleTorus K σ b * (trialityMiddleRep K)⁻¹ =
      trialityMiddleTorus K σ b⁻¹ := by
  rw [trialityMiddleRep_eq, trialityMiddleTorus_eq_rootDiagUnit, weylElt_conj_D4_two,
    trialityMiddleTorus_eq_rootDiagUnit, trialityFixedUnit_inv]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem trialityOuterRep_conj_middle
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityOuterRep K * trialityMiddleTorus K σ b * (trialityOuterRep K)⁻¹ =
      trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b) := by
  rw [trialityOuterRep_eq, conj_mul_mul_eq_nested, trialityMiddleTorus_eq_rootDiagUnit,
    weylElt_conj_D4_three, weylElt_conj_D4_one, weylElt_conj_D4_zero,
    trialityOuterTorus_eq_rootDiagUnit, units_map_trialityFixedUnit,
    units_map_trialityFixedUnit, ← rootDiagUnit_mul, vec4_mul]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem trialityMiddleRep_conj_outer
    (hσ : σ ^ 3 = 1) (a : Kˣ) :
    trialityMiddleRep K * trialityOuterTorus K σ a * (trialityMiddleRep K)⁻¹ =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ (trialityNorm σ hσ a) := by
  rw [trialityMiddleRep_eq, trialityOuterTorus_eq_rootDiagUnit, weylElt_conj_D4_two,
    trialityMiddleTorus_eq_rootDiagUnit, trialityFixedUnit_norm, ← rootDiagUnit_mul, vec4_mul]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem vec4_one : vec4 (1 : Kˣ) 1 1 1 = 1 := by
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem twist_d4Tuple (c₀ c₁ c₂ c₃ : Kˣ) :
    (fun i => σu (d4Tuple c₀ c₁ c₂ c₃ (TwistTag.D4.perm.symm i))) =
      vec4 (σu c₃) (σu c₀) (σu c₂) (σu c₁) := by
  funext j
  obtain ⟨n, hn⟩ := j
  have hn' : n < 4 := hn
  interval_cases n <;> rfl

theorem trialityOuter_mul_middle_eq
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityOuterTorus K σ a * trialityMiddleTorus K σ b = rootDiagUnit TwistTag.D4.tag
      (vec4 (a ^ 2 * (trialityFixedUnit K σ b)⁻¹) (σu a ^ 2 * (trialityFixedUnit K σ b)⁻¹)
        ((a * σu a * σu (σu a))⁻¹ * trialityFixedUnit K σ b ^ 2)
        (σu (σu a) ^ 2 * (trialityFixedUnit K σ b)⁻¹)) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, trialityMiddleTorus_eq_rootDiagUnit,
    ← rootDiagUnit_mul, vec4_mul]

variable (σ) in
@[expose] def trialityTorusHom :
    Kˣ × (trialityFixedField K σ.toRingHom)ˣ →* ModGL TwistTag.D4.tag K where
  toFun p := trialityOuterTorus K σ p.1 * trialityMiddleTorus K σ p.2
  map_one' := by
    rw [trialityOuter_mul_middle_eq, ← rootDiagUnit_one, ← vec4_one]
    refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith
  map_mul' p q := by
    rw [trialityOuter_mul_middle_eq, trialityOuter_mul_middle_eq, trialityOuter_mul_middle_eq,
      ← rootDiagUnit_mul, vec4_mul]
    refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> unit_arith

theorem trialityTorusHom_apply
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (a, b) = trialityOuterTorus K σ a * trialityMiddleTorus K σ b :=
  rfl

theorem trialityTorusHom_mem_graphFixedTorus
    (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ p ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
  obtain ⟨a, b⟩ := p
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [trialityTorusHom_apply, trialityOuterTorus_eq, trialityMiddleTorus]
    exact mul_mem (mul_mem (mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _))
      (torusElt_mem_torusGroup _ _)) (torusElt_mem_torusGroup _ _)
  · refine (mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).2 ⟨?_, ?_⟩
    · rw [trialityTorusHom_apply, trialityOuterTorus_eq, trialityMiddleTorus]
      exact mul_mem (mul_mem (mul_mem (torusElt_mem_adjointGroup _ _)
        (torusElt_mem_adjointGroup _ _)) (torusElt_mem_adjointGroup _ _))
        (torusElt_mem_adjointGroup _ _)
    · rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, twistHom_rootDiagUnit_eq,
        twist_d4Tuple]
      refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_)
      all_goals try simp only [map_mul, map_inv, map_pow, units_map_three hσ,
        units_map_trialityFixedUnit]
      all_goals unit_arith

theorem trialityTorusHom_injective
    [CharP K 2] :
    Function.Injective (trialityTorusHom (K := K) σ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hp
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq, ← rootDiagUnit_one, ← vec4_one] at hp
  obtain ⟨h0, h1, h2, -⟩ := eq_of_vec4_eq (rootDiagUnit_injective hp)
  set A : K := (a : K) with hA
  set B : K := ((trialityFixedUnit K σ b : Kˣ) : K) with hB
  have hA0 : A ≠ 0 := a.ne_zero
  have hB0 : B ≠ 0 := (trialityFixedUnit K σ b).ne_zero
  have e0 : A ^ 2 = B := by
    have := congrArg Units.val h0
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    field_simp at this
    exact this
  have e1 : σ A ^ 2 = B := by
    have := congrArg Units.val h1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    field_simp at this
    exact this
  have hσA : σ A = A := frobenius_inj K 2 (by rw [frobenius_def, frobenius_def, e1, e0])
  have e2 : B ^ 2 = A * σ A * σ (σ A) := by
    have := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_one] at this
    have hN : A * σ A * σ (σ A) ≠ 0 := by
      rw [hσA, hσA]
      exact mul_ne_zero (mul_ne_zero hA0 hA0) hA0
    field_simp at this
    exact this
  rw [hσA, hσA, ← e0] at e2
  have hA1 : A = 1 := by
    have h4 : A ^ 3 * (A - 1) = 0 := by linear_combination e2
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) hA0
    · exact sub_eq_zero.1 h
  have ha : a = 1 := Units.ext hA1
  have hb : b = 1 := by
    refine Units.ext (Subtype.ext ?_)
    change B = 1
    rw [← e0, hA1, one_pow]
  rw [ha, hb]
  rfl

theorem exists_trialityTorusHom_eq
    [Finite K] [CharP K 2] (hσ : σ ^ 3 = 1)
    {h : ModGL TwistTag.D4.tag K} (hh : h ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom) :
    ∃ p, trialityTorusHom σ p = h := by
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hl := compat_of_twistHom_rootDiagUnit
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hhΓ).2
  have p0 : TwistTag.D4.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p1 : TwistTag.D4.perm ⟨1, by decide⟩ = ⟨3, by decide⟩ := by decide
  have p2 : TwistTag.D4.perm ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hl1 := hl ⟨0, by decide⟩
  have hl3 := hl ⟨1, by decide⟩
  have hl2 := hl ⟨2, by decide⟩
  rw [p0] at hl1
  rw [p1] at hl3
  rw [p2] at hl2
  set L0 : K := ((l ⟨0, by decide⟩ : Kˣ) : K) with hL0
  set L2 : K := ((l ⟨2, by decide⟩ : Kˣ) : K) with hL2
  have hL1 : ((l ⟨1, by decide⟩ : Kˣ) : K) = σ L0 := congrArg Units.val hl1
  have hL3 : ((l ⟨3, by decide⟩ : Kˣ) : K) = σ (σ L0) := by
    rw [congrArg Units.val hl3, Units.coe_map, hL1]
    rfl
  have hσL2 : σ L2 = L2 := (congrArg Units.val hl2).symm
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  have hL0z : L0 ≠ 0 := (l ⟨0, by decide⟩).ne_zero
  have hL2z : L2 ≠ 0 := (l ⟨2, by decide⟩).ne_zero
  have hσL0z : σ L0 ≠ 0 := (map_ne_zero σ).2 hL0z
  have hσσL0z : σ (σ L0) ≠ 0 := (map_ne_zero σ).2 hσL0z
  set B : K := L2 ^ 2 * (L0 * σ L0 * σ (σ L0)) with hBdef
  have hBz : B ≠ 0 := mul_ne_zero (pow_ne_zero 2 hL2z)
    (mul_ne_zero (mul_ne_zero hL0z hσL0z) hσσL0z)
  have hσB : σ B = B := by
    rw [hBdef, map_mul, map_pow, hσL2, map_mul, map_mul, h3]
    ring
  have hBmem : B ∈ trialityFixedField K σ.toRingHom := (mem_trialityFixedField).2 hσB
  set b : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨B, hBmem⟩ fun h => hBz (congrArg Subtype.val h) with hb
  have hbB : ((trialityFixedUnit K σ b : Kˣ) : K) = B := rfl
  obtain ⟨R, hR⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (L0 * B)
  have hRz : R ≠ 0 := fun h => mul_ne_zero hL0z hBz (by rw [hR, h, mul_zero])
  set a : Kˣ := Units.mk0 R hRz with ha
  have haR : ((a : Kˣ) : K) = R := rfl
  have hR2 : R ^ 2 = L0 * B := by rw [sq, ← hR]
  have hσR2 : σ R ^ 2 = σ L0 * B := by rw [← map_pow, hR2, map_mul, hσB]
  have hσσR2 : σ (σ R) ^ 2 = σ (σ L0) * B := by rw [← map_pow, hσR2, map_mul, hσB]
  refine ⟨(a, b), ?_⟩
  rw [trialityTorusHom_apply, trialityOuter_mul_middle_eq]
  conv_rhs => rw [vec4_eta l]
  refine congrArg _ (vec4_eq ?_ ?_ ?_ ?_) <;> refine Units.ext ?_ <;>
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      coe_units_map_sigma, hbB, haR]
  · rw [← hL0, hR2]
    field_simp
  · rw [hL1, hσR2]
    field_simp
  · rw [← hL2]
    refine frobenius_inj K 2 ?_
    rw [frobenius_def, frobenius_def]
    have hσRz : σ R ≠ 0 := (map_ne_zero σ).2 hRz
    have hN : R * σ R * σ (σ R) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hRz hσRz) ((map_ne_zero σ).2 hσRz)
    have key : ((R * σ R * σ (σ R))⁻¹ * B ^ 2) ^ 2 * (L0 * σ L0 * σ (σ L0)) = B := by
      rw [mul_pow, inv_pow, mul_pow, mul_pow, hR2, hσR2, hσσR2]
      field_simp
    have hN0 : L0 * σ L0 * σ (σ L0) ≠ 0 := mul_ne_zero (mul_ne_zero hL0z hσL0z) hσσL0z
    refine mul_right_cancel₀ hN0 ?_
    rw [key, hBdef]
  · rw [hL3, hσσR2]
    field_simp

theorem even_triality_faithful_torus_coordinates
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (σ : K ≃+* K) (hσ : σ ^ 3 = 1) :
    graphFixedTorus TwistTag.D4 K σ.toRingHom = graphFixedRootTorus TwistTag.D4 K σ.toRingHom ∧
    (∃ e : (Kˣ × (trialityFixedField K σ.toRingHom)ˣ) ≃*
        graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∀ a b, (e (a, b) : ModGL TwistTag.D4.tag K) =
        trialityOuterTorus K σ a * trialityMiddleTorus K σ b) ∧
    (∀ a : Kˣ, trialityOuterRep K * trialityOuterTorus K σ a * (trialityOuterRep K)⁻¹ =
      trialityOuterTorus K σ a⁻¹) ∧
    (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityMiddleRep K * trialityMiddleTorus K σ b * (trialityMiddleRep K)⁻¹ =
        trialityMiddleTorus K σ b⁻¹) ∧
    (∀ b : (trialityFixedField K σ.toRingHom)ˣ,
      trialityOuterRep K * trialityMiddleTorus K σ b * (trialityOuterRep K)⁻¹ =
        trialityMiddleTorus K σ b * trialityOuterTorus K σ (trialityFixedUnit K σ b)) ∧
    ∀ a : Kˣ, trialityMiddleRep K * trialityOuterTorus K σ a * (trialityMiddleRep K)⁻¹ =
      trialityOuterTorus K σ a * trialityMiddleTorus K σ (trialityNorm σ hσ a) := by
  have h3 : ∀ c : K, σ (σ (σ c)) = c := fun c => by rw [← ringEquiv_pow_three_apply, hσ]; rfl
  have hΓ := (even_triality_fixed_group_eq_root_group K (ringChar.eq K 2) σ h3).1
  have hH0 : graphFixedTorus TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun h hh => by
    rw [← hΓ]
    exact (Subgroup.mem_inf.1 hh).2
  have hH : graphFixedTorus TwistTag.D4 K σ.toRingHom =
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
    rw [graphFixedRootTorus]
    exact (inf_eq_left.2 hH0).symm
  refine ⟨hH, ?_, trialityOuterRep_conj_outer, trialityMiddleRep_conj_middle,
    trialityOuterRep_conj_middle, trialityMiddleRep_conj_outer hσ⟩
  let f : Kˣ × (trialityFixedField K σ.toRingHom)ˣ →*
      graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    (trialityTorusHom σ).codRestrict _ fun p => by
      rw [← hH]
      exact trialityTorusHom_mem_graphFixedTorus hσ p
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => trialityTorusHom_injective (congrArg Subtype.val hpq), fun h => ?_⟩
    have hh : (h : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom := by
      rw [hH]
      exact h.2
    obtain ⟨p, hp⟩ := exists_trialityTorusHom_eq hσ hh
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨MulEquiv.ofBijective f hf, fun a b => rfl⟩

end CFSG.LieType.Chevalley
