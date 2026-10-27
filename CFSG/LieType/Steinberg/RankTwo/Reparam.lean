module

public import CFSG.LieType.Steinberg.RankTwo.ReparamRelations

public noncomputable section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.LieType.Steinberg
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {K : Type*} [Group K]

@[expose] def reparam (x : (ι → ℤ) → k → K) (η : (ι → ℤ) → kˣ) : (ι → ℤ) → k → K :=
  fun γ c => x γ (η γ * c)

@[expose] def reparamConst (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) (η : (ι → ℤ) → kˣ) :
    (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k :=
  fun α β p => C α β p * (η α : k) ^ p.1 * (η β : k) ^ p.2 *
    ((η (p.1 • α + p.2 • β))⁻¹ : kˣ)

@[expose] def substGen (η : (ι → ℤ) → kˣ) (g : ChevGen Φ k) : ChevGen Φ k :=
  (g.1, (η g.1 : k) * g.2)

theorem map_substGen_chevOf (η : (ι → ℤ) → kˣ) (γ : ι → ℤ) (c : k) :
    FreeGroup.map (substGen (Φ := Φ) η) (chevOf (Φ := Φ) γ c) =
      chevOf (Φ := Φ) γ ((η γ : k) * c) := by
  unfold chevOf
  split_ifs with h
  · rw [FreeGroup.map.of]
    rfl
  · exact map_one _

theorem mapsTo_substGen (O : CommOrder Φ) (η : (ι → ℤ) → kˣ)
    {C₁ C₂ : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k}
    (hC : ∀ α β p, (η (p.1 • α + p.2 • β) : k) * C₁ α β p =
      C₂ α β p * (η α : k) ^ p.1 * (η β : k) ^ p.2) :
    (relA Φ k ∪ relBk Φ k O C₁).MapsTo (FreeGroup.map (substGen η))
      (relA Φ k ∪ relBk Φ k O C₂) := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · refine Or.inl ⟨γ, hγ, η γ * c, η γ * d, ?_⟩
    simp only [map_mul, map_inv, map_substGen_chevOf, mul_add]
  · refine Or.inr ⟨α, hα, β, hβ, hαβ, η α * c, η β * d, ?_⟩
    rw [map_mul, map_inv, map_commutatorElement, map_substGen_chevOf, map_substGen_chevOf,
      map_list_prod, List.map_map]
    congr 3
    refine List.map_congr_left fun p _ => ?_
    rw [Function.comp_apply, map_substGen_chevOf]
    congr 1
    have h := hC α β p
    rw [mul_pow, mul_pow]
    linear_combination c ^ p.1 * d ^ p.2 * h

omit [Fintype ι] [DecidableEq ι] in
theorem reparamConst_compat (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) (η : (ι → ℤ) → kˣ)
    (α β : ι → ℤ) (p : ℕ × ℕ) :
    (η (p.1 • α + p.2 • β) : k) * reparamConst C η α β p =
      C α β p * (η α : k) ^ p.1 * (η β : k) ^ p.2 := by
  have h := Units.mul_inv (η (p.1 • α + p.2 • β))
  simp only [reparamConst]
  linear_combination C α β p * (η α : k) ^ p.1 * (η β : k) ^ p.2 * h

omit [Fintype ι] [DecidableEq ι] in
theorem reparamConst_compat_inv (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) (η : (ι → ℤ) → kˣ)
    (α β : ι → ℤ) (p : ℕ × ℕ) :
    ((η⁻¹ (p.1 • α + p.2 • β) : kˣ) : k) * C α β p =
      reparamConst C η α β p * ((η⁻¹ α : kˣ) : k) ^ p.1 * ((η⁻¹ β : kˣ) : k) ^ p.2 := by
  have ha := Units.mul_inv (η α)
  have hb := Units.mul_inv (η β)
  simp only [reparamConst, Pi.inv_apply]
  have e1 : ((η α : k)) ^ p.1 * (((η α)⁻¹ : kˣ) : k) ^ p.1 = 1 := by
    rw [← mul_pow, ha, one_pow]
  have e2 : ((η β : k)) ^ p.2 * (((η β)⁻¹ : kˣ) : k) ^ p.2 = 1 := by
    rw [← mul_pow, hb, one_pow]
  linear_combination (-(C α β p) * (((η (p.1 • α + p.2 • β))⁻¹ : kˣ) : k)) *
    ((((η β : k)) ^ p.2 * (((η β)⁻¹ : kˣ) : k) ^ p.2) * e1 + e2)

theorem substGen_substGen_inv (η : (ι → ℤ) → kˣ) (g : ChevGen Φ k) :
    substGen η (substGen η⁻¹ g) = g := by
  obtain ⟨γ, c⟩ := g
  simp only [substGen, Pi.inv_apply, ← mul_assoc, Units.mul_inv, one_mul]

theorem substGen_inv_substGen (η : (ι → ℤ) → kˣ) (g : ChevGen Φ k) :
    substGen η⁻¹ (substGen η g) = g := by
  obtain ⟨γ, c⟩ := g
  simp only [substGen, Pi.inv_apply, ← mul_assoc, Units.inv_mul, one_mul]

variable (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) (η : (ι → ℤ) → kˣ)

@[expose] def substHom :
    PresentedGroup (relA Φ k ∪ relBk Φ k O (reparamConst C η)) →*
      PresentedGroup (relA Φ k ∪ relBk Φ k O C) :=
  PresentedGroup.map (FreeGroup.map (substGen η)) (mapsTo_substGen O η (reparamConst_compat C η))

@[expose] def substHomInv :
    PresentedGroup (relA Φ k ∪ relBk Φ k O C) →*
      PresentedGroup (relA Φ k ∪ relBk Φ k O (reparamConst C η)) :=
  PresentedGroup.map (FreeGroup.map (substGen η⁻¹))
    (mapsTo_substGen O η⁻¹ (reparamConst_compat_inv C η))

theorem substHom_of (g : ChevGen Φ k) :
    substHom O C η (PresentedGroup.of g) = PresentedGroup.of (substGen η g) := by
  change PresentedGroup.mk _ (FreeGroup.map (substGen η) (FreeGroup.of g)) = _
  rw [FreeGroup.map.of]
  rfl

theorem substHomInv_of (g : ChevGen Φ k) :
    substHomInv O C η (PresentedGroup.of g) = PresentedGroup.of (substGen η⁻¹ g) := by
  change PresentedGroup.mk _ (FreeGroup.map (substGen η⁻¹) (FreeGroup.of g)) = _
  rw [FreeGroup.map.of]
  rfl

theorem substHom_comp_substHomInv :
    (substHom O C η).comp (substHomInv O C η) = MonoidHom.id _ :=
  PresentedGroup.ext fun g => by
    rw [MonoidHom.comp_apply, substHomInv_of, substHom_of, substGen_substGen_inv]
    rfl

theorem substHomInv_comp_substHom :
    (substHomInv O C η).comp (substHom O C η) = MonoidHom.id _ :=
  PresentedGroup.ext fun g => by
    rw [MonoidHom.comp_apply, substHom_of, substHomInv_of, substGen_inv_substGen]
    rfl

theorem substHom_bijective : Function.Bijective (substHom O C η) := by
  refine ⟨Function.LeftInverse.injective (g := substHomInv O C η) fun z => ?_,
    Function.RightInverse.surjective (g := substHomInv O C η) fun z => ?_⟩
  · exact DFunLike.congr_fun (substHomInv_comp_substHom O C η) z
  · exact DFunLike.congr_fun (substHom_comp_substHomInv O C η) z

variable {O C η}

theorem reparam_add {x : (ι → ℤ) → k → K}
    (hadd : ∀ γ ∈ Φ.roots, ∀ c d, x γ (c + d) = x γ c * x γ d) :
    ∀ γ ∈ Φ.roots, ∀ c d, reparam x η γ (c + d) = reparam x η γ c * reparam x η γ d :=
  fun γ hγ c d => by simp only [reparam, mul_add, hadd γ hγ]

theorem commutatorFormulaK_reparam {x : (ι → ℤ) → k → K} (hcomm : CommutatorFormulaK x O C) :
    CommutatorFormulaK (reparam x η) O (reparamConst C η) := by
  intro α hα β hβ hαβ c d
  simp only [reparam]
  rw [hcomm α hα β hβ hαβ]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  congr 1
  rw [mul_pow, mul_pow]
  linear_combination (-(c ^ p.1 * d ^ p.2)) * reparamConst_compat C η α β p

theorem reparam_rels {x : (ι → ℤ) → k → K}
    (hrel : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1) :
    ∀ r ∈ relA Φ k ∪ relBk Φ k O (reparamConst C η),
      FreeGroup.lift (chevEval (reparam x η)) r = 1 :=
  chevEval_relsK (reparam_add (add_of_rels hrel)) (commutatorFormulaK_reparam
    (commutatorFormulaK_of_rels hrel))

theorem toGroup_reparam_eq {x : (ι → ℤ) → k → K}
    (hrel : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1) :
    PresentedGroup.toGroup (reparam_rels (η := η) hrel) =
      (PresentedGroup.toGroup hrel).comp (substHom O C η) :=
  PresentedGroup.ext fun g => by
    rw [MonoidHom.comp_apply, substHom_of, PresentedGroup.toGroup.of, PresentedGroup.toGroup.of]
    rfl

theorem reparam_bijective {x : (ι → ℤ) → k → K}
    (hrel : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hrel)) :
    Function.Bijective (PresentedGroup.toGroup (reparam_rels (η := η) hrel)) := by
  rw [toGroup_reparam_eq hrel, MonoidHom.coe_comp]
  exact hbij.comp (substHom_bijective O C η)

theorem existsUnique_hom_reparam {x : (ι → ℤ) → k → K}
    (hrel : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hrel)) {H : Type*} [Group H]
    {y : (ι → ℤ) → k → H} (hyA : ∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d)
    (hyB : CommutatorFormulaK y O (reparamConst C η)) :
    ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (reparam x η γ c) = y γ c :=
  existsUnique_hom_of_bijective (reparam_rels hrel) (reparam_bijective hrel hbij) hyA hyB

omit [Fintype ι] [DecidableEq ι] [Group K] in
theorem reparam_one (x : (ι → ℤ) → k → K) : reparam x 1 = x := by
  funext γ c
  simp [reparam]

omit [Fintype ι] [DecidableEq ι] in
theorem reparamConst_one (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) : reparamConst C 1 = C := by
  funext α β p
  simp [reparamConst]

omit [Fintype ι] [DecidableEq ι] [Group K] in
theorem range_reparam (x : (ι → ℤ) → k → K) (η : (ι → ℤ) → kˣ) (γ : ι → ℤ) :
    Set.range (reparam x η γ) = Set.range (x γ) := by
  refine Set.ext fun g => ⟨?_, ?_⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨c, rfl⟩
    refine ⟨((η γ)⁻¹ : kˣ) * c, ?_⟩
    simp only [reparam, ← mul_assoc, Units.mul_inv, one_mul]

theorem isParametrization_reparam {X : (ι → ℤ) → Subgroup K} {x : (ι → ℤ) → k → K}
    (hx : IsParametrization (Φ := Φ) X x) (η : (ι → ℤ) → kˣ) :
    IsParametrization (Φ := Φ) X (reparam x η) := by
  intro γ hγ
  obtain ⟨hmem, hadd, hinj⟩ := hx γ hγ
  refine ⟨fun g => ?_, fun c d => ?_, fun c d h => ?_⟩
  · rw [hmem g]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨((η γ)⁻¹ : kˣ) * c, by simp only [reparam, ← mul_assoc, Units.mul_inv, one_mul]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, rfl⟩
  · simp only [reparam, mul_add, hadd]
  · exact (Units.mul_right_inj (η γ)).1 (hinj h)

universe w

theorem reparametrization {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
    (hrel : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hrel)) (η : (ι → ℤ) → kˣ) :
    CommutatorFormulaK (reparam x η) O (reparamConst (fun α β p => (C α β p : k)) η) ∧
    (∃ h : ∀ r ∈ relA Φ k ∪ relBk Φ k O (reparamConst (fun α β p => (C α β p : k)) η),
        FreeGroup.lift (chevEval (reparam x η)) r = 1,
      Function.Bijective (PresentedGroup.toGroup h)) ∧
    ∀ (H : Type w) [Group H] (y : (ι → ℤ) → k → H),
      (∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d) →
      CommutatorFormulaK y O (reparamConst (fun α β p => (C α β p : k)) η) →
      ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (reparam x η γ c) = y γ c :=
  ⟨commutatorFormulaK_reparam (commutatorFormulaK_of_rels (C := fun α β p => (C α β p : k)) hrel),
    ⟨reparam_rels (C := fun α β p => (C α β p : k)) hrel, reparam_bijective hrel hbij⟩,
    fun _ _ _ hyA hyB => existsUnique_hom_reparam (C := fun α β p => (C α β p : k)) hrel hbij
      hyA hyB⟩

theorem reparametrization_of_presentationB {x : (ι → ℤ) → k → K}
    (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ) {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula x O C) (η : (ι → ℤ) → kˣ) :
    CommutatorFormulaK (reparam x η) O (reparamConst (fun α β p => (C α β p : k)) η) ∧
    (∃ h : ∀ r ∈ relA Φ k ∪ relBk Φ k O (reparamConst (fun α β p => (C α β p : k)) η),
        FreeGroup.lift (chevEval (reparam x η)) r = 1,
      Function.Bijective (PresentedGroup.toGroup h)) ∧
    ∀ (H : Type w) [Group H] (y : (ι → ℤ) → k → H),
      (∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d) →
      CommutatorFormulaK y O (reparamConst (fun α β p => (C α β p : k)) η) →
      ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (reparam x η γ c) = y γ c := by
  obtain ⟨h, hbij⟩ := (hx O).2 C hC
  exact reparametrization h hbij η

end CFSG.LieType.Steinberg.RankTwo
