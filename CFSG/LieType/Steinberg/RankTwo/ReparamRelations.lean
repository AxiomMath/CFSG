module

public import CFSG.LieType.Steinberg.PartBProof

public noncomputable section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.LieType.Steinberg
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {K : Type*} [Group K]

variable (Φ k) in
@[expose] def relBk (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) :
    Set (FreeGroup (ChevGen Φ k)) :=
  {w | ∃ α ∈ Φ.roots, ∃ β ∈ Φ.roots, α + β ≠ 0 ∧ ∃ c d : k,
    w = ⁅chevOf (Φ := Φ) α c, chevOf (Φ := Φ) β d⁆ *
      ((O.list α β).map fun p =>
        chevOf (Φ := Φ) (p.1 • α + p.2 • β) (C α β p * c ^ p.1 * d ^ p.2)).prod⁻¹}

theorem relB_eq_relBk (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ) :
    relB Φ k O C = relBk Φ k O fun α β p => (C α β p : k) :=
  rfl

@[expose] def CommutatorFormulaK (x : (ι → ℤ) → k → K) (O : CommOrder Φ)
    (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k) : Prop :=
  ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ∀ c d : k,
    ⁅x α c, x β d⁆ =
      ((O.list α β).map fun p => x (p.1 • α + p.2 • β) (C α β p * c ^ p.1 * d ^ p.2)).prod

theorem commutatorFormula_iff_K {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ} :
    CommutatorFormula x O C ↔ CommutatorFormulaK x O fun α β p => (C α β p : k) :=
  Iff.rfl

theorem chevEval_relsK {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k}
    (hadd : ∀ γ ∈ Φ.roots, ∀ c d, x γ (c + d) = x γ c * x γ d)
    (hcomm : CommutatorFormulaK x O C) :
    ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · simp only [map_mul, map_inv, lift_chevEval_chevOf x hγ, hadd γ hγ, mul_inv_cancel]
  · rw [map_mul, map_inv, map_commutatorElement, lift_chevEval_chevOf x hα,
      lift_chevEval_chevOf x hβ, map_list_prod, List.map_map, mul_inv_eq_one,
      hcomm α hα β hβ hαβ c d]
    refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
    rw [Function.comp_apply, lift_chevEval_chevOf x ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2]

theorem add_of_rels {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k}
    (h : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1) :
    ∀ γ ∈ Φ.roots, ∀ c d, x γ (c + d) = x γ c * x γ d := by
  intro γ hγ c d
  have h1 := h _ (Or.inl ⟨γ, hγ, c, d, rfl⟩)
  rw [map_mul, map_mul, map_inv, lift_chevEval_chevOf x hγ, lift_chevEval_chevOf x hγ,
    lift_chevEval_chevOf x hγ, mul_inv_eq_one] at h1
  exact h1.symm

theorem commutatorFormulaK_of_rels {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k}
    (h : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1) :
    CommutatorFormulaK x O C := by
  intro α hα β hβ hαβ c d
  have h1 := h _ (Or.inr ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  rw [map_mul, map_inv, map_commutatorElement, lift_chevEval_chevOf x hα,
    lift_chevEval_chevOf x hβ, map_list_prod, List.map_map, mul_inv_eq_one] at h1
  rw [h1]
  refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
  rw [Function.comp_apply, lift_chevEval_chevOf x ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2]

theorem existsUnique_hom_of_bijective {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → k}
    (hrel : ∀ r ∈ relA Φ k ∪ relBk Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hrel)) {H : Type*} [Group H]
    {y : (ι → ℤ) → k → H} (hyA : ∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d)
    (hyB : CommutatorFormulaK y O C) :
    ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c := by
  have hy := chevEval_relsK hyA hyB
  set e := MulEquiv.ofBijective (PresentedGroup.toGroup hrel) hbij with he
  have hex : ∀ γ (hγ : γ ∈ Φ.roots) c,
      e.symm (x γ c) = PresentedGroup.of (rels := relA Φ k ∪ relBk Φ k O C) (⟨γ, hγ⟩, c) :=
    fun γ hγ c => e.symm_apply_eq.2 (by
      rw [he, MulEquiv.ofBijective_apply, PresentedGroup.toGroup.of]
      rfl)
  refine ⟨(PresentedGroup.toGroup hy).comp e.symm.toMonoidHom, fun γ hγ c => ?_,
    fun φ hφ => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hex γ hγ c, PresentedGroup.toGroup.of]
    rfl
  · have h1 : φ.comp e.toMonoidHom = PresentedGroup.toGroup hy :=
      PresentedGroup.ext fun g => by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, PresentedGroup.toGroup.of]
        have : e (PresentedGroup.of g) = x g.1.1 g.2 := PresentedGroup.toGroup.of hrel
        rw [this, hφ g.1.1 g.1.2 g.2]
        rfl
    refine MonoidHom.ext fun z => ?_
    rw [MonoidHom.comp_apply, ← h1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.coe_toMonoidHom, e.apply_symm_apply]

theorem existsUnique_hom_of_relB_bijective {x : (ι → ℤ) → k → K} {O : CommOrder Φ}
    {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
    (hrel : ∀ r ∈ relA Φ k ∪ relB Φ k O C, FreeGroup.lift (chevEval x) r = 1)
    (hbij : Function.Bijective (PresentedGroup.toGroup hrel)) {H : Type*} [Group H]
    {y : (ι → ℤ) → k → H} (hy : ChevRels O C y) :
    ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c :=
  existsUnique_hom_of_bijective (C := fun α β p => (C α β p : k)) hrel hbij hy.add hy.comm

theorem existsUnique_hom_of_presentationB {x : (ι → ℤ) → k → K}
    (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ) {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
    (hC : CommutatorFormula x O C) {H : Type*} [Group H] {y : (ι → ℤ) → k → H}
    (hy : ChevRels O C y) :
    ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c := by
  obtain ⟨h, hbij⟩ := (hx O).2 C hC
  exact existsUnique_hom_of_relB_bijective h hbij hy

end CFSG.LieType.Steinberg.RankTwo
