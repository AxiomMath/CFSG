module

public import CFSG.GH74.GLS.IVK.Proofs2.NatModGrp
public import Mathlib.RepresentationTheory.Irreducible
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Matrix

section Natural

variable {F : Type} [Field F]

theorem exists_mulVec_e1 {v : Fin 2 → F} (hv : v ≠ 0) :
    ∃ g : SL2 F, (g : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v := by
  by_cases ha : v 0 = 0
  · have hb : v 1 ≠ 0 := by
      intro hb
      apply hv
      ext i
      fin_cases i <;> simp [ha, hb]
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [det_fin_two, hb]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [ha, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [det_fin_two, ha]⟩, ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_mulVec_eq {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL2 F, (g : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
  obtain ⟨g, hg⟩ := exists_mulVec_e1 hv
  obtain ⟨h, hh⟩ := exists_mulVec_e1 hw
  refine ⟨h * g⁻¹, ?_⟩
  rw [← hg, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_assoc, inv_mul_cancel,
    mul_one, hh]

theorem second_coord_eq_zero_of_fixed {v : Fin 2 → F}
    (h : ∀ c : F, (upperSL c : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v 1 = 0 := by
  have := congrFun (h 1) 0
  simpa [coe_upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this

theorem eq_smul_of_equivariant (f : (Fin 2 → F) →+ (Fin 2 → F))
    (hf : ∀ (g : SL2 F) (v : Fin 2 → F),
      f ((g : Matrix (Fin 2) (Fin 2) F).mulVec v) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (f v)) :
    ∃ a : F, ∀ v, f v = a • v := by
  have hfix : ∀ c : F, (upperSL c : Matrix (Fin 2) (Fin 2) F).mulVec (f ![1, 0]) = f ![1, 0] := by
    intro c
    have h1 : (upperSL c : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = ![1, 0] := by
      ext i
      fin_cases i <;> simp [coe_upperSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [← hf, h1]
  have h2 := second_coord_eq_zero_of_fixed hfix
  obtain ⟨a, ha⟩ : ∃ a : F, a = f ![1, 0] 0 := ⟨_, rfl⟩
  have h3 : f ![1, 0] = a • ![1, 0] := by
    ext i
    fin_cases i <;> simp [h2, ha]
  refine ⟨a, fun v => ?_⟩
  by_cases hv : v = 0
  · rw [hv, map_zero, smul_zero]
  · obtain ⟨g, hg⟩ := exists_mulVec_e1 hv
    rw [← hg, hf, h3, Matrix.mulVec_smul]

end Natural

section Rep

variable {F : Type} [Field F] {p : ℕ} {K : Type} [Group K] {V : Type}
  [AddCommGroup V] [Module (ZMod p) V]

@[expose] def IsNatIso (ψ : K →* SL2 F) (ρ : Representation (ZMod p) K V) (Φ : (Fin 2 → F) ≃+ V) :
    Prop :=
  ∀ (k : K) (v : Fin 2 → F), Φ ((ψ k : Matrix (Fin 2) (Fin 2) F).mulVec v) = ρ k (Φ v)

theorem IsNatIso.exists_apply_eq {ψ : K →* SL2 F} (hψ : Function.Surjective ψ)
    {ρ : Representation (ZMod p) K V} {Φ : (Fin 2 → F) ≃+ V} (hΦ : IsNatIso ψ ρ Φ) {v w : V}
    (hv : v ≠ 0) (hw : w ≠ 0) : ∃ k : K, ρ k v = w := by
  obtain ⟨v', rfl⟩ := Φ.surjective v
  obtain ⟨w', rfl⟩ := Φ.surjective w
  have hv' : v' ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hw' : w' ≠ 0 := fun h => hw (by rw [h, map_zero])
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv' hw'
  obtain ⟨k, rfl⟩ := hψ g
  exact ⟨k, by rw [← hΦ, hg]⟩

theorem isIrreducible_of_transitive [Fact p.Prime] [Nontrivial V] (ρ : Representation (ZMod p) K V)
    (htr : ∀ v w : V, v ≠ 0 → w ≠ 0 → ∃ k : K, ρ k v = w) : Representation.IsIrreducible ρ := by
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hnt : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, fun h => by
    have : v₀ ∈ (⊤ : Subrepresentation ρ) := Submodule.mem_top
    rw [← h] at this
    exact hv₀ (Submodule.mem_bot _ |>.1 this)⟩⟩
  refine { toNontrivial := hnt, eq_bot_or_eq_top := fun a => ?_ }
  by_cases h : ∃ v ∈ a, v ≠ 0
  · right
    obtain ⟨v, hva, hv⟩ := h
    apply Subrepresentation.toSubmodule_injective
    refine Submodule.eq_top_iff'.2 fun w => ?_
    by_cases hw : w = 0
    · rw [hw]; exact a.toSubmodule.zero_mem
    · obtain ⟨k, hk⟩ := htr v w hv hw
      rw [← hk]
      exact a.apply_mem_toSubmodule k hva
  · left
    push Not at h
    apply Subrepresentation.toSubmodule_injective
    refine (Submodule.eq_bot_iff _).2 fun w hw => h w hw

@[expose] noncomputable def scalarLin (Φ : (Fin 2 → F) ≃+ V) (c : F) : V →ₗ[ZMod p] V :=
  AddMonoidHom.toZModLinearMap p ((Φ : (Fin 2 → F) →+ V).comp
    ((({ toFun := fun w => c • w, map_zero' := smul_zero c, map_add' := smul_add c } :
      (Fin 2 → F) →+ (Fin 2 → F))).comp (Φ.symm : V →+ (Fin 2 → F))))

theorem scalarLin_apply (Φ : (Fin 2 → F) ≃+ V) (c : F) (v : V) :
    scalarLin (p := p) Φ c v = Φ (c • Φ.symm v) := rfl

theorem IsNatIso.symm_apply {ψ : K →* SL2 F} {ρ : Representation (ZMod p) K V}
    {Φ : (Fin 2 → F) ≃+ V} (hΦ : IsNatIso ψ ρ Φ) (k : K) (v : V) :
    Φ.symm (ρ k v) = (ψ k : Matrix (Fin 2) (Fin 2) F).mulVec (Φ.symm v) := by
  apply Φ.injective
  rw [hΦ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[expose] noncomputable def scalarIM {ψ : K →* SL2 F} {ρ : Representation (ZMod p) K V}
    {Φ : (Fin 2 → F) ≃+ V} (hΦ : IsNatIso ψ ρ Φ) (c : F) : ρ.IntertwiningMap ρ where
  toLinearMap := scalarLin Φ c
  isIntertwining' k := by
    ext v
    show Φ (c • Φ.symm (ρ k v)) = ρ k (Φ (c • Φ.symm v))
    rw [hΦ.symm_apply, ← hΦ, Matrix.mulVec_smul]

@[expose] noncomputable def scalarRingHom {ψ : K →* SL2 F} {ρ : Representation (ZMod p) K V}
    {Φ : (Fin 2 → F) ≃+ V} (hΦ : IsNatIso ψ ρ Φ) : F →+* ρ.IntertwiningMap ρ where
  toFun := scalarIM hΦ
  map_one' := by
    ext v
    show Φ ((1 : F) • Φ.symm v) = v
    rw [one_smul, AddEquiv.apply_symm_apply]
  map_mul' c d := by
    ext v
    show Φ ((c * d) • Φ.symm v) = Φ (c • Φ.symm (Φ (d • Φ.symm v)))
    rw [AddEquiv.symm_apply_apply, mul_smul]
  map_zero' := by
    ext v
    show Φ ((0 : F) • Φ.symm v) = 0
    rw [zero_smul, map_zero]
  map_add' c d := by
    ext v
    show Φ ((c + d) • Φ.symm v) = Φ (c • Φ.symm v) + Φ (d • Φ.symm v)
    rw [add_smul, map_add]

theorem scalarRingHom_bijective {ψ : K →* SL2 F} (hψ : Function.Surjective ψ)
    {ρ : Representation (ZMod p) K V} {Φ : (Fin 2 → F) ≃+ V} (hΦ : IsNatIso ψ ρ Φ) :
    Function.Bijective (scalarRingHom hΦ) := by
  constructor
  · intro c d h
    have h1 := congrArg (fun f : ρ.IntertwiningMap ρ => f.toLinearMap (Φ ![1, 0])) h
    have h2 : Φ (c • ![1, 0]) = Φ (d • ![1, 0]) := by
      simpa [scalarRingHom, scalarIM, scalarLin_apply] using h1
    have h3 := congrFun (Φ.injective h2) 0
    simpa using h3
  · intro f
    let g : (Fin 2 → F) →+ (Fin 2 → F) :=
      (Φ.symm : V →+ (Fin 2 → F)).comp ((f.toLinearMap : V →+ V).comp (Φ : (Fin 2 → F) →+ V))
    have hg : ∀ (s : SL2 F) (v : Fin 2 → F),
        g ((s : Matrix (Fin 2) (Fin 2) F).mulVec v) = (s : Matrix (Fin 2) (Fin 2) F).mulVec (g v) := by
      intro s v
      obtain ⟨k, rfl⟩ := hψ s
      have h1 : f.toLinearMap (ρ k (Φ v)) = ρ k (f.toLinearMap (Φ v)) :=
        LinearMap.congr_fun (f.isIntertwining' k) (Φ v)
      show Φ.symm (f.toLinearMap (Φ ((ψ k : Matrix (Fin 2) (Fin 2) F).mulVec v))) =
        (ψ k : Matrix (Fin 2) (Fin 2) F).mulVec (Φ.symm (f.toLinearMap (Φ v)))
      rw [hΦ, h1, hΦ.symm_apply]
    obtain ⟨a, ha⟩ := eq_smul_of_equivariant g hg
    refine ⟨a, ?_⟩
    ext v
    obtain ⟨v', rfl⟩ := Φ.surjective v
    show Φ (a • Φ.symm (Φ v')) = f.toLinearMap (Φ v')
    have h2 : Φ.symm (f.toLinearMap (Φ v')) = a • v' := ha v'
    rw [AddEquiv.symm_apply_apply, ← h2, AddEquiv.apply_symm_apply]

theorem IsNatIso.nonempty_linearEquiv {V' : Type} [AddCommGroup V'] [Module (ZMod p) V']
    {ψ : K →* SL2 F} {ρ : Representation (ZMod p) K V} {ρ' : Representation (ZMod p) K V'}
    {Φ : (Fin 2 → F) ≃+ V} {Φ' : (Fin 2 → F) ≃+ V'} (hΦ : IsNatIso ψ ρ Φ) (hΦ' : IsNatIso ψ ρ' Φ') :
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra (ZMod p) K] ρ'.asModule) := by
  let Ψ : V ≃+ V' := Φ.symm.trans Φ'
  have hΨ : ∀ (k : K) (v : V), Ψ (ρ k v) = ρ' k (Ψ v) := by
    intro k v
    show Φ' (Φ.symm (ρ k v)) = ρ' k (Φ' (Φ.symm v))
    rw [hΦ.symm_apply, hΦ']
  let f : ρ.IntertwiningMap ρ' :=
    ⟨AddMonoidHom.toZModLinearMap p (Ψ : V →+ V'), fun k => by
      ext v
      exact hΨ k v⟩
  let g : ρ'.IntertwiningMap ρ :=
    ⟨AddMonoidHom.toZModLinearMap p (Ψ.symm : V' →+ V), fun k => by
      ext v
      show Ψ.symm (ρ' k v) = ρ k (Ψ.symm v)
      apply Ψ.injective
      rw [AddEquiv.apply_symm_apply, hΨ, AddEquiv.apply_symm_apply]⟩
  refine ⟨LinearEquiv.ofLinearMap (Representation.IntertwiningMap.equivLinearMapAsModule ρ ρ' f)
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ' ρ g) ?_ ?_⟩
  · ext v
    exact Ψ.apply_symm_apply v
  · ext v
    exact Ψ.symm_apply_apply v

end Rep

end CFSG.GH74.GLS.IVK.Proofs2
