module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Inner

variable {P Q : Type*} [Group P] [Group Q]

theorem conj_injective_of_center_eq_bot (hZ : center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyZ : y ∈ center P := by
    rw [mem_center_iff]
    intro z
    have h : y * z * y⁻¹ = z := by
      simpa only [MulAut.conj_apply, MulAut.one_apply] using congrArg (fun χ : MulAut P => χ z) hy
    calc z * y = y * z * y⁻¹ * y := by rw [h]
      _ = y * z := by group
  rw [hZ, mem_bot] at hyZ
  exact hyZ

theorem mulAut_mul_conj_mul_inv (χ : MulAut P) (y : P) :
    χ * MulAut.conj y * χ⁻¹ = MulAut.conj (χ y) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem mulAut_congr_conj (ψ : P ≃* Q) (y : P) :
    MulAut.congr ψ (MulAut.conj y) = MulAut.conj (ψ y) := by
  ext z
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup P] (hnab : ∃ x y : P, x * y ≠ y * x) :
    center P = ⊥ := by
  rcases (center P).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · obtain ⟨x, y, hxy⟩ := hnab
    exact absurd ((mem_center_iff.mp (h ▸ mem_top y)) x) hxy

end Inner

section Extension

variable {A P : Type*} [Group A] [Group P] {W : Subgroup A} [W.Normal]

omit [W.Normal] in
theorem map_eq_range_conj {ρ : A →* MulAut P} (φ : W ≃* P)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) :
    W.map ρ = (MulAut.conj : P →* MulAut P).range := by
  ext χ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ ⟨x, hx⟩, (hρW ⟨x, hx⟩).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨φ.symm y, (φ.symm y).2, ?_⟩
    rw [hρW (φ.symm y), MulEquiv.apply_symm_apply]

theorem socle_extension (hCW : centralizer (W : Set A) = ⊥) (φ : W ≃* P)
    (hZ : center P = ⊥) :
    ∃ ρ : A →* MulAut P, Function.Injective ρ ∧ (∀ w : W, ρ w = MulAut.conj (φ w)) ∧
      (∀ ρ' : A →* MulAut P, (∀ w : W, ρ' w = MulAut.conj (φ w)) → ρ' = ρ) ∧
      ∀ (g : A) (w : W), ρ g (φ w) = φ (MulAut.conjNormal g w) := by
  set ρ : A →* MulAut P := (MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal with hρ
  have happ : ∀ (g : A) (y : P), ρ g y = φ (MulAut.conjNormal g (φ.symm y)) := fun _ _ => rfl
  have hρW : ∀ w : W, ρ w = MulAut.conj (φ w) := by
    intro w
    ext y
    rw [happ, MulAut.conj_apply]
    have h : MulAut.conjNormal (w : A) (φ.symm y) = w * φ.symm y * w⁻¹ := Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgW : g ∈ centralizer (W : Set A) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h := congrArg (fun χ : MulAut P => χ (φ ⟨x, hx⟩)) hg
      simp only [MulAut.one_apply] at h
      rw [happ, MulEquiv.symm_apply_apply] at h
      have h3 : g * x * g⁻¹ = x := by
        simpa only [MulAut.conjNormal_apply] using congrArg Subtype.val (φ.injective h)
      calc x * g = g * x * g⁻¹ * g := by rw [h3]
        _ = g * x := by group
    rw [hCW] at hgW
    exact hgW
  have hconj : ∀ (g : A) (w : W), ρ g (φ w) = φ (MulAut.conjNormal g w) := by
    intro g w
    rw [happ, MulEquiv.symm_apply_apply]
  have key : ∀ ρ'' : A →* MulAut P, (∀ w : W, ρ'' w = MulAut.conj (φ w)) →
      ∀ (g : A) (w : W), ρ'' g (φ w) = φ (MulAut.conjNormal g w) := by
    intro ρ'' hρ'' g w
    apply conj_injective_of_center_eq_bot hZ
    have h1 : ρ'' (g * w * g⁻¹) = ρ'' g * MulAut.conj (φ w) * (ρ'' g)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hρ'' w]
    have h2 : ρ'' (g * w * g⁻¹) = MulAut.conj (φ (MulAut.conjNormal g w)) := by
      rw [← hρ'' (MulAut.conjNormal g w), MulAut.conjNormal_apply]
    rw [← mulAut_mul_conj_mul_inv, ← h1, h2]
  refine ⟨ρ, hinj, hρW, fun ρ' hρ' => MonoidHom.ext fun g => MulEquiv.ext fun y => ?_, hconj⟩
  obtain ⟨w, rfl⟩ := φ.surjective y
  rw [key ρ' hρ' g w, hconj g w]

end Extension

section IdentityForm

variable {p f : ℕ} {K : Type} [Field K]

theorem gramSU_one_eq (h : UnitaryFieldData p f K) (n : ℕ) :
    gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = unitarySU p f K n := by
  rw [Units.val_one]
  exact (unitarySU_eq_gramSU h n).symm

theorem map_normOneScalars_one (h : UnitaryFieldData p f K) (n : ℕ) :
    (normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n).map
      ((MulEquiv.subgroupCongr (gramSU_one_eq h n) :
          gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* unitarySU p f K n) :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →* unitarySU p f K n) =
      unitaryScalars h n := by
  ext z
  constructor
  · rintro ⟨y, ⟨c, hc, hcn, hy⟩, rfl⟩
    exact ⟨c, hc, hcn, hy⟩
  · rintro ⟨c, hc, hcn, hz⟩
    exact ⟨(MulEquiv.subgroupCongr (gramSU_one_eq h n)).symm z, ⟨c, hc, hcn, hz⟩,
      MulEquiv.apply_symm_apply _ _⟩

@[expose] noncomputable def primeFormOneEquiv (h : UnitaryFieldData p f K) (n : ℕ) :
    primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ≃* unitaryPSU h n :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (gramSU_one_eq h n)) (map_normOneScalars_one h n)

theorem primeFormOneEquiv_mk (h : UnitaryFieldData p f K) {n : ℕ}
    (g : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (g' : unitarySU p f K n)
    (hg : (g' : GL (Fin n) K) = g) :
    primeFormOneEquiv h n (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      unitaryProj h n g' := by
  rw [primeFormOneEquiv, QuotientGroup.congr_mk]
  change ((MulEquiv.subgroupCongr (gramSU_one_eq h n) g : unitarySU p f K n) :
    unitaryPSU h n) = QuotientGroup.mk' _ g'
  rw [QuotientGroup.mk'_apply]
  congr 1
  exact Subtype.ext hg.symm

end IdentityForm

theorem isComponent_eq_top_of_isSimpleGroup {D : Type*} [Group D] [IsSimpleGroup D]
    {M : Subgroup D} (hM : CFSG.IsComponent M) : M = ⊤ := by
  have hnt : Nontrivial M := CFSG.LocalCores.isQuasisimple_nontrivial hM.1
  rcases hM.2.eq_bot_or_top_of_isSimpleGroup ‹IsSimpleGroup D› with h | h
  · exact absurd h (M.nontrivial_iff_ne_bot.mp hnt)
  · exact h

end CFSG.ComponentClassification.OutcomeLocal
