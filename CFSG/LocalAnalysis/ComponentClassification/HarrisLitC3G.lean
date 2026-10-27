module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3E
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowSFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILg
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLa

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic InvClassL

variable {K : Type} [Field K] [Finite K]

theorem finite_mulAut : Finite (MulAut (projectiveSL 4 K)) :=
  Finite.of_injective (fun α : MulAut (projectiveSL 4 K) => (α : projectiveSL 4 K → _))
    fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)

@[expose] def kappaSL (ν : Kˣ) (Ψ : (Fin 2 → extension (ν : K)) ≃ₗ[K] (Fin 4 → K)) :
    SpecialLinearGroup (Fin 4) K :=
  ⟨(rowSKappa ν Ψ : Matrix (Fin 4) (Fin 4) K), det_rowSKappa ν Ψ⟩

omit [Finite K] in
theorem toGL_kappaSL (ν : Kˣ) (Ψ : (Fin 2 → extension (ν : K)) ≃ₗ[K] (Fin 4 → K)) :
    SpecialLinearGroup.toGL (kappaSL ν Ψ) = rowSKappa ν Ψ := Units.ext rfl

theorem rowS_aut {φ : MulAut (projectiveSL 4 K)} {Lφ : Subgroup (MulAut (projectiveSL 4 K))}
    (hK2 : ringChar K ≠ 2)
    (hrow : SelectorRowS 4 K (MonoidHom.id (MulAut (projectiveSL 4 K)))
      (OuterAutomorphisms.inner (projectiveSL 4 K)) φ Lφ) :
    ∃ (C : GL (Fin 4) K) (ν : Kˣ) (Ψ : (Fin 2 → extension (ν : K)) ≃ₗ[K] (Fin 4 → K)),
      φ = conjAut 4 K (C * rowSU ν Ψ * C⁻¹) ∧
      rowSKappa ν Ψ * rowSU ν Ψ = GeneralLinearGroup.scalar (Fin 4) (-1) * rowSU ν Ψ *
        rowSKappa ν Ψ ∧
      center ↥(Lφ ⊔ zpowers (conjAut 4 K (C * rowSKappa ν Ψ * C⁻¹))) = ⊥ ∧
      conjAut 4 K (C * rowSKappa ν Ψ * C⁻¹) ∉ Lφ ∧
      ∃ A₈ : Subgroup (MulAut (projectiveSL 4 K)),
        A₈ ≤ Lφ ⊔ zpowers (conjAut 4 K (C * rowSKappa ν Ψ * C⁻¹)) ∧ GrSLit.IsElemTwo A₈ ∧
          Nat.card A₈ = 8 := by
  obtain ⟨ν, hν, Ψ, C, hE, hφ, -, hdisj, -, hord, -, -, hL, hkerSL, -⟩ := hrow
  have : Fact (¬ IsSquare (ν : K)) := ⟨hν⟩
  have : Finite (extension (ν : K)) := Nat.finite_of_card_ne_zero (by
    rw [hE]
    exact pow_ne_zero _ Nat.card_pos.ne')
  have := finite_mulAut (K := K)
  set cC := conjAut 4 K C with hcC
  set cκ := conjAut 4 K (rowSKappa ν Ψ) with hcκ
  set πS : SpecialLinearGroup (Fin 2) (extension (ν : K)) →* MulAut (projectiveSL 4 K) :=
    (conjAut 4 K).comp ((rowSPi ν Ψ).comp SpecialLinearGroup.toGL) with hπS
  set π' : SpecialLinearGroup (Fin 2) (extension (ν : K)) →* MulAut (projectiveSL 4 K) :=
    (MulAut.conj cC).toMonoidHom.comp πS with hπ'
  have hc' : conjAut 4 K (C * rowSKappa ν Ψ * C⁻¹) = cC * cκ * cC⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have hLπ : Lφ = π'.range := by
    rw [Subgroup.map_id] at hL
    rw [hL, hπ', MonoidHom.range_comp]
    rfl
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have h2 : (2 : extension (ν : K)) ≠ 0 := by
    have h := (algebraMap K (extension (ν : K))).injective.ne h2K
    rwa [map_ofNat, map_zero] at h
  set σ : extension (ν : K) →+* extension (ν : K) :=
    ((extensionConj ν : extension (ν : K) ≃ₐ[K] _) : extension (ν : K) →+* extension (ν : K))
    with hσ
  have hker : ∀ g, π' g = 1 ↔ g = 1 ∨ g = -1 := by
    intro g
    rw [← hkerSL g]
    change cC * πS g * cC⁻¹ = 1 ↔ _
    constructor
    · intro h
      calc πS g = cC⁻¹ * (cC * πS g * cC⁻¹) * cC := by group
        _ = 1 := by rw [h]; group
    · intro h
      change cC * conjAut 4 K (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) * cC⁻¹ = 1
      rw [h, mul_one, mul_inv_cancel]
  have hκκ : rowSKappa ν Ψ * rowSKappa ν Ψ = 1 := rowSKappa_mul_self ν Ψ
  have hcc : cC * cκ * cC⁻¹ * (cC * cκ * cC⁻¹) = 1 := by
    rw [show cC * cκ * cC⁻¹ * (cC * cκ * cC⁻¹) = cC * (cκ * cκ) * cC⁻¹ by group, hcκ, ← map_mul,
      hκκ, map_one, mul_one, mul_inv_cancel]
  have hmapσ : ∀ g : SpecialLinearGroup (Fin 2) (extension (ν : K)),
      GeneralLinearGroup.map σ (SpecialLinearGroup.toGL g) =
        SpecialLinearGroup.toGL (SpecialLinearGroup.map σ g) := fun g => Units.ext rfl
  have hcσ : ∀ g, cC * cκ * cC⁻¹ * π' g * (cC * cκ * cC⁻¹) = π' (SpecialLinearGroup.map σ g) := by
    intro g
    change cC * cκ * cC⁻¹ * (cC * πS g * cC⁻¹) * (cC * cκ * cC⁻¹) =
      cC * πS (SpecialLinearGroup.map σ g) * cC⁻¹
    have h1 : cκ * πS g * cκ = πS (SpecialLinearGroup.map σ g) := by
      change cκ * conjAut 4 K (rowSPi ν Ψ (SpecialLinearGroup.toGL g)) * cκ =
        conjAut 4 K (rowSPi ν Ψ (SpecialLinearGroup.toGL (SpecialLinearGroup.map σ g)))
      rw [hcκ, ← map_mul, ← map_mul, rowSKappa_conj_rowSPi, ← hmapσ]
    rw [← h1]
    group
  have hrange : ∀ g, πS g ∈ rowST ν Ψ := by
    intro g
    refine ⟨SpecialLinearGroup.toGL g, ?_, rfl⟩
    change SpecialLinearGroup.toGL g ∈ normFourthPowers ν
    rw [mem_normFourthPowers]
    refine ⟨1, ?_⟩
    rw [SpecialLinearGroup.coe_GL_coe_matrix, g.2, map_one, Units.val_one, one_pow]
  have hcκ1 : cκ ≠ 1 := fun h => by rw [h, orderOf_one] at hord; omega
  have hcπ : cC * cκ * cC⁻¹ ∉ π'.range := by
    rintro ⟨g, hg⟩
    have hg' : πS g = cκ := by
      have h1 : cC * πS g * cC⁻¹ = cC * cκ * cC⁻¹ := hg
      calc πS g = cC⁻¹ * (cC * πS g * cC⁻¹) * cC := by group
        _ = cC⁻¹ * (cC * cκ * cC⁻¹) * cC := by rw [h1]
        _ = cκ := by group
    have hmem : cκ ∈ rowST ν Ψ ⊓ zpowers cκ := ⟨hg' ▸ hrange g, mem_zpowers _⟩
    rw [hdisj, mem_bot] at hmem
    exact hcκ1 hmem
  have ht₀ : σ (AdjoinRoot.root (quadraticPolynomial (ν : K))) ≠
      AdjoinRoot.root (quadraticPolynomial (ν : K)) := by
    rw [hσ]
    change extensionConj ν _ ≠ _
    rw [extensionConj_root]
    intro h
    have hr : AdjoinRoot.root (quadraticPolynomial (ν : K)) = 0 := by
      have h3 : (2 : extension (ν : K)) * AdjoinRoot.root (quadraticPolynomial (ν : K)) = 0 := by
        linear_combination -h
      exact (mul_eq_zero.mp h3).resolve_left h2
    have h4 := extension_root_square (ν : K)
    rw [hr, zero_pow two_ne_zero] at h4
    have h5 : algebraMap K (extension (ν : K)) (ν : K) ≠ 0 :=
      (map_ne_zero (algebraMap K (extension (ν : K)))).mpr ν.ne_zero
    exact h5 h4.symm
  have := Fintype.ofFinite K
  have hq : Fintype.card K % 2 = 1 := FiniteField.odd_card_of_char_ne_two hK2
  obtain ⟨a, b, hab⟩ := OIL.exists_sq_add_sq hq (-1 : K)
  have habE : (algebraMap K (extension (ν : K)) a) ^ 2 + (algebraMap K (extension (ν : K)) b) ^ 2 =
      -1 := by
    rw [← map_pow, ← map_pow, ← map_add, hab, map_neg, map_one]
  have hσK : ∀ y : K, σ (algebraMap K (extension (ν : K)) y) = algebraMap K _ y := fun y =>
    (extensionConj ν).commutes y
  refine ⟨C, ν, Ψ, ?_, rowSKappa_mul_rowSU ν Ψ, ?_, ?_, ?_⟩
  · rw [show φ = (MonoidHom.id _) φ from rfl, hφ, map_mul, map_mul, map_inv]
  · rw [hc', hLπ]
    exact center_sup_eq_bot π' h2 hker hcc hcσ hcπ ht₀
  · rw [hc', hLπ]
    exact hcπ
  · rw [hc', hLπ]
    exact exists_eight_le_sup π' h2 hker hcc hcσ hcπ habE (hσK a) (hσK b)

end CFSG.ComponentClassification.HarrisLit.C3
