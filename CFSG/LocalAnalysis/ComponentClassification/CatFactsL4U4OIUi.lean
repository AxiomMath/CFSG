module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUh
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUd

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def SelectorRowOU (h : UnitaryFieldData p f K)
    (φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K)))
    (J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))) : Prop :=
  ∃ (A : GL (Fin 4) K)
    (_ : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (_ : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = 1)
    (δ : h.fixedFieldˣ) (_ : ¬ IsSquare (δ : h.fixedField)) (h2 : (2 : h.fixedField) ≠ 0)
    (d : h.fixedFieldˣ) (P : GL (Fin 4) K)
    (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →*
      unitarySU p f K 4),
    (∀ g g' : unitarySU p f K 4, ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) → φ (thU p f K g) = thU p f K g') ∧
    (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = P ∧
    uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      ((d : h.fixedField) : K) • (gramQ (δ : h.fixedField)).map h.fixedField.subtype ∧
    (∀ g, ((y g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹) ∧
    J' = ((thU p f K).comp y).range

variable (h : UnitaryFieldData p f K)

theorem selectorRowOU_of_component (hp2 : p ≠ 2)
    {φ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hφ2 : φ ^ 2 = 1)
    (hφ : φ ∉ InnU p f K h) {J' : Subgroup (StatedProj (StatedSU 4 (p ^ f) K))}
    (hJφ : J' ≤ OutInv.fixSub φ) (hJ : CFSG.IsComponent (J'.subgroupOf (OutInv.fixSub φ)))
    (hJm : Blueprint.LieModel (↥J' ⧸ Subgroup.center ↥J') .PSL 2 p (2 * f)) :
    SelectorRowOU h φ J' := by
  classical
  have : Finite K := h.finite
  obtain ⟨A, ψ, hAu, hψ, hψA, c, hAA⟩ := exists_anti_form h hp2 hφ2 hφ
  obtain ⟨Y, hY, σY, hσs, hσk, hσv⟩ := exists_lift_component h hAu hψ hψA hAA hJφ hJ
  let eJX : ↥J' ≃* ↥(J'.map (GSThmB.Catalog7L4EU.ιU h)) :=
    J'.equivMapOfInjective _ (GSThmB.Catalog7L4EU.ιU_injective h)
  have hXm : Blueprint.LieModel (↥(J'.map (GSThmB.Catalog7L4EU.ιU h)) ⧸
      Subgroup.center ↥(J'.map (GSThmB.Catalog7L4EU.ιU h))) .PSL 2 p (2 * f) :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥J') _ eJX (Subgroup.map_center_eq eJX)) hJm
  obtain ⟨hc1, -, B', hB'v, hsym, δ, hδ, d, ψW, hψW, hYmem⟩ :=
    descent_model h hp2 hAu hAA hY σY hσs hσk hXm
  subst hc1
  rw [one_smul] at hAA
  have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
    have h1 := congrArg h.fixedField.subtype h0
    rw [map_ofNat, map_zero] at h1
    exact two_ne_zero_of_odd h hp2 h1
  have h3 : 2 < Nat.card h.fixedField := by
    rw [h.card_fixedField]
    have : 3 ≤ p := by have := h.prime.two_le; omega
    exact lt_of_lt_of_le (by omega) (this.trans (Nat.le_self_pow (by have := h.one_le; omega) p))
  obtain ⟨P, hPx, hPij, hAP⟩ := exists_basis_matrix h hp2 hAA
    ((hermitianCoordinates (δ : h.fixedField) h2).trans ψW.symm)
  have hPP := gram_basis_matrix h h2 ψW B' hB'v hsym d hψW P hPij
  have hmem := y_mem_SU h h2 hδ h3 P hPP
  refine ⟨A, hAu, hAA, δ, hδ, h2, d, P, yHom h h2 P hmem, ?_, hAP, hPP, fun g => rfl, ?_⟩
  · intro g g' hg
    rw [show thU p f K g = QuotientGroup.mk g from rfl, hψ]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [hψA, hg]
  · have hιU : ∀ g : unitarySU p f K 4, GSThmB.Catalog7L4EU.ιU h (thU p f K g) =
        QuotientGroup.mk (EscapingNotOddUnitary.toSesqUnitary h 4 g) := fun g =>
      GSThmB.Catalog7L4EU.ιU_mk h g
    ext x
    constructor
    · intro hx
      obtain ⟨y0, hy0⟩ := hσs ⟨GSThmB.Catalog7L4EU.ιU h x, ⟨x, hx, rfl⟩⟩
      have h1 := hσv y0
      rw [hy0] at h1
      obtain ⟨g, hg⟩ := (hYmem (y0 : sesqUnitaryGroup (stdHermForm h 4)) (hY.1 y0.2)).mp y0.2
      have hy0g := eq_toSesq_yHom h h2 P hmem ψW hPx g _ hg
      refine ⟨g, ?_⟩
      apply GSThmB.Catalog7L4EU.ιU_injective h
      rw [MonoidHom.comp_apply, hιU, ← hy0g]
      exact h1.symm
    · rintro ⟨g, rfl⟩
      have hu := toSesq_yHom_mem h h2 hAu P hmem hAP g
      have huY : EscapingNotOddUnitary.toSesqUnitary h 4 (yHom h h2 P hmem g) ∈ Y := by
        refine (hYmem _ hu).mpr ⟨g, fun w => ?_⟩
        rw [GSThmB.Catalog7U4.unitaryOp_toSesqUnitary h, Matrix.toLin'_apply]
        exact yHom_apply_fixW h h2 P hmem ψW hPx g w
      have h1 := hσv ⟨_, huY⟩
      obtain ⟨x', hx', hx'e⟩ := (σY ⟨_, huY⟩).2
      have h4 : GSThmB.Catalog7L4EU.ιU h x' =
          GSThmB.Catalog7L4EU.ιU h (thU p f K (yHom h h2 P hmem g)) := by
        rw [hx'e, h1, hιU]
        rfl
      rw [MonoidHom.comp_apply, ← GSThmB.Catalog7L4EU.ιU_injective h h4]
      exact hx'

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
