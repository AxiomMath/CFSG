module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary
open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {n : ℕ} {k : Type} [Field k] [Finite k]

private theorem ne_zero_of_nontrivial_subgroup {T : Subgroup (LinearFlag.projectiveSL n k)}
    (hT : Nontrivial ↥T) : n ≠ 0 := by
  rintro rfl
  haveI : Subsingleton (Matrix (Fin 0) (Fin 0) k) := inferInstance
  haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) k) := inferInstance
  haveI : Subsingleton (LinearFlag.projectiveSL 0 k) := inferInstance
  haveI : Subsingleton ↥T := inferInstance
  exact not_subsingleton_iff_nontrivial.mpr hT inferInstance

private theorem minpoly_glA_eq_of_not_pow {p : ℕ} (hp : p.Prime)
    {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ b : k, b ^ p ≠ (c : k)) (hn0 : n ≠ 0) :
    minpoly k (glA A : Module.End k (Fin n → k)) = X ^ p - C (c : k) ∧
      Irreducible (minpoly k (glA A : Module.End k (Fin n → k))) :=
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.minpoly_linEnd_of_pow_scalar_irreducible
    hp (c := c) (y := A) hA hc hn0

private theorem eq_of_isComponentOf_of_not_pow {p : ℕ} (hp : p.Prime) (hpk : (p : k) ≠ 0)
    {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ b : k, b ^ p ≠ (c : k)) (hn0 : n ≠ 0)
    {T T' : Subgroup (LinearFlag.projectiveSL n k)}
    (hT : IsComponentOf T (fixSubgroup (LinearFlag.conjAut n k A)))
    (hT' : IsComponentOf T' (fixSubgroup (LinearFlag.conjAut n k A))) : T' = T := by
  have hmin := minpoly_glA_eq_of_not_pow hp hA hc hn0
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA T hT
  obtain ⟨h', hT'eq⟩ := linear_inner_components hpk hA T' hT'
  have hfac : h.1.1 = minpoly k (glA A : Module.End k (Fin n → k)) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.eq_minpoly_of_mem_primaryFactors
      (y := A) (K := k) hmin.2 h.1.2
  have hfac' : h'.1.1 = minpoly k (glA A : Module.End k (Fin n → k)) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.eq_minpoly_of_mem_primaryFactors
      (y := A) (K := k) hmin.2 h'.1.2
  rw [hT'eq, hfac', hfac]

theorem linear_fieldType_component {p : ℕ}
    (hp : p.Prime) (hpk : (p : k) ≠ 0) {A : GL (Fin n) k} {c : kˣ}
    (hA : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hc : ∀ b : k, b ^ p ≠ (c : k))
    {T : Subgroup (LinearFlag.projectiveSL n k)}
    (hT : IsComponentOf T (fixSubgroup (LinearFlag.conjAut n k A))) :
    p ∣ n ∧ 2 ≤ n / p ∧
      (∀ T' : Subgroup (LinearFlag.projectiveSL n k),
        IsComponentOf T' (fixSubgroup (LinearFlag.conjAut n k A)) → T' = T) ∧
      ∃ (E : Type) (_ : Field E) (_ : Fintype E), Nat.card E = Nat.card k ^ p ∧
        ∃ g : Matrix.SpecialLinearGroup (Fin (n / p)) E →* ↥T, Function.Surjective g ∧
          g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n / p)) E) := by
  haveI : IsSimpleGroup (↥T ⧸ Subgroup.center ↥T) := hT.2.2.2
  haveI : Nontrivial ↥T := (QuotientGroup.mk'_surjective (Subgroup.center ↥T)).nontrivial
  have hn0 : n ≠ 0 := ne_zero_of_nontrivial_subgroup (T := T) inferInstance
  obtain ⟨h, rfl⟩ := linear_inner_components hpk hA T hT
  have hmin := minpoly_glA_eq_of_not_pow hp hA hc hn0
  have hfac : h.1.1 = minpoly k (glA A : Module.End k (Fin n → k)) :=
    CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.eq_minpoly_of_mem_primaryFactors
      (y := A) (K := k) hmin.2 h.1.2
  have hdeg : (minpoly k (glA A : Module.End k (Fin n → k))).natDegree = p := by
    rw [hmin.1, natDegree_X_pow_sub_C]
  have hmul : p * primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 = n := by
    have hdim := CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.finrank_eq_natDegree_mul_mult
      (y := A) (K := k) hmin.2 ⟨h.1.1, h.1.2⟩
    rw [← hdeg]
    exact hdim.symm
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 := by
    rcases h.2 with h3 | ⟨h2, -⟩ <;> omega
  have hnp : n / p = primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 :=
    Nat.div_eq_of_eq_mul_left hp.pos (by rw [mul_comm]; exact hmul.symm)
  refine ⟨⟨_, hmul.symm⟩, ?_, ?_, ?_⟩
  · rw [hnp]
    exact hm2
  · intro T' hT'
    exact eq_of_isComponentOf_of_not_pow hp hpk hA hc hn0 hT hT'
  · have hirr : Irreducible h.1.1 := hfac ▸ hmin.2
    haveI : Fact (Irreducible h.1.1) := ⟨hirr⟩
    haveI : Finite (AdjoinRoot h.1.1) := Module.finite_of_finite k
    have hcard : Nat.card (AdjoinRoot h.1.1) = Nat.card k ^ p := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h.1.1, hfac, hdeg]
    have hm : primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1 = n / p :=
      hnp.symm
    obtain ⟨e⟩ := nonempty_mulEquiv_specialFactor (squarefree_minpoly_glA hpk hA) h.1.2
    let eLin : (Fin (n / p) → AdjoinRoot h.1.1) ≃ₗ[AdjoinRoot h.1.1]
        (Fin (primaryMultiplicity (glA A : Module.End k (Fin n → k)) h.1.1) →
          AdjoinRoot h.1.1) :=
      LinearEquiv.piCongrLeft (R := AdjoinRoot h.1.1) (φ := fun _ => AdjoinRoot h.1.1)
        (finCongr hm.symm)
    let eSL : Matrix.SpecialLinearGroup (Fin (n / p)) (AdjoinRoot h.1.1) ≃*
        specialFactor A h.1.1 :=
      (Matrix.SpecialLinearGroup.toLin'_equiv).trans
        ((SpecialLinearGroup.congr_linearEquiv eLin).trans
          ((Matrix.SpecialLinearGroup.toLin'_equiv).symm.trans e))
    obtain ⟨g, hg, hgk⟩ := exists_surjective_ker_le_center_map_proj eSL
    exact ⟨AdjoinRoot h.1.1, inferInstance, Fintype.ofFinite _, hcard, g, hg, hgk⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
