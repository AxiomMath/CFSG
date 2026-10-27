module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.GH74.Generic.BProg.B2.PuG2OddAux
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsFine
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem stdUnitary_equiv_fin {ℓ f ν : ℕ} (hℓ : ℓ.Prime) {L : Type} [Field L] [Finite L]
    [CharP L ℓ] (hf : 1 ≤ f) (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hν : 3 ≤ ν)
    (hL : Nat.card L = (ℓ ^ f) ^ 4) :
    ∃ F : Subfield L, Nat.card F = (ℓ ^ f) ^ 2 ∧
      Nonempty (StatedSU ν (ℓ ^ f) F ≃* fixSubgroup (stdUnitaryEquiv (ν := ν) σ)) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set Φ := stdUnitaryEquiv (ν := ν) σ with hΦ
  let δ : L ≃+* L := iterateFrobeniusEquiv L ℓ (2 * f)
  have hδ : ∀ c, δ c = c ^ (ℓ ^ (2 * f)) := fun c => rfl
  set F : Subfield L := fixSubfield δ with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, mem_fixSubfield, hδ]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hLq : Nat.card L = (ℓ ^ (2 * f)) ^ 2 := by
    rw [hL, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2]
    exact CFSG.GH74.Generic.BProg.B2.PuG2OddAux.card_fixSubfield_quad hℓ (by omega) hLq δ hδ
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have hσmap : ∀ M : Matrix (Fin ν) (Fin ν) L, M.map σ.toRingHom = M.map (· ^ ℓ ^ f) := by
    intro M
    ext i j
    simp [hσ]
  have hfix : ∀ X : SL(ν, L), X ∈ fixSubgroup Φ ↔
      Matrix.SpecialLinearGroup.toGL X ∈ unitarySet (ℓ ^ f) ν := by
    intro X
    rw [mem_fixSubgroup, hΦ, stdUnitaryEquiv_apply]
    have hdetX : IsUnit ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)).det := by
      rw [← hσmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, X.2, map_one]
      exact isUnit_one
    constructor
    · intro h
      have hstd : stdUnitary σ.toRingHom X = X := h
      have h1 : (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ =
          (X : Matrix (Fin ν) (Fin ν) L) := by
        rw [← hσmap, ← coe_stdUnitary, hstd]
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := by
        have e1 : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
            (X : Matrix (Fin ν) (Fin ν) L) = ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
              (((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹)ᵀ := by rw [h1]
        rw [e1, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hdetX, Matrix.transpose_one]
      refine ⟨fun i j => ?_, X.2, hu⟩
      have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom X = invTransposeSL X := by
        have := congrArg invTransposeSL hstd
        rwa [stdUnitary, MonoidHom.comp_apply, invTransposeSL_invTransposeSL] at this
      have h2 : Matrix.SpecialLinearGroup.map σ.toRingHom
          (Matrix.SpecialLinearGroup.map σ.toRingHom X) = X := by
        rw [hmap, slMap_invTransposeSL, ← MonoidHom.comp_apply invTransposeSL, ← stdUnitary, hstd]
      have h3 := congrArg (fun Y : SL(ν, L) => (Y : Matrix (Fin ν) (Fin ν) L) i j) h2
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ] at h3
      rw [← pow_mul, ← sq] at h3
      exact h3
    · rintro ⟨-, -, hu'⟩
      have hu : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))ᵀ *
          (X : Matrix (Fin ν) (Fin ν) L) = 1 := hu'
      apply Subtype.ext
      rw [coe_stdUnitary, hσmap]
      have : ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f))⁻¹ =
          (X : Matrix (Fin ν) (Fin ν) L)ᵀ := by
        refine Matrix.inv_eq_left_inv ?_
        rw [← Matrix.transpose_transpose ((X : Matrix (Fin ν) (Fin ν) L).map (· ^ ℓ ^ f)),
          ← Matrix.transpose_mul, hu, Matrix.transpose_one]
      rw [this, Matrix.transpose_transpose]
  let Ψ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) := statedSUToSL F ν (ℓ ^ f)
  have hΨmem : ∀ Y, Ψ Y ∈ fixSubgroup Φ := fun Y =>
    (hfix _).2 ((mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩)
  let e : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ := MulEquiv.ofBijective (Ψ.codRestrict _ hΨmem)
    ⟨fun Y Z h => statedSUToSL_injective F ν (ℓ ^ f) (congrArg Subtype.val h), fun X => by
      obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff (n := ν) hℓ F hF hFcard (by omega) X).mpr
        ((hfix X).1 X.2)
      exact ⟨Y, Subtype.ext hY⟩⟩
  exact ⟨F, hFcard, ⟨e⟩⟩

theorem lieFactorData_statedSU_three {ℓ f : ℕ} (hℓ : ℓ.Prime) {F : Type} [Field F] [Finite F]
    [CharP F ℓ] (hF : Nat.card F = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f) :
    LieFactorData ℓ ↥(StatedSU 3 (ℓ ^ f) F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hnq : (3, ℓ ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hFc : Fintype.card F = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hring : ringChar F = ℓ := ringChar.eq F ℓ
  have := suFactorFacts_holds F 3 (ℓ ^ f) hFc le_rfl hnq
  rwa [hring] at this

theorem componentFactor_statedSU_of_surjective {ℓ f : ℕ} (hℓ : ℓ.Prime) {F : Type} [Field F]
    [Finite F] [CharP F ℓ] (hF : Nat.card F = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
    {Q : Type} [Group Q] [Finite Q] (g : ↥(StatedSU 3 (ℓ ^ f) F) →* Q)
    (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU 3 (ℓ ^ f) F)) :
    ComponentFactor ℓ Q := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hnq : (3, ℓ ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hFc : Fintype.card F = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hring : ringChar F = ℓ := ringChar.eq F ℓ
  have hFD : LieFactorData ℓ ↥(StatedSU 3 (ℓ ^ f) F) := by
    have := suFactorFacts_holds F 3 (ℓ ^ f) hFc le_rfl hnq
    rwa [hring] at this
  have hA6 := suAltSixFacts_holds F 3 (ℓ ^ f) hFc le_rfl
  refine ⟨⟨↥(StatedSU 3 (ℓ ^ f) F), inferInstance, inferInstance, hFD, g, hg, hgk⟩,
    ⟨fun a => ?_⟩⟩
  exact hA6.false ((nonempty_centralQuotient_mulEquiv hFD.perfect g hg hgk).some.trans a)

theorem compsWith_of_su_hom {P : (X : Type) → [Group X] → Prop}
    {ℓ f : ℕ} (hℓ : ℓ.Prime) {F : Type} [Field F] [Finite F] [CharP F ℓ]
    (hF : Nat.card F = (ℓ ^ f) ^ 2) (hq : 5 ≤ ℓ ^ f)
    (hPquot : ∀ {Q : Type} [Group Q] [Finite Q] (g : ↥(StatedSU 3 (ℓ ^ f) F) →* Q),
      Function.Surjective g → g.ker ≤ Subgroup.center ↥(StatedSU 3 (ℓ ^ f) F) → P Q)
    {C : Type} [Group C] [Finite C]
    (J : Subgroup C) [J.Normal] (hsol : Group.IsSolvable (C ⧸ J))
    (g : ↥(StatedSU 3 (ℓ ^ f) F) →* ↥J) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU 3 (ℓ ^ f) F)) : CompsWith P C := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hnq : (3, ℓ ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hFc : Fintype.card F = (ℓ ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hring : ringChar F = ℓ := ringChar.eq F ℓ
  have hFD : LieFactorData ℓ ↥(StatedSU 3 (ℓ ^ f) F) := by
    have := suFactorFacts_holds F 3 (ℓ ^ f) hFc le_rfl hnq
    rwa [hring] at this
  obtain ⟨hqs, -⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl hnq)
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F ℓ f hF 3 le_rfl hnq)
  have hPJ : P ↥J := hPquot g hg hgk
  exact compsWith_of_normal_quasisimple J
    (CFSG.LocalCores.isQuasisimple_of_surjective hqs g hg hgk) hsol hPJ

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
