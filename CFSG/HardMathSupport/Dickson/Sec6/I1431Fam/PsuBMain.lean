module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBKey
public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShellGl

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open scoped commutatorElement

section Main

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem s1431_false_psu_bad_three (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ ≠ 3) (hq2 : ℓ ^ f ≠ 2)
    {A : Subgroup (MulAut (primeFormP h (idGram K 3)))}
    {ψ : MulAut (primeFormP h (idGram K 3))} {J : Subgroup (primeFormP h (idGram K 3))} {q : ℕ}
    (c : S1431Cfg (primeFormP h (idGram K 3)) A ψ J q) (hq : 10 ≤ q)
    (hA : ∀ a ∈ A, ∃ B : primeFormUnitary h (idGram K 3), primeFormConjHom h (idGram K 3) B = a) :
    False := by
  classical
  haveI := h.finite
  haveI : Finite (GL (Fin 3) K) :=
    Finite.of_injective (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) Units.val_injective
  haveI : Finite ↥(gramSU h (idGram K 3)) := inferInstance
  haveI : Finite (primeFormP h (idGram K 3)) := inferInstance
  have hne : ¬(3 = 3 ∧ ℓ ^ f = 2) := fun hh => hq2 hh.2
  have hker : (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3)).ker ≤
      Subgroup.center ↥(gramSU h (idGram K 3)) := by
    rw [QuotientGroup.ker_mk']
    exact normOneScalars_le_center h _ 3
  refine s1431_false_of_lift_blocks_gl (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K 3)) 3))
    (QuotientGroup.mk'_surjective _) hker (t6psub_actSU h 3) (primeFormConjHom h (idGram K 3))
    (fun B x => t6psub_hact B x) c hA ?_
  intro g hg3 hg1
  have hg3' : primeFormConjHom h (idGram K 3) (g ^ 3) = 1 := by rw [map_pow]; exact hg3
  obtain ⟨ν, -, hν⟩ := (primeFormConjHom_eq_one_iff_of_ne (le_refl 3) hne (g ^ 3)).1 hg3'
  have hap : (g : GL (Fin 3) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) ν := by
    rw [← Subgroup.coe_pow]
    exact hν
  have H : UnitaryPrimaryData h.bar (idForm h 3) (t6psub_toLin g) :=
    t6psuh_primaryData_toLin' h g.2 Nat.prime_three (Ne.symm hℓ3) hap
  by_cases hgood : ∃ b : primaryFactors ((t6psub_toLin g : LinearMap.GeneralLinearGroup K
      (Fin 3 → K)) : Module.End K (Fin 3 → K)), IsGoodBlock h (t6psub_toLin g) b
  · right
    obtain ⟨b0, hb0⟩ := hgood
    refine ⟨t6psub_Idx h 3 g, inferInstance, t6psub_block g, ?_, t6psub_block_le_fix g,
      t6psub_block_normal g, t6psub_isQuasisimple_block g H, t6psub_derived g H, ?_⟩
    ·
      intro y
      constructor
      · intro hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
        refine ⟨x, ?_, rfl⟩
        have hz : t6psub_actSU h 3 g x * x⁻¹ ∈ normOneScalars h (gramSU h (idGram K 3)) 3 := by
          rw [← QuotientGroup.ker_mk' (normOneScalars h (gramSU h (idGram K 3)) 3),
            MonoidHom.mem_ker, map_mul, map_inv, t6psub_hact, hy, mul_inv_cancel]
        obtain ⟨c0, -, -, hc0⟩ := hz
        have e1 : (g : GL (Fin 3) K) * (x : GL (Fin 3) K) * (g : GL (Fin 3) K)⁻¹ *
            (x : GL (Fin 3) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) c0 := hc0
        have e2 : (g : GL (Fin 3) K) * (x : GL (Fin 3) K) =
            Matrix.GeneralLinearGroup.scalar (Fin 3) c0 * (x : GL (Fin 3) K) * g := by
          calc (g : GL (Fin 3) K) * (x : GL (Fin 3) K)
              = ((g : GL (Fin 3) K) * (x : GL (Fin 3) K) * (g : GL (Fin 3) K)⁻¹ *
                  (x : GL (Fin 3) K)⁻¹) * (x : GL (Fin 3) K) * g := by group
            _ = Matrix.GeneralLinearGroup.scalar (Fin 3) c0 * (x : GL (Fin 3) K) * g := by
              rw [e1]
        have hc1 : c0 = 1 := t6psub_no_twist e2 b0.2 hb0.1
        have hfix : t6psub_actSU h 3 g x = x := by
          have : t6psub_actSU h 3 g x * x⁻¹ = 1 :=
            Subtype.ext (by rw [hc0, hc1, map_one]; rfl)
          exact mul_inv_eq_one.1 this
        exact hfix
      · rintro ⟨x, hx, rfl⟩
        rw [← t6psub_hact g x, mem_fixSubgroup.1 (SetLike.mem_coe.1 hx)]
    ·
      intro i hT B hB3 hcomm
      have hB3' : primeFormConjHom h (idGram K 3) (B ^ 3) = 1 := by rw [map_pow]; exact hB3
      obtain ⟨ν', -, hν'⟩ := (primeFormConjHom_eq_one_iff_of_ne (le_refl 3) hne (B ^ 3)).1 hB3'
      have hap' : (B : GL (Fin 3) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) ν' := by
        rw [← Subgroup.coe_pow]
        exact hν'
      have hcc : primeFormConjHom h (idGram K 3) (B * g * B⁻¹ * g⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcomm]
        group
      obtain ⟨ζ, -, hζ⟩ := (primeFormConjHom_eq_one_iff_of_ne (le_refl 3) hne _).1 hcc
      have hζ' : (B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ *
          (g : GL (Fin 3) K)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ := hζ
      have e : (B : GL (Fin 3) K) * g =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (g : GL (Fin 3) K) * B := by
        calc (B : GL (Fin 3) K) * g
            = ((B : GL (Fin 3) K) * (g : GL (Fin 3) K) * (B : GL (Fin 3) K)⁻¹ *
                (g : GL (Fin 3) K)⁻¹) * g * B := by group
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (g : GL (Fin 3) K) * B := by
            rw [hζ']
      have hgB : (g : GL (Fin 3) K) * B =
          Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (B : GL (Fin 3) K) * g := by
        calc (g : GL (Fin 3) K) * B
            = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ *
                (Matrix.GeneralLinearGroup.scalar (Fin 3) ζ * (g : GL (Fin 3) K) * B) := by
              rw [← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * ((B : GL (Fin 3) K) * g) := by
              rw [e]
          _ = Matrix.GeneralLinearGroup.scalar (Fin 3) ζ⁻¹ * (B : GL (Fin 3) K) * g := by
              rw [mul_assoc]
      have hζ1 : ζ⁻¹ = 1 := t6psub_no_twist hgB i.1.2 i.2.1
      have hζ1' : ζ = 1 := inv_eq_one.1 hζ1
      have hBg : (B : GL (Fin 3) K) * g = g * B := by
        rw [e, hζ1', map_one, one_mul]
      exact t6psub_block_key hO g H i hq hT hBg hap'
  · left
    push Not at hgood
    exact t6psub_isSolvable_fixSub _ (QuotientGroup.mk'_surjective _) hker (t6psub_actSU h 3 g)
      (primeFormConjHom h (idGram K 3) g) (fun x => t6psub_hact g x)
      (t6psub_isSolvable_fix_of_no_good g H hgood)

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431
