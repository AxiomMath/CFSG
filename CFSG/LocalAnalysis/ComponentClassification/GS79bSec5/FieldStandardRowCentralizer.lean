module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRad
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNoncentralPairActionCentralQuotient

public noncomputable section

open Matrix Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_row_mul_centralizer_of_normalizes
    {G : Type u} [Group G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (hAperfect : Group.IsPerfect A)
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (b : G)
    (hbA : b ∈ Subgroup.normalizer (A : Set G))
    (hbE : b ∈ Subgroup.centralizer
      (((CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
        (A.subtype.comp φ) : Subgroup G) : Set G)) :
    let E : Subgroup G :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map
        (A.subtype.comp φ)
    ∃ a ∈ E, ∃ k ∈ Subgroup.centralizer (A : Set G), b = a * k := by
  classical
  let r : Matrix.SpecialLinearGroup (Fin 3) F →* G := A.subtype.comp φ
  let E : Subgroup G := (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F).map r
  let π : A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  change ∃ a ∈ E, ∃ k ∈ Subgroup.centralizer (A : Set G), b = a * k
  let bA : Subgroup.normalizer (A : Set G) := ⟨b, hbA⟩
  let α : MulAut A := A.normalizerMonoidHom bA
  have hZα : (Subgroup.center A).map α.toMonoidHom = Subgroup.center A :=
    Subgroup.map_center_eq α
  let αQ : MulAut (A ⧸ Subgroup.center A) :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center A) α hZα
  let β : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    e.symm.trans (αQ.trans e)
  have hβπ (x : A) :
      β (e (QuotientGroup.mk' (Subgroup.center A) x)) =
        e (QuotientGroup.mk' (Subgroup.center A) (α x)) := by
    change e (αQ (e.symm (e (QuotientGroup.mk' (Subgroup.center A) x)))) =
      e (QuotientGroup.mk' (Subgroup.center A) (α x))
    rw [MulEquiv.symm_apply_apply]
    have hq : αQ (QuotientGroup.mk' (Subgroup.center A) x) =
        QuotientGroup.mk' (Subgroup.center A) (α x) :=
      QuotientGroup.congr_mk (Subgroup.center A) (Subgroup.center A) α hZα x
    rw [hq]
  have hβfix : ∀ x ∈ CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.projRad F 0,
      β x = x := by
    intro x hx
    obtain ⟨a, c, hx⟩ :=
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.mem_projRad_zero).1 hx
    subst hx
    let v : Matrix.SpecialLinearGroup (Fin 3) F :=
      CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F a 0 c
    have hvOne : v ∈ CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipOne F :=
      ⟨a, c, rfl⟩
    have hvE : A.subtype (φ v) ∈ E := by
      dsimp [E, r]
      exact Subgroup.mem_map.mpr ⟨v, hvOne, rfl⟩
    have hbComm : (A.subtype (φ v)) * b = b * (A.subtype (φ v)) :=
      (Subgroup.mem_centralizer_iff.mp hbE) _ hvE
    have hαfix : α (φ v) = φ v := by
      apply A.subtype_injective
      have h := Subgroup.normalizerMonoidHom_apply_apply_coe (H := A) bA (φ v)
      dsimp [α, bA] at h ⊢
      rw [h]
      change b * (A.subtype (φ v)) * b⁻¹ = A.subtype (φ v)
      rw [hbComm.symm]
      group
    have hπv : e (QuotientGroup.mk' (Subgroup.center A) (φ v)) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F v := by
      have h := congrArg (fun f : Matrix.SpecialLinearGroup (Fin 3) F →*
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F => f v) hφproj
      simpa using h
    calc β (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F v)
        = β (e (QuotientGroup.mk' (Subgroup.center A) (φ v))) := by rw [hπv]
      _ = e (QuotientGroup.mk' (Subgroup.center A) (α (φ v))) := hβπ (φ v)
      _ = e (QuotientGroup.mk' (Subgroup.center A) (φ v)) := by rw [hαfix]
      _ = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F v := hπv
  obtain ⟨q, hqmem, hβeq⟩ :=
    CFSG.ComponentClassification.AS81.exists_eq_conj_of_fix_projRad_zero (α := β) hβfix
  obtain ⟨a0v, c0v, hqeq⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.mem_projRad_zero).1 hqmem
  let v0 : Matrix.SpecialLinearGroup (Fin 3) F :=
    CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F a0v 0 c0v
  let a0 : A := φ v0
  let e0 : G := A.subtype a0
  have hqeq' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F v0 = q := hqeq
  have hπa0 : π a0 = q := by
    have h := congrArg (fun f : Matrix.SpecialLinearGroup (Fin 3) F →*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F => f v0) hφproj
    have h' : π a0 = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F v0 := by
      simpa [π, a0] using h
    exact h'.trans hqeq'
  have he0E : e0 ∈ E := by
    dsimp [E, r, e0, a0]
    exact Subgroup.mem_map.mpr ⟨v0, ⟨a0v, c0v, rfl⟩, rfl⟩
  have hπconj : ∀ x : A, π (α x) = π a0 * π x * (π a0)⁻¹ := by
    intro x
    have h1 : π (α x) = β (π x) := (hβπ x).symm
    rw [hβeq, MulAut.conj_apply] at h1
    simpa only [← hπa0] using h1
  let δ : MulAut A := (MulAut.conj a0)⁻¹ * α
  have hδquot : ∀ x : A, QuotientGroup.mk' (Subgroup.center A) (δ x) =
      QuotientGroup.mk' (Subgroup.center A) x := by
    intro x
    apply e.injective
    have hπδ : π (δ x) = π x := by
      simp only [δ, MulAut.mul_apply, MulAut.conj_inv_apply, map_mul, map_inv]
      rw [hπconj x]
      group
    simpa [π] using hπδ
  have hδid :=
    @CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction.central_quotient_trivial_hom_eq_id
      A _ hAperfect (Subgroup.center A) Subgroup.instNormalCenter
      (le_rfl : Subgroup.center A ≤ Subgroup.center A) δ.toMonoidHom hδquot
  have hδeq : δ = 1 := by
    apply MulEquiv.ext
    intro x
    exact congrArg (fun f : A →* A => f x) hδid
  have hαeq : α = MulAut.conj a0 := by
    have h1 : MulAut.conj a0 * δ = MulAut.conj a0 := by rw [hδeq, mul_one]
    simpa [δ] using h1
  let k : G := e0⁻¹ * b
  have hkC : k ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hαval (y : A) : ((α y : A) : G) = e0 * (y : G) * e0⁻¹ := by
      rw [hαeq]
      simp [MulAut.conj_apply, e0, a0]
    have hαb (y : A) : ((α y : A) : G) = b * (y : G) * b⁻¹ := by
      simp [α, bA]
    have hαbG : b * (x : G) * b⁻¹ = e0 * (x : G) * e0⁻¹ := by
      have h1 := hαb ⟨x, hx⟩
      have h2 := hαval ⟨x, hx⟩
      simpa using h1.symm.trans h2
    have hconj : k * (x : G) * k⁻¹ = (x : G) := by
      dsimp [k]
      calc
        (e0⁻¹ * b) * (x : G) * (e0⁻¹ * b)⁻¹
            = e0⁻¹ * (b * (x : G) * b⁻¹) * e0 := by group
        _ = e0⁻¹ * (e0 * (x : G) * e0⁻¹) * e0 := by rw [hαbG]
        _ = (x : G) := by group
    calc (x : G) * k = (k * (x : G) * k⁻¹) * k := by rw [hconj]
      _ = k * (x : G) := by group
  refine ⟨e0, he0E, k, hkC, ?_⟩
  dsimp [k]
  group

end CFSG.ComponentClassification.GS79bSec5
