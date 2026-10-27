module

public import CFSG.GF2Type.Smith1980Orth.S3ThmAHalf
import Mathlib.FieldTheory.Finite.GaloisField

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions

theorem exists_singular_subspace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V) {P : Submodule (ZMod 2) V}
    (hP : ∀ a ∈ P, ∀ b ∈ P, polar Q a b = 0) :
    ∃ P₀ : Submodule (ZMod 2) V, P₀ ≤ P ∧ (∀ a ∈ P₀, Q a = 0) ∧
      finrank (ZMod 2) P ≤ finrank (ZMod 2) P₀ + 1 := by
  let f : P →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun a => Q a
      map_add' := fun a b => by
        show Q ((a : V) + b) = Q a + Q b
        rw [QuadraticMap.map_add Q, hP a a.2 b b.2, add_zero]
      map_smul' := fun r a => by
        show Q (r • (a : V)) = r • Q a
        have hrr : r * r = r := by fin_cases r <;> rfl
        rw [QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, hrr] }
  refine ⟨(LinearMap.ker f).map P.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range f)
      rwa [Module.finrank_self] at this
    have h3 : finrank (ZMod 2) ((LinearMap.ker f).map P.subtype) =
        finrank (ZMod 2) (LinearMap.ker f) :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ P.injective_subtype _).symm
    omega

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace S2Data

variable {M1 : Subgroup S.O} (D : S2Data S M1)

local notation "ρV" => D.resC

theorem orthogonal_commSpace_eq {c : D.Cbar} (hcc : (c : S.O) * c = 1)
    (hhalf : 2 * finrank (ZMod 2) (commSpace (ρV c)) = S.width) :
    LinearMap.BilinForm.orthogonal D.QV.polarBilin (commSpace (ρV c)) = commSpace (ρV c) := by
  have htt : ρV c * ρV c = 1 := LinearEquiv.ext fun w => by
    rw [LinearEquiv.mul_apply, D.resC_resC_apply hcc]
    rfl
  have hle : commSpace (ρV c) ≤
      LinearMap.BilinForm.orthogonal D.QV.polarBilin (commSpace (ρV c)) := fun a ha => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    exact polar_commSpace_eq_zero (D.resC_mem_orthogonalGroup c) htt hb ha
  have hdim := LinearMap.BilinForm.finrank_orthogonal D.QV_nondegenerate (commSpace (ρV c))
  rw [D.finrank_Vt] at hdim
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem card_le_of_fix {H : Subgroup S.O} {P : Submodule (ZMod 2) (Vt S D.g D.t)}
    (hP : LinearMap.BilinForm.orthogonal D.QV.polarBilin P = P)
    (hH : ∀ a ∈ H, ∃ ha : a ∈ D.Cbar, ∀ v ∈ P, ρV ⟨a, ha⟩ v = v) :
    Nat.card H ≤ 2 ^ ((finrank (ZMod 2) P).choose 2 + min (finrank (ZMod 2) P) 1) := by
  choose hC hfix using hH
  let F : H → CaseB.pstab D.QV P := fun a =>
    ⟨ρV ⟨a, hC a a.2⟩, CaseB.mem_pstab_iff.mpr ⟨D.QV_resC _, hfix a a.2⟩⟩
  have hF : Function.Injective F := fun a b e => by
    have h1 : ρV ⟨a, hC a a.2⟩ = ρV ⟨b, hC b b.2⟩ := congrArg Subtype.val e
    exact Subtype.ext (congrArg Subtype.val (D.resC_injective h1) :)
  exact (Nat.card_le_card_of_injective F hF).trans
    (CaseB.card_pstab_le_of_orthogonal_eq D.QV D.QV_nondegenerate hP)

end S2Data

end CFSG.GF2Type.Smith1980Orth
