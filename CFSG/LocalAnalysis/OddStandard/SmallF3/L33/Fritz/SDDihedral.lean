module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDDataCore

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDDihedral

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit

private def toR8Fun : DihedralGroup 4 → R8
  | .r m => ⟨aff8 1 (-(2 * ((m.val : ℕ) : ZMod 8))),
      ⟨1, -((m.val : ℕ) : ZMod 8), Or.inl rfl, by congr 1; ring⟩⟩
  | .sr m => ⟨aff8 (-1) (2 * ((m.val : ℕ) : ZMod 8)),
      ⟨-1, ((m.val : ℕ) : ZMod 8), Or.inr rfl, rfl⟩⟩

private theorem toR8Fun_one : toR8Fun 1 = 1 := by decide

private theorem toR8Fun_mul :
    ∀ g h : DihedralGroup 4, toR8Fun (g * h) = toR8Fun g * toR8Fun h := by decide

private theorem toR8Fun_injective : Function.Injective toR8Fun := by decide

private noncomputable def toR8Hom : DihedralGroup 4 →* R8 where
  toFun := toR8Fun
  map_one' := toR8Fun_one
  map_mul' := toR8Fun_mul

theorem nonempty_mulEquiv_R8 : Nonempty (↥R8 ≃* DihedralGroup 4) := by
  refine ⟨(MulEquiv.ofBijective toR8Hom ?_).symm⟩
  exact toR8Fun_injective.bijective_of_nat_card_le (by
    rw [L2Act.card_R8, DihedralGroup.nat_card])

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

private noncomputable def psiHom (A : SDData t L) : A.R →* R8 where
  toFun r := ⟨A.ψ ⟨r.1, r.2.1⟩, A.ψ_mem_R8' r.2⟩
  map_one' := by
    apply Subtype.ext
    exact (congrArg (fun g : A.T => A.ψ g) (Subtype.ext rfl)).trans (map_one A.ψ)
  map_mul' r s := by
    apply Subtype.ext
    exact (congrArg (fun g : A.T => A.ψ g) (Subtype.ext rfl)).trans
      (map_mul A.ψ ⟨r.1, r.2.1⟩ ⟨s.1, s.2.1⟩)

private theorem psiHom_injective (A : SDData t L) : Function.Injective (psiHom A) := by
  intro r s h
  apply Subtype.ext
  exact A.eq_of_ψ_eq r.2 s.2 (congrArg Subtype.val h)

private theorem psiHom_surjective (A : SDData t L) : Function.Surjective (psiHom A) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨r, hr, hrσ⟩ := A.exists_mem_R_ψ_eq hσ
  exact ⟨⟨r, hr⟩, Subtype.ext hrσ⟩

theorem nonempty_mulEquiv_R (A : SDData t L) : Nonempty (↥A.R ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_R8
  exact ⟨(MulEquiv.ofBijective (psiHom A)
    ⟨psiHom_injective A, psiHom_surjective A⟩).trans e⟩

end CFSG.OddStandard.SmallF3.L33.KD.SDDihedral
