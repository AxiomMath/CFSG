module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBRRawExceptionalTwoData
public import CFSG.Assembly.GL83LieDefs

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

open CFSG.Assembly

inductive GL2RawDatum : Type 1
  | classical (K : Type) [Field K] [Finite K] (ι : Type) [Fintype ι] [DecidableEq ι]
      (H : Subgroup (GL ι K)) (ξ : Option (K × K))
  | exceptional (K : Type) [Field K] [Finite K] (V : ExceptionalRawTwoSpace)
      (H : Subgroup (ExceptionalRawTwoGL K V))

abbrev GL2RawDatum.Quotient : GL2RawDatum → Type
  | @classical _ _ _ _ _ _ H _ => LargeEvenProj H
  | @exceptional _ _ _ _ H => LargeEvenCenterQuot H

instance GL2RawDatum.instGroupQuotient : (D : GL2RawDatum) → Group D.Quotient
  | @classical _ _ _ _ _ _ H _ => inferInstanceAs (Group (LargeEvenProj H))
  | @exceptional _ _ _ _ H => inferInstanceAs (Group (LargeEvenCenterQuot H))

section Transport

variable {L : Type*} [Group L]

@[expose] def gl2CenterQuotientAut (α : MulAut L) : MulAut (L ⧸ Subgroup.center L) :=
  QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) α
    (Subgroup.characteristic_iff_map_eq.1 inferInstance α)

theorem gl2CenterQuotientAut_mk (α : MulAut L) (g : L) :
    gl2CenterQuotientAut α (g : L ⧸ Subgroup.center L) = (α g : L ⧸ Subgroup.center L) :=
  QuotientGroup.congr_mk' _ _ _ _ g

variable {R : Type*} [Group R]

@[expose] def gl2MarkingAut (θ : L ⧸ Subgroup.center L ≃* R) (α : MulAut L) : MulAut R :=
  (θ.symm.trans (gl2CenterQuotientAut α)).trans θ

theorem gl2MarkingAut_apply (θ : L ⧸ Subgroup.center L ≃* R) (α : MulAut L) (r : R) :
    gl2MarkingAut θ α r = θ (gl2CenterQuotientAut α (θ.symm r)) :=
  rfl

theorem gl2MarkingAut_apply_mk (θ : L ⧸ Subgroup.center L ≃* R) (α : MulAut L) (g : L) :
    gl2MarkingAut θ α (θ (g : L ⧸ Subgroup.center L)) = θ (α g : L ⧸ Subgroup.center L) := by
  rw [gl2MarkingAut_apply, MulEquiv.symm_apply_apply, gl2CenterQuotientAut_mk]

theorem gl2MarkingAut_ext (θ : L ⧸ Subgroup.center L ≃* R) {φ ψ : MulAut R}
    (h : ∀ g : L, φ (θ (g : L ⧸ Subgroup.center L)) = ψ (θ (g : L ⧸ Subgroup.center L))) :
    φ = ψ := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨x, rfl⟩ := θ.surjective r
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact h g

theorem gl2MarkingAut_one (θ : L ⧸ Subgroup.center L ≃* R) : gl2MarkingAut θ 1 = 1 :=
  gl2MarkingAut_ext θ fun g => by rw [gl2MarkingAut_apply_mk]; rfl

theorem gl2MarkingAut_mul (θ : L ⧸ Subgroup.center L ≃* R) (α β : MulAut L) :
    gl2MarkingAut θ (α * β) = gl2MarkingAut θ α * gl2MarkingAut θ β :=
  gl2MarkingAut_ext θ fun g => by
    rw [MulAut.mul_apply, gl2MarkingAut_apply_mk, gl2MarkingAut_apply_mk,
      gl2MarkingAut_apply_mk, MulAut.mul_apply]

@[expose] def gl2MarkingAutHom (θ : L ⧸ Subgroup.center L ≃* R) : MulAut L →* MulAut R where
  toFun := gl2MarkingAut θ
  map_one' := gl2MarkingAut_one θ
  map_mul' := gl2MarkingAut_mul θ

theorem gl2MarkingAutHom_apply (θ : L ⧸ Subgroup.center L ≃* R) (α : MulAut L) :
    gl2MarkingAutHom θ α = gl2MarkingAut θ α :=
  rfl

theorem gl2MarkingAut_conj (θ : L ⧸ Subgroup.center L ≃* R) (g : L) :
    gl2MarkingAut θ (MulAut.conj g) = MulAut.conj (θ (g : L ⧸ Subgroup.center L)) :=
  gl2MarkingAut_ext θ fun h => by
    rw [gl2MarkingAut_apply_mk, MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul, map_inv]

end Transport

end CFSG.LocalAnalysis.GorensteinLyons
