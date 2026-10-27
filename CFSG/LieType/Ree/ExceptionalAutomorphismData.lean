module

public import CFSG.LieType.Ree.ExceptionalAutomorphism

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime]

@[expose] def finiteExceptionalAut :
    MulAut (adjointGroup t.tag K) :=
  MulEquiv.ofBijective
    (t.exceptionalEndo K (CharP.cast_eq_zero K t.prime)
      (shortFaithful (CharP.cast_eq_zero K t.prime)))
    (exceptionalEndo_injective _ _).bijective_of_finite

@[expose] def finiteFrobeniusAut :
    MulAut (adjointGroup t.tag K) :=
  MulEquiv.ofBijective (frobeniusTwist t.tag K (frobenius K t.prime))
    (frobeniusTwist_injective _).bijective_of_finite

@[expose] def finiteReeAut
    (a : ℕ) : MulAut (adjointGroup t.tag K) :=
  t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a

@[expose] def finiteReeFixedGroup
    (a : ℕ) : Subgroup (adjointGroup t.tag K) :=
  (t.finiteReeAut K a).toMonoidHom.eqLocus (MonoidHom.id _)

variable {t K}

theorem finiteExceptionalAut_xElement
    (i : Fin t.tag.rank) (c : K) :
    t.finiteExceptionalAut K (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) :=
  exceptionalEndo_xElement (CharP.cast_eq_zero K t.prime)
    (shortFaithful (CharP.cast_eq_zero K t.prime)) i c

theorem finiteExceptionalAut_yElement
    (i : Fin t.tag.rank) (c : K) :
    t.finiteExceptionalAut K (yElement i c) = yElement (t.perm i) (c ^ t.exponent i) :=
  exceptionalEndo_yElement (CharP.cast_eq_zero K t.prime)
    (shortFaithful (CharP.cast_eq_zero K t.prime)) i c

theorem eq_finiteExceptionalAut
    {ψ : MulAut (adjointGroup t.tag K)}
    (hψ : ∀ (i : Fin t.tag.rank) (c : K),
      ψ (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) ∧
        ψ (yElement i c) = yElement (t.perm i) (c ^ t.exponent i)) :
    ψ = t.finiteExceptionalAut K := by
  refine MulEquiv.ext fun g => ?_
  have h := adjointGroup_hom_ext (f := ψ.toMonoidHom) (g := (t.finiteExceptionalAut K).toMonoidHom)
    (fun i c => by
      change ψ (xElement i c) = t.finiteExceptionalAut K (xElement i c)
      rw [(hψ i c).1, finiteExceptionalAut_xElement])
    (fun i c => by
      change ψ (yElement i c) = t.finiteExceptionalAut K (yElement i c)
      rw [(hψ i c).2, finiteExceptionalAut_yElement])
  exact DFunLike.congr_fun h g

theorem coe_finiteFrobeniusAut
    (g : adjointGroup t.tag K) :
    (t.finiteFrobeniusAut K g : ModGL t.tag K) =
      entrywiseGL t.tag K (frobenius K t.prime) g :=
  rfl

theorem finiteFrobeniusAut_pow_xElement
    (a : ℕ) (i : Fin t.tag.rank) (c : K) :
    (t.finiteFrobeniusAut K ^ a) (xElement i c) = xElement i (c ^ t.prime ^ a) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, MulAut.mul_apply]
    change (t.finiteFrobeniusAut K ^ a) (frobeniusTwist t.tag K (frobenius K t.prime)
      (xElement i c)) = _
    rw [frobeniusTwist_xElement, frobenius_def, ih, ← pow_mul, ← pow_succ']

theorem finiteFrobeniusAut_pow_yElement
    (a : ℕ) (i : Fin t.tag.rank) (c : K) :
    (t.finiteFrobeniusAut K ^ a) (yElement i c) = yElement i (c ^ t.prime ^ a) := by
  induction a generalizing c with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, MulAut.mul_apply]
    change (t.finiteFrobeniusAut K ^ a) (frobeniusTwist t.tag K (frobenius K t.prime)
      (yElement i c)) = _
    rw [frobeniusTwist_yElement, frobenius_def, ih, ← pow_mul, ← pow_succ']

theorem finiteReeAut_toMonoidHom
    (a : ℕ) :
    (t.finiteReeAut K a).toMonoidHom =
      t.reeEndo K (shortFaithful (CharP.cast_eq_zero K t.prime)) a := by
  refine adjointGroup_hom_ext (fun i c => ?_) (fun i c => ?_)
  · change t.finiteExceptionalAut K ((t.finiteFrobeniusAut K ^ a) (xElement i c)) = _
    rw [finiteFrobeniusAut_pow_xElement, finiteExceptionalAut_xElement, reeEndo_xElement,
      ← pow_mul, relationExponent, relationExponent_eq]
  · change t.finiteExceptionalAut K ((t.finiteFrobeniusAut K ^ a) (yElement i c)) = _
    rw [finiteFrobeniusAut_pow_yElement, finiteExceptionalAut_yElement, reeEndo_yElement,
      ← pow_mul, relationExponent, relationExponent_eq]

theorem mem_finiteReeFixedGroup
    {a : ℕ} {g : adjointGroup t.tag K} :
    g ∈ t.finiteReeFixedGroup K a ↔ t.finiteReeAut K a g = g :=
  Iff.rfl

theorem map_subtype_finiteReeFixedGroup
    (a : ℕ) :
    (t.finiteReeFixedGroup K a).map (adjointGroup t.tag K).subtype =
      reeFixedGroup t.tag K t.perm (fun i => if i ∈ t.longSet then t.prime ^ a
        else t.prime ^ (a + 1)) := by
  rw [reeFixedGroup_eq (shortFaithful (CharP.cast_eq_zero K t.prime)) a, finiteReeFixedGroup,
    finiteReeAut_toMonoidHom]

end ReeTag

end CFSG.LieType.Ree
