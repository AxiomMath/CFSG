module

public import CFSG.Adapters.TauCetiExceptional.ReeNative
public import CFSG.Adapters.TauCetiExceptional.ReeFrob

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge.BigCell TauCeti
open CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti.G2ShortRoot.PrimeField

section Incl

variable (K L : Type) [Field K] [Field L] [Algebra K L]

@[expose] def incl
    : adjointGroup .G2 K →* adjointGroup .G2 L :=
  MonoidHom.codRestrict ((baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype) _
    fun g => baseChangeGL_mem_adjointGroup (algebraMap K L) g.2

variable {K L}

theorem coe_incl
    (g : adjointGroup .G2 K) :
    ((incl K L g : adjointGroup .G2 L) : ModGL .G2 L) =
      baseChangeGL (algebraMap K L) (g : ModGL .G2 K) :=
  rfl

theorem incl_injective
    : Function.Injective (incl K L) := fun _ _ e =>
  Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val e))

theorem incl_xElement
    (i : Fin Tag.G2.rank) (c : K) :
    incl K L (xElement i c) = xElement i (algebraMap K L c) :=
  Subtype.ext (baseChangeGL_xUnit (algebraMap K L) i c)

theorem incl_yElement
    (i : Fin Tag.G2.rank) (c : K) :
    incl K L (yElement i c) = yElement i (algebraMap K L c) :=
  Subtype.ext (baseChangeGL_yUnit (algebraMap K L) i c)

end Incl

variable (K : Type) [Field K] [Finite K] [CharP K 3]

@[expose] def reeF
    (a : ℕ) : adjointGroup .G2 K →* adjointGroup .G2 K :=
  haveI : CharP K ReeTag.G2.prime := ‹CharP K 3›
  (ReeTag.G2.reeAut K a).toMonoidHom

variable {K}

theorem reeF_xElement
    (a : ℕ) (i : Fin Tag.G2.rank) (c : K) :
    reeF K a (xElement i c) = xElement (reeG2Perm i) (c ^ reeExp a i) :=
  haveI : CharP K ReeTag.G2.prime := ‹CharP K 3›
  ((exceptional_reeFixedGroup_eq .G2 K a).1 i c).1

theorem reeF_yElement
    (a : ℕ) (i : Fin Tag.G2.rank) (c : K) :
    reeF K a (yElement i c) = yElement (reeG2Perm i) (c ^ reeExp a i) :=
  haveI : CharP K ReeTag.G2.prime := ‹CharP K 3›
  ((exceptional_reeFixedGroup_eq .G2 K a).1 i c).2

theorem reeFixedGroup_eq_map_fixedSubgroup
    (a : ℕ) :
    reeFixedGroup .G2 K reeG2Perm (fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) =
      (fixedSubgroup (reeF K a)).map (adjointGroup .G2 K).subtype :=
  haveI : CharP K ReeTag.G2.prime := ‹CharP K 3›
  (exceptional_reeFixedGroup_eq .G2 K a).2.2

@[expose] def nativeModelEquiv
    (a : ℕ) :
    CFSG.Blueprint.DerivedCentralQuotient
        (reeFixedGroup .G2 K reeG2Perm fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃*
      FixedPointCandidate (reeF K a) :=
  CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
    ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_fixedSubgroup a)).trans
      ((fixedSubgroup (reeF K a)).equivMapOfInjective _ Subtype.val_injective).symm)

variable {L : Type} [Field L] [Algebra K L] [Algebra (ZMod 3) L] (hZ : ZerosInAdjoint L)
variable {a : ℕ} {S : points L →* points L}

theorem nativeSteinberg_comp_incl
    (hS : IsReeSteinberg a S) :
    (nativeSteinberg hZ S).comp (incl K L) = (incl K L).comp (reeF K a) := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, incl_xElement, nativeSteinberg_xElement hZ hS,
      reeF_xElement, incl_xElement, map_pow]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, incl_yElement, nativeSteinberg_yElement hZ hS,
      reeF_yElement, incl_yElement, map_pow]

variable [Algebra.IsAlgebraic K L]

theorem fixedSubgroup_nativeSteinberg
    (hS : IsReeSteinberg a S)
    (hSS : ∀ g, S (S g) = frobenius (2 * a + 1) L g) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    fixedSubgroup (nativeSteinberg hZ S) = (fixedSubgroup (reeF K a)).map (incl K L) := by
  apply le_antisymm
  · intro x hx
    rw [mem_fixedSubgroup] at hx
    have hxy : adEquiv hZ ((adEquiv hZ).symm x) = x := MulEquiv.apply_symm_apply _ _
    have hSy : S ((adEquiv hZ).symm x) = (adEquiv hZ).symm x := by
      apply (adEquiv hZ).injective
      rw [hxy]
      exact hx
    have hfr : frobenius (2 * a + 1) L ((adEquiv hZ).symm x) = (adEquiv hZ).symm x := by
      rw [← hSS, hSy, hSy]
    set φ : L →+* L := (((FiniteField.frobeniusAlgHom (ZMod 3) L) ^ (2 * a + 1) :
      L →ₐ[ZMod 3] L) : L →+* L) with hφdef
    have hφ : ∀ c, φ c = c ^ Nat.card K := fun c => by
      rw [hK, hφdef]
      simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 3) L (2 * a + 1) c
    have hfix : Units.map (entrywiseHom φ) (x : ModGL .G2 L) = x := by
      have h := adPoints_frobenius (2 * a + 1) ((adEquiv hZ).symm x)
      rw [hfr, ← coe_adEquiv hZ, hxy] at h
      exact h.symm
    obtain ⟨g, hg, hgx⟩ := mem_map_adjointGroup_G2_of_frobenius_fixed φ hφ x.2 hfix
    have hincl : incl K L ⟨g, hg⟩ = x := Subtype.ext hgx
    refine ⟨⟨g, hg⟩, ?_, hincl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroup]
    apply incl_injective (K := K) (L := L)
    have e := congrArg (fun f => f ⟨g, hg⟩) (nativeSteinberg_comp_incl hZ hS)
    simp only [MonoidHom.comp_apply] at e
    rw [← e, hincl, hx]
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroup] at hg
    rw [mem_fixedSubgroup]
    have e := congrArg (fun f => f g) (nativeSteinberg_comp_incl hZ hS)
    simp only [MonoidHom.comp_apply] at e
    rw [e, hg]

@[expose] def fixedPointCandidateNativeEquiv
    (hS : IsReeSteinberg a S)
    (hSS : ∀ g, S (S g) = frobenius (2 * a + 1) L g) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    FixedPointCandidate (reeF K a) ≃* FixedPointCandidate (nativeSteinberg hZ S) :=
  TauCeti.DerivedCentralQuotient.congr
    (((fixedSubgroup (reeF K a)).equivMapOfInjective (incl K L) incl_injective).trans
      (MulEquiv.subgroupCongr (fixedSubgroup_nativeSteinberg hZ hS hSS hK).symm))

include hZ in
theorem nonempty_reeModel_equiv
    (hS : IsReeSteinberg a S)
    (hSS : ∀ g, S (S g) = frobenius (2 * a + 1) L g) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    Nonempty (CFSG.Blueprint.DerivedCentralQuotient
        (reeFixedGroup .G2 K reeG2Perm fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃*
      FixedPointCandidate S) :=
  ⟨((nativeModelEquiv a).trans (fixedPointCandidateNativeEquiv hZ hS hSS hK)).trans
    (fixedPointCandidateEquiv hZ S).symm⟩

end CFSG.TauCetiBridge.Ree
