module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueInput
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueLevi
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverUniqueOuter
public import CFSG.LieType.Multipliers.L34Upper
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Monster.B.TwoA.Census.CosetEnum
public import CFSG.Monster.Existence.Census.TrialityWitnesses
public import CFSG.Sporadic.Co1.Module.InvGroupBase
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10069Base
public import Certificates.Certificate10070
public import Certificates.Certificate10070Base
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate16005
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Steinberg.Exceptional CFSG.Monster.B.TwoA.Amalgam
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner centerQuotientOuterHom
  centerQuotient_outer_injective centerQuotient_conj congr_conj equivalence)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk)
open scoped MatrixGroups

section ConjSL

variable {F : Type*} [Field F]

@[expose] noncomputable def conjMat (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  (g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem det_conjMat (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    (conjMat g M).det = M.det := by
  rw [conjMat, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) M.det, mul_assoc,
    ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, mul_one]

theorem conjMat_mul (g : GL (Fin 3) F) (M N : Matrix (Fin 3) (Fin 3) F) :
    conjMat g (M * N) = conjMat g M * conjMat g N := by
  simp only [conjMat, mul_assoc]
  rw [← mul_assoc (((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)), Units.inv_mul, one_mul]

theorem conjMat_conjMat (g h : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    conjMat g (conjMat h M) = conjMat (g * h) M := by
  simp only [conjMat, mul_inv_rev, Units.val_mul, mul_assoc]

theorem conjMat_one (M : Matrix (Fin 3) (Fin 3) F) : conjMat 1 M = M := by
  simp [conjMat]

@[expose] noncomputable def conjSLFun (g : GL (Fin 3) F) (A : SL(3, F)) : SL(3, F) :=
  ⟨conjMat g A, by rw [det_conjMat, A.2]⟩

theorem coe_conjSLFun (g : GL (Fin 3) F) (A : SL(3, F)) :
    (conjSLFun g A : Matrix (Fin 3) (Fin 3) F) = conjMat g A :=
  rfl

theorem conjSLFun_conjSLFun (g h : GL (Fin 3) F) (A : SL(3, F)) :
    conjSLFun g (conjSLFun h A) = conjSLFun (g * h) A :=
  Subtype.ext (conjMat_conjMat g h A)

theorem conjSLFun_one (A : SL(3, F)) : conjSLFun 1 A = A :=
  Subtype.ext (conjMat_one (A : Matrix (Fin 3) (Fin 3) F))

@[expose] noncomputable def conjSLHom : GL (Fin 3) F →* MulAut SL(3, F) where
  toFun g :=
    { toFun := conjSLFun g
      invFun := conjSLFun g⁻¹
      left_inv := fun A => by rw [conjSLFun_conjSLFun, inv_mul_cancel, conjSLFun_one]
      right_inv := fun A => by rw [conjSLFun_conjSLFun, mul_inv_cancel, conjSLFun_one]
      map_mul' := fun A B => Subtype.ext (conjMat_mul g A B) }
  map_one' := MulEquiv.ext fun A => conjSLFun_one A
  map_mul' g h := MulEquiv.ext fun A => (conjSLFun_conjSLFun g h A).symm

theorem coe_conjSLHom (g : GL (Fin 3) F) (A : SL(3, F)) :
    ((conjSLHom g A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

end ConjSL

section Quot

variable {X : Type} [Group X]

@[expose] noncomputable def quotCover
    (ε : X ⧸ center X ≃* stdGroup) : X →* stdGroup :=
  ε.toMonoidHom.comp (QuotientGroup.mk' (center X))

theorem quotCover_apply
    (ε : X ⧸ center X ≃* stdGroup) (x : X) :
    quotCover ε x = ε (x : X ⧸ center X) :=
  rfl

theorem ker_quotCover
    (ε : X ⧸ center X ≃* stdGroup) : (quotCover ε).ker = center X := by
  ext x
  rw [MonoidHom.mem_ker, quotCover_apply, map_eq_one_iff _ ε.injective, QuotientGroup.eq_one_iff]

theorem isDoubleCover_quotCover
    (ε : X ⧸ center X ≃* stdGroup) (h2 : Nat.card (center X) = 2) :
    IsDoubleCover (quotCover ε) where
  surjective := ε.surjective.comp (QuotientGroup.mk'_surjective _)
  ker_le_center := (ker_quotCover ε).le
  card_ker := by rw [ker_quotCover, h2]

theorem IsDoubleCover.twist
    {π : X →* stdGroup} (hπ : IsDoubleCover π) (α : MulAut stdGroup) :
    IsDoubleCover (α.toMonoidHom.comp π) := by
  have hker : (α.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ α.injective]
  exact ⟨α.surjective.comp hπ.surjective, hker ▸ hπ.ker_le_center, hker ▸ hπ.card_ker⟩

end Quot

section SL

variable
    {X : Type} [Group X] {π : X →* stdGroup}
  (eK : SL(3, GaloisField 2 (2 * 1)) ≃* (twistedE6Datum 2 1).levi levi34)

@[expose] noncomputable def fibreSL
    (π : X →* stdGroup) :
    fibre34 π →* SL(3, GaloisField 2 (2 * 1)) :=
  eK.symm.toMonoidHom.comp (fibre34Hom π)

theorem fibreSL_apply
    (x : fibre34 π) : fibreSL eK π x = eK.symm (fibre34Hom π x) :=
  rfl

theorem ker_fibreSL
    : (fibreSL eK π).ker = (fibre34Hom π).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, fibreSL_apply, map_eq_one_iff _ eK.symm.injective]

theorem fibreSL_surjective
    (hπ : IsDoubleCover π) : Function.Surjective (fibreSL eK π) :=
  eK.symm.surjective.comp (fibre34Hom_surjective hπ)

theorem ker_fibreSL_le_center
    (hπ : IsDoubleCover π) :
    (fibreSL eK π).ker ≤ center (fibre34 π) :=
  (ker_fibreSL eK).le.trans (ker_fibre34Hom_le_center hπ)

theorem card_ker_fibreSL
    (hπ : IsDoubleCover π) : Nat.card (fibreSL eK π).ker = 2 := by
  rw [ker_fibreSL, card_ker_fibre34Hom hπ]

end SL

section Twist

variable {X : Type} [Group X]

@[expose] noncomputable def fibre34Twist
    (π : X →* stdGroup) {δ : MulAut stdGroup}
    {γ : MulAut ((twistedE6Datum 2 1).levi levi34)}
    (h : ∀ v : (twistedE6Datum 2 1).levi levi34, δ (isogenyStd v) = isogenyStd (γ v)) :
    fibre34 π ≃* fibre34 (δ.toMonoidHom.comp π) :=
  fibre34Equiv (MulEquiv.refl X) γ
    (fun x v hx => by
      change δ (π x) = _
      rw [hx]
      exact h v)
    (fun x v hx => by
      apply δ.injective
      rw [h, MulEquiv.apply_symm_apply]
      exact hx)

theorem fibre34Hom_fibre34Twist
    (π : X →* stdGroup) {δ : MulAut stdGroup}
    {γ : MulAut ((twistedE6Datum 2 1).levi levi34)}
    (h : ∀ v : (twistedE6Datum 2 1).levi levi34, δ (isogenyStd v) = isogenyStd (γ v))
    (x : fibre34 π) :
    fibre34Hom (δ.toMonoidHom.comp π) (fibre34Twist π h x) = γ (fibre34Hom π x) :=
  rfl

@[expose] noncomputable def fibre34OfAut
    (π : X →* stdGroup) {δ : MulAut stdGroup}
    (α : MulAut X) (hα : ∀ x, π (α x) = δ (π x)) :
    fibre34 (δ.toMonoidHom.comp π) ≃* fibre34 π :=
  fibre34Equiv α (MulEquiv.refl _)
    (fun x v hx => by
      rw [hα]
      exact hx)
    (fun x v hx => by
      change δ (π (α.symm x)) = _
      rw [← hα, MulEquiv.apply_symm_apply]
      exact hx)

theorem fibre34Hom_fibre34OfAut
    (π : X →* stdGroup) {δ : MulAut stdGroup}
    (α : MulAut X) (hα : ∀ x, π (α x) = δ (π x)) (x : fibre34 (δ.toMonoidHom.comp π)) :
    fibre34Hom π (fibre34OfAut π α hα x) = fibre34Hom (δ.toMonoidHom.comp π) x :=
  rfl

end Twist

theorem derived_Eam_facts :
    Group.IsPerfect (commutator Eam) ∧ Finite (commutator Eam) ∧
      Nat.card (center (commutator Eam)) = 2 ∧
      Nonempty ((commutator Eam) ⧸ center (commutator Eam) ≃* stdGroup) := by
  obtain ⟨-, hperf, -, hZ, hc, ⟨e⟩, -, hcard, -⟩ := short_F4_derived_standard_perfect_cover
  have hZ' : center (commutator Eam) = (zpowers cE').subgroupOf (commutator Eam) := by
    rw [← hZ, subgroupOf, comap_map_eq_self_of_injective (commutator Eam).subtype_injective]
  refine ⟨hperf, Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num), ?_,
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ').trans e⟩⟩
  rw [← card_map_of_injective (commutator Eam).subtype_injective, hZ, hc]

theorem natCard_galoisField_two_two : Nat.card (GaloisField 2 (2 * 1)) = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

section Diag

variable
    {e : SL(3, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1} (he : Function.Injective e)
  (hrange : e.range = (twistedE6Datum 2 1).levi levi34)

@[expose] noncomputable def leviSLEquiv :
    SL(3, GaloisField 2 (2 * 1)) ≃* (twistedE6Datum 2 1).levi levi34 :=
  (MonoidHom.ofInjective he).trans (MulEquiv.subgroupCongr hrange)

theorem coe_leviSLEquiv
    (A : SL(3, GaloisField 2 (2 * 1))) :
    (leviSLEquiv he hrange A : twistedE6Group 2 1) = e A :=
  rfl

@[expose] noncomputable def leviSLConj
    (g : GL (Fin 3) (GaloisField 2 (2 * 1))) :
    MulAut ((twistedE6Datum 2 1).levi levi34) :=
  MulAut.congr (leviSLEquiv he hrange) (conjSLHom g)

theorem leviSLEquiv_symm_leviSLConj_pow
    (g : GL (Fin 3) (GaloisField 2 (2 * 1))) (k : ℕ)
    (v : (twistedE6Datum 2 1).levi levi34) :
    (leviSLEquiv he hrange).symm ((leviSLConj he hrange g ^ k) v) =
      conjSLHom (g ^ k) ((leviSLEquiv he hrange).symm v) := by
  rw [leviSLConj, ← map_pow, ← map_pow]
  exact (leviSLEquiv he hrange).symm_apply_apply _

theorem isogenyStd_leviSLConj_pow
    {g : GL (Fin 3) (GaloisField 2 (2 * 1))} {δ : MulAut stdGroup}
    (hδ : ∀ A, δ (isogenyStd (e A)) = isogenyStd (e (conjSLHom g A)))
    (k : ℕ) (v : (twistedE6Datum 2 1).levi levi34) :
    (δ ^ k) (isogenyStd v) = isogenyStd ((leviSLConj he hrange g ^ k) v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, ih]
    have h := hδ ((leviSLEquiv he hrange).symm ((leviSLConj he hrange g ^ k) v))
    rw [← coe_leviSLEquiv he hrange, ← coe_leviSLEquiv he hrange,
      MulEquiv.apply_symm_apply] at h
    exact h

end Diag

theorem exists_fibre34_mulEquiv_pow
    {X₁ X₂ : Type} [Group X₁] [Group X₂] [Finite X₁] [Finite X₂]
    [Group.IsPerfect X₁] [Group.IsPerfect X₂] {π₁ : X₁ →* stdGroup} {π₂ : X₂ →* stdGroup}
    (h₁ : IsDoubleCover π₁) (h₂ : IsDoubleCover π₂)
    {e : SL(3, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1} (he : Function.Injective e)
    (hrange : e.range = (twistedE6Datum 2 1).levi levi34)
    {g : GL (Fin 3) (GaloisField 2 (2 * 1))}
    (hdet : (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))).det ≠ 1) :
    ∃ k : ℕ, ∃ φ : fibre34 π₁ ≃* fibre34 π₂,
      ∀ x, fibre34Hom π₂ (φ x) = (leviSLConj he hrange g ^ k) (fibre34Hom π₁ x) := by
  have := isPerfect_fibre34 h₁
  have := isPerfect_fibre34 h₂
  obtain ⟨k, -, φ, hφ⟩ := CFSG.LieType.Multipliers.L34Upper.exists_mulEquiv_conj_pow
    natCard_galoisField_two_two g hdet (fibreSL (leviSLEquiv he hrange) π₁)
    (fibreSL (leviSLEquiv he hrange) π₂) (fibreSL_surjective _ h₁) (fibreSL_surjective _ h₂)
    (ker_fibreSL_le_center _ h₁) (ker_fibreSL_le_center _ h₂) (card_ker_fibreSL _ h₁)
    (card_ker_fibreSL _ h₂)
  refine ⟨k, φ, fun x => (leviSLEquiv he hrange).symm.injective ?_⟩
  rw [leviSLEquiv_symm_leviSLConj_pow]
  exact Subtype.ext (hφ x)

theorem not_exists_fibre34_aut
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    {π : X →* stdGroup} (hπ : IsDoubleCover π)
    {e : SL(3, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1} (he : Function.Injective e)
    (hrange : e.range = (twistedE6Datum 2 1).levi levi34)
    {g : GL (Fin 3) (GaloisField 2 (2 * 1))}
    (hdet : (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))).det ≠ 1)
    (Φ : fibre34 π ≃* fibre34 π)
    (hΦ : ∀ x, fibre34Hom π (Φ x) = leviSLConj he hrange g (fibre34Hom π x)) : False := by
  have := isPerfect_fibre34 hπ
  refine CFSG.LieType.Multipliers.L34Upper.not_exists_mulEquiv_conj natCard_galoisField_two_two
    g hdet (fibreSL (leviSLEquiv he hrange) π) (fibreSL_surjective _ hπ)
    (ker_fibreSL_le_center _ hπ) (card_ker_fibreSL _ hπ) ⟨Φ, fun x => ?_⟩
  have h2 := leviSLEquiv_symm_leviSLConj_pow he hrange g 1 (fibre34Hom π x)
  simp only [pow_one] at h2
  have h3 : fibreSL (leviSLEquiv he hrange) π (Φ x) =
      conjSLHom g (fibreSL (leviSLEquiv he hrange) π x) := by
    rw [fibreSL_apply, fibreSL_apply, hΦ, h2]
  rw [h3]
  rfl

theorem doubleCoverUnique_of_inputs
    (h3 : LeviA2DiagInput) : DoubleCoverUnique := by
  intro A _ _ hA hZ hε
  obtain ⟨ε⟩ := hε
  have : Group.IsPerfect A := Group.isPerfect_def.2 hA.1
  obtain ⟨e, g, u, he, hrange, hdet, hδ⟩ := h3
  obtain ⟨hEperf, hEfin, hE2, ⟨εE⟩⟩ := derived_Eam_facts
  obtain ⟨δ, hδdef⟩ : ∃ δ : MulAut stdGroup, δ = compatDiagAutHom TwistTag.E6 K barHom u :=
    ⟨_, rfl⟩
  have hδ' : ∀ A, δ (isogenyStd (e A)) = isogenyStd (e (conjSLHom g A)) := fun A => by
    rw [hδdef]
    exact hδ A _ rfl
  have hA2 := isDoubleCover_quotCover ε hZ
  have hE2' := isDoubleCover_quotCover εE hE2
  obtain ⟨k, φ, hφ⟩ := exists_fibre34_mulEquiv_pow hA2 hE2' he hrange hdet
  have hδk := isogenyStd_leviSLConj_pow he hrange hδ' k
  have hA2' : IsDoubleCover ((δ ^ k).toMonoidHom.comp (quotCover ε)) := hA2.twist (δ ^ k)
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : fibre34 (quotCover ε) ≃* fibre34 ((δ ^ k).toMonoidHom.comp (quotCover ε)),
      Θ = fibre34Twist (quotCover ε) hδk := ⟨_, rfl⟩
  have hΘx : ∀ x, fibre34Hom _ (Θ x) = (leviSLConj he hrange g ^ k) (fibre34Hom _ x) :=
    fun x => by rw [hΘ]; rfl
  have hψ34 : ∀ y, fibreHom (quotCover εE) ((Θ.symm.trans φ) y) =
      fibreHom ((δ ^ k).toMonoidHom.comp (quotCover ε)) y := by
    intro y
    have h1 : fibre34Hom (quotCover εE) (φ (Θ.symm y)) =
        fibre34Hom ((δ ^ k).toMonoidHom.comp (quotCover ε)) y := by
      rw [hφ, ← hΘx, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val h1
  have := isPerfect_fibre hA2'
  have := isPerfect_fibre hE2'
  have := finite_fibre (π := (δ ^ k).toMonoidHom.comp (quotCover ε))
  have := finite_fibre (π := quotCover εE)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_of_levi34 (fibreHom_surjective hA2')
    (fibreHom_surjective hE2') (ker_fibreHom_le_center hA2') (ker_fibreHom_le_center hE2')
    (isPGroup_ker_fibreHom hA2') (isPGroup_ker_fibreHom hE2') (Θ.symm.trans φ) hψ34
  exact nonempty_mulEquiv_of_fibre hA2' hE2' ψ hψ

section Outer

variable {X : Type} [Group X]

@[expose] noncomputable def autCover
    (ε : X ⧸ center X ≃* stdGroup) : MulAut X →* MulAut stdGroup :=
  (MulAut.congr ε).toMonoidHom.comp (centerQuotientHom X)

theorem quotCover_autCover
    (ε : X ⧸ center X ≃* stdGroup) (β : MulAut X) (x : X) :
    quotCover ε (β x) = autCover ε β (quotCover ε x) := by
  change ε (QuotientGroup.mk' _ (β x)) =
    ε (centerQuotientHom X β (ε.symm (ε (QuotientGroup.mk' _ x))))
  rw [MulEquiv.symm_apply_apply]
  exact congrArg ε (onCenterQuotient_apply_mk β x).symm

theorem autCover_conj
    (ε : X ⧸ center X ≃* stdGroup) (t : X) :
    autCover ε (MulAut.conj t) = MulAut.conj (quotCover ε t) := by
  change MulAut.congr ε (centerQuotientHom X (MulAut.conj t)) = _
  rw [centerQuotient_conj, congr_conj]
  rfl

end Outer

section OutBound

variable
    {X : Type} [Group X] (ε : X ⧸ center X ≃* stdGroup)

theorem autCover_ne
    [Finite X] [Group.IsPerfect X] (h2 : Nat.card (center X) = 2)
    {e : SL(3, GaloisField 2 (2 * 1)) →* twistedE6Group 2 1} (he : Function.Injective e)
    (hrange : e.range = (twistedE6Datum 2 1).levi levi34)
    {g : GL (Fin 3) (GaloisField 2 (2 * 1))}
    (hdet : (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * 1))).det ≠ 1) {δ : MulAut stdGroup}
    (hδ : ∀ A, δ (isogenyStd (e A)) = isogenyStd (e (conjSLHom g A))) (α : MulAut X) :
    autCover ε α ≠ δ := by
  intro hα
  have hX := isDoubleCover_quotCover ε h2
  have hαx : ∀ x, quotCover ε (α x) = δ (quotCover ε x) := fun x => by
    rw [quotCover_autCover, hα]
  have hδ1 := isogenyStd_leviSLConj_pow he hrange hδ 1
  simp only [pow_one] at hδ1
  exact not_exists_fibre34_aut hX he hrange hdet
    ((fibre34Twist (quotCover ε) hδ1).trans (fibre34OfAut (quotCover ε) α hαx))
    fun x => (fibre34Hom_fibre34OfAut _ α hαx _).trans (fibre34Hom_fibre34Twist _ hδ1 x)

@[expose] noncomputable def outerCover
    : Outer X →* Outer stdGroup :=
  (equivalence ε).toMonoidHom.comp (centerQuotientOuterHom X)

theorem outerCover_injective
    [Group.IsPerfect X] : Function.Injective (outerCover ε) :=
  (equivalence ε).injective.comp (centerQuotient_outer_injective X)

theorem outerCover_mk (α : MulAut X) :
    outerCover ε (QuotientGroup.mk α) = QuotientGroup.mk (autCover ε α) :=
  rfl

theorem card_outer_le_two_of_forall_ne
    [Group.IsPerfect X] (h2 : Nat.card (center X) = 2)
    {δ : MulAut stdGroup}
    (hδu : ∃ u, δ = compatDiagAutHom TwistTag.E6 K barHom u)
    (hnot : ∀ α : MulAut X, autCover ε α ≠ δ) : Nat.card (Outer X) ≤ 2 := by
  have hX := isDoubleCover_quotCover ε h2
  have hu : (QuotientGroup.mk δ : Outer stdGroup) ∉ (outerCover ε).range := by
    rintro ⟨o, ho⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective o
    rw [outerCover_mk] at ho
    obtain ⟨s, hs⟩ := QuotientGroup.eq.1 ho
    obtain ⟨t, rfl⟩ := hX.surjective s
    refine hnot (α * MulAut.conj t) ?_
    have h1 : autCover ε (MulAut.conj t) = (autCover ε α)⁻¹ * δ := (autCover_conj ε t).trans hs
    rw [map_mul, h1, mul_inv_cancel_left]
  rw [Nat.card_congr (MonoidHom.ofInjective (outerCover_injective ε)).toEquiv]
  exact card_le_two_of_not_mem_std hδu hu

end OutBound

theorem coverOuterLeTwo_of_inputs
    (h3 : LeviA2DiagInput) : CoverOuterLeTwo := by
  obtain ⟨e, g, u, he, hrange, hdet, hδ⟩ := h3
  obtain ⟨hEperf, hEfin, hE2, ⟨εE⟩⟩ := derived_Eam_facts
  obtain ⟨δ, hδdef⟩ : ∃ δ : MulAut stdGroup, δ = compatDiagAutHom TwistTag.E6 K barHom u :=
    ⟨_, rfl⟩
  have hδ' : ∀ A, δ (isogenyStd (e A)) = isogenyStd (e (conjSLHom g A)) := fun A => by
    rw [hδdef]
    exact hδ A _ rfl
  change Nat.card (Outer (commutator Eam)) ≤ 2
  exact card_outer_le_two_of_forall_ne εE hE2 ⟨u, hδdef⟩ (autCover_ne εE hE2 he hrange hdet hδ')

end CFSG.EvenSmallLie.TwoE6
