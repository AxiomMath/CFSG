module

public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolution
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.ToralSign

open scoped CFSG.ConvolutionPoints

section Prelim

variable {τ : Tag} {k : Type} [Field k]

theorem mem_rootCharStabilizer_signCharTuple
    (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) {w : WeylGroup τ} :
    w ∈ rootCharStabilizer (signCharTuple (k := k) χ) ↔ w ∈ charStabilizer χ := by
  change (∀ v, rootChar (signCharTuple (k := k) χ) (w • v) = rootChar (signCharTuple χ) v) ↔ _
  simp only [rootChar_signCharTuple, (intUnitsMap_injective hk).eq_iff]
  rfl

theorem kernelReflectionGroup_signCharTuple
    (hk : ringChar k ≠ 2)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) :
    kernelReflectionGroup (signCharTuple (k := k) χ) = kernelWeylGroup χ := by
  rw [kernelReflectionGroup, kernelWeylGroup, rootCharKernel_signCharTuple hk]

theorem mapsRootLines_wordWeylMatrix
    (l : List (Fin τ.rank)) :
    MapsRootLines (wordWeylMatrix τ k l) (ToralSign.wordElt τ l) :=
  mapsRootLines_list_prod l.reverse

theorem wordWeylMatrix_mem_monomialSubgroup
    (l : List (Fin τ.rank)) :
    wordWeylMatrix τ k l ∈ monomialSubgroup τ k :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

end Prelim

section General

@[expose] def IsFiniteToralTwistReduction
    (τ : Tag) (k : Type) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (e : ℕ) (D : ModGL τ k) (reps : List (SignRep τ)) (x : ModGL τ k) : Prop :=
  ∃ r ∈ reps, ∃ l ∈ r.omegaWords,
    ToralSign.wordElt τ l ∈ kernelPosStabilizer (signMaskChar τ r.mask) ∧
    Finite (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
      (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))) ∧
    ∃ g₁ ∈ adjointGroup τ k, ∀ ℓ : ℕ, ℓ.Prime →
      (∀ L : Subgroup (ModGL τ k),
        (L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
            fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
              Subgroup.centralizer {x} ∧
          CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
            (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
              Subgroup.centralizer {x}))) ↔
        (L.map (MulAut.conj g₁).toMonoidHom ≤ fixedPointsIn
            (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
            (frobTwistGL τ k p e (wordWeylMatrix τ k l * D)) ∧
          CFSG.IsPComponent ℓ ((L.map (MulAut.conj g₁).toMonoidHom).subgroupOf
            (fixedPointsIn (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
              (frobTwistGL τ k p e (wordWeylMatrix τ k l * D)))))) ∧
      ∃ eqv : {L : Subgroup (ModGL τ k) // L ≤ ⁅fixedPointsIn (adjointGroup τ k)
            (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
              Subgroup.centralizer {x} ∧
          CFSG.IsPComponent ℓ (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
            (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
              Subgroup.centralizer {x}))} ≃
        {L : Subgroup (ModGL τ k) // L ≤ fixedPointsIn
            (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
            (frobTwistGL τ k p e (wordWeylMatrix τ k l * D)) ∧
          CFSG.IsPComponent ℓ (L.subgroupOf (fixedPointsIn
            (torusGroup τ k ⊔ rootSpan τ k (kernelRoots (signMaskChar τ r.mask)))
            (frobTwistGL τ k p e (wordWeylMatrix τ k l * D))))},
        ∀ L, (eqv L : Subgroup (ModGL τ k)) =
          (L : Subgroup (ModGL τ k)).map (MulAut.conj g₁).toMonoidHom

variable (p : ℕ) [Fact p.Prime] {τ : Tag} {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem isFiniteToralTwistReduction_of_reps
    (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e) {D : ModGL τ k}
    (hD : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (ρ : Equiv.Perm (Fin τ.rank))
    (hFd : ∀ b : Fin τ.rank → kˣ, (∀ i, b i = 1 ∨ b i = -1) →
      frobTwistGL τ k p e D (rootDiagUnit τ b) = rootDiagUnit τ fun i => b (ρ.symm i))
    (reps : List (SignRep τ))
    (hfix : ∀ r ∈ reps, permChar ρ (signMaskChar τ r.mask) = signMaskChar τ r.mask)
    (hrep : ∀ χ, permChar ρ χ ∈ charOrbit χ →
      ∃ r ∈ reps, χ ∈ charOrbit (signMaskChar τ r.mask))
    (hΩ : ∀ r ∈ reps, (kernelPosStabilizer (signMaskChar τ r.mask) : Set (WeylGroup τ)) =
      {w | ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = w})
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {x : ModGL τ k} (hx : x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    (hx2 : x ^ 2 = 1) :
    IsFiniteToralTwistReduction τ k p e D reps x := by
  classical
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  set F := frobTwistGL τ k p e D with hF
  set R := fixedPointsIn (adjointGroup τ k) F with hR
  have hFG : ∀ g ∈ adjointGroup τ k, F g ∈ adjointGroup τ k := fun g hg =>
    conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hg)
  obtain ⟨hxG, hxF⟩ := mem_fixedPointsIn.1 hx
  obtain ⟨g, hg, r, hr, hgx, hFt⟩ :=
    exists_conj_eq_rootDiagUnit_of_reps hp ρ F hFG hFd reps hfix hrep hxG hxF hx2
  set χ := signMaskChar τ r.mask with hχ
  set a := signCharTuple (k := k) χ with ha_def
  have ha : ∀ i, a i = 1 ∨ a i = -1 := signCharTuple_sign χ
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_signCharTuple hk χ
  have hFgx : F g * x * (F g)⁻¹ = rootDiagUnit τ a := by
    rw [← hFt, ← hgx, map_mul, map_mul, map_inv, hxF]
  have hcZ : g * (F g)⁻¹ ∈ toralCentralizer τ k a := by
    refine mem_toralCentralizer.2 ⟨mul_mem hg (inv_mem (hFG g hg)), ?_⟩
    calc rootDiagUnit τ a * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ =
        (g * x * g⁻¹) * (g * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by rw [hgx]
      _ = g * (F g)⁻¹ * (F g * x * (F g)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
      _ = g * (F g)⁻¹ := by rw [hFgx]; group
  obtain ⟨-, -, ⟨hMZ, hMn, -, -, eW, heW⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk a ha
  obtain ⟨q, hq⟩ := eW.surjective (QuotientGroup.mk ⟨_, hcZ⟩)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hwχ : w ∈ charStabilizer χ := (mem_rootCharStabilizer_signCharTuple hk χ).1 hw
  obtain ⟨u, hu, hωΩ⟩ := exists_mul_mem_kernelPosStabilizer hwχ
  set ω := w * u with hω_def
  have huW : u ∈ kernelReflectionGroup a := by
    rw [kernelReflectionGroup_signCharTuple hk]
    exact hu
  have hωa : ω ∈ rootCharStabilizer a :=
    (mem_rootCharStabilizer_signCharTuple hk χ).2 (kernelPosStabilizer_le hωΩ)
  have hmk : (QuotientGroup.mk ⟨w, hw⟩ : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) =
        QuotientGroup.mk ⟨ω, hωa⟩ := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change w⁻¹ * (w * u) ∈ kernelReflectionGroup a
    rw [inv_mul_cancel_left]
    exact huW
  rw [hmk, heW, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  change (canonicalRep (coxeterSystem τ) k ω)⁻¹ * (g * (F g)⁻¹) ∈ toralRootGroup τ k a at hq
  obtain ⟨l, hl, hlω⟩ : ∃ l ∈ r.omegaWords, ToralSign.wordElt τ l = ω := by
    have h1 : ω ∈ (kernelPosStabilizer χ : Set (WeylGroup τ)) := hωΩ
    rw [hΩ r hr] at h1
    exact h1
  set N := wordWeylMatrix τ k l with hN_def
  set n := canonicalRep (coxeterSystem τ) k ω with hn_def
  have hh₀ : N * n⁻¹ ∈ torusGroup τ k := by
    refine mem_torusGroup_of_mapsRootLines_one (mul_mem (wordWeylMatrix_mem_monomialSubgroup l)
      (inv_mem (canonicalRep_mem_monomialSubgroup k ω))) ?_
    have h := (mapsRootLines_wordWeylMatrix (k := k) l).mul
      (mapsRootLines_canonicalRep (R := k) ω).inv
    rwa [hlω, mul_inv_cancel] at h
  have hnZ : n ∈ toralCentralizer τ k a := canonicalRep_mem_toralCentralizer hωa
  have hNZ : N ∈ toralCentralizer τ k a := by
    have h := mul_mem (torusGroup_le_toralCentralizer a hh₀) hnZ
    rwa [inv_mul_cancel_right] at h
  have hcv : ∃ m ∈ toralRootGroup τ k a, g * (F g)⁻¹ = m * N := by
    refine ⟨(N * n⁻¹)⁻¹ * (N * (n⁻¹ * (g * (F g)⁻¹)) * N⁻¹), mul_mem
      (inv_mem (le_sup_left (a := torusGroup τ k) hh₀))
      ((Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hNZ) _).1 hq), ?_⟩
    group
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have := commutator_subgroupOf_normal R
  have := isSolvable_quotient_commutator_subgroupOf R
  obtain ⟨z, hzM, -, -, hQfin, -, -, hcomp⟩ := rational_centralizer_cocycle_reduction_of_map_conj p
    hp he hD hRfin hRsub ha hg hgx hFt hNZ hcv
  have hSeq : (MulAut.conj N).toMonoidHom.comp F = frobTwistGL τ k p e (N * D) := by
    refine MonoidHom.ext fun y => ?_
    simp only [hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev]
    group
  rw [hSeq, toralRootGroup, hker] at hQfin hcomp
  have hzG : z ∈ adjointGroup τ k := (mem_toralCentralizer.1 (hMZ hzM)).1
  refine ⟨r, hr, l, hl, by rw [hlω]; exact hωΩ, hQfin, z * g, mul_mem hzG hg,
    fun ℓ hℓ => ⟨(hcomp ℓ hℓ).1, (hcomp ℓ hℓ).2.1⟩⟩

end General

section Node

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit [IsAlgClosed k] in
theorem frobTwistGL_diagramMap_rootDiagUnit_of_sign
    (t : TwistTag) (e : ℕ)
    {b : Fin t.tag.rank → kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) :
    frobTwistGL t.tag k p e (diagramMap t k) (rootDiagUnit t.tag b) =
      rootDiagUnit t.tag fun i => b (t.perm.symm i) := by
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p e hb]
  have h := congrArg (fun f : ModGL t.tag k →* ModGL t.tag k => f (rootDiagUnit t.tag b))
    (conj_diagramMap_eq_twistHom t k)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [h, twistHom_rootDiagUnit_eq]
  rfl

omit [IsAlgClosed k] in
theorem finite_fixedPointsIn_frobTwistGL {τ : Tag} {e d : ℕ}
    (he : 1 ≤ e) (hd : 1 ≤ d)
    {Q : ModGL τ k} (hQ : entrywiseFrobGL τ k p e Q = Q) (hQd : Q ^ d = 1) :
    Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e Q)) := by
  refine ((finite_setOf_entrywiseFrobGL_eq p (Nat.mul_le_mul he hd)).subset ?_).to_subtype
  intro g hg
  obtain ⟨-, hgF⟩ := mem_fixedPointsIn.1 hg
  have h := frobTwistGL_iterate p e hQ d g
  rw [Function.iterate_fixed hgF, hQd, one_mul, inv_one, mul_one] at h
  exact h.symm

variable (k) in
theorem rational_inner_involution_finite_toral_twist_reduction
    (hp : p ≠ 2) (e : ℕ)
    (he : 1 ≤ e) :
    (∀ x ∈ fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e 1), x ^ 2 = 1 →
      IsFiniteToralTwistReduction .E7 k p e 1 e7SignDiagramReps x) ∧
    (∀ x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)), x ^ 2 = 1 →
      IsFiniteToralTwistReduction TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)
        e6SignDiagramReps x) ∧
    (∀ x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)), x ^ 2 = 1 →
      IsFiniteToralTwistReduction TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)
        d4SignDiagramReps x) := by
  obtain ⟨h7, h6, h4⟩ := rational_toral_sign_diagram_arithmetic
  have hdiag : ∀ t : TwistTag, Finite (fixedPointsIn (adjointGroup t.tag k)
      (frobTwistGL t.tag k p e (diagramMap t k))) := fun t =>
    finite_fixedPointsIn_frobTwistGL p he (by cases t <;> decide)
      (units_map_entrywiseHom_diagramMap (t := t) (iterateFrobenius k p e))
      (diagramMap_pow_order t k)
  refine ⟨fun x hx hx2 => ?_, fun x hx hx2 => ?_, fun x hx hx2 => ?_⟩
  · refine isFiniteToralTwistReduction_of_reps p hp he (map_conj_one_adjointGroup _ k) 1
      (fun b hb => ?_) e7SignDiagramReps h7.permChar_eq h7.exists_rep
      h7.coe_kernelPosStabilizer
      (finite_fixedPointsIn_frobTwistGL p he le_rfl (map_one _) (one_pow 1)) hx hx2
    rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_of_sign p e hb, one_mul, inv_one,
      mul_one]
    rfl
  · exact isFiniteToralTwistReduction_of_reps p hp he
      (map_conj_diagramMap TwistTag.E6 k (Or.inl rfl)) TwistTag.E6.perm
      (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.E6 e hb)
      e6SignDiagramReps h6.permChar_eq h6.exists_rep h6.coe_kernelPosStabilizer
      (hdiag TwistTag.E6) hx hx2
  · exact isFiniteToralTwistReduction_of_reps p hp he
      (map_conj_diagramMap TwistTag.D4 k (Or.inl rfl)) TwistTag.D4.perm
      (fun b hb => frobTwistGL_diagramMap_rootDiagUnit_of_sign p TwistTag.D4 e hb)
      d4SignDiagramReps h4.permChar_eq h4.exists_rep h4.coe_kernelPosStabilizer
      (hdiag TwistTag.D4) hx hx2

end Node

end CFSG.LieType.AlgebraicGroups
