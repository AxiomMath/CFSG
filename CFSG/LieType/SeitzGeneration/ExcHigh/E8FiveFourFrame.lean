module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveInputs
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8D4D4Family
public import CFSG.LieType.AlgebraicGroups.KernelRootDescent
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwConj
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.RankThree.Chevalley.SteinbergBIWE8Classes

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE


theorem coprime_five_card_sub_one {K : Type} [Field K] [Finite K]
    (h5 : orderOf ((Nat.card K : ℕ) : ZMod 5) = 4) : Nat.Coprime 5 (Nat.card K - 1) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 fun hdvd => ?_
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  have h0 : ((Nat.card K - 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
  rw [Nat.cast_sub h1, Nat.cast_one, sub_eq_zero] at h0
  rw [h0, orderOf_one] at h5
  exact absurd h5 (by decide)

theorem canonicalRep_conj_mem_torus_sup_rootSpan {L : Type} [Field L] [IsAlgClosed L]
    (c : WeylGroup Tag.E8) :
    (canonicalRep (coxeterSystem Tag.E8) L c)⁻¹ *
        canonicalRep (coxeterSystem Tag.E8) L (c * d4d4W * c⁻¹) *
        canonicalRep (coxeterSystem Tag.E8) L c ∈
      torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (kernelRoots d4d4Char) := by
  obtain ⟨k₁, hk₁, e₁⟩ := canonicalRep_mul_mem (τ := Tag.E8) (R := L) c d4d4W
  obtain ⟨k₂, hk₂, e₂⟩ := canonicalRep_mul_mem (τ := Tag.E8) (R := L) (c * d4d4W) c⁻¹
  obtain ⟨k₃, hk₃, e₃⟩ := canonicalRep_mul_mem (τ := Tag.E8) (R := L) c⁻¹ c
  rw [inv_mul_cancel, canonicalRep_one, mul_one] at e₃
  have hcd : canonicalRep (coxeterSystem Tag.E8) L (c * d4d4W) =
      k₁⁻¹ * (canonicalRep (coxeterSystem Tag.E8) L c *
        canonicalRep (coxeterSystem Tag.E8) L d4d4W) := by
    rw [e₁]
    group
  have hw : canonicalRep (coxeterSystem Tag.E8) L (c * d4d4W * c⁻¹) =
      k₂⁻¹ * (canonicalRep (coxeterSystem Tag.E8) L (c * d4d4W) *
        canonicalRep (coxeterSystem Tag.E8) L c⁻¹) := by
    rw [e₂]
    group
  have heq : (canonicalRep (coxeterSystem Tag.E8) L c)⁻¹ *
        canonicalRep (coxeterSystem Tag.E8) L (c * d4d4W * c⁻¹) *
        canonicalRep (coxeterSystem Tag.E8) L c =
      (canonicalRep (coxeterSystem Tag.E8) L c)⁻¹ * (k₂⁻¹ * k₁⁻¹) *
          canonicalRep (coxeterSystem Tag.E8) L c *
        canonicalRep (coxeterSystem Tag.E8) L d4d4W * k₃ := by
    rw [hw, hcd, ← e₃]
    group
  rw [heq]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.canonicalRep_inv_conj_mem_torusGroup c
      (mul_mem (inv_mem hk₂) (inv_mem hk₁))))
    (canonicalRep_mem_torus_sup_rootSpan_kernelRoots d4d4W_mem_closure))
    (Subgroup.mem_sup_left hk₃)

theorem e8FiveFourFrameDatum_holds : E8FiveFourFrameDatum := by
  intro K _ _ h5 Fr hFr w hw
  have hwz : w * w = CFSG.RankThree.Chevalley.WeylE8.z :=
    FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E8.rank → ℤ) fun u => by
      rw [mul_smul, hw, CFSG.RankThree.Chevalley.WeylE8.z_smul]
  obtain ⟨c, rfl⟩ := isConj_iff.1
    ((CFSG.RankThree.Chevalley.WeylE8.isConj_y0_of_sq d4d4W_mul_self).symm.trans
      (CFSG.RankThree.Chevalley.WeylE8.isConj_y0_of_sq hwz))
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  obtain ⟨g', hg', hg'eq⟩ := lang_torus_sup_rootSpan (L := AlgebraicClosure K) (ringChar K)
    d4d4Char (f : ℕ) f.pos _ (canonicalRep_conj_mem_torus_sup_rootSpan c)
  have hFg' : entrywiseFrobGL Tag.E8 (AlgebraicClosure K) (ringChar K) (f : ℕ) g' =
      g' * ((canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ *
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (c * d4d4W * c⁻¹) *
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c) := by
    rw [← hg'eq, mul_inv_cancel_left]
  have hFc : entrywiseFrobGL Tag.E8 (AlgebraicClosure K) (ringChar K) (f : ℕ)
      (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c) =
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c :=
    baseChangeGL_canonicalRep (iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ)) c
  have hFg : entrywiseFrobGL Tag.E8 (AlgebraicClosure K) (ringChar K) (f : ℕ)
      (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹) =
      canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
          (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ *
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) (c * d4d4W * c⁻¹) := by
    rw [map_mul, map_mul, map_inv, hFc, hFg']
    group
  refine ⟨canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
      (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹,
    mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ _ c)
      (torus_sup_rootSpan_le_adjointGroup _ hg')) (inv_mem (canonicalRep_mem_adjointGroup _ _ c)),
    by rw [hfr]; exact hFg,
    (⟨canonicalRep (coxeterSystem Tag.E8) K c, canonicalRep_mem_adjointGroup _ K c⟩ :
      adjointGroup Tag.E8 K)⁻¹, ?_⟩
  intro y hy5 hyT
  set nK : adjointGroup Tag.E8 K :=
    ⟨canonicalRep (coxeterSystem Tag.E8) K c, canonicalRep_mem_adjointGroup _ K c⟩ with hnK
  obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
  have htT : t ∈ torusGroup Tag.E8 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
  have hcoe : ((nK⁻¹ * y * nK⁻¹⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
      (canonicalRep (coxeterSystem Tag.E8) K c)⁻¹ * (y : ModGL Tag.E8 K) *
        (canonicalRep (coxeterSystem Tag.E8) K c)⁻¹⁻¹ := rfl
  have hx5 : (nK⁻¹ * y * nK⁻¹⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hy5, mul_one, mul_inv_cancel]
  refine mem_e8D4Group_of_mem_rootSpan
    (mem_rootSpan_of_mem_torus_sup_of_pow_eq_one (fun α hα => hα.1)
      (coprime_five_card_sub_one h5) ?_ (by rw [← Subgroup.coe_pow, hx5]; rfl))
  refine mem_torus_sup_rootSpan_of_baseChangeGL_mem (algebraMap K (AlgebraicClosure K)) d4d4Char
    (nK⁻¹ * y * nK⁻¹⁻¹).2 ?_
  rw [hcoe, inv_inv, map_mul, map_mul, map_inv, baseChangeGL_canonicalRep, ← hty]
  have hconj : (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
      (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹)).toMonoidHom t =
      canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ * t *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
          (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹)⁻¹ := rfl
  have hsimp : (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ *
      (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ * t *
        (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c * g' *
          (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹)⁻¹) *
      canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c =
      g' * ((canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c)⁻¹ * t *
        canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) c) * g'⁻¹ := by
    group
  rw [hconj, hsimp]
  exact mul_mem (mul_mem hg' (Subgroup.mem_sup_left
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.canonicalRep_inv_conj_mem_torusGroup c htT)))
    (inv_mem hg')

end CFSG.LieType.SeitzGeneration.ExcHigh
