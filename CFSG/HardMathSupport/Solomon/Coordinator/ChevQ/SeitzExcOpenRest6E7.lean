module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest5
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameFamily
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameProd
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Two
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenDescent
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

set_option linter.unusedSectionVars false

section E7Core

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.StandardType.TableBExcTwo
  CFSG.LieType.SeitzGeneration.ExcHigh WithConv
open scoped MatrixGroups CFSG.ConvolutionPoints


@[expose] def e7FrameCharAdd : (Fin Tag.E7.rank → ℤ) →+ (Fin 3 → ZMod 2) where
  toFun v s := ((v (![5, 3, 0] s) : ℤ) : ZMod 2)
  map_zero' := by ext s; simp
  map_add' u v := by ext s; simp

@[expose] def e7FrameChar :
    Multiplicative (Fin Tag.E7.rank → ℤ) →* Multiplicative (Fin 3 → ZMod 2) :=
  AddMonoidHom.toMultiplicative e7FrameCharAdd

theorem e7FrameChar_eq_one_iff (α : Fin Tag.E7.rank → ℤ) :
    e7FrameChar (Multiplicative.ofAdd α) = 1 ↔ α 5 % 2 = 0 ∧ α 3 % 2 = 0 ∧ α 0 % 2 = 0 := by
  have h : e7FrameChar (Multiplicative.ofAdd α) = Multiplicative.ofAdd (e7FrameCharAdd α) := rfl
  rw [h, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
  simp only [Pi.zero_apply, e7FrameCharAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    intCast_zmod_two_eq_zero_iff_E8]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ s
    fin_cases s
    · exact h0
    · exact h1
    · exact h2

theorem e7Frame_mem_kernelRoots (i : Fin 7) : frameE7Root i ∈ kernelRoots e7FrameChar :=
  ⟨e7Frame_isRoot i, (e7FrameChar_eq_one_iff _).2 (frameE7Root_coord_even i)⟩

theorem neg_mem_kernelRoots_e7FrameChar {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ kernelRoots e7FrameChar) : -α ∈ kernelRoots e7FrameChar := by
  refine ⟨IsRoot.neg hα.1, ?_⟩
  obtain ⟨h0, h2, h3⟩ := (e7FrameChar_eq_one_iff α).1 hα.2
  refine (e7FrameChar_eq_one_iff (-α)).2 ?_
  simp only [Pi.neg_apply]
  omega

theorem eq_e7Frame_of_mem_kernelRoots {α : Fin Tag.E7.rank → ℤ}
    (hα : α ∈ kernelRoots e7FrameChar) :
    ∃ i : Fin 7, α = frameE7Root i ∨ α = -frameE7Root i := by
  obtain ⟨hroot, hker⟩ := hα
  obtain ⟨h5, h3, h0⟩ := (e7FrameChar_eq_one_iff α).1 hker
  have key : ∀ β ∈ rootFinset .E7, β 5 % 2 = 0 → β 3 % 2 = 0 → β 0 % 2 = 0 →
      ∃ i : Fin 7, β = frameE7Root i ∨ β = -frameE7Root i := by
    decide +kernel
  exact key α (mem_rootFinset.2 hroot) h5 h3 h0

theorem frameW_mem_closure_kernelRoots :
    frameW ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots e7FrameChar) := by
  unfold frameW
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨frameE7Root i, e7Frame_mem_kernelRoots i, rfl⟩

theorem eq_frameW_of_smul_neg {w : WeylGroup Tag.E7}
    (hw : ∀ u : Fin Tag.E7.rank → ℤ, w • u = -u) : w = frameW :=
  FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E7.rank → ℤ) fun u => by
    rw [hw u, frameW_smul]

@[expose] def e7FrameCore (L : Type) [Field L] : Subgroup (ModGL Tag.E7 L) :=
  torusGroup Tag.E7 L ⊔ rootSpan Tag.E7 L (kernelRoots e7FrameChar)

theorem e7FrameCore_le_frameSpan {L : Type} [Field L] [IsAlgClosed L] :
    e7FrameCore L ≤ frameSpan L := by
  unfold e7FrameCore
  refine sup_le (torusGroup_le_frameSpan (L := L) fun x =>
    IsAlgClosed.exists_pow_nat_eq x two_pos) ?_
  unfold rootSpan
  refine iSup₂_le fun α hα => ?_
  have hrange : ∀ j : Fin 7, (rootSL2 Tag.E7 L (frameE7Root j)).range ≤ frameSpan L := fun j =>
    le_iSup (fun k : Fin 7 => (rootSL2 Tag.E7 L (frameE7Root k)).range) j
  obtain ⟨i, rfl | rfl⟩ := eq_e7Frame_of_mem_kernelRoots hα
  · exact (le_sup_left.trans (range_rootSL2_of_isRoot (K := L)
      (e7Frame_isRoot i)).symm.le).trans (hrange i)
  · exact (le_sup_right.trans (range_rootSL2_of_isRoot (K := L)
      (e7Frame_isRoot i)).symm.le).trans (hrange i)

theorem e7FrameCore_le_adjointGroup {L : Type} [Field L] :
    e7FrameCore L ≤ adjointGroup Tag.E7 L :=
  sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (rootSpan_le_adjointGroup L _)

theorem canonicalRep_mem_e7FrameCore_of_closure {L : Type} [Field L] {y : WeylGroup Tag.E7}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots e7FrameChar)) :
    canonicalRep (coxeterSystem Tag.E7) L y ∈ e7FrameCore L := by
  let R : Subgroup (WeylGroup Tag.E7) :=
    { carrier := {x | canonicalRep (coxeterSystem Tag.E7) L x ∈ e7FrameCore L}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem Tag.E7) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem Tag.E7) L x *
              canonicalRep (coxeterSystem Tag.E7) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L (x * x') ∈ e7FrameCore L
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem Tag.E7) L 1 ∈ e7FrameCore L
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E7) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem Tag.E7) L x⁻¹ =
            (canonicalRep (coxeterSystem Tag.E7) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem Tag.E7) L x⁻¹ ∈ e7FrameCore L
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' kernelRoots e7FrameChar, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem Tag.E7) L (rootReflection α) ∈ e7FrameCore L
    have hn := canonicalRep_rootReflection_mem (τ := Tag.E7) (K := L) hα.1
    have hsub : rootSubgroup Tag.E7 L α ⊔ rootSubgroup Tag.E7 L (-α) ≤ e7FrameCore L :=
      sup_le ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := Tag.E7) (K := L)
          (neg_mem_kernelRoots_e7FrameChar hα)).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem entrywiseFrobGL_mem_e7FrameCore (e : ℕ) {g : ModGL Tag.E7 L} (hg : g ∈ e7FrameCore L) :
    entrywiseFrobGL Tag.E7 L ℓ e g ∈ e7FrameCore L := by
  have hmap : (e7FrameCore L).map (entrywiseFrobGL Tag.E7 L ℓ e) ≤ e7FrameCore L := by
    rw [e7FrameCore, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ kernelRoots e7FrameChar) =>
        rootSubgroup Tag.E7 L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem lang_e7FrameCore (e : ℕ) (he : 1 ≤ e) :
    ∀ c ∈ e7FrameCore L, ∃ z ∈ e7FrameCore L, z⁻¹ * entrywiseFrobGL Tag.E7 L ℓ e z = c := by
  have hZ : IsConnectedAlgebraicSubgroup L
      ((e7FrameCore L).map (modGLPoint Tag.E7 L).toMonoidHom) :=
    isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := Tag.E7) (k := L) e7FrameChar
  have hst : ∀ g ∈ e7FrameCore L, frobTwistGL Tag.E7 L ℓ e 1 g ∈ e7FrameCore L := fun g hg => by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_mem_e7FrameCore ℓ e hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he 1 hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc; exact hzc⟩

end Lang

theorem mem_e7FrameGroup_of_frameSpan_four {K L : Type} [Field K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFrK : ∀ c : K, Fr (algebraMap K L c) = algebraMap K L c)
    (hfix : ∀ c : L, Fr c = c → c ∈ Set.range (algebraMap K L))
    {y : adjointGroup Tag.E7 K} (hy4 : y ^ 4 = y)
    (hy : baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) ∈ frameSpan L) :
    y ∈ e7FrameGroup K := by
  have hFY : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K)) =
      baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) := by
    have e : Fr.comp (algebraMap K L) = algebraMap K L := RingHom.ext fun b => hFrK b
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, e]
  rw [← frameProd_range] at hy
  obtain ⟨x, hx⟩ := hy
  have hFx : Units.map (entrywiseHom Fr) (frameProd L x) =
      frameProd L (fun i => Matrix.SpecialLinearGroup.map Fr (x i)) :=
    map_frameProd L (Units.map (entrywiseHom Fr)) (Matrix.SpecialLinearGroup.map Fr)
      (fun i A => entrywise_rootSL2_of_field Fr (frameE7Root i) A) x
  let FrP : (Fin 7 → SL2 L) →* (Fin 7 → SL2 L) :=
    (Matrix.SpecialLinearGroup.map Fr).compLeft (Fin 7)
  have hFrP : ∀ z, FrP z = fun i => Matrix.SpecialLinearGroup.map Fr (z i) := fun _ => rfl
  have hk : frameProd L (x⁻¹ * FrP x) = 1 := by
    rw [map_mul, map_inv, hFrP, ← hFx, hx, hFY, inv_mul_cancel]
  obtain ⟨hkc, hk2⟩ := frameProd_ker_sq L hk
  have hFrx : FrP x = x * (x⁻¹ * FrP x) := by rw [mul_inv_cancel_left]
  have hk4 : (x⁻¹ * FrP x) ^ 4 = 1 := by
    have e4 : (x⁻¹ * FrP x) ^ 4 = ((x⁻¹ * FrP x) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e4, hk2, one_pow]
  have hx4 : FrP (x ^ 4) = x ^ 4 := by
    rw [map_pow, hFrx, (hkc x).symm.mul_pow, hk4, mul_one]
  have hrat : ∀ i, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = (x ^ 4) i := by
    intro i
    refine exists_SL2_of_entries (algebraMap K L) _ fun a b => hfix _ ?_
    have h := congrArg
      (fun z : Fin 7 → SL2 L => ((z i : SL2 L) : Matrix (Fin 2) (Fin 2) L) a b) hx4
    exact h
  choose u hu using hrat
  have h1 : frameProd L (x ^ 4) = baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) := by
    rw [map_pow, hx, ← map_pow, ← Subgroup.coe_pow, hy4]
  have hYeq : baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) =
      baseChangeGL (algebraMap K L) (frameProd K u) := by
    rw [← h1, map_frameProd K (baseChangeGL (algebraMap K L))
      (Matrix.SpecialLinearGroup.map (algebraMap K L))
      (fun i A => baseChangeGL_rootSL2_of_field (algebraMap K L) (frameE7Root i) A) u]
    exact congrArg (frameProd L) (funext fun i => (hu i).symm)
  have hyu : frameProd K u = (y : ModGL Tag.E7 K) :=
    baseChangeGL_injective (algebraMap K L) hYeq.symm
  exact mem_e7FrameGroup_of_frameProd hyu

theorem e7_frameDatum_three (K : Type) [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ z ∈ adjointGroup Tag.E7 (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) z =
        z * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW ∧
      ∀ y : adjointGroup Tag.E7 K, y ^ 3 = 1 →
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E7 K) ∈
          (twistedTorusOf (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW)
            (Units.map (entrywiseHom Fr))).map (MulAut.conj z).toMonoidHom →
        y ∈ e7FrameGroup K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  have hn : canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW ∈
      e7FrameCore (AlgebraicClosure K) :=
    canonicalRep_mem_e7FrameCore_of_closure frameW_mem_closure_kernelRoots
  obtain ⟨z, hz, hzeq⟩ := lang_e7FrameCore (L := AlgebraicClosure K) (ringChar K)
    (f : ℕ) f.pos _ hn
  have hFz : entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW := by
    rw [← hzeq, mul_inv_cancel_left]
  refine ⟨z, e7FrameCore_le_adjointGroup hz, ?_, ?_⟩
  · rw [hfr]
    exact hFz
  · intro y hy3 hyT
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
    have htT : t ∈ torusGroup Tag.E7 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
    have hzS : z ∈ frameSpan (AlgebraicClosure K) := e7FrameCore_le_frameSpan hz
    have htS : t ∈ frameSpan (AlgebraicClosure K) :=
      torusGroup_le_frameSpan (fun x => IsAlgClosed.exists_pow_nat_eq x two_pos) htT
    have hyS : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E7 K) ∈
        frameSpan (AlgebraicClosure K) := by
      rw [← hty]
      exact mul_mem (mul_mem hzS htS) (inv_mem hzS)
    refine mem_e7FrameGroup_of_frameSpan_four Fr (fun c => ?_)
      (fun c hc => RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq ((hFr c).symm.trans hc))
      (by rw [pow_succ, hy3, one_mul]) hyS
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end E7Core

section E7Normal

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem conj_mem_map_adjointGroup_of_fixed {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) (hq : Nat.card K = ℓ ^ f) {h : ModGL Tag.E7 L}
    (hhG : h ∈ adjointGroup Tag.E7 L) (hhF : entrywiseFrobGL Tag.E7 L ℓ f h = h)
    {y : ModGL Tag.E7 L} (hy : y ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L))) :
    h * y * h⁻¹ ∈ (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  set H := (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) with hH
  have hHle : H ≤ adjointGroup Tag.E7 L := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hx
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hq]
  have hHF : H ≤ fixedSubE7 (L := L) ℓ f := by
    rintro _ ⟨x, -, rfl⟩
    rw [mem_fixedSubE7]
    exact baseChangeGL_frobenius_fixed (iterateFrobenius L ℓ f) hFr x
  have hhFix : h ∈ fixedSubE7 (L := L) ℓ f := (mem_fixedSubE7 ℓ f).2 hhF
  set X : Subgroup (ModGL Tag.E7 L) := H ⊔ Subgroup.closure {h} with hX
  have hXFix : X ≤ fixedSubE7 (L := L) ℓ f := by
    refine sup_le hHF (Subgroup.closure_le _ |>.2 ?_)
    rintro _ rfl
    exact hhFix
  have hXle : X ≤ adjointGroup Tag.E7 L := by
    refine sup_le hHle (Subgroup.closure_le _ |>.2 ?_)
    rintro _ rfl
    exact hhG
  haveI : Finite (fixedSubE7 (L := L) ℓ f) := finite_fixedSubE7 ℓ f hf
  haveI : Finite X := Finite.of_injective
    (fun x : X => (⟨x.1, hXFix x.2⟩ : fixedSubE7 (L := L) ℓ f))
    (by intro x y hxy; have h := congrArg Subtype.val hxy; exact Subtype.ext h)
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom (iterateFrobenius L ℓ f)) x = x :=
    fun x hx => (mem_fixedSubE7 ℓ f).1 (hXFix hx)
  have hdiv := (finite_fixed_subgroup_rational (d := 2) (τ := Tag.E7) (K := K) (L := L)
    (Or.inr (Or.inl ⟨rfl, rfl⟩)) (iterateFrobenius L ℓ f) hFr X hXle hXF).1
  have hhX : h ∈ X := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hyX : y ∈ X := Subgroup.mem_sup_left hy
  rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with h1 | h1
  · have hXH : X ≤ H := (Subgroup.relIndex_eq_one).1 h1
    exact H.mul_mem (H.mul_mem (hXH hhX) hy) (H.inv_mem (hXH hhX))
  · have h2 : (H.subgroupOf X).index = 2 := h1
    haveI : (H.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two h2
    have hyH : (⟨y, hyX⟩ : X) ∈ H.subgroupOf X := Subgroup.mem_subgroupOf.2 hy
    have hc := (inferInstance : (H.subgroupOf X).Normal).conj_mem _ hyH ⟨h, hhX⟩
    exact Subgroup.mem_subgroupOf.1 hc

theorem exists_mulEquiv_conj_of_fixed {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] (ℓ f : ℕ) [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) (hq : Nat.card K = ℓ ^ f) {h : ModGL Tag.E7 L}
    (hhG : h ∈ adjointGroup Tag.E7 L) (hhF : entrywiseFrobGL Tag.E7 L ℓ f h = h) :
    ∃ φ : adjointGroup Tag.E7 K ≃* adjointGroup Tag.E7 K, ∀ y : adjointGroup Tag.E7 K,
      baseChangeGL (algebraMap K L) ((φ y : adjointGroup Tag.E7 K) : ModGL Tag.E7 K) =
        h * baseChangeGL (algebraMap K L) (y : ModGL Tag.E7 K) * h⁻¹ := by
  set H := (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L)) with hH
  have hhG' : h⁻¹ ∈ adjointGroup Tag.E7 L := inv_mem hhG
  have hhF' : entrywiseFrobGL Tag.E7 L ℓ f h⁻¹ = h⁻¹ := by
    rw [map_inv, hhF]
  have hc : ∀ y ∈ H, h * y * h⁻¹ ∈ H := fun y hy =>
    conj_mem_map_adjointGroup_of_fixed (K := K) ℓ f hf hq hhG hhF hy
  have hc' : ∀ y ∈ H, h⁻¹ * y * h ∈ H := fun y hy => by
    have h1 := conj_mem_map_adjointGroup_of_fixed (K := K) ℓ f hf hq hhG' hhF' hy
    rwa [inv_inv] at h1
  let ψ : H ≃* H :=
    { toFun := fun y => ⟨h * y * h⁻¹, hc y y.2⟩
      invFun := fun y => ⟨h⁻¹ * y * h, hc' y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  let e : adjointGroup Tag.E7 K ≃* H :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (algebraMap K L))
  refine ⟨e.trans (ψ.trans e.symm), fun y => ?_⟩
  have h1 : (e (e.symm (ψ (e y))) : ModGL Tag.E7 L) = (ψ (e y) : ModGL Tag.E7 L) := by
    rw [MulEquiv.apply_symm_apply]
  exact h1

theorem e7_exists_mulEquiv_le_frame_of_neg {K : Type} [Field K] [Finite K]
    {E₀ : Subgroup (adjointGroup Tag.E7 K)} (hE₀p : ∀ x ∈ E₀, x ^ 3 = 1)
    (D : LangPlaneData Tag.E7 K E₀) (hw : ∀ u : Fin Tag.E7.rank → ℤ, D.w • u = -u) :
    ∃ φ : adjointGroup Tag.E7 K ≃* adjointGroup Tag.E7 K,
      E₀.map φ.toMonoidHom ≤ e7FrameGroup K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : D.Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [D.hFr, iterateFrobenius_def, hq]
  have hwW : D.w = frameW := eq_frameW_of_smul_neg hw
  obtain ⟨g, hg, hgF, hh⟩ := e7_frameDatum_three K D.Fr D.hFr
  rw [← hwW] at hgF hh
  have hmem : g * D.g0⁻¹ ∈ adjointGroup Tag.E7 (AlgebraicClosure K) := mul_mem hg (inv_mem D.hg0C)
  have hfix : Units.map (entrywiseHom D.Fr) (g * D.g0⁻¹) = g * D.g0⁻¹ := by
    rw [map_mul, map_inv, hgF, D.hg0]
    group
  have hfix' : entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ) (g * D.g0⁻¹) =
      g * D.g0⁻¹ := by
    have h1 := hfix
    rw [hfr] at h1
    exact h1
  obtain ⟨φ₁, hφ₁⟩ := exists_mulEquiv_conj_of_fixed (K := K) (ringChar K) (f : ℕ) f.pos hq hmem
    hfix'
  refine ⟨(MulAut.conj D.c).trans φ₁, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have happ : ((MulAut.conj D.c).trans φ₁).toMonoidHom x = φ₁ (D.c * x * D.c⁻¹) := rfl
  rw [happ]
  refine hh _ ?_ ?_
  · rw [← map_pow, conj_pow, hE₀p x hx]
    simp
  · obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (D.hc x hx)
    refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
    have htb' : D.g0 * t * D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * x * D.c⁻¹ : adjointGroup Tag.E7 K) : ModGL Tag.E7 K) := htb
    show g * t * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((φ₁ (D.c * x * D.c⁻¹) : adjointGroup Tag.E7 K) : ModGL Tag.E7 K)
    rw [hφ₁, ← htb']
    group

end E7Normal

namespace Aux

section Generic

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes

variable {G : Type*} [Group G] {p : ℕ}

theorem hyperGen_prod_of_disjoint {A B : Type*} [Group A] [Group B] (hp : p.Prime)
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p)
    (hBcube : ∀ E : Subgroup B, IsElemAbelian p E → Nat.card E = p ^ 3 → HyperGen p ⊤ E)
    {E : Subgroup (A × B)} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hdis : Disjoint E (MonoidHom.snd A B).ker) : HyperGen p ⊤ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hE₁ : IsElemAbelian p (E.map (MonoidHom.fst A B)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE₂ : IsElemAbelian p (E.map (MonoidHom.snd A B)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE _
  have hE₂c : Nat.card (E.map (MonoidHom.snd A B)) = p ^ 3 := by
    rw [card_map_eq_of_disjoint_ker _ hdis, hEc]
  have hAH : ∀ a : A, ((a, 1) : A × B) ∈ hyperClosure p ⊤ E := by
    intro a
    have hle : ((⊥ : Subgroup A).comap (MonoidHom.fst A B)).relIndex E ≤ p := by
      rw [Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
      exact hA _ hE₁
    obtain ⟨F, hFE, hF, hFD⟩ := exists_hyperplane_le_of_relIndex_le hp hle hEc
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F, hFE, hF, fun f hf => ?_⟩
    have h1 : f.1 = 1 := by
      have := hFD hf
      rwa [Subgroup.mem_comap, Subgroup.mem_bot] at this
    ext
    · simp [h1]
    · simp
  have hBH : ∀ b : B, ((1, b) : A × B) ∈ hyperClosure p ⊤ E := by
    intro b
    have hle : hyperClosure p ⊤ (E.map (MonoidHom.snd A B)) ≤
        (hyperClosure p ⊤ E).comap (MonoidHom.inr A B) := by
      rw [hyperClosure, Subgroup.closure_le]
      rintro k ⟨-, F₂, -, hF₂, hF₂k⟩
      refine Subgroup.subset_closure ⟨Subgroup.mem_top _, F₂.comap (MonoidHom.snd A B) ⊓ E,
        inf_le_right, ?_, ?_⟩
      · rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_comap]
        exact hF₂
      · intro f hf
        have h1 : f.2 * k = k * f.2 := hF₂k f.2 hf.1
        ext
        · simp
        · simp [h1]
    exact hle (hBcube _ hE₂ hE₂c (Subgroup.mem_top b))
  intro g _
  have hg : g = ((g.1, 1) : A × B) * ((1, g.2) : A × B) := by ext <;> simp
  rw [hg]
  exact (hyperClosure p ⊤ E).mul_mem (hAH g.1) (hBH g.2)

theorem range_le_hyperClosure_of_hom_of_disjoint {X : Type*} [Group X] [Finite X]
    (hp : p.Prime) (N : Subgroup X)
    (hcube : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E = p ^ 3 → Disjoint E N →
      HyperGen p ⊤ E)
    (Ψ : X →* G) (hΨcop : ¬ p ∣ Nat.card Ψ.ker) {E : Subgroup G} (hE : E ≤ Ψ.range)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hEN : Disjoint E (N.map Ψ)) :
    Ψ.range ≤ hyperClosure p ⊤ E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Ψ' : X →* Ψ.range := Ψ.rangeRestrict with hΨ'
  have hΨ'surj : Function.Surjective Ψ' := Ψ.rangeRestrict_surjective
  have hΨ'ker : Ψ'.ker = Ψ.ker := Ψ.ker_rangeRestrict
  set E1 : Subgroup Ψ.range := E.subgroupOf Ψ.range with hE1def
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE1 : IsElemAbelian p E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEa.2 x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker Ψ' hΨ'surj (hΨ'ker ▸ hΨcop) hE1
  have hcardE1 : Nat.card E1 = p ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hcardE' : Nat.card E' = p ^ 3 := by
    rw [← card_map_eq_of_disjoint_ker Ψ' hdisE', hmapE', hcardE1]
  have hmapE : E'.map Ψ = E := by
    have h1 : E'.map Ψ = (E'.map Ψ').map Ψ.range.subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [h1, hmapE', hE1def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hE]
  have hdisΨ : Disjoint E' Ψ.ker := hΨ'ker ▸ hdisE'
  have hE'N : Disjoint E' N := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxN
    have h1 : Ψ x ∈ E := hmapE ▸ ⟨x, hxE, rfl⟩
    have h2 : Ψ x ∈ N.map Ψ := ⟨x, hxN, rfl⟩
    have h3 : Ψ x = 1 := Subgroup.disjoint_def.1 hEN h1 h2
    exact Subgroup.disjoint_def.1 hdisΨ hxE h3
  have hE' : HyperGen p ⊤ E' := hcube E' hE'ea hcardE' hE'N
  rw [MonoidHom.range_eq_map]
  exact (Subgroup.map_mono hE').trans (map_hyperClosure_le_of_lift (p := p) hmapE hdisΨ)

theorem hyperGen_of_two_conj_disjoint (X R₀ R₁ : Subgroup G) (n : G)
    (hgen : ∀ M : Subgroup G, X ≤ M → X.map (MulAut.conj n).toMonoidHom ≤ M → M = ⊤)
    (hnR : R₀.map (MulAut.conj n).toMonoidHom = R₁)
    (hX : ∀ E : Subgroup G, E ≤ X → IsElemAbelian p E → Nat.card E = p ^ 3 → Disjoint E R₀ →
      X ≤ hyperClosure p ⊤ E)
    {E : Subgroup G} (hEX : E ≤ X) (hEnX : E ≤ X.map (MulAut.conj n).toMonoidHom)
    (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (h0 : Disjoint E R₀)
    (h1 : Disjoint E R₁) : HyperGen p ⊤ E := by
  have hX1 : X ≤ hyperClosure p ⊤ E := hX E hEX hEa hEc h0
  set E' := E.map (MulAut.conj n⁻¹).toMonoidHom with hE'def
  have hE'X : E' ≤ X := by
    have := Subgroup.map_mono (f := (MulAut.conj n⁻¹).toMonoidHom) hEnX
    rwa [map_conj_map_conj_inv] at this
  have hE'a : IsElemAbelian p E' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hEa _
  have hE'c : Nat.card E' = p ^ 3 := by
    rw [hE'def, Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective, hEc]
  have hE'n : E'.map (MulAut.conj n).toMonoidHom = E := by
    have := map_conj_map_conj_inv n⁻¹ E
    rwa [inv_inv] at this
  have hE'R : Disjoint E' R₀ := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxR
    have h2 : (MulAut.conj n).toMonoidHom x ∈ E := by
      rw [← hE'n]
      exact ⟨x, hxE, rfl⟩
    have h3 : (MulAut.conj n).toMonoidHom x ∈ R₁ := by
      rw [← hnR]
      exact ⟨x, hxR, rfl⟩
    have h4 := Subgroup.disjoint_def.1 h1 h2 h3
    exact (MulAut.conj n).injective (h4.trans (map_one _).symm)
  have hX2 : X ≤ hyperClosure p ⊤ E' := hX E' hE'X hE'a hE'c hE'R
  have hX3 : X.map (MulAut.conj n).toMonoidHom ≤ hyperClosure p ⊤ E := by
    refine (Subgroup.map_mono hX2).trans ?_
    have h4 := map_hyperClosure_le (p := p) (⊤ : Subgroup G) E' n
    rwa [hE'n] at h4
  have htop := hgen _ hX1 hX3
  intro k _
  show k ∈ hyperClosure p ⊤ E
  rw [htop]
  exact Subgroup.mem_top k

end Generic

end Aux

section E7A1D6

open scoped MatrixGroups
open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti
  CFSG.LieType.Seitz CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.OrthAut


theorem not_isTwoPow_of_seitzGoodIndex_E7 {q : PrimePower}
    (h : SeitzGoodIndex 3 (LieTypeIndex.E7 q)) : ¬ IsTwoPow q 1 ∧ ¬ IsTwoPow q 3 := by
  rcases h with h | h
  · refine ⟨fun h1 => h ?_, fun h3 => h ?_⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl (by simp [Gen2318Index, h1]))⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inl (by simp [Gen2318Index, h3]))⟩
  · rcases h with h | h | h <;> simp [IsF4EightIndex, IsD4FourIndex, FourIndex] at h

theorem plusModel_cubes_three_six {K : Type} [Field K] [Finite K] {q : PrimePower}
    (hK : Nat.card K = q.card) (hq2 : ¬ IsTwoPow q 1) (hq8 : ¬ IsTwoPow q 3)
    (hpK : ¬ 3 ∣ Nat.card K)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K)))) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : HyperGen 3 ⊤ E := by
  have hv : (LieTypeIndex.D 6 q).Valid :=
    (LieTypeIndex.valid_iff _).mpr ⟨(LieTypeIndex.inStandardRange_iff _).mpr (by norm_num),
      by simp⟩
  refine SeitzExcOpenRest.plusModel_cubes_of_cat hv hK (fun E₀ hE₀ hc => ?_) E hE hEc
  have hpq : 3 ≠ q.p := by
    intro h
    apply hpK
    rw [hK, PrimePower.card_def, ← h]
    exact dvd_pow_self _ q.exponent_pos.ne'
  exact SeitzExcOpenRest.seitzHyperLie_orth_good seitzGoodInnerOrthTwo_holds ⟨.D 6 q, hv⟩ 3
    Nat.prime_three (by norm_num) (by simpa using hpq)
    (SeitzExcOpenRest5.not_p1ThreeLieList_three_D (by norm_num) hv)
    E₀ hE₀ hc ⟨Or.inr (Or.inl ⟨6, q, rfl⟩), SeitzExcOpenRest5.seitzGoodIndex_three_D (by norm_num) hq2 hq8⟩

theorem e7A1D6_le_hyperClosure_three {K : Type} [Field K] [Finite K] (hK3 : Nat.card K % 3 = 2)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → HyperGen 3 ⊤ E)
    (F : Subgroup (adjointGroup .E7 K)) (hF : F ≤ e7A1D6 K) (hFa : IsElemAbelian 3 F)
    (hFc : Nat.card F = 3 ^ 3) (hFθ : Disjoint F (rootPairE7 K e7Theta)) :
    e7A1D6 K ≤ hyperClosure 3 ⊤ F := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by omega
  have hpq1 : ¬ 3 ∣ Nat.card K - 1 := by omega
  have hpK0 : ((3 : ℕ) : K) ≠ 0 := ExcHigh.natCast_ne_zero_of_not_dvd_card hp hpK
  have hn3 : 3 ≤ 6 := by norm_num
  have : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) isRoot_e7Theta
  have hcentr : e7D6Group K ≤
      Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact commutes_rootPair_of_noG2 (K := K) noG2_E7 isRoot_e7Theta (isRoot_single _ _)
      h1 h2 h3 h4 h5 x hx y hy
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (Spin.quadPlus 6 K)), Commute (ρ a) (Ψ t) := by
    intro a t
    have hx : ρ a ∈ rootPairE7 K e7Theta := hρr ▸ ⟨a, rfl⟩
    have hy : Ψ t ∈ e7D6Group K := hrange ▸ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcentr hy) _ hx
  let ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hrangeψ : ψ.range = e7A1D6 K := by
    rw [MonoidHom.noncommCoprod_range, hρr, hrange, e7A1D6, sup_comm]
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  set π := spinToStatedProj (quadPlus 6 K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ 3 ∣ Nat.card π.ker := by
    rw [hZ]
    exact hcen
  have hψker : ¬ 3 ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
    obtain ⟨⟨a, s⟩, hxk⟩ := x
    have hxk' : ρ a * Ψ s = 1 := hxk
    have hxp : (a, s) ^ 3 = 1 := by
      have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : ψ.ker)
      rw [hx] at this
      exact congrArg Subtype.val this
    have hap : a ^ 3 = 1 := congrArg Prod.fst hxp
    have hsp : s ^ 3 = 1 := congrArg Prod.snd hxp
    have hacent : a ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
      have h2 : Commute (ρ b) (ρ a) := by
        rw [h1]
        exact (hcomm b s).inv_right
      apply hρi
      rw [map_mul, map_mul]
      exact h2.eq
    obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
    simp only [Fintype.card_fin] at hr
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hra, ← map_mul, ← pow_two, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ha1 : a = 1 := by
      have hcop : Nat.Coprime 2 3 := by norm_num
      have hd2 : orderOf a ∣ Nat.gcd 2 3 :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
      rw [hcop] at hd2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
    have hΨs : Ψ s = 1 := by
      rw [ha1, map_one, one_mul] at hxk'
      exact hxk'
    have hs1 : s = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
    have hx1 : (⟨(a, s), hxk⟩ : ψ.ker) = 1 := Subtype.ext (Prod.ext ha1 hs1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hH : ∀ F' : Subgroup (SL(2, K) × spinGroup (Spin.quadPlus 6 K)), IsElemAbelian 3 F' →
      Nat.card F' = 3 ^ 3 → Disjoint F' (MonoidHom.snd _ _).ker → HyperGen 3 ⊤ F' :=
    fun F' hF' hc hd => Aux.hyperGen_prod_of_disjoint hp
      (fun F'' hF'' => card_le_of_isElemAbelian_specialLinear_two hpK0 hF'')
      (cubes_of_central_quotient hp π hπsurj hZ.le hπcop hcube) hF' hc hd
  have hN : ((MonoidHom.snd (SL(2, K)) (spinGroup (Spin.quadPlus 6 K))).ker).map ψ ≤
      rootPairE7 K e7Theta := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x.2 = 1 := hx
    have hψx : ψ x = ρ x.1 := by
      show ρ x.1 * Ψ x.2 = ρ x.1
      rw [hx2, map_one, mul_one]
    rw [hψx, ← hρr]
    exact ⟨x.1, rfl⟩
  rw [← hrangeψ]
  exact Aux.range_le_hyperClosure_of_hom_of_disjoint hp _ hH ψ hψker (hrangeψ ▸ hF) hFa hFc
    (hFθ.mono_right hN)

end E7A1D6

section E7Frame

open scoped MatrixGroups
open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcHigh TauCeti
  CFSG.LieType.Seitz CFSG.AGLEmbedding CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenCubes
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4
open CFSG.ComponentClassification CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.StandardType.TableBExcTwo


abbrev frameR (K : Type) [Field K] (i : Fin 7) : Subgroup (adjointGroup .E7 K) :=
  rootPairE7 K (frameE7Root i)

theorem frameR_commute {K : Type} [Field K] {i j : Fin 7} (hij : i ≠ j)
    {x y : adjointGroup .E7 K} (hx : x ∈ frameR K i) (hy : y ∈ frameR K j) : x * y = y * x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := e7Frame_facts i j hij
  exact commutes_rootPair_of_noG2 (K := K) noG2_E7 (e7Frame_isRoot i) (e7Frame_isRoot j)
    h1 h2 h3 h4 h5 x hx y hy

theorem sq_eq_one_of_mem_frameR {K : Type} [Field K] {i : Fin 7} {x : adjointGroup .E7 K}
    (hx : x ∈ frameR K i) (hc : ∀ y ∈ frameR K i, x * y = y * x) : x ^ 2 = 1 := by
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) (e7Frame_isRoot i)
  obtain ⟨A, rfl⟩ : x ∈ ρ.range := by rw [hρr]; exact hx
  have hA : A ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have hB : ρ B ∈ frameR K i := by
      show ρ B ∈ rootPairE7 K (frameE7Root i)
      rw [← hρr]
      exact ⟨B, rfl⟩
    have h := hc (ρ B) hB
    apply hρi
    rw [map_mul, map_mul]
    exact h.symm
  rw [← map_pow, sq_eq_one_of_mem_center_SL2 K hA, map_one]

theorem false_of_four_frameR {K : Type} [Field K] {E : Subgroup (adjointGroup .E7 K)}
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) (i : Fin 4 → Fin 7)
    (hi : Function.Injective i) (hne : ∀ k, ¬ Disjoint E (frameR K (i k))) : False := by
  classical
  set A : Fin 4 → Subgroup (adjointGroup .E7 K) := fun k => E ⊓ frameR K (i k) with hA
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEa.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcomm : Pairwise fun k l => ∀ x y : adjointGroup .E7 K, x ∈ A k → y ∈ A l →
      Commute x y :=
    fun k l _ x y hx hy => hEcomm x hx.1 y hy.1
  have hind : iSupIndep A := by
    intro k
    rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hle : (⨆ (l) (_ : l ≠ k), A l) ≤
        Subgroup.centralizer (frameR K (i k) : Set (adjointGroup .E7 K)) := by
      refine iSup₂_le fun l hl => ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact frameR_commute (hi.ne (Ne.symm hl)) hy hz.2
    have hc : ∀ y ∈ frameR K (i k), x * y = y * x := fun y hy =>
      ((Subgroup.mem_centralizer_iff.1 (hle hx')) y hy).symm
    have hx2 : x ^ 2 = 1 := sq_eq_one_of_mem_frameR hx.2 hc
    have hx3 : x ^ 3 = 1 := hEa.2 x hx.1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx2, hx3, inv_one, mul_one]
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hrange : ∀ x, Subgroup.noncommPiCoprod hcomm x ∈ E := by
    intro x
    have hmem : Subgroup.noncommPiCoprod hcomm x ∈ (Subgroup.noncommPiCoprod hcomm).range :=
      ⟨x, rfl⟩
    rw [Subgroup.noncommPiCoprod_range] at hmem
    exact (iSup_le fun k => (inf_le_left : A k ≤ E)) hmem
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  have hle : Nat.card (∀ k, A k) ≤ Nat.card E :=
    Nat.card_le_card_of_injective (fun x => (⟨_, hrange x⟩ : E))
      (fun x y hxy => hinj (congrArg Subtype.val hxy))
  have hcardA : ∀ k, 3 ≤ Nat.card (A k) := by
    intro k
    have hne' : A k ≠ ⊥ := fun h => hne k (disjoint_iff.2 h)
    have hd : Nat.card (A k) ∣ 3 ^ 3 := hEc ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, -, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hm'
      exact hne' (Subgroup.card_eq_one.1 hm')
    rw [hm']
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hm0)
  rw [Nat.card_pi, Fin.prod_univ_four, hEc] at hle
  have h81 : 81 ≤ Nat.card (A 0) * Nat.card (A 1) * Nat.card (A 2) * Nat.card (A 3) :=
    calc 81 = 3 * 3 * 3 * 3 := by norm_num
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hcardA 0) (hcardA 1))
          (hcardA 2)) (hcardA 3)
  omega

theorem exists_frame_pair {K : Type} [Field K] {E : Subgroup (adjointGroup .E7 K)}
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) :
    (Disjoint E (frameR K 0) ∧ Disjoint E (frameR K 1)) ∨
      (Disjoint E (frameR K 0) ∧ Disjoint E (frameR K 2)) ∨
      (Disjoint E (frameR K 1) ∧ Disjoint E (frameR K 2)) ∨
      (Disjoint E (frameR K 3) ∧ Disjoint E (frameR K 4)) ∨
      (Disjoint E (frameR K 5) ∧ Disjoint E (frameR K 6)) := by
  have F : ∀ i : Fin 4 → Fin 7, Function.Injective i →
      (∀ k, ¬ Disjoint E (frameR K (i k))) → False :=
    fun i hi hne => false_of_four_frameR hEa hEc i hi hne
  by_cases d34 : Disjoint E (frameR K 3) ∧ Disjoint E (frameR K 4)
  · exact Or.inr (Or.inr (Or.inr (Or.inl d34)))
  by_cases d56 : Disjoint E (frameR K 5) ∧ Disjoint E (frameR K 6)
  · exact Or.inr (Or.inr (Or.inr (Or.inr d56)))
  by_cases d01 : Disjoint E (frameR K 0) ∧ Disjoint E (frameR K 1)
  · exact Or.inl d01
  by_cases d02 : Disjoint E (frameR K 0) ∧ Disjoint E (frameR K 2)
  · exact Or.inr (Or.inl d02)
  by_cases d12 : Disjoint E (frameR K 1) ∧ Disjoint E (frameR K 2)
  · exact Or.inr (Or.inr (Or.inl d12))
  exfalso
  rw [not_and_or] at d34 d56 d01 d02 d12
  have F' : ∀ i : Fin 4 → Fin 7, Function.Injective i → ¬ Disjoint E (frameR K (i 0)) →
      ¬ Disjoint E (frameR K (i 1)) → ¬ Disjoint E (frameR K (i 2)) →
        ¬ Disjoint E (frameR K (i 3)) → False := by
    intro i hi a b c d
    refine F i hi fun k => ?_
    fin_cases k
    · exact a
    · exact b
    · exact c
    · exact d
  by_cases e0 : Disjoint E (frameR K 0)
  · have h1 : ¬ Disjoint E (frameR K 1) := d01.resolve_left (not_not.2 e0)
    have h2 : ¬ Disjoint E (frameR K 2) := d02.resolve_left (not_not.2 e0)
    rcases d34 with h3 | h4 <;> rcases d56 with h5 | h6
    · exact F' ![1, 2, 3, 5] (by decide) h1 h2 h3 h5
    · exact F' ![1, 2, 3, 6] (by decide) h1 h2 h3 h6
    · exact F' ![1, 2, 4, 5] (by decide) h1 h2 h4 h5
    · exact F' ![1, 2, 4, 6] (by decide) h1 h2 h4 h6
  · rcases d12 with h1 | h2 <;> rcases d34 with h3 | h4 <;> rcases d56 with h5 | h6
    · exact F' ![0, 1, 3, 5] (by decide) e0 h1 h3 h5
    · exact F' ![0, 1, 3, 6] (by decide) e0 h1 h3 h6
    · exact F' ![0, 1, 4, 5] (by decide) e0 h1 h4 h5
    · exact F' ![0, 1, 4, 6] (by decide) e0 h1 h4 h6
    · exact F' ![0, 2, 3, 5] (by decide) e0 h2 h3 h5
    · exact F' ![0, 2, 3, 6] (by decide) e0 h2 h3 h6
    · exact F' ![0, 2, 4, 5] (by decide) e0 h2 h4 h5
    · exact F' ![0, 2, 4, 6] (by decide) e0 h2 h4 h6

theorem map_conj_frameR {K : Type} [Field K] (w : List (Fin (Tag.rank .E7))) {k k' : Fin 7}
    (h : CatLeafProof.wordReflect .E7 w (frameE7Root k) = frameE7Root k' ∨
      CatLeafProof.wordReflect .E7 w (frameE7Root k) = -frameE7Root k') :
    (frameR K k).map (MulAut.conj (weylWordElt .E7 K w)).toMonoidHom = frameR K k' := by
  have hmap := map_conj_weylWordElt_rootPair (K := K) w (e7Frame_isRoot k)
  rcases h with h | h
  · rw [h] at hmap
    exact hmap
  · rw [h, neg_neg] at hmap
    exact hmap.trans (sup_comm _ _)

theorem map_conj_e7FrameGroup_le {K : Type} [Field K] (w : List (Fin (Tag.rank .E7)))
    (σ : Fin 7 → Fin 7)
    (hσ : ∀ k, CatLeafProof.wordReflect .E7 w (frameE7Root k) = frameE7Root (σ k) ∨
      CatLeafProof.wordReflect .E7 w (frameE7Root k) = -frameE7Root (σ k)) :
    (e7FrameGroup K).map (MulAut.conj (weylWordElt .E7 K w)).toMonoidHom ≤ e7FrameGroup K := by
  rw [e7FrameGroup, Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  have h := map_conj_frameR (K := K) w (hσ k)
  rw [frameR] at h
  rw [h]
  exact le_iSup (fun j => rootPairE7 K (frameE7Root j)) (σ k)

theorem disjoint_map_conj {G : Type*} [Group G] {E R : Subgroup G} (g : G) (h : Disjoint E R) :
    Disjoint (E.map (MulAut.conj g).toMonoidHom) (R.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  rintro _ ⟨x, hx, rfl⟩ hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hxy : y = x := (MulAut.conj g).injective hyx
  subst hxy
  rw [Subgroup.disjoint_def.1 h hx hy, map_one]

namespace Aux

@[expose] def w02 : List (Fin (Tag.rank .E7)) := e7w [3, 2, 1, 3, 4, 3, 1, 2, 3, 5, 4, 6, 5, 2, 4]
@[expose] def σ02 : Fin 7 → Fin 7 := ![0, 2, 1, 4, 3, 5, 6]

@[expose] def w12 : List (Fin (Tag.rank .E7)) :=
  e7w [3, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0, 3, 1, 2, 3, 4, 3, 1, 2, 3, 1, 6]
@[expose] def σ12 : Fin 7 → Fin 7 := ![2, 0, 1, 4, 6, 5, 3]

@[expose] def w34 : List (Fin (Tag.rank .E7)) :=
  e7w [3, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 6, 5, 3,
    1, 2, 3, 2, 1, 4]
@[expose] def σ34 : Fin 7 → Fin 7 := ![2, 6, 4, 1, 0, 5, 3]

@[expose] def w56 : List (Fin (Tag.rank .E7)) :=
  e7w [5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0, 3, 2, 1, 3, 4, 3, 1, 2, 3, 5, 4, 6, 5, 2, 3,
    1, 4, 3, 1, 4]
@[expose] def σ56 : Fin 7 → Fin 7 := ![3, 2, 6, 5, 4, 0, 1]

theorem w02_frame : ∀ k : Fin 7, CatLeafProof.wordReflect .E7 w02 (frameE7Root k) =
    frameE7Root (σ02 k) ∨ CatLeafProof.wordReflect .E7 w02 (frameE7Root k) = -frameE7Root (σ02 k) := by
  decide +kernel

theorem w12_frame : ∀ k : Fin 7, CatLeafProof.wordReflect .E7 w12 (frameE7Root k) =
    frameE7Root (σ12 k) ∨ CatLeafProof.wordReflect .E7 w12 (frameE7Root k) = -frameE7Root (σ12 k) := by
  decide +kernel

theorem w34_frame : ∀ k : Fin 7, CatLeafProof.wordReflect .E7 w34 (frameE7Root k) =
    frameE7Root (σ34 k) ∨ CatLeafProof.wordReflect .E7 w34 (frameE7Root k) = -frameE7Root (σ34 k) := by
  decide +kernel

theorem w56_frame : ∀ k : Fin 7, CatLeafProof.wordReflect .E7 w56 (frameE7Root k) =
    frameE7Root (σ56 k) ∨ CatLeafProof.wordReflect .E7 w56 (frameE7Root k) = -frameE7Root (σ56 k) := by
  decide +kernel

end Aux

theorem hyperGen_E7_of_frame_disjoint {K : Type} [Field K] [Finite K] (hK3 : Nat.card K % 3 = 2)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → HyperGen 3 ⊤ E)
    {E : Subgroup (adjointGroup .E7 K)} (hE : E ≤ e7FrameGroup K) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (h0 : Disjoint E (frameR K 0)) (h1 : Disjoint E (frameR K 1)) :
    HyperGen 3 ⊤ E := by
  have hθ : frameE7Root 0 = e7Theta := by decide
  have hnR : (frameR K 0).map (MulAut.conj (weylWordElt .E7 K e7Word)).toMonoidHom = frameR K 1 :=
    map_conj_frameR e7Word (Or.inl (wordReflect_e7Word_frame 0))
  refine Aux.hyperGen_of_two_conj_disjoint (e7A1D6 K) (frameR K 0) (frameR K 1)
    (weylWordElt .E7 K e7Word) (fun M hX hn => eq_top_of_e7A1D6_le_of_conj_le M hX hn) hnR
    (fun F hF hFa hFc hFd => ?_) (hE.trans e7FrameGroup_le_e7A1D6)
    (hE.trans e7FrameGroup_le_conj_e7A1D6) hEa hEc h0 h1
  have hFd' : Disjoint F (rootPairE7 K e7Theta) := by
    rw [← hθ]
    exact hFd
  exact e7A1D6_le_hyperClosure_three hK3 hcube F hF hFa hFc hFd'

theorem hyperGen_E7_of_frame {K : Type} [Field K] [Finite K] (hK3 : Nat.card K % 3 = 2)
    (hcube : ∀ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 6 K))),
      IsElemAbelian 3 E → Nat.card E = 3 ^ 3 → HyperGen 3 ⊤ E)
    {E : Subgroup (adjointGroup .E7 K)} (hE : E ≤ e7FrameGroup K) (hEa : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) : HyperGen 3 ⊤ E := by
  have hmove : ∀ (w : List (Fin (Tag.rank .E7))) (σ : Fin 7 → Fin 7)
      (_ : ∀ k, CatLeafProof.wordReflect .E7 w (frameE7Root k) = frameE7Root (σ k) ∨
        CatLeafProof.wordReflect .E7 w (frameE7Root k) = -frameE7Root (σ k)) (a b : Fin 7),
      (frameR K a).map (MulAut.conj (weylWordElt .E7 K w)).toMonoidHom = frameR K 0 →
      (frameR K b).map (MulAut.conj (weylWordElt .E7 K w)).toMonoidHom = frameR K 1 →
      Disjoint E (frameR K a) → Disjoint E (frameR K b) → HyperGen 3 ⊤ E := by
    intro w σ hσ a b ha hb hda hdb
    set n := weylWordElt .E7 K w with hn
    have hE' : E.map (MulAut.conj n).toMonoidHom ≤ e7FrameGroup K :=
      (Subgroup.map_mono hE).trans (map_conj_e7FrameGroup_le w σ hσ)
    have hE'a : IsElemAbelian 3 (E.map (MulAut.conj n).toMonoidHom) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEa _
    have hE'c : Nat.card (E.map (MulAut.conj n).toMonoidHom) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hEc]
    have hd0 : Disjoint (E.map (MulAut.conj n).toMonoidHom) (frameR K 0) := by
      rw [← ha]
      exact disjoint_map_conj n hda
    have hd1 : Disjoint (E.map (MulAut.conj n).toMonoidHom) (frameR K 1) := by
      rw [← hb]
      exact disjoint_map_conj n hdb
    have h := hyperGen_conj n⁻¹ (hyperGen_E7_of_frame_disjoint hK3 hcube hE' hE'a hE'c hd0 hd1)
    have hE₀ : (E.map (MulAut.conj n).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom = E :=
      map_conj_map_conj_inv n E
    rwa [hE₀] at h
  rcases exists_frame_pair hEa hEc with ⟨h0, h1⟩ | ⟨h0, h2⟩ | ⟨h1, h2⟩ | ⟨h3, h4⟩ | ⟨h5, h6⟩
  · exact hyperGen_E7_of_frame_disjoint hK3 hcube hE hEa hEc h0 h1
  · exact hmove Aux.w02 Aux.σ02 Aux.w02_frame 0 2 (map_conj_frameR _ (Aux.w02_frame 0))
      (map_conj_frameR _ (Aux.w02_frame 2)) h0 h2
  · exact hmove Aux.w12 Aux.σ12 Aux.w12_frame 1 2 (map_conj_frameR _ (Aux.w12_frame 1))
      (map_conj_frameR _ (Aux.w12_frame 2)) h1 h2
  · exact hmove Aux.w34 Aux.σ34 Aux.w34_frame 4 3 (map_conj_frameR _ (Aux.w34_frame 4))
      (map_conj_frameR _ (Aux.w34_frame 3)) h4 h3
  · exact hmove Aux.w56 Aux.σ56 Aux.w56_frame 5 6 (map_conj_frameR _ (Aux.w56_frame 5))
      (map_conj_frameR _ (Aux.w56_frame 6)) h5 h6

theorem hyperGen_E7_of_neg_datum {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (hs : ThreeScope LieTypeIndex.E7 K) {E₀ : Subgroup (adjointGroup .E7 K)}
    (hE₀ : IsElemAbelian 3 E₀) (hc : Nat.card E₀ = 3 ^ 3) (D : LangPlaneData .E7 K E₀)
    (hw : ∀ u : Fin Tag.E7.rank → ℤ, D.w • u = -u) : HyperGen 3 ⊤ E₀ := by
  obtain ⟨q, hv, hKq, hgood, -⟩ := hs
  obtain ⟨hq2, hq8⟩ := not_isTwoPow_of_seitzGoodIndex_E7 hgood
  have hpK : ¬ 3 ∣ Nat.card K := by omega
  obtain ⟨φ, hφ⟩ := e7_exists_mulEquiv_le_frame_of_neg hE₀.2 D hw
  refine hyperGen_of_mulEquiv φ ?_
  exact hyperGen_E7_of_frame hK (plusModel_cubes_three_six hKq hq2 hq8 hpK) hφ
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE₀ _)
    (by rw [Subgroup.card_map_of_injective φ.injective, hc])

end E7Frame

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest6

end
