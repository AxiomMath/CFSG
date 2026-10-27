module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverE6RankMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover

public section

namespace CFSG.HardMathSupport.Lang.AlphaThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.AGLEmbedding (LiftableNormalizerGen pairCentralizing liftableNormalizerGen_of_inverters)

open CFSG.AGLEmbedding.KFactProofs.CoverE6 (fourRoots fourRootsCheck commute_rootSubgroup
  exists_order_three_inverter)

open scoped commutatorElement

namespace E6Gen

@[expose] def orthB (γ β : Fin Tag.E6.rank → ℤ) : Bool :=
  decide (γ ≠ β) && decide (γ ≠ -β) && !RootOps.isRootB Tag.E6 (γ + β) &&
    !RootOps.isRootB Tag.E6 (γ + -β)


theorem not_isRoot_of_isRootB {v : Fin Tag.E6.rank → ℤ} (h : RootOps.isRootB Tag.E6 v = false) :
    ¬ IsRoot Tag.E6 v := fun hr => by
  rw [← RootOps.isRootB_iff, h] at hr
  exact Bool.false_ne_true hr

theorem commute_of_orthB (F : Type) [Field F] {γ β : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ)
    (hβ : IsRoot Tag.E6 β) (h : orthB γ β = true) :
    ∀ x ∈ rootSubgroup Tag.E6 F γ,
      ∀ y ∈ rootSubgroup Tag.E6 F β ⊔ rootSubgroup Tag.E6 F (-β), Commute x y := by
  simp only [orthB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hne, hne'⟩, h1⟩, h2⟩ := h
  intro x hx y hy
  have hle : rootSubgroup Tag.E6 F β ⊔ rootSubgroup Tag.E6 F (-β) ≤
      Subgroup.centralizer {x} := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_rootSubgroup hγ hβ hne hne' (not_isRoot_of_isRootB h1) F x hx y hy).symm.eq
    · have hne'' : γ ≠ - -β := by rw [neg_neg]; exact hne
      exact Subgroup.mem_centralizer_singleton_iff.2
        (commute_rootSubgroup hγ (IsRoot.neg hβ) hne' hne'' (not_isRoot_of_isRootB h2) F x hx
          y hy).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem exists_inverter_data_adjoint_mem (F : Type) [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    ∃ h w : Fin 4 → ↥(adjointGroup Tag.E6 F), (∀ i j, Commute (h i) (h j)) ∧
      (∀ i, orderOf (h i) = 3) ∧ (∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹) ∧
      (∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) ∧
      ∀ i, ((h i : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈
        rootSubgroup Tag.E6 F (fourRoots i) ⊔ rootSubgroup Tag.E6 F (-fourRoots i) := by
  obtain ⟨e, u, he1, he3, heu⟩ := exists_order_three_inverter F h3
  let ψ : Fin 4 → Matrix.SpecialLinearGroup (Fin 2) F →* ↥(adjointGroup Tag.E6 F) := fun i =>
    (rootSL2 Tag.E6 F (fourRoots i)).codRestrict _
      (fun A => (exceptional_Lang_root_rank_one_data Tag.E6 F (fourRoots i)).2.2.2.2.1 A)
  have hψ : ∀ i A, ((ψ i A : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      rootSL2 Tag.E6 F (fourRoots i) A := fun i A => rfl
  have hinj : ∀ i, Function.Injective (ψ i) := fun i A B h =>
    rootSL2_injective_of_field (fourRoots i) (by
      simpa only [hψ] using congrArg (fun g : ↥(adjointGroup Tag.E6 F) => (g : ModGL Tag.E6 F)) h)
  have hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B) := fun i j hij A B =>
    Subtype.ext (CFSG.AGLEmbedding.KFactProofs.CoverE6.commute_rootSL2 F hij A B).eq
  refine ⟨fun i => ψ i e, fun i => ψ i u, fun i j => ?_, fun i => ?_, fun i => ?_,
    fun i j hij => ?_, fun i => ?_⟩
  · by_cases hij : i = j
    · rw [hij]
    · exact hcomm i j hij e e
  · exact orderOf_eq_prime (by rw [← map_pow, he3, map_one])
      fun h => he1 (hinj i (h.trans (map_one _).symm))
  · show ψ i u * ψ i e * (ψ i u)⁻¹ = (ψ i e)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, heu, map_inv]
  · rw [mul_inv_eq_iff_eq_mul]
    exact (hcomm i j hij u e).eq
  · obtain ⟨hroot, -⟩ := fourRootsCheck
    rw [hψ, ← range_rootSL2_of_isRoot (RootOps.isRootB_iff.1 (hroot i))]
    exact MonoidHom.mem_range.2 ⟨e, rfl⟩

theorem mem_pairCentralizing_of_orthB (F : Type) [Field F]
    (h : Fin 4 → ↥(adjointGroup Tag.E6 F))
    (hh : ∀ i, ((h i : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈
      rootSubgroup Tag.E6 F (fourRoots i) ⊔ rootSubgroup Tag.E6 F (-fourRoots i))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (j k : Fin 4) (hjk : j ≠ k)
    (hj : orthB γ (fourRoots j) = true) (hk : orthB γ (fourRoots k) = true)
    (x : ↥(adjointGroup Tag.E6 F)) (hx : (x : ModGL Tag.E6 F) ∈ rootSubgroup Tag.E6 F γ) :
    x ∈ pairCentralizing h := by
  obtain ⟨hroot, -⟩ := fourRootsCheck
  refine ⟨j, k, hjk, Subtype.ext ?_, Subtype.ext ?_⟩
  · exact (commute_of_orthB F hγ (RootOps.isRootB_iff.1 (hroot j)) hj _ hx _ (hh j)).eq
  · exact (commute_of_orthB F hγ (RootOps.isRootB_iff.1 (hroot k)) hk _ hx _ (hh k)).eq

@[expose] def rootFourFive : Fin Tag.E6.rank → ℤ := ![0, 0, 0, 1, 1, 0]

@[expose] def i4 : Fin Tag.E6.rank := ⟨3, by decide⟩

@[expose] def i5 : Fin Tag.E6.rank := ⟨4, by decide⟩

theorem pinnedX_mem_closure (F : Type) [Field F] (h : Fin 4 → ↥(adjointGroup Tag.E6 F))
    (hh : ∀ i, ((h i : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈
      rootSubgroup Tag.E6 F (fourRoots i) ⊔ rootSubgroup Tag.E6 F (-fourRoots i))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : RootOps.isRootB Tag.E6 γ = true) (j k : Fin 4) (hjk : j ≠ k)
    (hj : orthB γ (fourRoots j) = true) (hk : orthB γ (fourRoots k) = true) (c : F) :
    (⟨pinnedX Tag.E6 F γ c, pinnedX_mem_adjointGroup γ c⟩ : ↥(adjointGroup Tag.E6 F)) ∈
      Subgroup.closure (pairCentralizing h) :=
  Subgroup.subset_closure (mem_pairCentralizing_of_orthB F h hh (RootOps.isRootB_iff.1 hγ) j k hjk
    hj hk _ (CFSG.Blueprint.Chevalley.mem_rootSubgroup.2 ⟨c, rfl⟩))

theorem exists_pinnedX_eq_commutator (F : Type) [Field F] {γ₁ γ₂ α : Fin Tag.E6.rank → ℤ}
    (h₁ : IsRoot Tag.E6 γ₁) (h₂ : IsRoot Tag.E6 γ₂) (hne : γ₁ ≠ γ₂) (hne' : γ₁ ≠ -γ₂)
    (hsum : γ₁ + γ₂ = α) (hα : IsRoot Tag.E6 α) (c : F) :
    ∃ a : F, pinnedX Tag.E6 F α c = ⁅pinnedX Tag.E6 F γ₁ a, pinnedX Tag.E6 F γ₂ 1⁆ := by
  obtain ⟨hε, hF⟩ := (simply_laced_root_commutator_unit Tag.E6 (Or.inr (Or.inl rfl)) h₁ h₂ hne
    hne').1 (hsum ▸ hα)
  refine ⟨(commConst Tag.E6 γ₁ γ₂ (1, 1) : F) * c, ?_⟩
  rw [hF F, hsum]
  congr 1
  rcases hε with hε | hε <;> simp [hε]

theorem closure_pairCentralizing_eq_top (F : Type) [Field F]
    (h : Fin 4 → ↥(adjointGroup Tag.E6 F))
    (hh : ∀ i, ((h i : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) ∈
      rootSubgroup Tag.E6 F (fourRoots i) ⊔ rootSubgroup Tag.E6 F (-fourRoots i)) :
    Subgroup.closure (pairCentralizing h) = ⊤ := by
  have hP {γ : Fin Tag.E6.rank → ℤ} := pinnedX_mem_closure F h hh (γ := γ)
  have hcomm : ∀ (s : ℤ), (s = 1 ∨ s = -1) → ∀ c : F,
      (⟨pinnedX Tag.E6 F (s • Pi.single i4 1) c, pinnedX_mem_adjointGroup _ c⟩ :
        ↥(adjointGroup Tag.E6 F)) ∈ Subgroup.closure (pairCentralizing h) := by
    intro s hs c
    obtain ⟨hr₁, hr₂, hr, hne, hne', hsum, hj₁, hk₁, hj₂, hk₂⟩ :
        RootOps.isRootB Tag.E6 (s • rootFourFive) = true ∧
        RootOps.isRootB Tag.E6 (-s • Pi.single i5 1) = true ∧
        RootOps.isRootB Tag.E6 (s • Pi.single i4 1) = true ∧
        s • rootFourFive ≠ -s • (Pi.single i5 1 : Fin Tag.E6.rank → ℤ) ∧
        s • rootFourFive ≠ -(-s • (Pi.single i5 1 : Fin Tag.E6.rank → ℤ)) ∧
        s • rootFourFive + -s • (Pi.single i5 1 : Fin Tag.E6.rank → ℤ) = s • Pi.single i4 1 ∧
        orthB (s • rootFourFive) (fourRoots 2) = true ∧
        orthB (s • rootFourFive) (fourRoots 3) = true ∧
        orthB (-s • Pi.single i5 1) (fourRoots 0) = true ∧
        orthB (-s • Pi.single i5 1) (fourRoots 1) = true := by
      rcases hs with rfl | rfl <;> decide +kernel
    obtain ⟨a, ha⟩ := exists_pinnedX_eq_commutator F (RootOps.isRootB_iff.1 hr₁)
      (RootOps.isRootB_iff.1 hr₂) hne hne' hsum (RootOps.isRootB_iff.1 hr) c
    have hx₁ := hP hr₁ 2 3 (by decide) hj₁ hk₁ a
    have hx₂ := hP hr₂ 0 1 (by decide) hj₂ hk₂ 1
    have heq : (⟨pinnedX Tag.E6 F (s • Pi.single i4 1) c, pinnedX_mem_adjointGroup _ c⟩ :
        ↥(adjointGroup Tag.E6 F)) =
        ⁅(⟨pinnedX Tag.E6 F (s • rootFourFive) a, pinnedX_mem_adjointGroup _ a⟩ :
          ↥(adjointGroup Tag.E6 F)),
          ⟨pinnedX Tag.E6 F (-s • Pi.single i5 1) 1, pinnedX_mem_adjointGroup _ 1⟩⁆ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ha, commutatorElement_def]
    rw [heq, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₁)) (inv_mem hx₂)
  have hgen : ∀ (s : ℤ), (s = 1 ∨ s = -1) → ∀ (i : Fin Tag.E6.rank) (c : F),
      (⟨pinnedX Tag.E6 F (s • Pi.single i 1) c, pinnedX_mem_adjointGroup _ c⟩ :
        ↥(adjointGroup Tag.E6 F)) ∈ Subgroup.closure (pairCentralizing h) := by
    intro s hs i c
    fin_cases i
    · rcases hs with rfl | rfl <;>
        exact hP (by decide +kernel) 0 3 (by decide) (by decide +kernel) (by decide +kernel) c
    · rcases hs with rfl | rfl <;>
        exact hP (by decide +kernel) 1 2 (by decide) (by decide +kernel) (by decide +kernel) c
    · rcases hs with rfl | rfl <;>
        exact hP (by decide +kernel) 0 1 (by decide) (by decide +kernel) (by decide +kernel) c
    · exact hcomm s hs c
    · rcases hs with rfl | rfl <;>
        exact hP (by decide +kernel) 0 1 (by decide) (by decide +kernel) (by decide +kernel) c
    · rcases hs with rfl | rfl <;>
        exact hP (by decide +kernel) 0 3 (by decide) (by decide +kernel) (by decide +kernel) c
  rw [Subgroup.eq_top_iff']
  rintro ⟨x, hx⟩
  induction hx using Subgroup.closure_induction with
  | mem x hS =>
    obtain ⟨i, c, hxc | hyc⟩ := hS
    · have : x = pinnedX Tag.E6 F ((1 : ℤ) • Pi.single i 1) c := by
        rw [one_smul, pinnedX_single]
        exact Units.ext hxc
      subst this
      exact hgen 1 (Or.inl rfl) i c
    · have : x = pinnedX Tag.E6 F ((-1 : ℤ) • Pi.single i 1) c := by
        rw [neg_one_smul, pinnedX_neg_single]
        exact Units.ext hyc
      subst this
      exact hgen (-1) (Or.inr rfl) i c
  | one => exact one_mem _
  | mul x y hx hy ihx ihy => exact mul_mem ihx ihy
  | inv x hx ih => exact inv_mem ih

end E6Gen

theorem liftableNormalizerGen_adjointGroup_E6 (F : Type) [Field F] [Finite F] (h3 : (3 : F) ≠ 0) :
    LiftableNormalizerGen ↥(adjointGroup Tag.E6 F) := by
  obtain ⟨h, w, hcomm, hord, hinv, hfix, hh⟩ := E6Gen.exists_inverter_data_adjoint_mem F h3
  refine liftableNormalizerGen_of_inverters h w hcomm hord hinv hfix ?_
  exact eq_top_iff.2 ((E6Gen.closure_pairCentralizing_eq_top F h hh).symm.le.trans
    (Subgroup.closure_mono Set.subset_union_left))

theorem liftableNormalizerGen_E6_of_ne_three (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hp3 : q.p ≠ 3) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  obtain ⟨br⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).e6 q hv
    (GaloisField q.p q.exponent) hcard
  have h3 : (3 : GaloisField q.p q.exponent) ≠ 0 :=
    CFSG.AGLEmbedding.KFactProofs.CoverThree.three_ne_zero_of_card q.prime_p q.exponent_pos
      (by rw [hcard, TauCeti.PrimePower.card_def]) hp3
  exact ((liftableNormalizerGen_adjointGroup_E6 _ h3).of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot).symm).of_mulEquiv br

theorem liftableNormalizerGen_E6 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) (hq3 : 3 ∣ q.card - 1) :
    LiftableNormalizerGen (TauCeti.ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) := by
  refine liftableNormalizerGen_E6_of_ne_three q hv fun hp => ?_
  have h1 : 0 < q.card := by rw [TauCeti.PrimePower.card_def]; exact pow_pos q.prime_p.pos _
  have h2 : 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, hp]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  omega

end CFSG.HardMathSupport.Lang.AlphaThree
