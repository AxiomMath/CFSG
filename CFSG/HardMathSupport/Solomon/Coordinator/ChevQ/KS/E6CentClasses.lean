module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentData
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6CentFin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6UniqFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompStd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.LangTorus TwE6UniqAbs
open scoped MatrixGroups Matrix

section Classes


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

@[expose] def a0 (ω : Lˣ) : Fin Tag.E6.rank → Lˣ := Pi.mulSingle 3 ω

theorem dV_x0_eq (ω : Lˣ) : dV ω x0 = rootDiagUnit Tag.E6 (a0 ω) := by
  unfold dV
  congr 1
  funext i
  by_cases hi : i = 3
  · subst hi
    simp only [torV, x0, a0, Pi.single_eq_same, Pi.mulSingle_eq_same]
    rw [show ZMod.val (1 : ZMod 3) = 1 from rfl, pow_one]
  · simp [torV, x0, a0, Pi.single_apply, Pi.mulSingle_apply, hi]

theorem rootChar_a0 (ω : Lˣ) (β : Fin Tag.E6.rank → ℤ) : rootChar (a0 ω) β = ω ^ β 3 :=
  CFSG.RankThree.Chevalley.rootChar_mulSingle_eq_zpow 3 ω β

theorem mem_kernelRoots_a0 {ω : Lˣ} (hω : orderOf ω = 3) {β : Fin Tag.E6.rank → ℤ} :
    β ∈ kernelRoots (rootCharHom (a0 ω)) ↔ IsRoot Tag.E6 β ∧ 3 ∣ β 3 := by
  change IsRoot Tag.E6 β ∧ rootChar (a0 ω) β = 1 ↔ _
  rw [rootChar_a0, ← orderOf_dvd_iff_zpow_eq_one, hω]
  simp


theorem R6_nodup : R6.Nodup := by decide +kernel

theorem exists_classEquiv {ω : Lˣ} (hω : orderOf ω = 3) :
    ∃ e : KernelComponent (rootCharHom (a0 ω)) ≃ Fin 3, ∀ i,
      componentRoots (rootCharHom (a0 ω)) i =
        {β | IsRoot Tag.E6 β ∧ 3 ∣ β 3 ∧ cls β = e i} := by
  set χ := rootCharHom (a0 ω) with hχ
  have hmem : ∀ x : kernelRoots χ, x.1 ∈ R6 ∧ 3 ∣ x.1 3 := fun x =>
    ⟨mem_R6_of_isRoot ((mem_kernelRoots_a0 hω).1 x.2).1, ((mem_kernelRoots_a0 hω).1 x.2).2⟩
  have hresp : ∀ x y : kernelRoots χ, (kernelRootSetoid χ).r x y → cls x.1 = cls y.1 := by
    intro x y h
    change Relation.EqvGen _ x y at h
    induction h with
    | rel x y hxy =>
      rw [dotProduct_mulVec_eq_iform] at hxy
      exact cls_respects x.1 (hmem x).1 (hmem x).2 y.1 (hmem y).1 (hmem y).2 hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  let F : KernelComponent χ → Fin 3 := Quotient.lift (fun x : kernelRoots χ => cls x.1) hresp
  have hF : ∀ x : kernelRoots χ, F ⟦x⟧ = cls x.1 := fun x => rfl
  have hinj : Function.Injective F := by
    intro i j hij
    induction i using Quotient.inductionOn with | _ x => ?_
    induction j using Quotient.inductionOn with | _ y => ?_
    rw [hF, hF] at hij
    exact mk_eq_of_iform_ne_zero (cls_connected x.1 (hmem x).1 (hmem x).2 y.1 (hmem y).1
      (hmem y).2 hij)
  have hsurj : Function.Surjective F := by
    intro k
    obtain ⟨β, hβ, h3, hk⟩ := cls_surj k
    exact ⟨⟦⟨β, (mem_kernelRoots_a0 hω).2 ⟨isRoot_of_mem_R6 hβ, h3⟩⟩⟧, by rw [hF]; exact hk⟩
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun i => ?_⟩
  ext β
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨((mem_kernelRoots_a0 hω).1 h).1, ((mem_kernelRoots_a0 hω).1 h).2, rfl⟩
  · rintro ⟨hr, h3, hk⟩
    refine ⟨(mem_kernelRoots_a0 hω).2 ⟨hr, h3⟩, ?_⟩
    apply (Equiv.ofBijective F ⟨hinj, hsurj⟩).injective
    exact hk

theorem ncard_classRoots (k : Fin 3) :
    {β : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 β ∧ 3 ∣ β 3 ∧ cls β = k}.ncard = 6 := by
  have hset : {β : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 β ∧ 3 ∣ β 3 ∧ cls β = k} =
      ↑(R6.filter fun β => 3 ∣ β 3 ∧ cls β = k).toFinset := by
    ext β
    simp only [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨mem_R6_of_isRoot h1, h2, h3⟩,
      fun ⟨h1, h2, h3⟩ => ⟨isRoot_of_mem_R6 h1, h2, h3⟩⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (R6_nodup.filter _)]
  exact card_cls k

theorem exists_frames_a0 {ω : Lˣ}
    (hω : orderOf ω = 3) (i : KernelComponent (rootCharHom (a0 ω))) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.E6 L) (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsSLFrame ψ σ ∧ (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2) ∧
        componentRoots (rootCharHom (a0 ω)) i = frameRoots σ := by
  obtain ⟨e, he⟩ := exists_classEquiv hω
  have hap : ∀ j, a0 ω j ^ 3 = 1 := fun j => by
    have hω3 : ω ^ 3 = 1 := by
      have := pow_orderOf_eq_one ω
      rwa [hω] at this
    by_cases hj : j = 3
    · subst hj
      simpa [a0] using hω3
    · simp [a0, Pi.mulSingle_apply, hj]
  have h6 : (componentRoots (rootCharHom (a0 ω)) i).ncard = 6 := by
    rw [he i]
    exact ncard_classRoots _
  exact (kac_facts TwE6InnerAbs.natCast_three_ne_zero_of_charTwo hap).frame i h6

end Classes

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
