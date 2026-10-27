module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4StdKernel
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.F4InnerCompOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoMain
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSF4Std

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem not_isSolvable_of_model_PSU {G : Type} [Group G] {ν p f : ℕ}
    (h : StatedClassicalModel G .PSU ν p f) : ¬ Group.IsSolvable G := by
  obtain ⟨⟨hp, -, hn, hne⟩, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  have : Fact p.Prime := ⟨hp⟩
  have hperfSU : Group.IsPerfect (StatedSU ν (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn hne
  have hsimple := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK ν hn hne
  have hperfP : Group.IsPerfect (StatedProj (StatedSU ν (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk'
      ((StatedScalars (Fin ν) K).subgroupOf (StatedSU ν (p ^ f) K))) (QuotientGroup.mk'_surjective _)
  intro hs
  have hs' : Group.IsSolvable (StatedProj (StatedSU ν (p ^ f) K)) :=
    solvable_of_solvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  haveI := hsimple.toNontrivial
  exact (IsSolvable.commutator_lt_top_of_nontrivial _).ne hperfP.commutator_eq_top

theorem isQuasisimple_of_tame_of_model_PSU {R : Type} [Group R]
    (hT : CFSG.IsQuasisimple R ∨ Group.IsSolvable R) {ν p f : ℕ}
    (h : StatedClassicalModel (R ⧸ Subgroup.center R) .PSU ν p f) : CFSG.Open.IsQuasisimple R := by
  rcases hT with h1 | h1
  · exact open_isQuasisimple h1
  · exfalso
    haveI : Group.IsSolvable R := h1
    exact not_isSolvable_of_model_PSU h inferInstance

section SULane


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem rationalComponent_su3_model (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {ψ : SL(3, L) →* ModGL Tag.F4 L} {σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ}
    (hψ : IsSLFrame ψ σ) (hΨ : componentRoots (rootCharHom a) i = frameRoots σ)
    (π : Equiv.Perm (Fin 3)) (hπ : ∀ x y : Fin 3, x ≠ y → S.ρ (σ x y) = σ (π y) (π x))
    (hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) (hq : S.D.q = 8)
    (hTame : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
      Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSU 3 2 3 := by
  have hmodel := KSExact.rationalComponent_suN_model S hT i (le_refl 3) hψ hΨ π
    (fun x y hxy => by rw [hs1]; simpa using hπ x y hxy) Nat.prime_two inferInstance
    (by norm_num : 0 < 3) (by rw [hq]; norm_num) (by rw [hs1]; decide)
  rw [hs1] at hmodel
  exact ⟨isQuasisimple_of_tame_of_model_PSU hTame hmodel, hmodel⟩

end SULane

section Classes


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}

theorem f4_count18 : ∀ c ∈ f4Conn,
    kacCount Tag.F4 ![2, 3, 4, 2] (c.map (idxNode (r := Tag.F4.rank))).toFinset = 18 →
      c = [1, 2, 3] ∨ c = [2, 3, 4] := by
  decide +kernel

theorem rootDiagUnit_pow_eq_one {a : Fin Tag.F4.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) :
    rootDiagUnit Tag.F4 a ^ 3 = 1 := by
  have h1 : rootDiagUnit Tag.F4 (a ^ 3) = 1 := by
    have : a ^ 3 = 1 := funext hap
    rw [this]
    exact rootDiagUnit_one
  rw [← h1]
  exact (map_pow (rootDiagUnitHom Tag.F4 L) a 3).symm

theorem twistInner_of_rank3_card18 (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hr3 : compRank (componentRoots (rootCharHom a) i) = 3)
    (hn18 : (componentRoots (rootCharHom a) i).ncard = 18) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
    by_cases hin : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])
    · unfold twistKind
      rw [if_pos hin]
    · unfold twistKind
      rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
        if_neg (fun h => by omega),
        if_neg (fun h => by have := h.2; rw [hr3, hn18] at this; omega)]
  exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hTor i hkind

theorem class_good_of_kernelB (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (hq : S.D.q = 8)
    (hpL : ((3 : ℕ) : L) ≠ 0) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hak : ∀ i, a i = ω ^ k i) (hk : KernelB k) (i : KernelComponent (rootCharHom a)) :
    CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) KSF4Out.F4EightCompIndex := by
  classical
  have hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1 := rootDiagUnit_pow_eq_one hap
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      hpL hT3 i
  have hn18 := ncard_componentRoots_of_kernelB hω3 hω1 hak hk i
  have hc18 : c = [1, 2, 3] ∨ c = [2, 3, 4] := by
    exact f4_count18 c hc (hncard.symm.trans hn18)
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 :=
    componentOrbitLength_eq_one S hT i (rho_image_eq_of_kernelB S hT hω3 hω1 hak hk i)
  have hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 8 := by
    rw [hs1, hq]
    norm_num
  rcases hc18 with rfl | rfl
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
        (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
    obtain ⟨hqs, hmodel⟩ := KSExactSp.rationalComponent_sp3_model S hT i v (J := f4LeviB3)
      (Or.inl rfl) hroots' (twistInner_of_rank3_card18 S hT i hr3 hn18) hQ
    exact ⟨hqs, KSExactSp.isLieQuot_of_B_model hmodel (by norm_num) _
      (fun q hp he => Or.inl ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  · have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hroots' : componentRoots (rootCharHom a) i =
        (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
      rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
        (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
    obtain ⟨hqs, hmodel⟩ := KSExactSp.rationalComponent_sp3_model S hT i v (J := f4LeviC3)
      (Or.inr rfl) hroots' (twistInner_of_rank3_card18 S hT i hr3 hn18) hQ
    exact ⟨hqs, KSExactSp.isLieQuot_of_B_model hmodel (by norm_num) _
      (fun q hp he => Or.inl ⟨q, ⟨hp, he⟩, rfl⟩)⟩

theorem classes_good_of_kernelA2A2 (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1) (hq : S.D.q = 8)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hk3 : ∀ i, k i < 3)
    (hk0 : ∃ i, k i ≠ 0) (hak : ∀ i, a i = ω ^ k i) (hk : KernelA2A2 k) :
    (∀ i : KernelComponent (rootCharHom a),
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) KSF4Out.F4EightCompIndex) ∧
    ∀ i j l : KernelComponent (rootCharHom a), i = j ∨ i = l ∨ j = l := by
  classical
  obtain ⟨σ, τ, κ, κ', ψ, ψ', iΛ, iΘ, hP, hψ, hψ', hΛ, hΘ, hSig, hall, hρσ, hρτ⟩ :=
    exists_pair_frames S hT hap hω3 hω1 hak hk
  have hq3 : S.D.q % 3 = 2 := by rw [hq]
  obtain ⟨π, hπ⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP hψ hSig hq3 hρσ
  obtain ⟨π', hπ'⟩ := exists_outer_shape S hT hω3 hω1 hk3 hk0 hak hP.symm hψ'
    (fun γ hγ hk' => (hSig γ hγ hk').symm) hq3 hρτ
  have hΛgood : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΛ) KSF4Out.F4EightCompIndex := by
    have hs1 := componentOrbitLength_eq_one S hT iΛ (by rw [hΛ]; exact hρσ)
    obtain ⟨hqs, hmodel⟩ := rationalComponent_su3_model S hT iΛ (IsSLFrame.of_isA2Frame hψ) hΛ π
      hπ hs1 hq (hTame iΛ)
    exact ⟨hqs, KSExact.isLieQuot_of_twistedA_model hmodel _
      (fun q hp he => Or.inr ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  have hΘgood : CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) ∧
      IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) iΘ) KSF4Out.F4EightCompIndex := by
    have hs1 := componentOrbitLength_eq_one S hT iΘ (by rw [hΘ]; exact hρτ)
    obtain ⟨hqs, hmodel⟩ := rationalComponent_su3_model S hT iΘ (IsSLFrame.of_isA2Frame hψ') hΘ π'
      hπ' hs1 hq (hTame iΘ)
    exact ⟨hqs, KSExact.isLieQuot_of_twistedA_model hmodel _
      (fun q hp he => Or.inr ⟨q, ⟨hp, he⟩, rfl⟩)⟩
  refine ⟨fun i => ?_, fun i j l => ?_⟩
  · rcases hall i with rfl | rfl
    · exact hΛgood
    · exact hΘgood
  · rcases hall i with rfl | rfl <;> rcases hall j with rfl | rfl <;>
      rcases hall l with rfl | rfl <;> simp

theorem f4_classes_good (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ i, a i ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (hq : S.D.q = 8) (hpL : ((3 : ℕ) : L) ≠ 0)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    (∀ i : KernelComponent (rootCharHom a),
      CFSG.Open.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        IsLieQuot ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) KSF4Out.F4EightCompIndex) ∧
    ∀ i j l : KernelComponent (rootCharHom a), i = j ∨ i = l ∨ j = l := by
  obtain ⟨ω, k, hω3, hω1, hk3, hak⟩ := exists_omega_param hap
  have hk0 : ∃ i, k i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply h1
    have : a = 1 := funext fun i => by rw [hak i, hcon i]; simp
    rw [this]
    exact rootDiagUnit_one
  rcases classify_kernel2 k hk3 hk0 with hB | hA
  · exact ⟨fun i => class_good_of_kernelB S hT hap hq hpL hω3 hω1 hak hB i,
      fun i j l => Or.inl (eq_of_kernelB hω3 hω1 hak hB i j)⟩
  · exact classes_good_of_kernelA2A2 S hT hap hq hTame hω3 hω1 hk3 hk0 hak hA

end Classes

end KSF4Std

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
