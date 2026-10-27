module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PslBadAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
  CFSG.ComponentClassification.CatLeaf CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open Up34Chev2
open scoped commutatorElement

@[expose] def Up34C2OutDiagLinAt (n : ℕ) : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ f → Nat.card K = 2 ^ f →
    ∀ A : GL (Fin n) K, conjAut n K A ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K) →
      ¬ Up34Pumpup (projectiveSL n K) (conjAut n K A)

@[expose] def Up34C2OutDiag_A2 : Prop := Up34C2OutDiagLinAt 3

@[expose] def Up34C2OutDiag_AHigh : Prop := ∀ n : ℕ, 4 ≤ n → Up34C2OutDiagLinAt n

namespace Up34Chev2

section Field


theorem lieModel_psl_two_of_isLThreeFour {X : Type} [Group X] {n f : ℕ} (hn : 3 ≤ n)
    (hX : Blueprint.LieModel X .PSL n 2 f) (h : IsLThreeFour X) : n = 3 ∧ f = 2 := by
  have h34 : Blueprint.LieModel X .PSL 3 2 2 := isL34Type_of_isLThreeFour h
  obtain ⟨-, hn3, hf⟩ := CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique (by norm_num) h34 hX
  exact ⟨hn3, hf⟩

theorem noL34Layer_fieldAut_psl {n : ℕ} (hn3 : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hσ : orderOf σ = 3) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hne : ¬ (n = 3 ∧ f = 6)) : NoL34Layer (fieldAut n K σ) := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ x, x ∈ k ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) k
  let S : Subgroup (projectiveSL n K) := (linearSubfieldInclusion n k).range
  let eS : ↥S ≃* projectiveSL n ↥k := (MonoidHom.ofInjective hinj).symm
  haveI : IsSimpleGroup (projectiveSL n ↥k) := KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnabk : ∃ a b : projectiveSL n ↥k, a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL (n := n) (K := ↥k) hn3
    push Not at h1
    exact h1
  have hs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabk
    exact ⟨eS.symm a, eS.symm b, fun h => hab (by
      have := congrArg eS h
      simpa using this)⟩
  have hSle : S ≤ fixSubgroup (fieldAut n K σ) := by
    rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).mp hc) y
  have hcomm : ⁅fixSubgroup (fieldAut n K σ), fixSubgroup (fieldAut n K σ)⁆ ≤ S :=
    Subgroup.commutator_le.2 fun a ha b hb => commutator_fixed_mem_range (by omega) ha hb
  obtain ⟨h3f, hkcard⟩ := card_semilinearFixedSubfield Nat.prime_two hf hK hσ
  have hf0 : 1 ≤ f / 3 := by
    have : 3 ≤ f := Nat.le_of_dvd (by omega) h3f
    omega
  refine noL34_of_simple_normal_comm _ S hSle hcomm hs hnab fun hT => ?_
  have hadm : StatedLieAdmissible .PSL n 2 (f / 3) :=
    ⟨Nat.prime_two, hf0, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
      fun hc => by have := (Prod.mk.inj hc).1; omega⟩
  have hmodel : LieModel ↥S .PSL n 2 (f / 3) :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, ↥k, inferInstance, inferInstance, hkcard,
        ⟨eS.trans (statedProjEquiv n ↥k).symm⟩⟩
  obtain ⟨hn, hf3⟩ := lieModel_psl_two_of_isLThreeFour hn3 hmodel hT
  exact hne ⟨hn, by omega⟩

theorem up34C2Out_lin_model {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hD : Up34C2OutDiagLinAt n) {S : Type} [Group S] [Finite S]
    (hm : Blueprint.LieModel S .PSL n 2 f) (α : MulAut S)
    (hα : α ∉ (MulAut.conj : S →* MulAut S).range) (hp : Up34Pumpup S α) :
    n = 3 ∧ f = 6 := by
  have hC : StatedClassicalModel S .PSL n 2 f := (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨hadm, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : S ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  haveI : Finite (projectiveSL n K) := Finite.of_equiv S e.toEquiv
  have hψ3 : MulAut.congr e α ^ 3 = 1 := by rw [← map_pow, ((up34Pumpup_iff α).1 hp).1, map_one]
  have hψinn : MulAut.congr e α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL n K) := fun h =>
    hα ((congr_mem_inner_iff_of_equiv e α).mp h)
  by_cases hdiag : MulAut.congr e α ∈ linearAutGroup n K
  · exfalso
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hdiag
    refine hD f K hf hK A ?_ ?_
    · rw [hA]
      exact hψinn
    · rw [hA]
      exact hp.of_congr e
  · by_contra hne
    obtain ⟨σ, hσ, H, hψH⟩ := linear_order_three_field_descent hn (MulAut.congr e α) hψ3 hdiag
    have h1 : NoL34Layer (MulAut.congr e α) := by
      rw [hψH]
      exact noL34Layer_conj _ (noL34Layer_fieldAut_psl hn hσ hf hK hne)
    exact ((up34Pumpup_iff α).1 hp).2.2 (noL34Layer_congr e h1)

end Field

end Up34Chev2

section Family


theorem up34C2Out_a2_of_diag (hD : Up34C2OutDiag_A2) : Up34Chev2Out FamA2 := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | A r q =>
    have hq2 : q.p = 2 := hc
    have hr2 : r = 2 := hF
    subst hr2
    have hm := blueprintLieModel_A 2 q hv e
    rw [hq2] at hm
    obtain ⟨-, hf6⟩ := up34C2Out_lin_model (by norm_num) q.exponent_pos hD hm α hα hp
    exact Or.inl ⟨rfl, hq2, hf6⟩
  | _ => exact hF.elim

theorem up34C2Out_aHigh_of_diag (hD : Up34C2OutDiag_AHigh) : Up34Chev2Out FamAHigh := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα hp
  cases d with
  | A r q =>
    exfalso
    have hq2 : q.p = 2 := hc
    have hr3 : 3 ≤ r := hF
    have hm := blueprintLieModel_A r q hv e
    rw [hq2] at hm
    obtain ⟨hn3, -⟩ := up34C2Out_lin_model (by omega) q.exponent_pos (hD (r + 1) (by omega)) hm α
      hα hp
    omega
  | _ => exact hF.elim

end Family

end CFSG.HardMathSupport.Dickson.Sec6
