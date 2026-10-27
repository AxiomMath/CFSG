module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.CatLeaf (lieModel_odd_card_ne_L34)
open scoped commutatorElement

@[expose] def NoL34Layer {P : Type} [Group P] (ψ : MulAut P) : Prop :=
  ∀ A : Subgroup P, GLAPComponent 3 (fixSubgroup ψ) A → ¬ IsLThreeFour (barOf 3 A)

theorem noL34Layer_of_fix_eq {P : Type} [Group P] {ψ ψ' : MulAut P}
    (h : fixSubgroup ψ = fixSubgroup ψ') (hψ' : NoL34Layer ψ') : NoL34Layer ψ := by
  intro A hA hT
  rw [h] at hA
  exact hψ' A hA hT

theorem noL34Layer_conj {P : Type} [Group P] [Finite P] {f : MulAut P} (γ : MulAut P)
    (h : NoL34Layer f) : NoL34Layer (γ * f * γ⁻¹) := by
  intro A hA hT
  let π : P →* P := (γ⁻¹ : MulAut P).toMonoidHom
  have hπ : Function.Surjective π := (γ⁻¹ : MulAut P).surjective
  have hker : π.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := (γ⁻¹ : MulAut P).injective (by simpa [π] using hx)
    rw [this]
    exact one_mem _
  have hαψ : ∀ y, π ((γ * f * γ⁻¹) y) = f (π y) := fun y => by simp [π, MulAut.mul_apply]
  obtain ⟨A', hA', hT'⟩ := isLThreeFour_barOf_of_central π hπ hker (γ * f * γ⁻¹) f hαψ hA hT
  exact h A' hA' hT'

theorem noL34Layer_congr {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P'] (θ : P ≃* P')
    {ψ : MulAut P} (h : NoL34Layer (MulAut.congr θ ψ)) : NoL34Layer ψ := by
  intro A hA hT
  have hker : θ.toMonoidHom.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := θ.injective (by simpa using hx)
    rw [this]
    exact one_mem _
  obtain ⟨A', hA', hT'⟩ := isLThreeFour_barOf_of_central θ.toMonoidHom θ.surjective hker ψ
    (MulAut.congr θ ψ) (fun y => by simp [MulAut.congr_apply]) hA hT
  exact h A' hA' hT'

theorem noL34Layer_of_conj_pow {P : Type} [Group P] [Finite P] {β η δ : MulAut P} {r j : ℕ}
    (hrj : (β ^ r) ^ j = β) (hδ : δ * β ^ r * δ⁻¹ = η) (h : NoL34Layer η) : NoL34Layer β := by
  have h1 : NoL34Layer (δ⁻¹ * η * δ⁻¹⁻¹) := noL34Layer_conj δ⁻¹ h
  have h2 : δ⁻¹ * η * δ⁻¹⁻¹ = β ^ r := by
    rw [← hδ]
    group
  rw [h2] at h1
  exact noL34Layer_of_fix_eq (fixSubgroup_pow_eq_of_pow_pow hrj).symm h1

theorem noL34_of_simple_normal_comm {P : Type} [Group P] [Finite P] (ψ : MulAut P)
    (S : Subgroup P) (hSle : S ≤ fixSubgroup ψ)
    (hcomm : ⁅fixSubgroup ψ, fixSubgroup ψ⁆ ≤ S) (hs : IsSimpleGroup ↥S)
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour ↥S) : NoL34Layer ψ := by
  intro A hA hT
  have hq : CFSG.Open.IsQuasisimple ↥S := isQuasisimple_of_simple hnab
  have hAD : A ≤ fixSubgroup ψ := hA.1
  have hAS : A ≤ S := by
    have hperf := glaPComponent_perfect hA
    calc A = ⁅A, A⁆ := hperf.symm
      _ ≤ ⁅fixSubgroup ψ, fixSubgroup ψ⁆ := Subgroup.commutator_mono hAD hAD
      _ ≤ S := hcomm
  have hsn : IsSubnormal A S := isSubnormal_of_le_of_le hA.2.1 hAS hSle
  have hAeq : A = S :=
    Lemma510Ns.eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hA)
      (glaPComponent_ne_bot hA)
  have hAq := isQuasisimple_barOf_of_glaPComponent Nat.prime_three hA
  subst hAeq
  have hcore : GLAPPrimeCore 3 ↥A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥A) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (barOf 3 A) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            rw [h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (barOf 3 A ⧸ Subgroup.center (barOf 3 A)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (barOf 3 A))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hAq.2.toNontrivial
  have e : barOf 3 A ≃* ↥A :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot (G := ↥A))
  exact hL34 (IsLThreeFour.of_mulEquiv e hT)

theorem not_isLThreeFour_of_lieModel_odd (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {X : Type} [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hp2 : p ≠ 2)
    (hm : CFSG.Blueprint.LieModel X t n p f) : ¬ IsLThreeFour X := fun h =>
  lieModel_odd_card_ne_L34 hO hp2 hm.admissible hm (card_eq_of_isLThreeFour h)

theorem noL34Layer_of_fixed_equiv {P : Type} [Group P] [Finite P] (ψ : MulAut P) {X : Type}
    [Group X] (e : ↥(fixSubgroup ψ) ≃* X) (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) (hL34 : ¬ IsLThreeFour X) : NoL34Layer ψ := by
  haveI : IsSimpleGroup ↥(fixSubgroup ψ) := e.isSimpleGroup
  refine noL34_of_simple_normal_comm ψ (fixSubgroup ψ) le_rfl ?_ inferInstance ?_ ?_
  · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa using h))⟩
  · intro h
    exact hL34 (IsLThreeFour.of_mulEquiv e h)

@[expose] def NoL34OuterAt
    (Fam : CFSG.Assembly.LowTwoRank.StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → 5 ≤ p →
    CFSG.Blueprint.LieModel P t n p f →
    ∀ ψ : MulAut P, ψ ^ 3 = 1 →
      ψ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P → NoL34Layer ψ

@[expose] def NoL34InnAt
    (Fam : CFSG.Assembly.LowTwoRank.StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → 5 ≤ p →
    CFSG.Blueprint.LieModel P t n p f →
    ∀ ψ : MulAut P, ψ ^ 3 = 1 →
      ψ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner P → NoL34Layer ψ

@[expose] def NoL34OuterAtThree
    (Fam : CFSG.Assembly.LowTwoRank.StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n f : ℕ),
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 f → t ≠ .Tits → Fam t n 3 f →
    CFSG.Blueprint.LieModel P t n 3 f →
    ∀ ψ : MulAut P, ψ ^ 3 = 1 →
      ψ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P → NoL34Layer ψ

end CFSG.HardMathSupport.Dickson.Sec6
