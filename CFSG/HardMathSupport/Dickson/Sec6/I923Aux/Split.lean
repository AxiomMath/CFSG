module

public import CFSG.HardMathSupport.Dickson.Sec6.I923
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transfer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartTwo.KFacts

@[expose] def Y923_LieRestAt (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    CFSG.Open.GLAPPrimeCore 3 Y = ⊥ → (∀ s : ℕ, ¬ IsTypeL2 s Y) →
    ∀ (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f →
      LieModel (Y ⧸ Subgroup.center Y) t n p f →
      ∀ α : MulAut Y, α ^ 3 = 1 → α ∉ innAutDerived Y →
        ∀ J : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub α) J →
          ∀ r0 : ℕ, 10 ≤ r0 → ¬ IsTypeL2 r0 (barOf 3 J)

theorem Y923_LieRestAt.union {F G : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hF : Y923_LieRestAt F) (hG : Y923_LieRestAt G) :
    Y923_LieRestAt (fun t n p f => F t n p f ∨ G t n p f) :=
  fun Y _ _ hq hcore hL2 t n p f hadm ht hFG hm => by
    rcases hFG with h | h
    · exact hF Y hq hcore hL2 t n p f hadm ht h hm
    · exact hG Y hq hcore hL2 t n p f hadm ht h hm

theorem y923_lieRest_of_cover {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hcov : ∀ t n p f, StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f)
    (h : Y923_LieRestAt Fam) : Y923_LieRest :=
  fun Y _ _ hq hcore hL2 t n p f hadm ht hm =>
    h Y hq hcore hL2 t n p f hadm ht (hcov t n p f hadm ht) hm

theorem congr_trans_apply {A B : Type*} [Group A] [Group B] (e : A ≃* B) (δ : MulAut B)
    (φ : MulAut A) : MulAut.congr (e.trans δ) φ = δ * MulAut.congr e φ * δ⁻¹ := by
  ext b
  simp [MulAut.congr_apply]

theorem noL2_of_conj_descent {Y P : Type} [Group Y] [Finite Y] [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) {ψ : MulAut P}
    (hψ : MulAut.congr e (centerDescend Y α) = ψ) {γ f : MulAut P} (hγ : ψ = γ * f * γ⁻¹)
    (h : NoL2Layer f) {J : Subgroup Y} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) {r : ℕ}
    (hr : 10 ≤ r) : ¬ IsTypeL2 r (barOf 3 J) := by
  refine noL2_of_descent (e.trans (γ⁻¹ : MulAut P)) α ?_ h hJ hr
  rw [congr_trans_apply, hψ, hγ]
  group

@[expose] def FamOK (P : Type) [Group P] : Prop :=
  ∀ ψ : MulAut P, ψ ^ 3 = 1 → ¬ IsInnerAut ψ →
    ∃ γ f : MulAut P, ψ = γ * f * γ⁻¹ ∧ NoL2Layer f

theorem noL2_of_famOK {Y P : Type} [Group Y] [Finite Y] [Group P] (hY : CFSG.Open.IsQuasisimple Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (hP : FamOK P) {α : MulAut Y} (h3 : α ^ 3 = 1)
    (hnot : α ∉ innAutDerived Y) {J : Subgroup Y}
    (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) {r : ℕ} (hr : 10 ≤ r) :
    ¬ IsTypeL2 r (barOf 3 J) := by
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  have hψ3 : (MulAut.congr e (centerDescend Y α)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, h3, map_one, map_one]
  have hninn : ¬ IsInnerAut (MulAut.congr e (centerDescend Y α)) := fun hinn => hnot
    (innerAut_le_innAutDerived Y
      (isInnerAut_of_isInnerAut_centerDescend ((isInnerAut_congr e _).1 hinn)))
  obtain ⟨γ, f, hγ, hf⟩ := hP _ hψ3 hninn
  exact noL2_of_conj_descent e α rfl hγ hf hJ hr

theorem noL2Layer_conj {P : Type} [Group P] [Finite P] {f : MulAut P} (γ : MulAut P)
    (h : NoL2Layer f) : NoL2Layer (γ * f * γ⁻¹) := by
  intro A hA r hr hT
  let π : P →* P := (γ⁻¹ : MulAut P).toMonoidHom
  have hπ : Function.Surjective π := (γ⁻¹ : MulAut P).surjective
  have hker : π.ker ≤ Subgroup.center P := by
    intro x hx
    have : x = 1 := (γ⁻¹ : MulAut P).injective (by simpa [π] using hx)
    rw [this]
    exact one_mem _
  have hαψ : ∀ y, π ((γ * f * γ⁻¹) y) = f (π y) := fun y => by simp [π, MulAut.mul_apply]
  obtain ⟨A', hA', hT'⟩ := typeL2_barOf_of_central π hπ hker (γ * f * γ⁻¹) f hαψ hA hT
  exact h A' hA' r hr hT'

@[expose] def NoL2OuterAt (Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ), StatedLieAdmissible t n p f →
    t ≠ .Tits → Fam t n p f → LieModel P t n p f →
    ∀ ψ : MulAut P, ψ ^ 3 = 1 → ψ ∉ inner P → NoL2Layer ψ

theorem y923_lieRestAt_of_noL2Outer {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : NoL2OuterAt Fam) : Y923_LieRestAt Fam := by
  intro Y _ _ hq hcore hL2 t n p f hadm ht hF hm α h3 hnot J hJ r hr
  have hnoL2 := h (Y ⧸ Subgroup.center Y) t n p f hadm ht hF hm
  have hP : FamOK (Y ⧸ Subgroup.center Y) := fun ψ hψ3 hninn =>
    ⟨1, ψ, by simp, hnoL2 ψ hψ3 hninn⟩
  exact noL2_of_famOK hq (MulEquiv.refl _) hP h3 hnot hJ hr

@[expose] def FamPslTwo : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t n _ _ => t = .PSL ∧ n = 2

@[expose] def FamPslGood : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSL ∧ 3 ≤ n ∧ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))

@[expose] def FamPslBad : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSL ∧ 3 ≤ n ∧ ¬ Nat.Coprime 3 (Nat.gcd n (p ^ f - 1))

@[expose] def Y923_PslBad : Prop := Y923_LieRestAt FamPslBad

@[expose] def FamPsp : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSp ∧ 2 ≤ n ∧ ¬ (n = 2 ∧ p ^ f = 8)

@[expose] def FamPspTwoEight : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSp ∧ n = 2 ∧ p ^ f = 8

@[expose] def FamPsuGood : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ 3 ≤ n ∧ ¬ 3 ∣ Nat.gcd n (p ^ f + 1)

@[expose] def FamPsuBad : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => t = .PSU ∧ 3 ≤ n ∧ 3 ∣ Nat.gcd n (p ^ f + 1)

@[expose] def Y923_PsuGood : Prop := Y923_LieRestAt FamPsuGood

@[expose] def Y923_PsuBad : Prop := Y923_LieRestAt FamPsuBad

@[expose] def FamOrthOdd : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .POmegaOdd

@[expose] def Y923_OrthOdd : Prop := Y923_LieRestAt FamOrthOdd

@[expose] def FamOrthPlus : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n _ _ => t = .POmegaPlus ∧ 5 ≤ n

@[expose] def Y923_OrthPlus : Prop := Y923_LieRestAt FamOrthPlus

@[expose] def FamOrthMinus : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .POmegaMinus

@[expose] def Y923_OrthMinus : Prop := Y923_LieRestAt FamOrthMinus

@[expose] def FamD4 : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n _ _ => t = .POmegaPlus ∧ n = 4

@[expose] def Y923_D4 : Prop := Y923_LieRestAt FamD4

@[expose] def FamTriD4 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .trialityD4

@[expose] def Y923_TriD4 : Prop := Y923_LieRestAt FamTriD4

@[expose] def FamG2 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .G2

@[expose] def Y923_G2 : Prop := Y923_LieRestAt FamG2

@[expose] def FamF4 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .F4

@[expose] def Y923_F4 : Prop := Y923_LieRestAt FamF4

@[expose] def FamE6 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .E6

@[expose] def Y923_E6 : Prop := Y923_LieRestAt FamE6

@[expose] def FamTwE6 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .twistedE6

@[expose] def Y923_TwE6 : Prop := Y923_LieRestAt FamTwE6

@[expose] def FamE7 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .E7

@[expose] def Y923_E7 : Prop := Y923_LieRestAt FamE7

@[expose] def FamE8 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .E8

@[expose] def Y923_E8 : Prop := Y923_LieRestAt FamE8

@[expose] def FamSz : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .twistedB2

@[expose] def FamReeG2 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .twistedG2

@[expose] def Y923_ReeG2 : Prop := Y923_LieRestAt FamReeG2

@[expose] def FamReeF4 : StatedLieTag → ℕ → ℕ → ℕ → Prop := fun t _ _ _ => t = .twistedF4

@[expose] def Y923_ReeF4 : Prop := Y923_LieRestAt FamReeF4

end CFSG.HardMathSupport.Dickson.Sec6.I923
