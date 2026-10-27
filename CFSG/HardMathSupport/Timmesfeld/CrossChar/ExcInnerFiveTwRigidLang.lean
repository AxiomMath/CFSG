module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFiveTwRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LangTorusSylowFree

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.Lattice CFSG.RankThree.Classical CFSG.RankThree.PartOne.KGD
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

theorem mem_bigComponentSet_of_twistedSL2 {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (hp2 : p ≠ 2) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = p ^ 2) {K₀ : Type} [Field K₀] [Finite K₀] [Algebra K₀ L]
    (hK₀ : 4 ≤ Nat.card K₀) (hpK₀ : p ∣ Nat.card K₀ + 1) (i : Fin τ.rank) (P : GL (Fin 2) L)
    (hPΓ : ∀ A : SL2 K₀, rootSL2 τ L (Pi.single i 1)
      (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) ∈ S.Γ)
    (hPH : ∀ ζ : Lˣ, ζ ^ (Nat.card K₀ + 1) = 1 →
      HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P))
    (A : SL2 K₀) :
    rootSL2 τ L (Pi.single i 1) (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K₀ L) A)) ∈
      bigComponentSet S D₁ := by
  classical
  have hp := S.hp
  have := S.finite_Γ
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  have hD₁p : ∀ x ∈ D₁, x ^ p = 1 := fun x hx => S.E_exp x (hD₁E hx)
  have hcard : p < Nat.card D₁ := by
    rw [hD₁c]
    have := hp.one_lt
    nlinarith
  obtain ⟨a, haD, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite hp hD₁T hD₁p hcard (Pi.single i 1)
  have hαk : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ kernelRoots (rootCharHom a) :=
    ⟨isRoot_single τ i, hχ⟩
  set i₀ : KernelComponent (rootCharHom a) := ⟦⟨_, hαk⟩⟧ with hi₀
  have hαi : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i₀ := ⟨hαk, rfl⟩
  have hnegi := (isRootComponent_componentRoots (χ := rootCharHom a) i₀).neg_mem _ hαi
  obtain ⟨hfin, hqs⟩ := sl2_conj_range_quasisimple (K := K₀) (L := L) hK₀ P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K₀ L)).range.map (conjSL P) with hS₀
  set X := S₀.map (rootSL2 τ L (Pi.single i 1)) with hX
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hXΓ : X ≤ S.Γ := by
    rintro _ ⟨B, ⟨_, ⟨A', rfl⟩, rfl⟩, rfl⟩
    exact hPΓ A'
  have hXspan : X ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i₀) := by
    rintro _ ⟨B, -, rfl⟩
    refine (?_ : rootSpan τ L {Pi.single i 1, -Pi.single i 1} ≤ _)
      (rootSL2_mem_rootSpan_pair (isRoot_single τ i) B)
    refine iSup₂_le fun γ hγ => le_iSup₂_of_le (f := fun δ (_ : δ ∈ rationalRoots S.ρ
      (rootCharHom a) i₀) => rootSubgroup τ L δ) γ ?_ le_rfl
    rcases hγ with rfl | hγ
    · exact ⟨0, _, hαi, rfl⟩
    · rw [Set.mem_singleton_iff.1 hγ]
      exact ⟨0, _, hnegi, rfl⟩
  have hXR : X ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i₀ := by
    rw [← hXp]
    exact Subgroup.commutator_mono (le_inf hXspan hXΓ) (le_inf hXspan hXΓ)
  have hRΓ : rationalComponent S.ρ S.Γ (rootCharHom a) i₀ ≤ S.Γ :=
    (commutator_self_le_self _).trans inf_le_right
  have : Finite (rationalComponent S.ρ S.Γ (rootCharHom a) i₀) :=
    Finite.of_injective (Subgroup.inclusion hRΓ) (Subgroup.inclusion_injective hRΓ)
  obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K₀ (L := L) hpK₀
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hζord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have h3 := hp.two_le
    exact hp2 (by omega)
  obtain ⟨_, ⟨A', rfl⟩, hA'⟩ := hPH ζ hζq
  have hζX : torusElt τ L i ζ ∈ X := ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, by
    rw [hA', rootSL2_single, simpleRootSL2_HSL]⟩
  have hord : orderOf (torusElt τ L i ζ) = p := by
    have h1 := orderOf_canonicalRep_conj_torusElt (K := L) hp (1 : WeylGroup τ) i hζord hζ2
    rwa [canonicalRep_one, one_mul, inv_one, mul_one] at h1
  have hbig : ¬ Nat.Coprime p (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i₀)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
    have h1 := orderOf_dvd_natCard (⟨_, hXR hζX⟩ :
      ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i₀))
    rwa [Subgroup.orderOf_mk, hord] at h1
  refine ⟨a, haD, ha1, i₀, hbig, hXR ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩⟩

section TwistedE6

theorem setupRigid_twistedE6_neg {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {v : WeylGroup TwistTag.E6.tag}
    (hv : ∀ x, v • x = -permLattice TwistTag.E6.perm x)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hq4 : 4 ≤ ℓ ^ f) (hq8 : ℓ ^ f ≠ 8) {p : ℕ} (hp2 : p ≠ 2) (hpq1 : p ∣ ℓ ^ f + 1)
    [IsAlgClosed (AlgebraicClosure K)] (S : LangSetup TwistTag.E6.tag (AlgebraicClosure K) p)
    (hSD : S.D = LangDatum.ofTwist TwistTag.E6 Fr (ℓ ^ f) hFr v hg0C hg0) : SetupRigid S := by
  obtain ⟨D, ρ, frob, E, hp, hq, hqpow, hpq, hfin, hEle, hEexp, hEall⟩ := S
  simp only at hSD
  subst hSD
  intro D₁ hD₁E hD₁c δ _ _ hfixX
  obtain ⟨K₀, _, _, _, hK₀, P, hPΓ, hPH, hrig⟩ :=
    exists_twistedSL2_rigid_twistedE6_neg hℓ hf hK hσ hFr hv hg0C hg0 hq4 hq8
  refine hrig δ fun i A => hfixX _ ?_
  exact mem_bigComponentSet_of_twistedSL2 _ hp2 hD₁E hD₁c (hK₀ ▸ hq4) (hK₀ ▸ hpq1) i (P i)
    (hPΓ i) (hPH i) A

theorem twistedE6LangTorusPlaneBalance_neg_of_components (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ x, v • x = -permLattice TwistTag.E6.perm x) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Q : ℕ → Prop}
    (hQ : ∀ q, 2 ≤ q → Q q → ¬ p ∣ q ∧ (5 ≤ p ∨ 4 ≤ q) ∧ p ∣ q + 1 ∧ 4 ≤ q ∧ q ≠ 8)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc) : TwistedE6LangTorusPlaneBalance v p Q :=
  twistedE6LangTorusPlaneBalance_of_setupRigidAt v hp
    (fun q hq2 hq => ⟨(hQ q hq2 hq).1, (hQ q hq2 hq).2.1⟩)
    (fun ℓ f hℓ hf hQq K _ hK σ hσ Fr hFr g0 hg0C hg0 S hSD => by
      obtain ⟨-, -, hpq1, hq4, hq8⟩ := hQ _ (Nat.one_lt_pow (by omega) hℓ.one_lt) hQq
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      exact setupRigid_twistedE6_neg hℓ hf hK hσ hFr hv hg0C hg0 hq4 hq8 hp2 hpq1 S hSD)
    hsub hin hsu htw hex

theorem toMat_twE6TwoMat : toMat TwistTag.E6.tag.rank twE6TwoMat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem twE6PhiTwoWeyl_smul_neg (x : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6PhiTwoWeyl • x = -permLattice TwistTag.E6.perm x := by
  rw [twE6PhiTwoWeyl_smul, toMat_twE6TwoMat, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem twistedE6LangTorusPlaneBalance_two_five_of_components (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc) :
    TwistedE6LangTorusPlaneBalance twE6PhiTwoWeyl 5 fun q => 5 ∣ q + 1 :=
  twistedE6LangTorusPlaneBalance_neg_of_components twE6PhiTwoWeyl twE6PhiTwoWeyl_smul_neg
    Nat.prime_five (by norm_num) (fun q _ (hq : 5 ∣ q + 1) =>
      ⟨by omega, Or.inl le_rfl, hq, by omega, by omega⟩) hsub hin hsu htw hex

theorem crossCharInnerAt_twistedE6_five_of_components (hsub : LangSubnormal)
    (hin : LangComponentsQuasisimple .inner) (hsu : LangComponentsQuasisimple .suN)
    (htw : LangComponentsQuasisimple .twoD) (hex : LangComponentsQuasisimple .exc)
    (h1 : TwistedE6LangTorusPlaneBalance twE6PhiOneWeyl 5 fun q => 5 ∣ q - 1) :
    CrossCharInnerAt .twistedE6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5 :=
  crossCharInnerAt_twistedE6_five_of_lang
    (twistedE6LangTorusPlaneBalance_two_five_of_components hsub hin hsu htw hex) h1

end TwistedE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
