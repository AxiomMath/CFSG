module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangUntwist
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem f4Three_map_HSL {K₀ L : Type} [Field K₀] [Field L] (ι : K₀ →+* L) (t : K₀ˣ) :
    Matrix.SpecialLinearGroup.map ι (HSL t) = HSL (Units.map ι.toMonoidHom t) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HSL, RingHom.mapMatrix_apply]

theorem f4Three_map_map_fixed {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ Nat.card K) (A : SL2 K) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.map (algebraMap K L) A) =
      Matrix.SpecialLinearGroup.map (algebraMap K L) A := by
  have : Fintype K := Fintype.ofFinite K
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]


section Family

variable (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.F4}
  {g0 : ModGL Tag.F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
  (S : LangSetup Tag.F4 (AlgebraicClosure K) 3)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem f4Three_q_eq : S.D.q = Nat.card K := by
  rw [hSD]
  rfl

include hSD in
theorem f4Three_rho_eq : ∀ γ, IsRoot Tag.F4 γ → S.ρ γ = w • γ := by
  have hfrob : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) S.ρ := by
    rw [← hSD]
    exact S.frob
  intro γ hγ
  exact frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hfrob hγ

theorem f4Three_rootSL2_mem_component {a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (B : SL2 (AlgebraicClosure K)) :
    rootSL2 Tag.F4 (AlgebraicClosure K) γ B ∈
      rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  refine rootSpan_mono (fun δ hδ => ?_) (rootSL2_mem_rootSpan_pair (hΨ.isRoot γ hγ) B)
  rcases hδ with rfl | rfl
  · exact hγ
  · exact hΨ.neg_mem _ hγ

include hSD in
theorem f4Three_exists_family (hq3 : ¬ 3 ∣ Nat.card K)
    {a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ} (hE : rootDiagUnit Tag.F4 a ∈ S.E)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (z : ModGL Tag.F4 (AlgebraicClosure K))
      (P : (Fin Tag.F4.rank → ℤ) → GL (Fin 2) (AlgebraicClosure K)),
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL Tag.F4 (AlgebraicClosure K),
        g ∈ rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈
            rootSpan Tag.F4 (AlgebraicClosure K) (componentRoots (rootCharHom a) j)) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ A : SL2 K,
        S.D.step (z * rootSL2 Tag.F4 (AlgebraicClosure K) γ (conjSL (P γ)
          (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) =
          z * rootSL2 Tag.F4 (AlgebraicClosure K) γ (conjSL (P γ)
            (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∃ ζ : (AlgebraicClosure K)ˣ, orderOf ζ = 3 ∧
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (conjSL (P γ))) := by
  classical
  have hq := f4Three_q_eq K hFr hg0C hg0 S hSD
  have hρ := f4Three_rho_eq K hFr hg0C hg0 S hSD
  have : Fintype K := Fintype.ofFinite K
  have hmod : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 2 := by omega
  rcases hmod with h1 | h2
  ·
    obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwist S hE i one_pos
      (f4Three_twistInner_one S hρ hE (by rw [hq]; exact h1) i)
    have hσK : ∀ c, σ c = c ^ Nat.card K := fun c => by rw [hσ, hq, pow_one]
    refine ⟨z, fun _ => 1, hnorm, fun γ hγ A => ?_, fun γ _ => ?_⟩
    · have hγr := isRoot_of_mem_componentRoots hγ
      have hgS := f4Three_rootSL2_mem_component K i hγ
        (conjSL 1 (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
      have h := hz _ hgS
      rw [iterHom_eq_iterate, Function.iterate_one] at h
      rw [h, frobGL_rootSL2 σ hγr, conjSL_one, f4Three_map_map_fixed σ hσK]
    ·
      have h3 : 3 ∣ Fintype.card Kˣ := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
        omega
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 3 h3
      refine ⟨Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ, ?_, ?_⟩
      · rw [orderOf_injective _ (Units.map_injective (algebraMap K _).injective) ζ, hζ]
      · refine ⟨_, ⟨HSL ζ, rfl⟩, ?_⟩
        rw [conjSL_one, f4Three_map_HSL]
  ·
    obtain ⟨u, hu, hρu⟩ := f4Three_twist_neg_two S hρ hE (by rw [hq]; exact h2) i
    obtain ⟨σ, z, hσ, hnorm, hz⟩ := f4Three_exists_untwist_neg S f4Neg_smul hE i hu hρu
    have hσK : ∀ c, σ.toRingHom c = c ^ Nat.card K := fun c => by
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hq]
    have hP : ∀ γ : Fin Tag.F4.rank → ℤ, ∃ P : GL (Fin 2) (AlgebraicClosure K),
        IsRoot Tag.F4 γ →
          (∀ B : SL2 (AlgebraicClosure K),
            canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg *
              Units.map (entrywiseHom σ.toRingHom) (rootSL2 Tag.F4 (AlgebraicClosure K) γ B) *
              (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) f4Neg)⁻¹ =
              rootSL2 Tag.F4 (AlgebraicClosure K) γ B ↔
            B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
              (conjSL P)) ∧
          ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ (Nat.card K + 1) = 1 →
            HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
              (conjSL P) := by
      intro γ
      by_cases hγ : IsRoot Tag.F4 γ
      · obtain ⟨P, hP1, hP2⟩ := exists_twisted_rootSL2 (K := K) hσK hγ (f4Neg_smul γ)
        exact ⟨P, fun _ => ⟨hP1, hP2⟩⟩
      · exact ⟨1, fun h => absurd h hγ⟩
    choose P hP using hP
    obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K
      (L := AlgebraicClosure K) (N := 3) (by omega)
    refine ⟨z, P, hnorm, fun γ hγ A => ?_, fun γ hγ =>
      ⟨ζ, hζord, ((hP γ) (isRoot_of_mem_componentRoots hγ)).2 ζ hζq⟩⟩
    have hγr := isRoot_of_mem_componentRoots hγ
    have hgS := f4Three_rootSL2_mem_component K i hγ
      (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
    rw [hz _ hgS]
    have hfix := (((hP γ) hγr).1
      (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))).2
        ⟨_, ⟨A, rfl⟩, rfl⟩
    exact congrArg (fun x => z * x * z⁻¹) hfix

end Family

section Component

variable {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup Tag.F4 L 3)

theorem f4Three_mem_rationalComponent {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK4 : 4 ≤ Nat.card K) {a : Fin Tag.F4.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {z : ModGL Tag.F4 L}
    (hnorm : ∀ g : ModGL Tag.F4 L,
      g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i))
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {P : GL (Fin 2) L}
    (hfix : ∀ A : SL2 K,
      S.D.step (z * rootSL2 Tag.F4 L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A))
        * z⁻¹) =
        z * rootSL2 Tag.F4 L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) * z⁻¹)
    {B : SL2 L} (hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) :
    z * rootSL2 Tag.F4 L γ B * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨-, hqs⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) with hS₀
  set Y := S₀.map ((MulAut.conj z).toMonoidHom.comp (rootSL2 Tag.F4 L γ)) with hY
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hγr := hΨ.isRoot γ hγ
  have hYp : ⁅Y, Y⁆ = Y := by
    rw [hY, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hYS : Y ≤ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) := by
    rintro _ ⟨B', -, rfl⟩
    exact (hnorm _).1 (rootSpan_mono (fun δ hδ => by
      rcases hδ with rfl | rfl
      · exact hγ
      · exact hΨ.neg_mem _ hγ) (rootSL2_mem_rootSpan_pair hγr B'))
  have hYM : Y ≤ S.D.model := by
    rintro _ ⟨B', ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    refine (LangDatum.mem_model S.D).2 ⟨rootSpan_le_adjointGroup L _ (hYS ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩,
      rfl⟩), ?_⟩
    have h := hfix A
    exact h
  have hYΓ : Y ≤ S.Γ := by
    rw [← hYp]
    exact Subgroup.commutator_mono hYM hYM
  have hYR : Y ≤ rootSpan Tag.F4 L (rationalRoots S.ρ (rootCharHom a) i) :=
    hYS.trans (rootSpan_mono fun δ hδ => ⟨0, δ, hδ, rfl⟩)
  have hYsp : Y ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := le_inf hYR hYΓ
  have hYc : Y ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hYp]
    exact Subgroup.commutator_mono hYsp hYsp
  exact hYc ⟨B, hB, rfl⟩

theorem f4Three_mem_bigComponentSet {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK4 : 4 ≤ Nat.card K) {D₁ : Subgroup (ModGL Tag.F4 L)} {a : Fin Tag.F4.rank → Lˣ}
    (haD : rootDiagUnit Tag.F4 a ∈ D₁) (ha1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {z : ModGL Tag.F4 L}
    (hnorm : ∀ g : ModGL Tag.F4 L,
      g ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i) ↔
        z * g * z⁻¹ ∈ rootSpan Tag.F4 L (componentRoots (rootCharHom a) i))
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {P : GL (Fin 2) L}
    (hfix : ∀ A : SL2 K,
      S.D.step (z * rootSL2 Tag.F4 L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A))
        * z⁻¹) =
        z * rootSL2 Tag.F4 L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) * z⁻¹)
    {ζ : Lˣ} (hζ : orderOf ζ = 3)
    (hζP : HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P))
    {B : SL2 L} (hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) :
    z * rootSL2 Tag.F4 L γ B * z⁻¹ ∈ bigComponentSet S D₁ := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hγr := hΨ.isRoot γ hγ
  refine ⟨a, haD, ha1, i, ?_, f4Three_mem_rationalComponent S hK4 i hnorm hγ hfix hB⟩
  have hx := f4Three_mem_rationalComponent S hK4 i hnorm hγ hfix hζP
  set x := z * rootSL2 Tag.F4 L γ (HSL ζ) * z⁻¹ with hxdef
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    omega
  have hHSL : ∀ n : ℕ, HSL ζ ^ n = HSL (ζ ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact (HSL_one_eq).symm
    | succ n ih => rw [pow_succ, ih, HSL_mul_HSL, pow_succ]
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, conj_pow, ← map_pow, hHSL, hζ3, HSL_one_eq, map_one, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : rootSL2 Tag.F4 L γ (HSL ζ) = 1 := by
      have := congrArg (fun y => z⁻¹ * y * z) h1
      simpa [hxdef, mul_assoc] using this
    have h3 : HSL ζ = 1 := CFSG.RankThree.PartTwo.Census.Exceptional.rootSL2_injective hγr
      (h2.trans (map_one _).symm)
    apply hζ1
    have h4 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h3
    simp [HSL] at h4
    exact h4
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd := orderOf_dvd_natCard (⟨x, hx⟩ : rationalComponent S.ρ S.Γ (rootCharHom a) i)
  rw [Subgroup.orderOf_mk, hord] at hdvd
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three, not_not]
  exact hdvd

end Component

end CFSG.HardMathSupport.Timmesfeld.CrossChar
