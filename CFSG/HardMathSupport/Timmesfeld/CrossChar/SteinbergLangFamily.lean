module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangInner
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangFamily

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Family

variable {τ : Tag} (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup τ}
  {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
  {p : ℕ} (S : LangSetup τ (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem steinbergLang_q_eq : S.D.q = Nat.card K := by
  rw [hSD]
  rfl

include hSD in
theorem steinbergLang_rho_eq : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ := by
  have hfrob : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0) S.ρ := by
    rw [← hSD]
    exact S.frob
  intro γ hγ
  exact frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hfrob hγ

theorem steinbergLang_rootSL2_mem_component {a : Fin τ.rank → (AlgebraicClosure K)ˣ}
    (i : KernelComponent (rootCharHom a)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ componentRoots (rootCharHom a) i) (B : SL2 (AlgebraicClosure K)) :
    rootSL2 τ (AlgebraicClosure K) γ B ∈
      rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) := by
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  refine rootSpan_mono (fun δ hδ => ?_) (rootSL2_mem_rootSpan_pair (hΨ.isRoot γ hγ) B)
  rcases hδ with rfl | rfl
  · exact hγ
  · exact hΨ.neg_mem _ hγ

include hSD in
theorem steinbergLang_exists_family (hp : p.Prime)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hqp : Nat.card K % p = 1 ∨ Nat.card K % p = p - 1)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hE : rootDiagUnit τ a ∈ S.E)
    (i : KernelComponent (rootCharHom a)) :
    ∃ (z : ModGL τ (AlgebraicClosure K))
      (P : (Fin τ.rank → ℤ) → GL (Fin 2) (AlgebraicClosure K)),
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ (AlgebraicClosure K),
        g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) j)) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ A : SL2 K,
        S.D.step (z * rootSL2 τ (AlgebraicClosure K) γ (conjSL (P γ)
          (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) =
          z * rootSL2 τ (AlgebraicClosure K) γ (conjSL (P γ)
            (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) * z⁻¹) ∧
      (∀ γ ∈ componentRoots (rootCharHom a) i, ∃ ζ : (AlgebraicClosure K)ˣ, orderOf ζ = p ∧
        HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
          (conjSL (P γ))) := by
  classical
  have hq := steinbergLang_q_eq K hFr hg0C hg0 S hSD
  have hρ := steinbergLang_rho_eq K hFr hg0C hg0 S hSD
  have : Fintype K := Fintype.ofFinite K
  have hp2 := hp.two_le
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  rcases hqp with h1 | h2
  ·
    obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwist S hE i one_pos
      (steinbergLang_twistInner_one S hρ hE hst (by rw [hq]; exact h1) i)
    have hσK : ∀ c, σ c = c ^ Nat.card K := fun c => by rw [hσ, hq, pow_one]
    refine ⟨z, fun _ => 1, hnorm, fun γ hγ A => ?_, fun γ _ => ?_⟩
    · have hγr := isRoot_of_mem_componentRoots hγ
      have hgS := steinbergLang_rootSL2_mem_component K i hγ
        (conjSL 1 (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
      have h := hz _ hgS
      rw [iterHom_eq_iterate, Function.iterate_one] at h
      rw [h, frobGL_rootSL2 σ hγr, conjSL_one, f4Three_map_map_fixed σ hσK]
    ·
      have hdvd : p ∣ Fintype.card Kˣ := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card]
        have h3 := Nat.mod_add_div (Nat.card K) p
        rw [h1] at h3
        exact ⟨Nat.card K / p, by omega⟩
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card p hdvd
      refine ⟨Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom ζ, ?_, ?_⟩
      · rw [orderOf_injective _ (Units.map_injective (algebraMap K _).injective) ζ, hζ]
      · refine ⟨_, ⟨HSL ζ, rfl⟩, ?_⟩
        rw [conjSL_one, f4Three_map_HSL]
  ·
    obtain ⟨u, hu, hρu⟩ := steinbergLang_twist_neg S hρ hE hst hw₀ hp.one_lt.le
      (by rw [hq]; exact h2) i
    obtain ⟨σ, z, hσ, hnorm, hz⟩ := f4Three_exists_untwist_neg S hw₀ hE i hu hρu
    have hσK : ∀ c, σ.toRingHom c = c ^ Nat.card K := fun c => by
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hq]
    have hP : ∀ γ : Fin τ.rank → ℤ, ∃ P : GL (Fin 2) (AlgebraicClosure K),
        IsRoot τ γ →
          (∀ B : SL2 (AlgebraicClosure K),
            canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀ *
              Units.map (entrywiseHom σ.toRingHom) (rootSL2 τ (AlgebraicClosure K) γ B) *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w₀)⁻¹ =
              rootSL2 τ (AlgebraicClosure K) γ B ↔
            B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
              (conjSL P)) ∧
          ∀ ζ : (AlgebraicClosure K)ˣ, ζ ^ (Nat.card K + 1) = 1 →
            HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))).range.map
              (conjSL P) := by
      intro γ
      by_cases hγ : IsRoot τ γ
      · obtain ⟨P, hP1, hP2⟩ := exists_twisted_rootSL2 (K := K) hσK hγ (hw₀ γ)
        exact ⟨P, fun _ => ⟨hP1, hP2⟩⟩
      · exact ⟨1, fun h => absurd h hγ⟩
    choose P hP using hP
    have hdvd : p ∣ Nat.card K + 1 := by
      have h3 := Nat.mod_add_div (Nat.card K) p
      rw [h2] at h3
      exact ⟨Nat.card K / p + 1, by
        have : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
        nlinarith⟩
    obtain ⟨ζ, hζord, hζq⟩ := exists_orderOf_eq_of_dvd_card_add_one K
      (L := AlgebraicClosure K) hdvd
    refine ⟨z, P, hnorm, fun γ hγ A => ?_, fun γ hγ =>
      ⟨ζ, hζord, ((hP γ) (isRoot_of_mem_componentRoots hγ)).2 ζ hζq⟩⟩
    have hγr := isRoot_of_mem_componentRoots hγ
    have hgS := steinbergLang_rootSL2_mem_component K i hγ
      (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))
    rw [hz _ hgS]
    have hfix := (((hP γ) hγr).1
      (conjSL (P γ) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A))).2
        ⟨_, ⟨A, rfl⟩, rfl⟩
    exact congrArg (fun x => z * x * z⁻¹) hfix

end Family

section Component

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem steinbergLang_mem_rationalComponent {K : Type} [Field K] [Finite K] [Algebra K L]
    (hK4 : 4 ≤ Nat.card K) {a : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {P : GL (Fin 2) L}
    (hfix : ∀ A : SL2 K,
      S.D.step (z * rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A))
        * z⁻¹) =
        z * rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) * z⁻¹)
    {B : SL2 L} (hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) :
    z * rootSL2 τ L γ B * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  obtain ⟨-, hqs⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 P
  set S₀ := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P) with hS₀
  set Y := S₀.map ((MulAut.conj z).toMonoidHom.comp (rootSL2 τ L γ)) with hY
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hγr := hΨ.isRoot γ hγ
  have hYp : ⁅Y, Y⁆ = Y := by
    rw [hY, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hqs.1]
  have hYS : Y ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rintro _ ⟨B', -, rfl⟩
    exact (hnorm _).1 (rootSpan_mono (fun δ hδ => by
      rcases hδ with rfl | rfl
      · exact hγ
      · exact hΨ.neg_mem _ hγ) (rootSL2_mem_rootSpan_pair hγr B'))
  have hYM : Y ≤ S.D.model := by
    rintro _ ⟨B', ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    refine (LangDatum.mem_model S.D).2 ⟨rootSpan_le_adjointGroup L _ (hYS ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩,
      rfl⟩), ?_⟩
    exact hfix A
  have hYΓ : Y ≤ S.Γ := by
    rw [← hYp]
    exact Subgroup.commutator_mono hYM hYM
  have hYR : Y ≤ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
    hYS.trans (rootSpan_mono fun δ hδ => ⟨0, δ, hδ, rfl⟩)
  have hYsp : Y ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i := le_inf hYR hYΓ
  have hYc : Y ≤ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [← hYp]
    exact Subgroup.commutator_mono hYsp hYsp
  exact hYc ⟨B, hB, rfl⟩

theorem steinbergLang_mem_bigComponentSet (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [Algebra K L] (hK4 : 4 ≤ Nat.card K) {D₁ : Subgroup (ModGL τ L)} {a : Fin τ.rank → Lˣ}
    (haD : rootDiagUnit τ a ∈ D₁) (ha1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a)) {z : ModGL τ L}
    (hnorm : ∀ g : ModGL τ L,
      g ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ↔
        z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) i))
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ componentRoots (rootCharHom a) i) {P : GL (Fin 2) L}
    (hfix : ∀ A : SL2 K,
      S.D.step (z * rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A))
        * z⁻¹) =
        z * rootSL2 τ L γ (conjSL P (Matrix.SpecialLinearGroup.map (algebraMap K L) A)) * z⁻¹)
    {ζ : Lˣ} (hζ : orderOf ζ = p)
    (hζP : HSL ζ ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P))
    {B : SL2 L} (hB : B ∈ (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map (conjSL P)) :
    z * rootSL2 τ L γ B * z⁻¹ ∈ bigComponentSet S D₁ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hγr := hΨ.isRoot γ hγ
  refine ⟨a, haD, ha1, i, ?_, steinbergLang_mem_rationalComponent S hK4 i hnorm hγ hfix hB⟩
  have hx := steinbergLang_mem_rationalComponent S hK4 i hnorm hγ hfix hζP
  set x := z * rootSL2 τ L γ (HSL ζ) * z⁻¹ with hxdef
  have hζp : ζ ^ p = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.one_lt.ne' hζ.symm
  have hHSL : ∀ n : ℕ, HSL ζ ^ n = HSL (ζ ^ n) := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact (HSL_one_eq).symm
    | succ n ih => rw [pow_succ, ih, HSL_mul_HSL, pow_succ]
  have hxp : x ^ p = 1 := by
    rw [hxdef, conj_pow, ← map_pow, hHSL, hζp, HSL_one_eq, map_one, mul_one, mul_inv_cancel]
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : rootSL2 τ L γ (HSL ζ) = 1 := by
      have := congrArg (fun y => z⁻¹ * y * z) h1
      simpa [hxdef, mul_assoc] using this
    have h3 : HSL ζ = 1 := CFSG.RankThree.PartTwo.Census.Exceptional.rootSL2_injective hγr
      (h2.trans (map_one _).symm)
    apply hζ1
    have h4 := congrArg (fun A : SL2 L => (A : Matrix (Fin 2) (Fin 2) L) 0 0) h3
    simp [HSL] at h4
    exact h4
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvd := orderOf_dvd_natCard (⟨x, hx⟩ : rationalComponent S.ρ S.Γ (rootCharHom a) i)
  rw [Subgroup.orderOf_mk, hord] at hdvd
  rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
  exact hdvd

end Component

end CFSG.HardMathSupport.Timmesfeld.CrossChar
