module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcBigDefs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedBad
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.RankThree.Chevalley

theorem k1419e_card_mul_dvd_of_le {G : Type} [Group G] {P : Subgroup G} [Finite P]
    {X Y Z : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) (hZ : Z ≤ P)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a) (hXZ : ∀ a ∈ X, ∀ b ∈ Z, a * b = b * a)
    (hYZ : ∀ a ∈ Y, ∀ b ∈ Z, a * b = b * a)
    (cX : ∀ a ∈ X, (∀ b ∈ X, a * b = b * a) → a = 1)
    (cY : ∀ a ∈ Y, (∀ b ∈ Y, a * b = b * a) → a = 1)
    (cZ : ∀ a ∈ Z, (∀ b ∈ Z, a * b = b * a) → a = 1) :
    Nat.card X * Nat.card Y * Nat.card Z ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) := by
  have hcomm : ∀ {A B : Subgroup G}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      ∀ a ∈ A.subgroupOf P, ∀ b ∈ B.subgroupOf P, a * b = b * a := by
    intro A B hAB a ha b hb
    exact Subtype.ext (hAB _ ha _ hb)
  have hcl : ∀ {A : Subgroup G}, A ≤ P → (∀ a ∈ A, (∀ b ∈ A, a * b = b * a) → a = 1) →
      ∀ a ∈ A.subgroupOf P, (∀ b ∈ A.subgroupOf P, a * b = b * a) → a = 1 := by
    intro A hA cA a ha hab
    apply Subtype.ext
    refine cA _ ha fun b hb => ?_
    have := hab ⟨b, hA hb⟩ hb
    exact congrArg Subtype.val this
  have hcardA : ∀ {A : Subgroup G}, A ≤ P → Nat.card (A.subgroupOf P) = Nat.card A :=
    fun {A} hA => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hdvd := Up34Chev2.card_mul_dvd_card_centerQuotient (X.subgroupOf P) (Y.subgroupOf P)
    (Z.subgroupOf P) (hcomm hXY) (hcomm hXZ) (hcomm hYZ) (hcl hX cX) (hcl hY cY) (hcl hZ cZ)
  rwa [hcardA hX, hcardA hY, hcardA hZ] at hdvd

theorem k1419e_three_dvd_sl2_card (m : ℕ) : 3 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h : (2 ^ m) ^ 2 = 4 ^ m := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h]
  simpa using Nat.sub_dvd_pow_sub_pow 4 1 m

section RankOne

variable
  {τ : Tag} {K : Type} [Field K]

theorem k1419e_rootSL2_centerless [CharP K 2] (β : Fin τ.rank → ℤ) :
    ∀ a ∈ (rootSL2 τ K β).range, (∀ b ∈ (rootSL2 τ K β).range, a * b = b * a) → a = 1 := by
  rintro _ ⟨A, rfl⟩ h
  have hA : A ∈ Subgroup.center (SL2 K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply rootSL2_injective_of_field β
    rw [map_mul, map_mul]
    exact (h _ ⟨B, rfl⟩).symm
  rw [center_sl2_eq_bot_two, Subgroup.mem_bot] at hA
  rw [hA, map_one]

theorem k1419e_three_dvd_card_range [Finite K] (h3 : 3 ∣ Nat.card K * (Nat.card K ^ 2 - 1))
    (β : Fin τ.rank → ℤ) : 3 ∣ Nat.card (rootSL2 τ K β).range := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (rootSL2_injective_of_field β)).toEquiv,
    card_sl2_eq]
  exact h3

end RankOne

section ClassGroup


theorem k1419e_dvd_27_aux {τ : Tag} {M : Type} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) {K : Type} [Field K]
    [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K * (Nat.card K ^ 2 - 1))
    (htr : k1419eHasTriple τ (componentRoots χ i)) :
    27 ∣ Nat.card (↥(componentRootSpan K χ i) ⧸ Subgroup.center ↥(componentRootSpan K χ i)) := by
  classical
  obtain ⟨β₁, h₁, β₂, h₂, β₃, h₃, o₁₂, o₁₃, o₂₃⟩ := htr
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hle : ∀ β ∈ componentRoots χ i, (rootSL2 τ K β).range ≤ componentRootSpan K χ i := by
    intro β hβ
    rw [range_rootSL2_of_isRoot (hΨ.isRoot β hβ)]
    exact sup_le (rootSubgroup_le_rootSpan hβ) (rootSubgroup_le_rootSpan (hΨ.neg_mem β hβ))
  have hcomm : ∀ {β γ : Fin τ.rank → ℤ}, β ∈ componentRoots χ i → γ ∈ componentRoots χ i →
      k1419eStrongOrth τ β γ → ∀ a ∈ (rootSL2 τ K β).range, ∀ b ∈ (rootSL2 τ K γ).range,
        a * b = b * a :=
    fun hβ hγ o => exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K
      (hΨ.isRoot _ hβ) (hΨ.isRoot _ hγ) o.1 o.2.1 o.2.2
  have hdvd := k1419e_card_mul_dvd_of_le (P := componentRootSpan K χ i) (hle _ h₁) (hle _ h₂)
    (hle _ h₃) (hcomm h₁ h₂ o₁₂) (hcomm h₁ h₃ o₁₃) (hcomm h₂ h₃ o₂₃)
    (k1419e_rootSL2_centerless _) (k1419e_rootSL2_centerless _) (k1419e_rootSL2_centerless _)
  have h27 : 27 ∣ Nat.card (rootSL2 τ K β₁).range * Nat.card (rootSL2 τ K β₂).range *
      Nat.card (rootSL2 τ K β₃).range := by
    have := mul_dvd_mul (mul_dvd_mul (k1419e_three_dvd_card_range h3 β₁)
      (k1419e_three_dvd_card_range h3 β₂)) (k1419e_three_dvd_card_range h3 β₃)
    simpa using this
  exact h27.trans hdvd

end ClassGroup

section Rational


theorem k1419e_dvd_27_of_triple {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2] {S : LangSetup τ L p₀}
    {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)} (D : InnerData S a i)
    (hbig : 14 ≤ (componentRoots (rootCharHom a) i).ncard)
    (htr : k1419eHasTriple τ (componentRoots (rootCharHom a) i)) :
    27 ∣ Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  haveI := D.hKfin
  haveI := finite_rationalComponent S a i
  have hperf := isPerfect_componentRootSpan_of_big hτ D hbig
  obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
  obtain ⟨e⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf g hg hgk
  rw [← Nat.card_congr e.toEquiv]
  refine k1419e_dvd_27_aux i (K := fixSubfield D.σ) ?_ htr
  rw [D.hKcard]
  exact k1419e_three_dvd_sl2_card _

end Rational

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
