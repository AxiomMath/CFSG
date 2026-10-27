module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE

section Statements

@[expose] def AnyKindCommute : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), τ ≠ .G2 →
    ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.E → ∀ i : KernelComponent (rootCharHom a),
      3 ≤ S.D.q → 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) →
      ∀ z : ModGL τ L, (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
        ∀ g ∈ rootSpan τ L (componentRoots (rootCharHom a) i), Commute z g

@[expose] def AnyKindNoFrobenius : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p : ℕ) (S : LangSetup τ L p), τ ≠ .G2 →
    (S.D.q ≠ 4 ∨ SimplyLacedTag τ) → ∀ D₁ : Subgroup (ModGL τ L), D₁ ≤ S.E →
      HasBigAnyComponent S D₁ → NoFrobeniusInner S D₁

@[expose] def ThreeBigComponents : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (S : LangSetup τ L 3) (a : Fin τ.rank → Lˣ),
    rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ Nat.Coprime 3 (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i))

end Statements

section Roots

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem exists_component_of_plane (S : LangSetup τ L p) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = p ^ 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ D₁ ∧ rootDiagUnit τ a ≠ 1 ∧
      ∃ i : KernelComponent (rootCharHom a), γ ∈ componentRoots (rootCharHom a) i := by
  have := S.finite_Γ
  have hD₁Γ : D₁ ≤ S.Γ := fun x hx => (S.E_le (hD₁E hx)).2
  have : Finite D₁ := Finite.of_injective (Subgroup.inclusion hD₁Γ)
    (Subgroup.inclusion_injective hD₁Γ)
  have hD₁T : D₁ ≤ torusGroup τ L := fun x hx => (mem_twistedTorusOf.1 (S.E_le (hD₁E hx)).1).1
  have hp := S.hp
  obtain ⟨a, haD, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite hp hD₁T
    (fun x hx => S.E_exp x (hD₁E hx))
    (by rw [hD₁c]; exact lt_self_pow₀ hp.one_lt (by norm_num)) γ
  have hk : γ ∈ kernelRoots (rootCharHom a) := ⟨hγ, hχ⟩
  exact ⟨a, haD, ha1, ⟦⟨γ, hk⟩⟧, hk, rfl⟩

theorem mem_bigAnyRoots_of_threeBig (hbig : ThreeBigComponents) (S : LangSetup τ L 3)
    (hq4 : 4 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = 3 ^ 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    γ ∈ bigAnyRoots S D₁ := by
  obtain ⟨a, haD, ha1, i, hγi⟩ := exists_component_of_plane S hD₁E hD₁c hγ
  have hE := hD₁E haD
  obtain ⟨hs0, -, -⟩ := componentOrbitLength_spec S hE i
  refine ⟨a, haD, ha1, i, hbig τ L S a (S.E_le hE).1 ha1 i, ?_, hγi⟩
  calc 4 ≤ S.D.q := hq4
    _ = S.D.q ^ 1 := (pow_one _).symm
    _ ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) :=
      Nat.pow_le_pow_right (by omega) hs0

theorem hasBigAnyComponent_of_threeBig (hbig : ThreeBigComponents) (S : LangSetup τ L 3)
    (hq4 : 4 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E)
    (hD₁c : Nat.card D₁ = 3 ^ 2) : HasBigAnyComponent S D₁ := by
  obtain ⟨a, haD, ha1, i, hbig', hQ, -⟩ :=
    mem_bigAnyRoots_of_threeBig hbig S hq4 hD₁E hD₁c (isRoot_single τ 0)
  exact ⟨a, haD, ha1, i, hbig', hQ⟩

end Roots

section Commute

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

theorem commute_adjointGroup_of_anyKind (hAK : AnyKindCommute) (hbig : ThreeBigComponents)
    (S : LangSetup τ L 3) (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) {z : ModGL τ L}
    (hz : ∀ x ∈ bigComponentSet S D₁, Commute z x) :
    ∀ g ∈ adjointGroup τ L, Commute z g := by
  have hroot : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c : L, Commute z (pinnedX τ L γ c) := by
    intro γ hγ c
    obtain ⟨a, haD, ha1, i, hbig', hQ, hγi⟩ := mem_bigAnyRoots_of_threeBig hbig S hq4 hD₁E hD₁c hγ
    exact hAK τ L 3 S hτ a (hD₁E haD) i (by omega) hQ z
      (fun x hx => hz x ⟨a, haD, ha1, i, hbig', hx⟩) _ (pinnedX_mem_rootSpan hγi c)
  have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
    rw [adjointGroup, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have hgx : g = pinnedX τ L (Pi.single i 1) c := by
        rw [pinnedX_single]
        exact Units.ext (hg.trans (coe_xUnit i c).symm)
      rw [hgx]
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroot _ (isRoot_single τ i) c).symm.eq
    · have hgy : g = pinnedX τ L (-Pi.single i 1) c := by
        rw [pinnedX_neg_single]
        exact Units.ext (hg.trans (coe_yUnit i c).symm)
      rw [hgy]
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroot _ (isRoot_neg_single τ i) c).symm.eq
  intro g hg
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm

theorem centralizerTrivial_of_anyKind (hAK : AnyKindCommute) (hbig : ThreeBigComponents)
    (S : LangSetup τ L 3) (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) {D₁ : Subgroup (ModGL τ L)}
    (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) : CentralizerTrivial S D₁ := by
  intro z hzC hcomm
  have hz := commute_adjointGroup_of_anyKind hAK hbig S hτ hq4 hD₁E hD₁c
    (fun x hx => hcomm x (Or.inl hx))
  have hcent : (⟨z, hzC⟩ : adjointGroup τ L) ∈ Subgroup.center (adjointGroup τ L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hz g g.2).symm.eq
  rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
  exact congrArg Subtype.val hcent

theorem noFrobeniusInner_of_anyKind (hAF : AnyKindNoFrobenius) (hbig : ThreeBigComponents)
    (S : LangSetup τ L 3) (hτ : τ ≠ .G2) (hq4 : 4 ≤ S.D.q) (hq4' : S.D.q ≠ 4 ∨ SimplyLacedTag τ)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hD₁c : Nat.card D₁ = 3 ^ 2) :
    NoFrobeniusInner S D₁ :=
  hAF τ L 3 S hτ hq4' D₁ hD₁E (hasBigAnyComponent_of_threeBig hbig S hq4 hD₁E hD₁c)

end Commute

end CFSG.HardMathSupport.Timmesfeld.CrossChar
