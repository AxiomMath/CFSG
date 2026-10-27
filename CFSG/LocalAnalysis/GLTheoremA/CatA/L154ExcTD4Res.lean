module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcTD4Cube
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobRoot
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.RankThree.PartOne.KE (mem_twistedTorusOf)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Interface

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}

@[expose] def L154RootD0
    (S : LangSetup τ L p₀) (R : FrobRoot S.D p) : Prop :=
  ∃ D₀ : LangDatum τ L, D₀.q = R.q0 ∧ ∀ g : ModGL τ L, D₀.step g = R.step0 g

end Interface

section CubeSetup

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p₀ : ℕ}

theorem l154td4_exists_cubeSetup (S : LangSetup τ L p₀) (R : FrobRoot S.D 3)
    (D₀ : LangDatum τ L) (hD₀ : ∀ g, D₀.step g = R.step0 g) {e : ℕ} (he : 1 ≤ e)
    (hq0 : R.q0 = 2 ^ e) (hD₀q : D₀.q = R.q0) :
    ∃ S₀ : LangSetup τ L 5, S₀.D = D₀ ∧
      ∀ γ, IsRoot τ γ → S₀.ρ (S₀.ρ (S₀.ρ γ)) = S.ρ γ := by
  classical
  obtain ⟨ρ₀, hρ₀⟩ := frobeniusOnRoots_proved τ L D₀
  have hq : D₀.q = 2 ^ e := hD₀q.trans hq0
  have hqpow : IsPrimePow D₀.q ∧ ((D₀.q : ℕ) : L) = 0 := by
    rw [hq]
    exact ⟨(Nat.prime_two.isPrimePow).pow (by omega),
      (CharP.cast_eq_zero_iff L 2 _).2 (dvd_pow_self 2 (by omega))⟩
  have hpq : ¬ 5 ∣ D₀.q := by
    rw [hq]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
      ((by norm_num : Nat.Prime 5).dvd_of_dvd_pow h)
    omega
  have hsub : D₀.model ≤ S.D.model := by
    intro x hx
    rw [LangDatum.mem_model] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h1 : R.step0 x = x := by rw [← hD₀]; exact hx.2
    have h2 := R.step0_iterate x
    rw [Function.iterate_fixed h1 3] at h2
    exact h2.symm
  haveI := S.finite
  have hfin : Finite D₀.model := Finite.of_injective (Subgroup.inclusion hsub)
    (Subgroup.inclusion_injective hsub)
  refine ⟨D₀.toSetup 5 ρ₀ hρ₀ (by norm_num) (Or.inl le_rfl) hqpow hpq hfin, rfl, fun γ hγ => ?_⟩
  have hstep3 : S.D.step = D₀.step.comp (D₀.step.comp D₀.step) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, hD₀]
    exact (R.step0_iterate g).symm
  have h1 : (rootSubgroup τ L γ).map S.D.step =
      rootSubgroup τ L (ρ₀ (ρ₀ (ρ₀ γ))) := by
    rw [hstep3, ← Subgroup.map_map, ← Subgroup.map_map, hρ₀.map_rootSubgroup γ hγ,
      hρ₀.map_rootSubgroup _ ((hρ₀.isRoot_iff γ).2 hγ),
      hρ₀.map_rootSubgroup _ ((hρ₀.isRoot_iff _).2 ((hρ₀.isRoot_iff γ).2 hγ))]
  have h2 := S.frob.map_rootSubgroup γ hγ
  have hr3 : IsRoot τ (ρ₀ (ρ₀ (ρ₀ γ))) :=
    (hρ₀.isRoot_iff _).2 ((hρ₀.isRoot_iff _).2 ((hρ₀.isRoot_iff γ).2 hγ))
  have hmem : pinnedX τ L (ρ₀ (ρ₀ (ρ₀ γ))) 1 ∈ rootSubgroup τ L (S.ρ γ) := by
    rw [← h2, h1]
    exact mem_rootSubgroup.2 ⟨1, rfl⟩
  exact eq_of_pinnedX_one_mem_rootSubgroup hr3 ((S.frob.isRoot_iff γ).2 hγ) hmem

end CubeSetup

section Classes

@[expose] def L154TD4Rank : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (onLie fun | .trialityD4 _ => True | _ => False) →
    compRank (componentRoots (rootCharHom a) i) = 4

@[expose] def L154TD4Class : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (onLie fun | .trialityD4 _ => True | _ => False) →
    compRank (componentRoots (rootCharHom a) i) = 4 ∧
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)])

@[expose] def L154LangTD4ResD0 : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (R : FrobRoot S.D 3) (e : ℕ) (a : Fin τ.rank → Lˣ) (i : KernelComponent (rootCharHom a)),
    L154RootD0 S R → 1 ≤ e → R.q0 = 2 ^ e →
    rootDiagUnit τ a ∈ S.D.torus → (∀ k, a k ^ 3 = 1) → rootDiagUnit τ a ≠ 1 →
    R.step0 (rootDiagUnit τ a) = rootDiagUnit τ a →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      R.step0 x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    ¬ catalogIs (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
      (onLie fun | .trialityD4 _ => True | _ => False)

end Classes

section Reduction

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
  {p₀ : ℕ}

theorem l154LangTD4ResD0_of_class (hC : L154TD4Class) : L154LangTD4ResD0 := by
  intro τ L _ _ _ p₀ S R e a i hD0 he hq0 hT hap ha1 hfa hqi _ hTD
  obtain ⟨hr, hn⟩ := hC τ L p₀ S a i hT hap ha1 hqi hTD
  obtain ⟨D₀, hD₀q, hD₀⟩ := hD0
  obtain ⟨S₀, hS₀D, hcube⟩ := l154td4_exists_cubeSetup S R D₀ hD₀ he hq0 hD₀q
  have hT₀ : rootDiagUnit τ a ∈ S₀.D.torus := by
    rw [hS₀D]
    refine mem_twistedTorusOf.2 ⟨(mem_twistedTorusOf.1 hT).1, ?_⟩
    have h1 := hfa
    rw [← hD₀] at h1
    exact h1
  exact hn (l154td4_twistInner_of_cube S S₀ hcube hT hT₀ i hr)

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.K155X

end
