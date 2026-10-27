module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.CurtisTits

theorem exists_standardPair_partner_of_nodes {K : Type} [Group K] {D : UniversalRootDatum K}
    {F : Type} [Field F] (hbd : HasBruhatDatum D) (hok : CartanOK D) {i j : Fin D.rank}
    (hi : IsLongestRoot D (Pi.single i 1)) (hj : IsLongestRoot D (Pi.single j 1))
    (hp : IsPartner D.isFiniteType (Pi.single i 1) (Pi.single j 1))
    (hpair : ∃ W, LinearBlockStandardPair F W (rankOne D.rootGroup i) (rankOne D.rootGroup j))
    {γ : Fin D.rank → ℤ} (hγ : IsLongestRoot D γ) :
    ∃ δ : Fin D.rank → ℤ, IsLongestRoot D δ ∧ IsPartner D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair F W (D.rootGroup γ ⊔ D.rootGroup (-γ))
        (D.rootGroup δ ⊔ D.rootGroup (-δ)) := by
  obtain ⟨_, _, hct, -⟩ := hbd
  exact exists_standardPair_partner hct hok.irreducible hok.ratio hi hj hp hpair hγ

theorem standardPair_specialLinear (F : Type) [Field F] (m : ℕ) (hm : 2 ≤ m) :
    ∃ W, LinearBlockStandardPair F W
      (rankOne (SpecialLinear.rootGroup m F) ⟨0, by omega⟩)
      (rankOne (SpecialLinear.rootGroup m F) ⟨1, by omega⟩) := by
  rw [rankOne_eq_range, rankOne_eq_range]
  exact ⟨_, (weakCTSystem_standard (K := F) m).pair ⟨0, by omega⟩ ⟨1, by omega⟩ rfl⟩

theorem exists_standardPair_partner_PSL (n p f : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible .PSL n p f) (hn : 3 ≤ n)
    {γ : Fin (modelUniv .PSL n p f hp.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv .PSL n p f hp.out).D γ) :
    ∃ δ : Fin (modelUniv .PSL n p f hp.out).D.rank → ℤ,
      IsLongestRoot (modelUniv .PSL n p f hp.out).D δ ∧
      IsPartner (modelUniv .PSL n p f hp.out).D.isFiniteType γ δ ∧
      ∃ W, LinearBlockStandardPair (GaloisField p f) W
        ((modelUniv .PSL n p f hp.out).D.rootGroup γ ⊔
          (modelUniv .PSL n p f hp.out).D.rootGroup (-γ))
        ((modelUniv .PSL n p f hp.out).D.rootGroup δ ⊔
          (modelUniv .PSL n p f hp.out).D.rootGroup (-δ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .PSL (m + 1) p f hp.out trivial hadm
  obtain ⟨hirr, hratio⟩ := cartanOK .PSL (m + 1) p f hp.out trivial hadm
  have hm : 2 ≤ m := by omega
  let i₀ : Fin (modelUniv .PSL (m + 1) p f hp.out).D.rank := ⟨0, by show 0 < m; omega⟩
  let i₁ : Fin (modelUniv .PSL (m + 1) p f hp.out).D.rank := ⟨1, by show 1 < m; omega⟩
  have h0 : IsLongestRoot (modelUniv .PSL (m + 1) p f hp.out).D (Pi.single i₀ 1) :=
    isLongestRoot_single .PSL (m + 1) p f hp.out trivial hadm i₀ trivial
  have h1 : IsLongestRoot (modelUniv .PSL (m + 1) p f hp.out).D (Pi.single i₁ 1) :=
    isLongestRoot_single .PSL (m + 1) p f hp.out trivial hadm i₁ trivial
  have hp01 : IsPartner (modelUniv .PSL (m + 1) p f hp.out).D.isFiniteType
      (Pi.single i₀ 1) (Pi.single i₁ 1) :=
    isPartner_single_single _
      (by
        show CartanMatrix.A m (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩ = -1
        simp [CartanMatrix.A])
      (by
        show CartanMatrix.A m (⟨1, by omega⟩ : Fin m) ⟨0, by omega⟩ = -1
        simp [CartanMatrix.A])
  exact exists_standardPair_partner hct hirr hratio h0 h1 hp01
    (standardPair_specialLinear (GaloisField p f) m hm) hγ

end CFSG.ClassicalInvolution.ModelFacts
