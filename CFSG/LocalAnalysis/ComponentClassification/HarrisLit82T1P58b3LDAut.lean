module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCBasic
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical.SteinbergBY
  (OrthogonalGates orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open scoped MatrixGroups

namespace P58b3L

theorem oddAutInner_of_index_inner {X T : Type} [Group X] [Finite X] [Group T]
    (hX : Group.IsPerfect X) (e' : X ⧸ center X ≃* T) {m : ℕ}
    (hm : (inner T).index = 2 ^ m) : P58b3.OddAutInner X := by
  intro α k hk hα
  have : Group.IsPerfect X := hX
  let Φ : MulAut X →* MulAut T :=
    (MulAut.congr e').toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
  have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (e' (QuotientGroup.mk' (center X) x)) :=
    fun x => by
      change MulAut.congr e' (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
      rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
  have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (e'.symm y)
    exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e').injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
  have hI : (inner T).comap Φ = (MulAut.conj : X →* MulAut X).range := by
    ext β
    rw [mem_comap]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hconjΦ y
      exact ⟨x, hΦ (hx.symm.trans hy)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hΦconj x).symm⟩
  rw [← hI] at hα ⊢
  rw [mem_comap, map_pow] at hα
  exact mem_of_pow_mem_of_index_eq_two_pow hm hk hα

theorem oddAutInner_of_POmegaMinus_three {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    {n : ℕ} (hn : 4 ≤ n) (hm : Blueprint.LieModel (X ⧸ center X) .POmegaMinus n 3 1) :
    P58b3.OddAutInner X := by
  rcases hm with ⟨-, hcm⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hcm' := hcm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  have hn1 : 1 ≤ n := by omega
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hm⟩, -⟩ :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates
      (X ⧸ center X) .POmegaMinus (Or.inr (Or.inr rfl)) n 3 1 hcm hn1 K hK b c hirr e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn
    b c hirr
  have hD : (linearConjugationHom (coordinateQuadMinus n K hn1 b c)).range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have ha : a ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := htop ▸ mem_top a
    have hker : (⟨a, ha⟩ : matrixProjectiveImage (coordinateQuadMinus n K hn1 b c)) ∈ ψ.ker :=
      MonoidHom.mem_ker.mpr (ringEquiv_eq_one_of_card_eq_three hK3 _)
    rw [hψker] at hker
    exact hker
  rw [hD, relIndex_top_right] at hm
  exact oddAutInner_of_index_inner hX.1 (coordinateMinusWitnessEquiv K hn1 b c e) hm

theorem oddAutInner_of_POmegaPlus_three {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    {n : ℕ} (hn : 5 ≤ n) (hm : Blueprint.LieModel (X ⧸ center X) .POmegaPlus n 3 1) :
    P58b3.OddAutInner X := by
  rcases hm with ⟨-, hcm⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  rotate_left
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  have hcm' := hcm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, m, hm⟩, -⟩ :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates
      (X ⧸ center X) .POmegaPlus (Or.inr (Or.inl rfl)) n 3 1 hcm K hK e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn
  have hD : (linearConjugationHom (coordinateQuadPlus n K)).range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have ha : a ∈ matrixProjectiveImage (coordinateQuadPlus n K) := htop ▸ mem_top a
    have hker : (⟨a, ha⟩ : matrixProjectiveImage (coordinateQuadPlus n K)) ∈ ψ.ker :=
      MonoidHom.mem_ker.mpr (ringEquiv_eq_one_of_card_eq_three hK3 _)
    rw [hψker] at hker
    exact hker
  rw [hD, relIndex_top_right] at hm
  exact oddAutInner_of_index_inner hX.1 (coordinatePlusWitnessEquiv K e) hm

end P58b3L

end CFSG.ComponentClassification.HarrisLit.T1
