module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Dickson.Bal207.SpShape
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoOBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open Polynomial Module
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ}

private theorem exists_reciprocalOrbit_eq_of_isComponentOf (hF : Nat.card F = 2) (hℓ : 1 ≤ ℓ)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {Kb : Subgroup ↥(StatedSp ℓ F)}
    (hcomp : IsComponentOf Kb (Subgroup.centralizer ({d} : Set ↥(StatedSp ℓ F)))) :
    ∃ O : reciprocalOrbits (spEnd d),
      Kb = ⁅spSupported d (O : Set F[X]), spSupported d (O : Set F[X])⁆ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Finite ↥(StatedSp ℓ F) := Subtype.finite
  have hcard : Fintype.card F = 2 ^ 1 := by rw [Fintype.card_eq_nat_card, hF]; norm_num
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1) hcard
  have hpK : ((3 : ℕ) : F) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff F 2] at h
    norm_num at h
  have hxp : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hker := CFSG.HardMathSupport.Dickson.Bal207.ker_proj_eq_bot_of_two (r := ℓ) hℓ hF
    (Or.inl rfl)
  have ha1 : SymplecticFlag.proj ℓ F d ≠ 1 := fun h =>
    hd1 ((MonoidHom.ker_eq_bot_iff _).1 hker (by rw [h, map_one]))
  have ha : orderOf (SymplecticFlag.proj ℓ F d) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hd3, map_one]) ha1
  have hK : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := 1) (p := 3)
    (r := ℓ) (K := F) Nat.prime_two le_rfl hK Nat.prime_three (by norm_num) (by norm_num) hℓ
    (SymplecticFlag.proj ℓ F d) ha).2 d rfl hxp
  have hsq : Squarefree (minpoly F (spEnd d)) := (altPrimaryData_spLin hpK hd3).squarefree
  haveI : Finite (reciprocalOrbits (spEnd d)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hfix := CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj d
  have hcomp' : IsComponentOf Kb (fixSubgroup (MulAut.conj d)) := by
    rw [hfix]
    exact hcomp
  obtain ⟨i, -, hi⟩ := components_conj_of_orbit_family
    (MonoidHom.id (↥(StatedSp ℓ F))) Function.surjective_id (by simp) d
    (fun O : reciprocalOrbits (spEnd d) => spSupported d (O : Set F[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O => quasisimple_or_solvable_spSupported le_rfl (by norm_num) hsq blocks O)
    Kb hcomp'
  rw [Subgroup.map_id] at hi
  exact ⟨i, hi⟩

theorem eq_or_of_isComponentOf_centralizer (hF : Nat.card F = 2) (hℓ : 1 ≤ ℓ)
    {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) {Kb : Subgroup ↥(StatedSp ℓ F)}
    (hcomp : IsComponentOf Kb (Subgroup.centralizer ({d} : Set ↥(StatedSp ℓ F)))) :
    Kb = ⁅spSupported d {X - 1}, spSupported d {X - 1}⁆ ∨
      Kb = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆ := by
  obtain ⟨O, hi⟩ := exists_reciprocalOrbit_eq_of_isComponentOf hF hℓ hd3 hd1 hcomp
  obtain ⟨h, hh, hO⟩ := O.2
  rw [← hO] at hi
  rcases CFSG.HardMathSupport.Dickson.Bal207.primaryFactor_cases_of_card hF (Or.inl rfl)
    (spEnd_pow hd3) hh with rfl | rfl
  · left
    have hset : (fun h => ({h, reciprocalPolynomial h} : Set F[X])) (X - 1) = {X - 1} := by
      show ({X - 1, reciprocalPolynomial (X - 1)} : Set F[X]) = {X - 1}
      rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    rw [hset] at hi
    exact hi
  · right
    have hset : (fun h => ({h, reciprocalPolynomial h} : Set F[X])) (X ^ 2 + X + 1) =
        {X ^ 2 + X + 1} := by
      show ({X ^ 2 + X + 1, reciprocalPolynomial (X ^ 2 + X + 1)} : Set F[X]) = {X ^ 2 + X + 1}
      rw [CFSG.AGLEmbedding.reciprocalPolynomial_X_sq_add_X_add_one, Set.pair_eq_singleton]
    rw [hset] at hi
    exact hi

theorem stdLayer_eq_or (hF : Nat.card F = 2) (hℓ : 1 ≤ ℓ) {d : ↥(StatedSp ℓ F)} (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (hcomp : IsComponentOf (stdLayer d)
      (Subgroup.centralizer ({d} : Set ↥(StatedSp ℓ F)))) :
    stdLayer d = ⁅spSupported d {X - 1}, spSupported d {X - 1}⁆ ∨
      stdLayer d = ⁅spSupported d {X ^ 2 + X + 1}, spSupported d {X ^ 2 + X + 1}⁆ :=
  eq_or_of_isComponentOf_centralizer hF hℓ hd3 hd1 hcomp

theorem inf_spSupported_le_zpowers {A : Subgroup ↥(StatedSp ℓ F)} {d : ↥(StatedSp ℓ F)}
    (hd : IsStdElt 3 A d) {O : Set F[X]}
    (hO : spSupported d O ≤ Subgroup.centralizer (stdLayer d : Set ↥(StatedSp ℓ F))) :
    A ⊓ spSupported d O ≤ Subgroup.zpowers d :=
  (inf_le_inf_left A hO).trans_eq hd.2.2.2.2

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
