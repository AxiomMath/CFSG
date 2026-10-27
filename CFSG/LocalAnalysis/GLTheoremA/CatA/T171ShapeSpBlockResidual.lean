module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockInnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInOmGen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieCore
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open Polynomial
open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open scoped commutatorElement

@[expose] def UnitaryBlockInnAutDerived : Prop :=
  ∀ (a n : ℕ) (E : Type) [Field E] [Finite E], UnitaryFieldData 2 n E →
    ∀ {p : ℕ}, p.Prime → p ≠ 2 → 2 ≤ a → (a, 2 ^ n) ≠ (3, 2) →
    ∀ (M : GL (Fin a) E), M ∈ LargeEvenGUSet (Fin a) E (2 ^ n) →
      ∀ (hN : M ∈ Subgroup.normalizer (unitarySU 2 n E a : Set (GL (Fin a) E))),
      M ^ p = 1 →
      TableB.projConj (unitarySU 2 n E a) ⟨M, hN⟩ ∈
        innAutDerived (LargeEvenProj (unitarySU 2 n E a))

theorem sympComponentOrbit {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp m K} (hx : x ^ p = 1) (hx1 : x ≠ 1)
    {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J) :
    ∃ O ∈ reciprocalOrbits (spEnd x),
      J = (⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆).map (proj m K) := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [pow_zero] at hK
      have h2 : 1 < Nat.card K := Finite.one_lt_card
      omega
    · exact h
  haveI hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [Fintype.card_eq_nat_card, hK])
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h).symm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero m := ⟨by omega⟩
  have hm1 : 1 ≤ m := by omega
  have ha1 : proj m K x ≠ 1 := fun h => hx1
    ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := m) (K := K)).1 (by rw [h, map_one]))
  have ha : orderOf (proj m K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  have hblocks : SpPrimaryBlocks 2 n p x (proj m K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := n) (p := p) (r := m)
      (K := K) Nat.prime_two hn hK hp hp2 hp2 hm1 (proj m K x) ha).2 x rfl hxp
  have hsq : Squarefree (minpoly K (spEnd x)) :=
    (altPrimaryData_spLin hpK hx).squarefree
  have hq : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have htame : ∀ O : reciprocalOrbits (spEnd x),
      CFSG.IsQuasisimple ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ∨
        Group.IsSolvable ↥(spSupported x (O : Set K[X])) :=
    fun O =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
        (by have := hp.two_le; omega) hq hsq hblocks O
  have hZc : (proj m K).ker ≤ Subgroup.center (StatedSp m K) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer
      (MulAut.conj (proj m K x)) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp
      (ℓ := 2) (f := n) (p := p) (r := m) (K := K)
      Nat.prime_two hn hK hm1 hp hp2 hp2 x hx
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp := (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
    hJ hJle).1
  have hcomm := hblocks.directProduct.1
  have hjoin := hblocks.directProduct.2.2
  obtain ⟨O, -, hJeq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family (proj m K)
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective hZc x
      (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
      (fun i j hij a ha b hb =>
        hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hjoin htame J hJcomp
  exact ⟨O, O.2, hJeq⟩

@[expose] def SympComponentDescent : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
    (K : Type) [Field K] [Finite K] (x y : StatedSp m K)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp m K)),
    (hS : Setup p L J A d b) →
    LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * l * d)
      (MulAut.conj (proj m K x)) →
    LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b)
      (MulAut.conj (proj m K y)) →
    ∀ (hN : proj m K y ∈ Subgroup.normalizer
        (((J.subgroupOf L).map (piCenterQuot θ)) :
          Set (StatedProj (StatedSp m K)))),
      ∃ e : PSimple p J ≃* PSimple p ((J.subgroupOf L).map (piCenterQuot θ)),
        MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm) =
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p ((J.subgroupOf L).map (piCenterQuot θ))
            (proj m K y)⁻¹ (Subgroup.inv_mem _ hN)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
