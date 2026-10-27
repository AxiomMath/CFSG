module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma89
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Norm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem i1420Model_of_component {p : ℕ} (hp : p.Prime) {a : G} {J I₀ D : Subgroup G}
    (hD : IsElemAbelian p D) (hDc : Nat.card D = p ^ 2) (haD : a ∈ D) (ha1 : a ≠ 1)
    (hK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)))
    (hJ : GLAPComponent p (Subgroup.centralizer ({a} : Set G)) J)
    (hI : GLAPComponent p (J ⊓ Subgroup.centralizer (D : Set G)) I₀)
    (hnot : ¬ J ≤ I₀ ⊔ GLAPPrimeCoreOf p J) :
    I1420Model p J I₀ D := by
  have hIJ : I₀ ≤ J := hI.1.trans inf_le_left
  have hIC : I₀ ≤ Subgroup.centralizer (D : Set G) := hI.1.trans inf_le_right
  have hIperf : ⁅I₀, I₀⁆ = I₀ := glaPComponent_perfect hI
  have hIn : ¬ I₀ ≤ GLAPPrimeCoreOf p J := not_le_glaPPrimeCoreOf_of_component hp hI inf_le_left
  have hDN : D ≤ Subgroup.normalizer (J : Set G) := by
    intro y hy
    have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact isElemAbelian_commute hD haD hy
    refine normalizer_of_centralized hp hJ (mem_normalizer_centralizer hyC) hIJ ?_ hIperf hIn
    intro i hi
    refine Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)
    rw [Set.mem_singleton_iff.1 hh]
    exact Subgroup.mem_centralizer_iff.1 (hIC hi) y hy
  have hJK : CFSG.Open.IsKGroup ↥J := CFSG.Open.IsKGroup.of_le hK hJ.1
  have hQ : CFSG.Open.IsQuasisimple (PQuot p J) := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hKq : CFSG.Open.IsKGroup (PQuot p J) := CFSG.Open.IsKGroup.quotient hJK _
  have hcat : IsCatalogGroup (PSimple p J) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' hKq hQ
  exact ⟨hD, hDc, hDN, hQ, hcat, hI, hnot, a, haD, ha1, hJ.1⟩

end CFSG.LocalAnalysis.GLTheoremA.H1420

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L89

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.H1420 (i1420Model_of_component)

theorem in8910_i1420_of_facts (hLy : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420Ly)
    (hCo1 : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420Co1)
    (hSuz : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420Suz)
    (hSuzh : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420Suzh)
    (hM3 : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420M3)
    (hM5 : CFSG.LocalAnalysis.GLTheoremA.H1420.I1420M5)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I1420CfgAt G p := by
  intro x L row c _hx _hL hRow hrow a haD _ha1 hKa J hJ hI hnot
  have hD : IsElemAbelian p c.D := c.hD.2.1
  have hDc : Nat.card c.D = p ^ 2 := c.hD.2.2.1
  have hRI : RowI row p (cfgI p L c.D) := c.hData.2.2.1
  rcases hrow with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain rfl : p = 3 := hRow.1
    exact hLy G J (cfgI 3 L c.D) c.D
      (i1420Model_of_component Nat.prime_three hD hDc haD _ha1 hKa hJ hI hnot) hRI
  ·
    obtain rfl : p = 3 := hRow.1
    exact hCo1 G J (cfgI 3 L c.D) c.D
      (i1420Model_of_component Nat.prime_three hD hDc haD _ha1 hKa hJ hI hnot) hRI
  ·
    obtain rfl : p = 3 := hRow.1
    exact hSuz G J (cfgI 3 L c.D) c.D
      (i1420Model_of_component Nat.prime_three hD hDc haD _ha1 hKa hJ hI hnot) hRI
  ·
    obtain rfl : p = 3 := hRow.1
    exact hSuzh G J (cfgI 3 L c.D) c.D
      (i1420Model_of_component Nat.prime_three hD hDc haD _ha1 hKa hJ hI hnot) hRI
  ·
    obtain rfl : p = 3 := hRow.1
    exact hM3 G J (cfgI 3 L c.D) c.D
      (i1420Model_of_component Nat.prime_three hD hDc haD _ha1 hKa hJ hI hnot) hRI
  ·
    obtain rfl : p = 5 := hRow.1
    exact hM5 G J (cfgI 5 L c.D) c.D
      (i1420Model_of_component (by norm_num) hD hDc haD _ha1 hKa hJ hI hnot) hRI

end CFSG.LocalAnalysis.GLTheoremA.S8.L89

end
