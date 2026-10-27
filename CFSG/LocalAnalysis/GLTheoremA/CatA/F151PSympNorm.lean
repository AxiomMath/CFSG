module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open Polynomial
open CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCSpFull CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement

private theorem conj_mem_spSupported {r : ℕ} {K : Type} [Field K] {x y g : StatedSp r K}
    {O : Set K[X]} (hxy : Commute x y) (hg : g ∈ spSupported x O) :
    y * g * y⁻¹ ∈ spSupported x O := by
  rw [mem_spSupported] at hg ⊢
  refine ⟨?_, ?_⟩
  · have hxg : Commute x g := hg.1.symm
    have hx : Commute x (y * g * y⁻¹) := (hxy.mul_right hxg).mul_right hxy.inv_right
    exact hx.symm.eq
  · intro k hk hkO v hv
    have hsp : Commute (spEnd y⁻¹) (spEnd x) := by
      show spEnd y⁻¹ * spEnd x = spEnd x * spEnd y⁻¹
      rw [← spEnd_mul, ← spEnd_mul, hxy.inv_right.eq]
    have hv' : spEnd y⁻¹ v ∈ primaryComponent (spEnd x) k :=
      apply_mem_primaryComponent hsp hv
    have h1 : spEnd g (spEnd y⁻¹ v) = spEnd y⁻¹ v := hg.2 k hk hkO _ hv'
    calc spEnd (y * g * y⁻¹) v = spEnd y (spEnd g (spEnd y⁻¹ v)) := by
          simp only [spEnd_mul, Module.End.mul_apply]
      _ = spEnd y (spEnd y⁻¹ v) := by rw [h1]
      _ = v := by
          rw [← Module.End.mul_apply, ← spEnd_mul, mul_inv_cancel, spEnd_one,
            Module.End.one_apply]

private theorem mem_normalizer_spSupported {r : ℕ} {K : Type} [Field K] {x y : StatedSp r K}
    {O : Set K[X]} (hxy : Commute x y) :
    y ∈ Subgroup.normalizer (spSupported x O : Set (StatedSp r K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact conj_mem_spSupported hxy hg
  · intro hg
    have hg' := conj_mem_spSupported hxy.inv_right hg
    simpa [mul_assoc] using hg'

private theorem mem_normalizer_commutator {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer (⁅H, H⁆ : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem sympNorm_holds : SympNorm := by
  intro n m K _ _ hn _hneq hK p hp hp2
  intro x y hx1 hxp _hyp hcomm J hJ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero] at hK
      have h2 : 2 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
      omega
    · exact h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI hchar : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := m)
      (by rw [Fintype.card_eq_nat_card, hK])
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hxp' : orderOf x = p := orderOf_eq_prime hxp hx1
  have ha1 : proj n K x ≠ 1 := fun h => hx1
    ((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
      (r := n) (K := K)).1 (by rw [h, map_one]))
  have ha : orderOf (proj n K x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) ha1
  have hblocks : SpPrimaryBlocks 2 m p x (proj n K x) :=
    (symplectic_cross_prime_primary_centralizer_blocks (ℓ := 2) (f := m) (p := p) (r := n)
      (K := K) Nat.prime_two hm1 hK hp hp2 hp2 hn1 (proj n K x) ha).2 x rfl hxp'
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact hp2 (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp |>.1 h).symm
  have hsq : Squarefree (minpoly K (spEnd x)) := (altPrimaryData_spLin hpK hxp).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcommf, -, hjoin⟩ := hblocks.directProduct
  let A : reciprocalOrbits (spEnd x) → Subgroup (StatedSp n K) :=
    fun O => spSupported x (O : Set K[X])
  have hcommO : ∀ i j : reciprocalOrbits (spEnd x), i ≠ j →
      ∀ a ∈ A i, ∀ b ∈ A j, Commute a b :=
    fun i j hij a ha b hb =>
      hcommf i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  have htame : ∀ i : reciprocalOrbits (spEnd x),
      IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i) :=
    fun O => quasisimple_or_solvable_spSupported hp3 hq hsq hblocks O
  have hPIL : PerfectInLayer (MulAut.conj x) := by
    simpa using perfectInLayer_conj_of_orbit_family (MonoidHom.id (StatedSp n K))
      Function.surjective_id (by simp) x A hcommO hjoin htame
  have hJfix : J ≤ fixSubgroup (MulAut.conj x) := by
    rw [b3Lie_fixSubgroup_conj]
    exact hJ.1
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle : J ≤ GLALayer (fixSubgroup (MulAut.conj x)) := hPIL J hJfix hJperf
  have hJleC : J ≤ GLALayer (Subgroup.centralizer ({x} : Set (StatedSp n K))) := by
    rwa [b3Lie_fixSubgroup_conj] at hJle
  have hJcomp : IsComponentOf J (Subgroup.centralizer ({x} : Set (StatedSp n K))) :=
    (glaPComponent_isComponent_of_le_layer hJ hJleC).1
  have hJcompFix : IsComponentOf J (fixSubgroup (MulAut.conj x)) := by
    rwa [b3Lie_fixSubgroup_conj]
  obtain ⟨O, -, hJeq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
      (MonoidHom.id (StatedSp n K)) Function.surjective_id (by simp) x A hcommO hjoin htame J
      hJcompFix
  rw [Subgroup.map_id] at hJeq
  rw [hJeq]
  exact mem_normalizer_commutator (mem_normalizer_spSupported (O := (O : Set K[X])) hcomm)

end CFSG.LocalAnalysis.GLTheoremA.F151

end
