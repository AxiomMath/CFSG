module

public import CFSG.RankThree.PartOne.F106.OddRadOrthInner
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryField
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.Universal.Spin CFSG.LocalCores
  CFSG.RankThree.PartOne.F106.OddRadOrth
open scoped commutatorElement

section CentersSpecial

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial

theorem sdo_specialBlock_center_sq_selfDual [CharP K 2] (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp2' : p ≠ 2) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    {g : V ≃ₗ[K] V}
    (hg : g ∈ specialBlock Q x h) (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g)
    (hg2 : g ^ 2 = 1) : g = 1 := by
  classical
  have hp2 : Odd p := hp.odd_of_ne_two hp2'
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hd0 : d ≠ 0 := by
    rintro rfl
    have : 0 < finrank K (AdjoinRoot h) := Module.finrank_pos
    omega
  have hq2 : 2 ≤ ℓ ^ (f * d) := by
    have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
    have h2 : Nat.card K ≤ Nat.card K ^ d := Nat.le_self_pow hd0 _
    have h3 : 1 < Nat.card K := Finite.one_lt_card
    omega
  set γ : BlockGL x h := specialBlockGL Q x h ⟨g, hg⟩ with hγdef
  obtain ⟨c, hc'⟩ := KCUnitary.exists_smul_of_commute_special_unitary hU hBsymm hBl hm hq2
    (γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (fun δ hδ => by
      rw [← hrange] at hδ
      obtain ⟨⟨g', hg'⟩, rfl⟩ := hδ
      have h1 : γ * specialBlockGL Q x h ⟨g', hg'⟩ = specialBlockGL Q x h ⟨g', hg'⟩ * γ := by
        rw [hγdef, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc g' hg')
      exact congrArg (fun u : BlockGL x h =>
        (u : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))) h1)
  have hγ : (γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) =
      c • LinearMap.id := LinearMap.ext hc'
  have hcp : c ^ 2 = 1 := by
    obtain ⟨v, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hγp : γ ^ 2 = 1 := by
      rw [hγdef, ← map_pow]
      have : (⟨g, hg⟩ : ↥(specialBlock Q x h)) ^ 2 = 1 := Subtype.ext hg2
      rw [this, map_one]
    have h1 : ((γ ^ 2 : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) = LinearMap.id := by
      rw [hγp]
      rfl
    have hid : (LinearMap.id : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ^ 2 =
        LinearMap.id := by
      rw [← Module.End.one_eq_id, one_pow]
    rw [Units.val_pow_eq_pow_val, hγ, _root_.smul_pow, hid] at h1
    have h2 := congrArg (fun T => T ⟨v, hv0.1⟩) h1
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h2
    have h3 : (c ^ 2 - 1) • (⟨v, hv0.1⟩ : primaryComponent x.toLinearMap h) = 0 := by
      rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd (congrArg Subtype.val h4) hv0.2
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2b : (2 : AdjoinRoot h) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, h2K, map_zero]
  have hc1 : c = 1 := eq_one_of_sq_eq_one_of_two_eq_zero h2b hcp
  have hγ1 : γ = 1 := Units.ext (by rw [hγ, hc1, one_smul]; rfl)
  have h5 : (⟨g, hg⟩ : ↥(specialBlock Q x h)) = 1 :=
    hx.specialBlockGL_injective hh (by rw [← hγdef, hγ1, map_one])
  exact congrArg Subtype.val h5

end SelfDual

theorem sdo_specialBlock_center_two [CharP K 2] (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) {z : V ≃ₗ[K] V} (hz : z ∈ specialBlock Q x h)
    (hc : ∀ g' ∈ specialBlock Q x h, z * g' = g' * z) (n : ℕ) (hzn : z ^ 2 ^ n = 1) : z = 1 := by
  have key : ∀ w : V ≃ₗ[K] V, w ∈ specialBlock Q x h → (∀ g' ∈ specialBlock Q x h, w * g' = g' * w) →
      w ^ 2 = 1 → w = 1 := by
    intro w hw hwc hw2
    by_cases hself : h = reciprocalPolynomial h
    · exact sdo_specialBlock_center_sq_selfDual hx hp hp2 hh hne1 hself hm hw hwc hw2
    · exact specialBlock_center_sq_paired hx hh hself (by omega) hw hwc hw2
  induction n with
  | zero => simpa using hzn
  | succ n ih =>
    refine ih ?_
    refine key (z ^ 2 ^ n) (Subgroup.pow_mem _ hz _) (fun g' hg' => ?_) ?_
    · exact (Commute.pow_left (show Commute z g' from hc g' hg') _).eq
    · rw [← pow_mul, ← pow_succ]
      exact hzn

end CentersSpecial

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
