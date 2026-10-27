module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrRank

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding
open scoped commutatorElement

theorem false_of_large {Y : Type} [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y)) (hS : ParabStruct Y)
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (R1 : OutPTwoGen Y p) (R2 : AutScalarTorus Y)
    (S₀ : Sylow 2 Y) {J : Subgroup Y} (hJ : Subgroup.normalizer (S₀ : Set Y) ≤ J)
    (hcyc : PerfectCyclicSylow p J) {U Z : Subgroup (MulAut Y)} {y : MulAut Y}
    (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrel : p ^ 3 ≤ Z.relIndex U)
    (hpow : ∀ u ∈ U, u ^ p ∈ Z) (hyU : y ∈ Subgroup.normalizer (U : Set (MulAut Y)))
    (hUJ : U ≤ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyJ : y ∈ Subgroup.normalizer
      ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
    (hyr : ∃ a : ℕ, y ^ r ^ a = 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hrank : NeedsThree U Z :=
    needsThree_of_relIndex (hZ ▸ Subgroup.commutator_le_self U) hZ.ge hpow hrel
  have hr6 : Nat.Coprime r 6 := by
    have hr23 : ¬ r ∣ 6 := by
      intro h
      have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) h
      interval_cases r <;> simp_all (config := {decide := true})
    exact (Nat.Prime.coprime_iff_not_dvd hr).2 hr23
  obtain ⟨a, ha⟩ := hyr
  have hyo : ∃ e : ℕ, 0 < e ∧ Nat.Coprime e 6 ∧ y ^ e ∈ inn Y :=
    ⟨r ^ a, pow_pos hr.pos a, Nat.Coprime.pow_left a hr6, by rw [ha]; exact (inn Y).one_mem⟩
  exact noIrr_aut hp2 hinj hS R1 R2 S₀ hJ hcyc hU hZ hirr hrank hyU hUJ hyJ hyo

end CFSG.AGLEmbedding.ParabAutIrr
