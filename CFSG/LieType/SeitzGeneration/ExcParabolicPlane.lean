module

public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.ExcParabolicNormalize
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section Radical


theorem parabolicRadical_le_adjointGroup (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ≤ adjointGroup τ K :=
  (parabolicRadical_le_posUnipotent J).trans
    ((posUnipotent_le_parabolicSubgroup J).trans (parabolicSubgroup_le_adjointGroup τ K J))

end Radical

section Plane

variable [Finite K]

theorem exists_normalized_of_not_dvd_relIndex {C : Type*} [Group C]
    (e : C ≃* ↥(adjointGroup τ K)) {r p : ℕ} [Fact p.Prime] (hr : ∃ n, Nat.card K = r ^ n)
    {J : Set (Fin τ.rank)} (hJ : J ≠ Set.univ)
    (hidx : ¬ p ∣ (parabolicSubgroup τ K J).relIndex (adjointGroup τ K))
    {E : Subgroup (MulAut C)} (hEp : IsPGroup p E)
    (hE : E ≤ (MulAut.conj : C →* MulAut C).range) :
    ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r R ∧ ∀ ε ∈ E, R.map ε.toMonoidHom = R := by
  have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  have hZ : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot (τ := τ) (K := K)
  have hinj := conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot hZ)
  have hQA := parabolicRadical_le_adjointGroup (τ := τ) (K := K) J
  refine exists_normalized_of_inner e
    (P := (parabolicSubgroup τ K J).subgroupOf (adjointGroup τ K))
    (Q := (parabolicRadical τ K J).subgroupOf (adjointGroup τ K)) hidx ?_ ?_ ?_ hinj hEp hE
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hxP : (x : ModGL τ K) ∈ parabolicSubgroup τ K J := hx
    have h := Subgroup.mem_normalizer_iff.1
      (parabolicSubgroup_le_normalizer_parabolicRadical J hxP) (z : ModGL τ K)
    exact h
  · intro h
    refine parabolicRadical_ne_bot (τ := τ) (K := K) hJ ?_
    rw [eq_bot_iff]
    intro y hy
    have hy' : (⟨y, hQA hy⟩ : ↥(adjointGroup τ K)) ∈
        (parabolicRadical τ K J).subgroupOf (adjointGroup τ K) := hy
    rw [h, Subgroup.mem_bot] at hy'
    simpa using congrArg Subtype.val hy'
  · obtain ⟨n, hn⟩ := hr
    have hrad : IsPGroup r (parabolicRadical τ K J) :=
      IsPGroup.of_card (n := n * (parabolicRadicalRoots τ J).ncard) (by
        rw [card_parabolicRadical, hn, ← pow_mul])
    exact hrad.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm

end Plane

end CFSG.LieType.SeitzGeneration
