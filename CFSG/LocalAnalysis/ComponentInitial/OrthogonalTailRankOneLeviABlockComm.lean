module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviHom
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise commutatorElement

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

private lemma tailRankOneLeviHom_coe_snd_snd_H08 {i : Fin r} (hi : i.val + 1 < r)
    (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) (g : ↥(tailRankOneParabolic qA a₀ i)) :
    (((tailRankOneLeviHom hi hani ha₀ g).2.2 : LinearMap.GeneralLinearGroup K A) :
        Module.End K A) = tailABlock (g : TailModel K A r) := by
  rw [tailRankOneLeviHom_apply, tailLeviHom_apply]
  exact coe_tailLeviAutHom hi _

theorem tailABlock_tailWeylElt {i : Fin r} (hi : i.val + 1 < r) (a₀ : A) :
    tailABlock (tailWeylElt r qA a₀ i) = 1 := by
  rw [tailWeylElt_eq_prodCongr a₀ hi]
  refine LinearMap.ext fun a => ?_
  rw [tailABlock_apply]
  simp [LinearEquiv.prodCongr_apply]

theorem tailABlock_eq_one_of_mem_tailUnipotent [FiniteDimensional K A] (hani : qA.Anisotropic)
    {g : TailModel K A r} (hg : g ∈ tailUnipotent r qA) : tailABlock g = 1 := by
  obtain ⟨hg', h1⟩ := (mem_tailUnipotent_iff_ker hani).1 hg
  exact congrArg Prod.snd h1

private lemma tailABlock_comm_of_mem_tailBorel_H08 [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    (u v : ↥(tailRankOneParabolic qA a₀ i))
    (hu : (u : TailModel K A r) ∈ tailBorel r qA)
    (hv : (v : TailModel K A r) ∈ tailBorel r qA) :
    Commute (tailRankOneLeviHom hi hani ha₀ u).2.2
      (tailRankOneLeviHom hi hani ha₀ v).2.2 := by
  let τ : ↥(tailRankOneParabolic qA a₀ i) →* LinearMap.GeneralLinearGroup K A :=
    (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (tailRankOneLeviHom hi hani ha₀))
  change Commute (τ u) (τ v)
  have hτ : ∀ g : ↥(tailRankOneParabolic qA a₀ i),
      ((τ g : LinearMap.GeneralLinearGroup K A) : Module.End K A) =
        tailABlock (g : TailModel K A r) := fun g =>
    tailRankOneLeviHom_coe_snd_snd_H08 hi hani ha₀ g
  have hmem : (⁅(u : TailModel K A r), (v : TailModel K A r)⁆ : TailModel K A r) ∈
      tailUnipotent r qA := hcomm _ hu _ hv
  have hcoe : ((⁅u, v⁆ : ↥(tailRankOneParabolic qA a₀ i)) : TailModel K A r) =
      ⁅(u : TailModel K A r), (v : TailModel K A r)⁆ := by
    simpa only [Subgroup.coe_subtype] using
      map_commutatorElement (Subgroup.subtype (tailRankOneParabolic qA a₀ i)) u v
  have hz : τ ⁅u, v⁆ = 1 := by
    apply Units.ext
    rw [hτ ⁅u, v⁆, hcoe, tailABlock_eq_one_of_mem_tailUnipotent hani hmem, Units.val_one]
  exact commutatorElement_eq_one_iff_commute.mp (by
    rw [← map_commutatorElement τ u v, hz])

theorem tailRankOneLeviHom_aut_comm [FiniteDimensional K A] {i : Fin r} (hi : i.val + 1 < r)
    (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0)
    (hcomm : ∀ b₁ ∈ tailBorel r qA, ∀ b₂ ∈ tailBorel r qA, ⁅b₁, b₂⁆ ∈ tailUnipotent r qA)
    (x y : ↥(tailRankOneParabolic qA a₀ i)) :
    (tailRankOneLeviHom hi hani ha₀ x).2.2 * (tailRankOneLeviHom hi hani ha₀ y).2.2 =
      (tailRankOneLeviHom hi hani ha₀ y).2.2 * (tailRankOneLeviHom hi hani ha₀ x).2.2 := by
  let τ : ↥(tailRankOneParabolic qA a₀ i) →* LinearMap.GeneralLinearGroup K A :=
    (MonoidHom.snd _ _).comp ((MonoidHom.snd _ _).comp (tailRankOneLeviHom hi hani ha₀))
  change τ x * τ y = τ y * τ x
  have hτ : ∀ g : ↥(tailRankOneParabolic qA a₀ i),
      ((τ g : LinearMap.GeneralLinearGroup K A) : Module.End K A) =
        tailABlock (g : TailModel K A r) := fun g =>
    tailRankOneLeviHom_coe_snd_snd_H08 hi hani ha₀ g
  let k : Set (TailModel K A r) :=
    (tailBorel r qA : Set (TailModel K A r)) ∪ {tailWeylElt r qA a₀ i}
  let S : Set ↥(tailRankOneParabolic qA a₀ i) := Subtype.val ⁻¹' k
  have hgen : Subgroup.closure S = ⊤ := by
    change Subgroup.closure (Subtype.val ⁻¹' k) = (⊤ : Subgroup ↥(Subgroup.closure k))
    exact Subgroup.closure_closure_coe_preimage
  have hScomm : ∀ u ∈ S, ∀ v ∈ S, Commute (τ u) (τ v) := by
    intro u hu v hv
    have hu' : (u : TailModel K A r) ∈
        (tailBorel r qA : Set (TailModel K A r)) ∪ {tailWeylElt r qA a₀ i} := hu
    have hv' : (v : TailModel K A r) ∈
        (tailBorel r qA : Set (TailModel K A r)) ∪ {tailWeylElt r qA a₀ i} := hv
    rw [Set.mem_union, Set.mem_singleton_iff] at hu' hv'
    rcases hu' with huB | huN
    · rcases hv' with hvB | hvN
      · exact tailABlock_comm_of_mem_tailBorel_H08 hi hani ha₀ hcomm u v huB hvB
      · have hvτ : τ v = 1 := by
          apply Units.ext
          rw [hτ v, hvN, tailABlock_tailWeylElt hi a₀, Units.val_one]
        rw [hvτ]
        exact Commute.one_right (τ u)
    · have huτ : τ u = 1 := by
        apply Units.ext
        rw [hτ u, huN, tailABlock_tailWeylElt hi a₀, Units.val_one]
      rw [huτ]
      exact Commute.one_left (τ v)
  have hpair : (τ '' S).Pairwise Commute := by
    rintro u ⟨u', hu', rfl⟩ v ⟨v', hv', rfl⟩ -
    exact hScomm u' hu' v' hv'
  have hclosure : Subgroup.closure (τ '' S) = τ.range := by
    rw [← MonoidHom.map_closure τ S, hgen, Subgroup.map_top]
  haveI : IsMulCommutative τ.range := hclosure ▸ Subgroup.isMulCommutative_closure hpair
  exact congrArg Subtype.val
    (mul_comm' (⟨τ x, ⟨x, rfl⟩⟩ : τ.range) ⟨τ y, ⟨y, rfl⟩⟩)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
