module

public import CFSG.LieType.CurtisTits.AmalgamPresentation

public noncomputable section

namespace CFSG.LieType.CurtisTits

open Subgroup

universe u v w
variable {K : Type u} [Group K] {ι : Type v} [Preorder ι] {L : ι → Subgroup K}

theorem isUniversalCompletion_of_isPresentedByAmalgam
    (hP : IsPresentedByAmalgam L) : IsUniversalCompletion.{u,v,w} L := by
  intro G _ φ hφ
  have hrel : ∀ r ∈ amalgamRels L,
      FreeGroup.lift (fun g : Σ i, L i => φ g.1 g.2) r = 1 := by
    rintro r (⟨i, x, y, rfl⟩ | ⟨i, j, hij, x, y, hxy, rfl⟩)
    · simp
    · simp [hφ i j hij x y hxy]
  let lifted := PresentedGroup.toGroup hrel
  let π := PresentedGroup.toGroup (amalgamRels_hold L)
  let e : PresentedGroup (amalgamRels L) ≃* K := MulEquiv.ofBijective π hP
  let ψ := lifted.comp e.symm.toMonoidHom
  have hπgen : ∀ (i : ι) (x : L i), π (PresentedGroup.of ⟨i, x⟩) = x := by
    intro i x
    simp [π, PresentedGroup.toGroup.of, amalgamEval]
  have hinv : ∀ (i : ι) (x : L i), e.symm (x : K) = PresentedGroup.of ⟨i, x⟩ := by
    intro i x
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact (hπgen i x).symm
  have hψ : ∀ (i : ι) (x : L i), ψ x = φ i x := by
    intro i x
    change lifted (e.symm (x : K)) = φ i x
    rw [hinv]
    simp [lifted, PresentedGroup.toGroup.of]
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  have heq : ψ'.comp π = ψ.comp π := by
    apply PresentedGroup.ext
    rintro ⟨i, x⟩
    simp only [MonoidHom.comp_apply, hπgen, hψ', hψ]
  ext x
  obtain ⟨a, rfl⟩ := hP.surjective x
  exact congrArg (fun f : PresentedGroup (amalgamRels L) →* G => f a) heq

theorem isPresentedByAmalgam_of_surjective [Finite K]
    (hgen : ⨆ i, L i = ⊤)
    (back : K →* PresentedGroup (amalgamRels L)) (hback : Function.Surjective back) :
    IsPresentedByAmalgam L := by
  let π := PresentedGroup.toGroup (amalgamRels_hold L)
  have hπgen : ∀ (i : ι) (x : L i), π (PresentedGroup.of ⟨i, x⟩) = x := by
    intro i x
    simp [π, PresentedGroup.toGroup.of, amalgamEval]
  have hπsurj : Function.Surjective π := by
    have hle : (⊤ : Subgroup K) ≤ π.range := by
      rw [← hgen]
      refine iSup_le fun i x hx => ?_
      exact ⟨PresentedGroup.of ⟨i, ⟨x, hx⟩⟩, hπgen i ⟨x, hx⟩⟩
    exact fun y => hle (Subgroup.mem_top y)
  have hcomp : Function.Injective (π.comp back) :=
    Finite.injective_iff_surjective.mpr (hπsurj.comp hback)
  refine ⟨?_, hπsurj⟩
  intro a b hab
  obtain ⟨x, rfl⟩ := hback a
  obtain ⟨y, rfl⟩ := hback b
  exact congrArg back (hcomp hab)

theorem recognition_of_surjective_amalgamPresentation [Finite K]
    (hgen : ⨆ i, L i = ⊤) (hK : IsQuasisimple K)
    (back : K →* PresentedGroup (amalgamRels L)) (hback : Function.Surjective back)
    {G : Type w} [Group G] (φ : ∀ i, L i →* G) (hφ : IsCompatible L φ)
    (hGgen : ⨆ i, (φ i).range = ⊤) (hnt : ∃ i, ∃ x : L i, φ i x ≠ 1) :
    ∃ ψ : K →* G, (∀ i (x : L i), ψ x = φ i x) ∧
      Function.Surjective ψ ∧ ψ.ker ≤ center K := by
  have hP := isPresentedByAmalgam_of_surjective hgen back hback
  have hU : IsUniversalCompletion.{u,v,w} L :=
    isUniversalCompletion_of_isPresentedByAmalgam hP
  obtain ⟨ψ, hψ, hsurj, hker, _⟩ :=
    recognition_of_isUniversalCompletion hgen hK hU φ hφ hGgen hnt
  exact ⟨ψ, hψ, hsurj, hker⟩

end CFSG.LieType.CurtisTits
