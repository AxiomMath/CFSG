module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ActionAgrees
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.OuterInvolutions
public import CFSG.Monster.B.Recog.GenericIndexTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz

open Subgroup CFSG.EvenSporadicStandard.HNRecog

variable {C : Type} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.exists_aut_extend (hC : AschbacherHyp C Q)
    (f : ↥(commutator C) ≃* ↥(commutator C)) {x : C} (hx : x ∉ commutator C) (hx2 : x ^ 2 = 1) :
    ∃ (g : ↥(commutator C)) (η : C ≃* C), η x = x ∧
      ∀ l : ↥(commutator C), η (l : C) = (g : C) * (f l : C) * (g : C)⁻¹ := by
  classical
  obtain ⟨t, ht⟩ := hC.exists_isOuterInvolution
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  obtain ⟨k, z₁, hz₁, hk⟩ := hC.exists_conj_of_sq_mem_centerOf ht.1 hx
    (by rw [ht.2.1]; exact one_mem _) (by rw [hx2]; exact one_mem _)
  have hz₁c : ∀ y : C, y * z₁ = z₁ * y :=
    Subgroup.mem_center_iff.mp (hC.centerOf_le_center hz₁)
  obtain ⟨τ, hτL, hτ⟩ :=
    hC.exists_conj_of_isOuterInvolution hC ((MulAut.conjNormal k).trans f) ht
  have hτ' : ∀ l : ↥(commutator C), ((f (MulAut.conjNormal x l) : ↥(commutator C)) : C) =
      τ * (f l : C) * τ⁻¹ := by
    intro l
    obtain ⟨l₀, rfl⟩ := (MulAut.conjNormal k).surjective l
    have h2 : MulAut.conjNormal k (MulAut.conjNormal t l₀) =
        MulAut.conjNormal x (MulAut.conjNormal k l₀) := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      calc k * (t * (l₀ : C) * t⁻¹) * k⁻¹
          = (k * t * k⁻¹) * (k * (l₀ : C) * k⁻¹) * (k * t * k⁻¹)⁻¹ := by group
        _ = (x * z₁) * (k * (l₀ : C) * k⁻¹) * (x * z₁)⁻¹ := by rw [hk]
        _ = x * (z₁ * (k * (l₀ : C) * k⁻¹) * z₁⁻¹) * x⁻¹ := by group
        _ = x * (k * (l₀ : C) * k⁻¹) * x⁻¹ := by rw [← hz₁c (k * (l₀ : C) * k⁻¹)]; group
    simpa [h2] using hτ l₀
  have hτ2 : τ ^ 2 ∈ centerOf Q := by
    refine hC.centralizer_commutator_le ?_
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl⟩ := f.surjective ⟨y, hy⟩
    have h1 := hτ' l
    have h2 := hτ' (MulAut.conjNormal x l)
    have h3 : MulAut.conjNormal x (MulAut.conjNormal x l) = l := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      calc x * (x * (l : C) * x⁻¹) * x⁻¹ = (x * x) * (l : C) * (x * x)⁻¹ := by group
        _ = l := by rw [hxx]; group
    rw [h3, h1] at h2
    have hy' : y = (f l : C) := by rw [hl]
    rw [hy']
    calc (f l : C) * τ ^ 2 = (τ * (τ * (f l : C) * τ⁻¹) * τ⁻¹) * τ ^ 2 := by rw [← h2]
      _ = τ ^ 2 * (f l : C) := by rw [pow_two]; group
  obtain ⟨g₀, z, hz, hg₀⟩ := hC.exists_conj_of_sq_mem_centerOf hτL hx hτ2
    (by rw [hx2]; exact one_mem _)
  have hzc : ∀ y : C, y * z = z * y := Subgroup.mem_center_iff.mp (hC.centerOf_le_center hz)
  obtain ⟨g, hgL, hg⟩ : ∃ g : C, g ∈ commutator C ∧ g * τ * g⁻¹ = x * z := by
    by_cases h : g₀ ∈ commutator C
    · exact ⟨g₀, h, hg₀⟩
    · refine ⟨g₀ * τ, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hC.index_commutator]
        exact iff_of_false h hτL
      · rw [← hg₀]; group
  let gL : ↥(commutator C) := ⟨g, hgL⟩
  let f₂ : ↥(commutator C) ≃* ↥(commutator C) := f.trans (MulAut.conj gL)
  have hf₂ : ∀ l, (f₂ l : C) = g * (f l : C) * g⁻¹ := fun l => rfl
  have hcomm : ∀ l : ↥(commutator C),
      (f₂ (MulAut.conjNormal x l) : C) = x * (f₂ l : C) * x⁻¹ := by
    intro l
    rw [hf₂, hf₂, hτ' l]
    calc g * (τ * (f l : C) * τ⁻¹) * g⁻¹
        = (g * τ * g⁻¹) * (g * (f l : C) * g⁻¹) * (g * τ * g⁻¹)⁻¹ := by group
      _ = (x * z) * (g * (f l : C) * g⁻¹) * (x * z)⁻¹ := by rw [hg]
      _ = x * (z * (g * (f l : C) * g⁻¹) * z⁻¹) * x⁻¹ := by group
      _ = x * (g * (f l : C) * g⁻¹) * x⁻¹ := by rw [← hzc (g * (f l : C) * g⁻¹)]; group
  let ι₁ : ↥(commutator C) →* C := (commutator C).subtype
  let ι₂ : ↥(commutator C) →* C := (commutator C).subtype.comp f₂.toMonoidHom
  have hι₁ : Function.Injective ι₁ := (commutator C).subtype_injective
  have hι₂ : Function.Injective ι₂ := (commutator C).subtype_injective.comp f₂.injective
  have hr₁ : ι₁.range = commutator C := (commutator C).range_subtype
  have hr₂ : ι₂.range = commutator C := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact (f₂ l).2
    · intro hy
      obtain ⟨l, hl⟩ := f₂.surjective ⟨y, hy⟩
      exact ⟨l, by simp [ι₂, hl]⟩
  have h₁ : ι₁.range.index = 2 := by rw [hr₁]; exact hC.index_commutator
  have h₂ : ι₂.range.index = 2 := by rw [hr₂]; exact hC.index_commutator
  have hs₁ : x ∉ ι₁.range := by rw [hr₁]; exact hx
  have hs₂ : x ∉ ι₂.range := by rw [hr₂]; exact hx
  obtain ⟨η, hη, hηx⟩ := CFSG.Monster.B.Recog.exists_mulEquiv_of_index_two_of_eq ι₁ ι₂ hι₁ hι₂
    h₁ h₂ hs₁ hs₂ (fun a => MulAut.conjNormal x a) 1
    (fun a => by simp [ι₁, MulAut.conjNormal_apply])
    (fun a => by simpa [ι₂] using (hcomm a).symm)
    (by simpa [ι₁] using hxx) (by simpa [ι₂] using hxx)
  exact ⟨gL, η, hηx, fun l => (hη l).trans (hf₂ l)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4.EtaGz
