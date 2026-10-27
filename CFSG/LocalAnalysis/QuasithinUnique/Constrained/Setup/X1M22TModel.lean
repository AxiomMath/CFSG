module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TMu

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

section Model

variable {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
  (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
  (hEn : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
  (e : CQ L ≃* S22) (hcent : Subgroup.center ↥L = ⊥)

include hW hperf hirr hEel hcent in
theorem actS_injective : Function.Injective (actS hEn e) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn) x = 1 := by
    have : actS hEn e x = 1 := hx
    rw [actS_apply] at this
    exact (MulAut.congr e).injective (by rw [this, map_one])
  have h2 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ E) (normal_sup_of_le_normalizer hEn)
    hperf x).1 h1
  have h3 : (x : MulAut W) ∈ L := centralizer_inf_le hW hirr hEn hEel ⟨x.2, h2⟩
  have h4 : (⟨(x : MulAut W), h3⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 z z.2)
  rw [hcent, Subgroup.mem_bot] at h4
  have h5 : (x : MulAut W) = 1 := Subtype.ext_iff.1 h4
  exact Subtype.ext h5

include hW hperf hirr hEel in
theorem actS_surjective
    (hEL : ¬ E ≤ L) : Function.Surjective (actS hEn e) := by
  intro ψ
  by_cases hψ : ψ ∈ (MulAut.conj : S22 →* MulAut S22).range
  · obtain ⟨s, rfl⟩ := hψ
    exact conj_mem_range_actS hEn e s
  · obtain ⟨b, hbE, hbL⟩ : ∃ b ∈ E, b ∉ L := by
      by_contra h
      push Not at h
      exact hEL h
    set b' : ↥(L ⊔ E) := ⟨b, Subgroup.mem_sup_right hbE⟩ with hb'
    have hbo : actS hEn e b' ∉ (MulAut.conj : S22 →* MulAut S22).range := fun h =>
      hbL (mem_of_actS_inner hW hperf hirr hEn hEel e hbE h)
    obtain ⟨s, hs⟩ := inner_of_outer_mul m22_center_eq_bot' m22_mulAut_card hbo hψ
    obtain ⟨x, hx⟩ := conj_mem_range_actS hEn e s
    refine ⟨b' * x, ?_⟩
    rw [map_mul, hx, hs]
    group

include hW hperf hirr hEel hcent in
theorem exists_model
    (hEL : ¬ E ≤ L) :
    ∃ ι : ↥m22A →* MulAut W, Function.Injective ι ∧ (∀ x ∈ E, ∃ a, ι a = x) ∧
      (∀ a : ↥m22A, ∃ x : ↥(L ⊔ E), (x : MulAut W) = ι a ∧ actS hEn e x = muA a) ∧
      (∀ m : S22, ∃ l : ↥L, (l : MulAut W) = ι ⟨(m : Equiv.Perm (Fin 22)), m22_le_A m.2⟩ ∧
        redHom L e l = m) := by
  have hν : Function.Bijective (actS hEn e) :=
    ⟨actS_injective hW hperf hirr hEn hEel e hcent, actS_surjective hW hperf hirr hEn hEel e hEL⟩
  let ν' := MulEquiv.ofBijective (actS hEn e) hν
  let ι : ↥m22A →* MulAut W :=
    ((L ⊔ E).subtype).comp (ν'.symm.toMonoidHom.comp muA)
  have hι : ∀ a, ι a = (ν'.symm (muA a) : MulAut W) := fun a => rfl
  refine ⟨ι, Subtype.val_injective.comp (ν'.symm.injective.comp muA_injective), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha⟩ := muA_surjective (actS hEn e ⟨x, Subgroup.mem_sup_right hx⟩)
    refine ⟨a, ?_⟩
    rw [hι, ha]
    have : ν'.symm (actS hEn e ⟨x, Subgroup.mem_sup_right hx⟩) = ⟨x, Subgroup.mem_sup_right hx⟩ :=
      ν'.symm_apply_apply _
    rw [this]
  · intro a
    refine ⟨ν'.symm (muA a), rfl.trans (hι a).symm, ?_⟩
    exact ν'.apply_symm_apply (muA a)
  · intro m
    obtain ⟨l, hl⟩ := redHom_surjective L e m
    refine ⟨l, ?_, hl⟩
    have h1 : ν' ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ =
        muA ⟨(m : Equiv.Perm (Fin 22)), m22_le_A m.2⟩ := by
      rw [muA_of_mem, ← hl]
      exact actS_of_mem hEn e l
    rw [hι]
    have : ν'.symm (muA ⟨(m : Equiv.Perm (Fin 22)), m22_le_A m.2⟩) =
        ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩ := by
      rw [← h1]
      exact ν'.symm_apply_apply _
    rw [this]

end Model

end CFSG.QuasithinUnique.Setup.X1
