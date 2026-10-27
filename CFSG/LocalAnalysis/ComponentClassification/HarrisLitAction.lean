module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] (L : Subgroup X)

@[expose] def normalizerConj : ↥(normalizer (L : Set X)) →* MulAut ↥L where
  toFun g :=
    { toFun := fun l => ⟨(g : X) * l * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 l).mp l.2⟩
      invFun := fun l => ⟨(g : X)⁻¹ * l * g, by
        have h := (mem_normalizer_iff.mp (inv_mem g.2) l).mp l.2
        rwa [inv_inv] at h⟩
      left_inv := fun l => Subtype.ext (by simp [mul_assoc])
      right_inv := fun l => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_assoc]

theorem normalizerConj_apply (g : ↥(normalizer (L : Set X))) (l : L) :
    ((normalizerConj L g l : L) : X) = (g : X) * l * (g : X)⁻¹ :=
  rfl

@[expose] def barAut : MulAut ↥L →* MulAut (Bar L) where
  toFun φ := QuotientGroup.congr (pPrimeCore 2 ↥L) (pPrimeCore 2 ↥L) φ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance φ)
  map_one' := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' φ ψ := by
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem barAut_mk (φ : MulAut ↥L) (l : L) :
    barAut L φ (QuotientGroup.mk l : Bar L) = (QuotientGroup.mk (φ l) : Bar L) :=
  rfl

@[expose] def barAction : ↥(normalizer (L : Set X)) →* MulAut (Bar L) :=
  (barAut L).comp (normalizerConj L)

theorem barAction_mk (g : ↥(normalizer (L : Set X))) (l : L) :
    barAction L g (QuotientGroup.mk l : Bar L) =
      (QuotientGroup.mk (normalizerConj L g l) : Bar L) :=
  rfl

theorem barAction_of_mem (l : L) (hl : (l : X) ∈ normalizer (L : Set X)) :
    barAction L ⟨l, hl⟩ = MulAut.conj (QuotientGroup.mk l : Bar L) := by
  ext x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  rw [barAction_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1

theorem mem_ker_barAction (g : ↥(normalizer (L : Set X))) :
    g ∈ (barAction L).ker ↔ (g : X) ∈ coreActionKernel L := by
  rw [← inv_mem_iff (x := g), MonoidHom.mem_ker, mem_coreActionKernel]
  constructor
  · intro h
    refine ⟨g.2, fun j hj => ?_⟩
    have h1 := congrArg (fun φ : MulAut (Bar L) => φ (QuotientGroup.mk ⟨j, hj⟩)) h
    simp only [barAction_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    refine ⟨_, inv_mem h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, normalizerConj_apply,
      inv_inv]
    group
  · rintro ⟨-, h⟩
    ext x
    obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk_surjective x
    rw [barAction_mk, MulAut.one_apply, QuotientGroup.eq]
    obtain ⟨y, hy, hyx⟩ := h j hj
    have hy' : (normalizerConj L g⁻¹ ⟨j, hj⟩)⁻¹ * ⟨j, hj⟩ = y⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_subtype] at hyx
      simp only [Subgroup.coe_inv, Subgroup.coe_mul, normalizerConj_apply, inv_inv, hyx]
      group
    rw [hy']
    exact inv_mem hy

theorem isInducedAut_iff (s : X) (hs : s ∈ normalizer (L : Set X)) (φ : Bar L ≃* Bar L) :
    IsInducedAut L s φ ↔ φ = (barAction L ⟨s, hs⟩)⁻¹ := by
  constructor
  · intro h
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← map_inv, barAction_mk]
    refine h l _ ?_
    rw [normalizerConj_apply]
    simp
  · rintro rfl l l' hl
    rw [← map_inv, barAction_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply, hl]
    simp

end CFSG.ComponentClassification.HarrisLit
