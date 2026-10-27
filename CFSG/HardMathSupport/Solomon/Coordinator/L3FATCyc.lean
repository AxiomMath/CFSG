module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AExcl

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Solomon.LocalBalance

theorem isCyclic_descend_of_members {Y M C : Type} [Group Y] [Group M]
    [Group C] [IsCyclic C] (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M)
    (hP : GoodPinned P) (fld : C →* MulAut M) (Ab : Subgroup (MulAut Y))
    (hmem : ∀ α ∈ Ab, ∃ d ∈ P.inndiag, ∃ c : C,
      MulAut.congr e (centerDescend Y α) = d * fld c)
    (hker : ∀ α ∈ Ab, MulAut.congr e (centerDescend Y α) ∈ P.inndiag → centerDescend Y α = 1) :
    IsCyclic ↥(Ab.map (centerDescend Y)) := by
  set C₀ : MulAut (Y ⧸ Subgroup.center Y) →* MulAut M := (MulAut.congr e).toMonoidHom with hC₀
  set Φ : MulAut Y →* MulAut M := C₀.comp (centerDescend Y) with hΦ
  set q : MulAut M →* Abelianization (MulAut M) := Abelianization.of with hq
  set R : Subgroup (Abelianization (MulAut M)) := (q.comp fld).range with hR
  have hRcyc : IsCyclic ↥R := isCyclic_of_surjective (q.comp fld).rangeRestrict
    (q.comp fld).rangeRestrict_surjective
  have hmem' : ∀ β ∈ Ab.map Φ, q β ∈ R := by
    rintro _ ⟨α, hα, rfl⟩
    obtain ⟨d, hd, c, hdc⟩ := hmem α hα
    have hqd : q d = 1 := by
      have : d ∈ commutator (MulAut M) := hP.up hd
      rw [← Abelianization.ker_of] at this
      exact this
    refine ⟨c, ?_⟩
    show (q (fld c)) = q (Φ α)
    have : Φ α = d * fld c := hdc
    rw [this, map_mul, hqd, one_mul]
  let g : ↥(Ab.map Φ) →* ↥R := ((q.comp (Ab.map Φ).subtype)).codRestrict R
    (fun β => hmem' β β.2)
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    have h1 : q β = 1 := congrArg Subtype.val hβ
    have h2 : (β : MulAut M) ∈ commutator (MulAut M) := by
      rw [← Abelianization.ker_of]
      exact h1
    have h3' := hP.down h2
    obtain ⟨α, hα, hαβ⟩ := β.2
    have h4 := hker α hα (by
      have : MulAut.congr e (centerDescend Y α) = (β : MulAut M) := hαβ
      rw [this]; exact h3')
    apply Subtype.ext
    rw [← hαβ]
    show C₀ (centerDescend Y α) = 1
    rw [h4, map_one]
  have hcyc : IsCyclic ↥(Ab.map Φ) := isCyclic_of_injective g hginj
  have hCinj : Function.Injective C₀ := (MulAut.congr e).injective
  have e1 := Subgroup.equivMapOfInjective (Ab.map (centerDescend Y)) C₀ hCinj
  have hmapeq : (Ab.map (centerDescend Y)).map C₀ = Ab.map Φ := Subgroup.map_map _ _ _
  rw [hmapeq] at e1
  exact isCyclic_of_injective e1.toMonoidHom e1.injective

@[expose] def mulSubgroup {M : Type*} [Group M] (D : Subgroup M) (hD : D.Normal)
    (Φ : Subgroup M) : Subgroup M where
  carrier := {x | ∃ d ∈ D, ∃ c ∈ Φ, x = d * c}
  mul_mem' := by
    rintro _ _ ⟨d₁, hd₁, c₁, hc₁, rfl⟩ ⟨d₂, hd₂, c₂, hc₂, rfl⟩
    refine ⟨d₁ * (c₁ * d₂ * c₁⁻¹), mul_mem hd₁ (hD.conj_mem d₂ hd₂ c₁),
      c₁ * c₂, mul_mem hc₁ hc₂, by group⟩
  one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
  inv_mem' := by
    rintro _ ⟨d, hd, c, hc, rfl⟩
    exact ⟨c⁻¹ * d⁻¹ * c⁻¹⁻¹, hD.conj_mem d⁻¹ (inv_mem hd) c⁻¹, c⁻¹, inv_mem hc, by group⟩

theorem isCyclic_descend_of_two {Y M C : Type} [Group Y] [Group M] [Group C] [IsCyclic C]
    (e : (Y ⧸ Subgroup.center Y) ≃* M) (P : PinnedAut M) (hP : GoodPinned P) (fld : C →* MulAut M)
    (ε α : MulAut Y) (hε : ∃ c, MulAut.congr e (centerDescend Y ε) = fld c)
    (hα : ∃ d ∈ P.inndiag, ∃ c, MulAut.congr e (centerDescend Y α) = d * fld c)
    (hker : ∀ x ∈ Subgroup.closure ({ε, α} : Set (MulAut Y)),
      MulAut.congr e (centerDescend Y x) ∈ P.inndiag → centerDescend Y x = 1) :
    IsCyclic ↥((Subgroup.closure ({ε, α} : Set (MulAut Y))).map (centerDescend Y)) := by
  set D' := mulSubgroup P.inndiag hP.norm (fld.range) with hD'
  set Φ : MulAut Y →* MulAut M := (MulAut.congr e).toMonoidHom.comp (centerDescend Y) with hΦ
  have hle : Subgroup.closure ({ε, α} : Set (MulAut Y)) ≤ D'.comap Φ := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · obtain ⟨c, hc⟩ := hε
      exact ⟨1, one_mem _, fld c, ⟨c, rfl⟩, by
        show MulAut.congr e (centerDescend Y x) = 1 * fld c
        rw [hc, one_mul]⟩
    · obtain ⟨d, hd, c, hc⟩ := hα
      exact ⟨d, hd, fld c, ⟨c, rfl⟩, hc⟩
  refine isCyclic_descend_of_members e P hP fld _ (fun x hx => ?_) hker
  obtain ⟨d, hd, _, ⟨c, rfl⟩, h⟩ := hle hx
  exact ⟨d, hd, c, h⟩

end CFSG.HardMathSupport.Solomon.Coordinator
