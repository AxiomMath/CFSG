module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv
  isHatSix_of_mulEquiv pQuotEquiv pSimpleEquiv fixSubgroup_congr)

structure FixedData3 {S : Type} [Group S] (C : Subgroup S) : Prop where
  unique : ∀ I J : Subgroup S, GLAPComponent 3 C I → GLAPComponent 3 C J → I = J
  chev : ∀ I : Subgroup S, GLAPComponent 3 C I → IsChevSimple 3 (PSimple 3 I)
  core : GLAPPrimeCoreOf 3 C = ⊥
  noHatSix : ∀ I : Subgroup S, GLAPComponent 3 C I → ¬ IsHatSix (↥I ⧸ GLAPPrimeCore 3 ↥I)
  noL227 : ∀ I : Subgroup S, GLAPComponent 3 C I → ¬ IsLTwoTwentySeven (PSimple 3 I)

section Transfer

variable {S T : Type} [Group S] [Group T]

theorem FixedData3.coprime_inf_ker (f : S →* T) (hf : Function.Injective f) (A : Subgroup S) :
    Nat.Coprime 3 (Nat.card ↥(A ⊓ f.ker)) := by
  rw [(MonoidHom.ker_eq_bot_iff f).2 hf, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

theorem FixedData3.map_injective [Finite S] (f : S →* T) (hf : Function.Injective f)
    {C : Subgroup S} (h : FixedData3 C) : FixedData3 (C.map f) where
  unique I' J' hI' hJ' := by
    obtain ⟨I, hI, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f
      (FixedData3.coprime_inf_ker f hf C) hI'
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f
      (FixedData3.coprime_inf_ker f hf C) hJ'
    rw [h.unique I J hI hJ]
  chev I' hI' := by
    obtain ⟨I, hI, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f
      (FixedData3.coprime_inf_ker f hf C) hI'
    exact isChevSimple_of_mulEquiv (pSimpleEquiv 3 (I.equivMapOfInjective f hf)) (h.chev I hI)
  core := by
    rw [← map_glaPPrimeCoreOf_of_injective 3 f hf C, h.core, Subgroup.map_bot]
  noHatSix I' hI' hH := by
    obtain ⟨I, hI, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f
      (FixedData3.coprime_inf_ker f hf C) hI'
    exact h.noHatSix I hI
      (isHatSix_of_mulEquiv (pQuotEquiv 3 (I.equivMapOfInjective f hf)).symm hH)
  noL227 I' hI' hL := by
    obtain ⟨I, hI, rfl⟩ := exists_glaPComponent_map_eq Nat.prime_three f
      (FixedData3.coprime_inf_ker f hf C) hI'
    exact h.noL227 I hI
      (isLTwoTwentySeven_of_mulEquiv (pSimpleEquiv 3 (I.equivMapOfInjective f hf)).symm hL)

theorem FixedData3.of_map_injective [Finite S] (f : S →* T) (hf : Function.Injective f)
    {C : Subgroup S} (h : FixedData3 (C.map f)) : FixedData3 C where
  unique I J hI hJ :=
    Subgroup.map_injective hf (h.unique _ _
      (glaPComponent_map Nat.prime_three f (FixedData3.coprime_inf_ker f hf C) hI)
      (glaPComponent_map Nat.prime_three f (FixedData3.coprime_inf_ker f hf C) hJ))
  chev I hI :=
    isChevSimple_of_mulEquiv (pSimpleEquiv 3 (I.equivMapOfInjective f hf)).symm
      (h.chev _ (glaPComponent_map Nat.prime_three f (FixedData3.coprime_inf_ker f hf C) hI))
  core := by
    have h1 := h.core
    rw [← map_glaPPrimeCoreOf_of_injective 3 f hf C] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 h1
  noHatSix I hI hH :=
    h.noHatSix _ (glaPComponent_map Nat.prime_three f (FixedData3.coprime_inf_ker f hf C) hI)
      (isHatSix_of_mulEquiv (pQuotEquiv 3 (I.equivMapOfInjective f hf)) hH)
  noL227 I hI hL :=
    h.noL227 _ (glaPComponent_map Nat.prime_three f (FixedData3.coprime_inf_ker f hf C) hI)
      (isLTwoTwentySeven_of_mulEquiv (pSimpleEquiv 3 (I.equivMapOfInjective f hf)) hL)

theorem FixedData3.of_congr [Finite S] (e : S ≃* T) {β : MulAut S}
    (h : FixedData3 (fixSubgroup (MulAut.congr e β))) : FixedData3 (fixSubgroup β) := by
  rw [fixSubgroup_congr e β] at h
  exact FixedData3.of_map_injective e.toMonoidHom e.injective h

theorem FixedData3.of_conj_aut [Finite S] (ε : MulAut S) {β : MulAut S}
    (h : FixedData3 (fixSubgroup (ε * β * ε⁻¹))) : FixedData3 (fixSubgroup β) := by
  refine FixedData3.of_congr (ε : S ≃* S) (β := β) ?_
  have : MulAut.congr (ε : S ≃* S) β = ε * β * ε⁻¹ := by
    ext x
    rfl
  rw [this]
  exact h

theorem FixedData3.of_inv {β : MulAut S} (h : FixedData3 (fixSubgroup β⁻¹)) :
    FixedData3 (fixSubgroup β) := by
  have hfix : fixSubgroup β⁻¹ = fixSubgroup β := by
    ext x
    show β⁻¹ x = x ↔ β x = x
    constructor
    · intro hx
      calc β x = β (β⁻¹ x) := by rw [hx]
        _ = x := MulAut.apply_inv_self _ β x
    · intro hx
      calc β⁻¹ x = β⁻¹ (β x) := by rw [hx]
        _ = x := MulAut.inv_apply_self _ β x
  rwa [hfix] at h

end Transfer

section Assembly

variable {S : Type} [Group S]

theorem OuterCentData.ofFixedData {β : MulAut S} (h : FixedData3 (fixSubgroup β))
    (cent : ∀ w : MulAut S, Nat.Coprime 3 (orderOf w) → w * β = β * w →
      (∀ x ∈ fixSubgroup β, w x = x) → w ∈ innerAut S) : OuterCentData 3 β where
  unique := h.unique
  chev := h.chev
  core _ := h.core
  cent _ := cent
  noHatSix _ := h.noHatSix
  l227 hp3 I hI hL := absurd hL (h.noL227 I hI)

variable [Finite S] {β : MulAut S} {M : Subgroup S}

theorem FixedData3.ofSimpleNormal (h : SimpleNormalData 3 β M) (hL27 : ¬ IsLTwoTwentySeven ↥M) :
    FixedData3 (fixSubgroup β) where
  unique I J hI hJ := (h.eq_of_glaPComponent hI).trans (h.eq_of_glaPComponent hJ).symm
  chev I hI := by
    rw [h.eq_of_glaPComponent hI]
    exact isChevSimple_of_mulEquiv (h.pSimpleEquivSelf Nat.prime_three).symm h.chev
  core := h.core_eq_bot Nat.prime_three
  noHatSix I hI hH := by
    rw [h.eq_of_glaPComponent hI] at hH
    have h1 := hH.2.1
    rw [h.center_pQuot_eq_bot Nat.prime_three, Subgroup.card_bot] at h1
    exact absurd h1 (by norm_num)
  noL227 I hI hL := by
    rw [h.eq_of_glaPComponent hI] at hL
    exact hL27 (isLTwoTwentySeven_of_mulEquiv (h.pSimpleEquivSelf Nat.prime_three) hL)

theorem FixedData3.ofNoComponent
    (hno : ∀ I : Subgroup S, ¬ GLAPComponent 3 (fixSubgroup β) I)
    (core : GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥) : FixedData3 (fixSubgroup β) where
  unique I _ hI _ := (hno I hI).elim
  chev I hI := (hno I hI).elim
  core := core
  noHatSix I hI := (hno I hI).elim
  noL227 I hI := (hno I hI).elim

end Assembly

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
