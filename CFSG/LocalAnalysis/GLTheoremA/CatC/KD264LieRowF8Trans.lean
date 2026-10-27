module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Trans

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer

theorem iInf_fixSubgroup_eq_inf {S : Type} [Group S] (b c : MulAut S) :
    (⨅ (f : MulAut S) (_ : f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c), fixSubgroup f) =
      fixSubgroup b ⊓ fixSubgroup c := by
  apply le_antisymm
  · exact le_inf (iInf₂_le b (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)))
      (iInf₂_le c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))
  · have hb : fixSubgroup b ⊓ fixSubgroup c ≤ fixSubgroup b := inf_le_left
    have hc : fixSubgroup b ⊓ fixSubgroup c ≤ fixSubgroup c := inf_le_right
    exact kd264F8_le_fixSubgroup_iInf hb hc

section Congr

variable {S P : Type*} [Group S] [Group P]

theorem congr_apply' (e : S ≃* P) (φ : MulAut S) (x : P) :
    MulAut.congr e φ x = e (φ (e.symm x)) := rfl

theorem mem_fixSubgroup_congr (e : S ≃* P) (φ : MulAut S) (x : P) :
    x ∈ fixSubgroup (MulAut.congr e φ) ↔ e.symm x ∈ fixSubgroup φ := by
  rw [mem_fixSubgroup, mem_fixSubgroup, congr_apply']
  constructor
  · intro h
    have := congrArg e.symm h
    simpa using this
  · intro h
    rw [h]
    simp

theorem congr_conj (e : S ≃* P) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  simp [congr_apply', MulAut.conj_apply]

end Congr

theorem datum_of_equiv {S P : Type} [Group S] [Group P] (e : S ≃* P) (A : Subgroup (MulAut S))
    (h : KD264F8Datum P (A.map (MulAut.congr e : MulAut S →* MulAut P))) : KD264F8Datum S A := by
  obtain ⟨bP, hbP, cP, hcP, hbI, hcI, hc1, H, hHb, hHc, hsub, hq, hdvd⟩ := h
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hbP
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hcP
  have hbI' : b ∉ innAutDerived S := fun h' => hbI ((mem_innAutDerived_congr e).2 h')
  have hcI' : c ∈ innAutDerived S := (mem_innAutDerived_congr e).1 hcI
  have hc1' : c ≠ 1 := fun h' => hc1 (by
    show MulAut.congr e c = 1
    rw [h', map_one])
  have hT : (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c, fixSubgroup f) =
      (⨅ f ∈ Subgroup.zpowers (MulAut.congr e b) ⊔ Subgroup.zpowers (MulAut.congr e c),
        fixSubgroup f).map (e.symm : P →* S) := by
    rw [iInf_fixSubgroup_eq_inf, iInf_fixSubgroup_eq_inf]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨e y, ⟨(mem_fixSubgroup_congr e b _).2 (by simpa using h1),
        (mem_fixSubgroup_congr e c _).2 (by simpa using h2)⟩, by simp⟩
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨(mem_fixSubgroup_congr e b _).1 h1, (mem_fixSubgroup_congr e c _).1 h2⟩
  refine ⟨b, hb, c, hc, hbI', hcI', hc1', H.map (e.symm : P →* S), ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_fixSubgroup_congr e b x).1 (hHb hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_fixSubgroup_congr e c x).1 (hHc hx)
  · rw [hT]
    exact CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hsub
  · exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (H.equivMapOfInjective (e.symm : P →* S) e.symm.injective) hq
  · rw [← card_quotient_center_mulEquiv' e.symm H]
    exact hdvd

theorem hyp_transport {S P : Type} [Group S] [Group P] [Finite S] [Finite P] (e : S ≃* P)
    (A : Subgroup (MulAut S)) (hA : KD264F8Hyp S A) :
    IsElemAbelian 3 (A.map (MulAut.congr e : MulAut S →* MulAut P)) ∧
    (∀ a ∈ A.map (MulAut.congr e : MulAut S →* MulAut P),
      a ∉ (MulAut.conj : P →* MulAut P).range →
      ∀ E : Subgroup P, E ≤ fixSubgroup a → IsElemAbelian 3 E →
        CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 (A.map (MulAut.congr e : MulAut S →* MulAut P))) ∧
    ¬ A.map (MulAut.congr e : MulAut S →* MulAut P) ≤ innAutDerived P := by
  obtain ⟨hAab, -, -, -, hout, hnot⟩ := hA
  refine ⟨isElemAbelian_map_gen _ hAab, ?_, ?_⟩
  · rintro aP haP haPn E hE hEab
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 haP
    have han : a ∉ (MulAut.conj : S →* MulAut S).range := by
      rintro ⟨s, rfl⟩
      exact haPn ⟨e s, (congr_conj e s).symm⟩
    have hfix : E.map (e.symm : P →* S) ≤ fixSubgroup a := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_fixSubgroup_congr e a x).1 (hE hx)
    have h1 := hout a ha han (E.map (e.symm : P →* S)) hfix (isElemAbelian_map_gen _ hEab)
    have h2 := pRank_map_mulEquiv (p := 3) e.symm E
    have h3 := pRank_map_mulEquiv (p := 3) (MulAut.congr e) A
    rw [h2] at h1
    rw [h3]
    exact h1
  · intro hle
    apply hnot
    intro a ha
    exact (mem_innAutDerived_congr e).1 (hle (Subgroup.mem_map_of_mem _ ha))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Trans

end
