module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwHSFusionCheck
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwA8Class
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.ComponentClassification.PSL3Four
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.Th.Native

private def tw_fixCard (σ : Equiv.Perm (Fin 3850)) : ℕ :=
  ((Finset.univ : Finset (Fin 3850)).filter fun i => σ i = i).card

private theorem tw_fusFix_eq {t : Tab} {σ : Equiv.Perm (Fin 3850)} (ht : TabRep t σ) :
    fusFix t = tw_fixCard σ := by
  simp only [fusFix, countBelow_eq, tw_fixCard]
  refine Finset.card_bij
    (fun k hk => (⟨k, Finset.mem_range.1 (Finset.mem_filter.1 hk).1⟩ : Fin 3850))
    ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    have h1 : t[k]! = k := by simpa using (Finset.mem_filter.1 hk).2
    have h2 := ht.apply ⟨k, Finset.mem_range.1 (Finset.mem_filter.1 hk).1⟩
    exact h2.symm.trans h1
  · intro k1 _ k2 _ h
    exact congrArg Fin.val h
  · intro i hi
    have hi' : σ i = i := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    refine ⟨i.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨i.isLt, by have h := ht.apply i; rw [hi'] at h; simpa using h⟩
    · apply Fin.ext
      rfl

private theorem tw_fixCard_conj (g σ : Equiv.Perm (Fin 3850)) :
    tw_fixCard (g * σ * g⁻¹) = tw_fixCard σ := by
  simp only [tw_fixCard]
  refine Finset.card_bij (fun i _ => g.symm i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have h := congrArg (g.symm : Fin 3850 → Fin 3850) hi
    simpa [Equiv.Perm.mul_apply] using h
  · intro i _ j _ hij
    exact g.symm.injective hij
  · intro j hj
    have hj' : σ j = j := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
    refine ⟨g j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (g * σ * g⁻¹) (g j) = g j
    simp [Equiv.Perm.mul_apply, hj']

theorem not_conj_outerU_mul_of_equiv
    (eE : ↥outerE ≃* alternatingGroup (Fin 8)) (h : Equiv.Perm (Fin 3850)) :
    h * outerU * h⁻¹ ≠ outerU * ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850)) := by
  classical
  intro hEq
  have hf := fusionCheck_eq
  simp only [fusionCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hf
  obtain ⟨⟨⟨⟨⟨hsize, hperm⟩, hcomp⟩, horbitOK⟩, horbitsz⟩, hfixne⟩ := hf
  have htU : TabRep fusUTab outerU := by
    simpa [fusUTab, outerU] using tabRep_natArr (T := hsCentTbl 21) hsize hperm
  have hx : TabRep (comp 3850 e2Tab e1Tab) (e2 * e1) := tabRep_e2.comp tabRep_e1
  set b0 : Equiv.Perm (Fin 3850) := (e2 * e1) * ((e2 * e1) * (e2 * e1)) with hb0def
  have htB0 : TabRep fusB0Tab b0 := by
    rw [hb0def]
    simp only [fusB0Tab]
    exact hx.comp (hx.comp hx)
  have hb0sq : b0 * b0 = 1 := by
    have h := htB0.comp htB0
    rw [hcomp] at h
    exact h.perm_eq TabRep.idTab
  have he1 : e1 ∈ outerE := Subgroup.subset_closure (by simp)
  have he2 : e2 ∈ outerE := Subgroup.subset_closure (by simp)
  have hb0mem : b0 ∈ outerE := by
    rw [hb0def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ he2 he1)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ he2 he1) (Subgroup.mul_mem _ he2 he1))
  let b0' : ↥outerE := ⟨b0, hb0mem⟩
  have hb0'sq : b0' * b0' = 1 := by
    apply Subtype.ext
    show b0 * b0 = (1 : Equiv.Perm (Fin 3850))
    exact hb0sq
  have hx0 : eE b0' * eE b0' = 1 := by
    rw [← map_mul, hb0'sq, map_one]
  let X : Set (Equiv.Perm (Fin 3850)) := {p | ∃ c ∈ outerE, p = c * b0 * c⁻¹}
  have horbit := conj_orbit (n := 3850) (gens := gensE)
      (A := ({e1, e2} : Set (Equiv.Perm (Fin 3850)))) (ginv := ginvE)
      (E := fusOrbit) (x₀ := b0) (root := fusB0Tab)
      gensE_cover gensE_tabs htB0 horbitOK
  have hcardX : Nat.card X = 210 := by
    have hs : ∀ t ∈ fusOrbit.tabs.toList, ∃ g ∈ X, TabRep t g := by
      intro t ht
      obtain ⟨c, hc, hrep⟩ := horbit.1 t ht
      exact ⟨c * b0 * c⁻¹, ⟨c, hc, rfl⟩, hrep⟩
    have hc' : ∀ g ∈ X, ∃ t ∈ fusOrbit.tabs.toList, TabRep t g := by
      intro g hg
      obtain ⟨c, hc, rfl⟩ := hg
      exact horbit.2.1 c hc
    rw [card_set_of_tabs (n := 3850) (X := X) hs hc' horbit.2.2,
      Array.length_toList, horbitsz]
  have hcardE : Nat.card {y : ↥outerE // IsConj b0' y} = 210 := by
    rw [← hcardX]
    let f : {y : ↥outerE // IsConj b0' y} → {p : Equiv.Perm (Fin 3850) // p ∈ X} :=
      fun y => ⟨(y.1 : Equiv.Perm (Fin 3850)), by
        obtain ⟨c, hcy⟩ := isConj_iff.1 y.2
        refine ⟨(c : Equiv.Perm (Fin 3850)), c.2, ?_⟩
        have hceq : (c : Equiv.Perm (Fin 3850)) * b0 * (c : Equiv.Perm (Fin 3850))⁻¹
            = (y.1 : Equiv.Perm (Fin 3850)) := by
          rw [← hcy]; rfl
        exact hceq.symm⟩
    refine Nat.card_congr (Equiv.ofBijective f ?_)
    constructor
    · intro y1 y2 h
      have hval : (y1.1 : Equiv.Perm (Fin 3850)) = (y2.1 : Equiv.Perm (Fin 3850)) := by
        have hπ := congrArg (fun t : {p : Equiv.Perm (Fin 3850) // p ∈ X} =>
          (t.1 : Equiv.Perm (Fin 3850))) h
        dsimp only [f] at hπ
        exact hπ
      exact Subtype.ext (Subtype.ext hval)
    · rintro ⟨p, hp⟩
      obtain ⟨c, hc, hpc⟩ := hp
      refine ⟨⟨⟨c, hc⟩ * b0' * ⟨c, hc⟩⁻¹, isConj_iff.2 ⟨⟨c, hc⟩, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      show (f ⟨⟨c, hc⟩ * b0' * ⟨c, hc⟩⁻¹, _⟩).1 = p
      dsimp only [f]
      rw [hpc]
      rfl
  have hcardA :
      Nat.card {z : alternatingGroup (Fin 8) // IsConj (eE b0') z} = 210 := by
    rw [← hcardE]
    let f : {y : ↥outerE // IsConj b0' y} →
        {z : alternatingGroup (Fin 8) // IsConj (eE b0') z} :=
      fun y => ⟨eE y.1, (eE : ↥outerE →* alternatingGroup (Fin 8)).map_isConj y.2⟩
    refine Nat.card_congr (Equiv.ofBijective f ?_).symm
    constructor
    · intro y1 y2 h
      apply Subtype.ext
      exact eE.injective (congrArg Subtype.val h)
    · rintro ⟨z, hz⟩
      refine ⟨⟨eE.symm z, ?_⟩, ?_⟩
      · have hz' := ((eE.symm : alternatingGroup (Fin 8) ≃* ↥outerE) :
            alternatingGroup (Fin 8) →* ↥outerE).map_isConj hz
        simpa using hz'
      · apply Subtype.ext
        dsimp only [f]
        simp
  have hconj : IsConj (eE b0') abType22 := isConj_abType22_of_card_eq hx0 hcardA
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let e : ↥outerE := eE.symm c
  have hb'e : e * b0' * e⁻¹ = eE.symm abType22 := by
    apply eE.injective
    simp only [map_mul, map_inv]
    simp [e, hc]
  have hb_perm : (e : Equiv.Perm (Fin 3850)) * b0 * (e : Equiv.Perm (Fin 3850))⁻¹
      = ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850)) := by
    simpa using congrArg Subtype.val hb'e
  have he_comm : (e : Equiv.Perm (Fin 3850)) * outerU
      = outerU * (e : Equiv.Perm (Fin 3850)) := by
    have heC : (e : Equiv.Perm (Fin 3850)) ∈ outerC := outerE_le_outerC e.2
    rw [outerC] at heC
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 heC).2
  have hub : outerU * ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850))
      = e * (outerU * b0) * e⁻¹ := by
    rw [← hb_perm]
    calc outerU * ((e : Equiv.Perm (Fin 3850)) * b0 * (e : Equiv.Perm (Fin 3850))⁻¹)
        = (outerU * (e : Equiv.Perm (Fin 3850))) * b0
            * (e : Equiv.Perm (Fin 3850))⁻¹ := by group
      _ = ((e : Equiv.Perm (Fin 3850)) * outerU) * b0
            * (e : Equiv.Perm (Fin 3850))⁻¹ := by rw [← he_comm]
      _ = (e : Equiv.Perm (Fin 3850)) * (outerU * b0)
            * (e : Equiv.Perm (Fin 3850))⁻¹ := by group
  have htUB0 : TabRep (comp 3850 fusUTab fusB0Tab) (outerU * b0) := htU.comp htB0
  have h1 := tw_fixCard_conj h outerU
  rw [hEq] at h1
  have h2 : tw_fixCard (outerU * ((eE.symm abType22 : ↥outerE) : Equiv.Perm (Fin 3850)))
      = tw_fixCard (outerU * b0) := by
    rw [hub]
    exact tw_fixCard_conj e (outerU * b0)
  have hfixeq : tw_fixCard (outerU * b0) = tw_fixCard outerU := h2.symm.trans h1
  have hfinal : fusFix (comp 3850 fusUTab fusB0Tab) = fusFix fusUTab := by
    rw [tw_fusFix_eq htUB0, tw_fusFix_eq htU]
    exact hfixeq
  exact hfixne hfinal

end CFSG.OddStandard.AltStdSec.SwapPartner
