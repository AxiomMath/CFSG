module

public import CFSG.HardMathSupport.Lang.Triality.WeylCert
public import CFSG.HardMathSupport.Lang.Triality.OrbitCounts
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedWeyl

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CoxeterSystem

variable {t : TwistTag}


@[expose] def negRootSet (τ : Tag) (c : Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ 0 < height γ ∧ labelPairing τ γ c < 0}

@[expose] def orbCnt (t : TwistTag) (c : Fin t.tag.rank → ℤ) : ℕ :=
  orbitsIn t (negRootSet t.tag c)

section OrbitList

variable {L : List (Fin t.tag.rank → ℤ)} {lam : Fin t.tag.rank → ℤ}
  (hL : IsOrbitList t.tag Finset.univ ∅ lam L)
include hL

theorem parabolic_univ_mem (u : WeylGroup t.tag) :
    u ∈ (coxeterSystem t.tag).parabolic ((Finset.univ : Finset (Fin t.tag.rank)) :
      Set (Fin t.tag.rank)) := by
  rw [Finset.coe_univ, (coxeterSystem t.tag).parabolic_univ]
  exact Subgroup.mem_top u

theorem isMinimalCosetRep_empty (u : WeylGroup t.tag) :
    (coxeterSystem t.tag).IsMinimalCosetRep ((∅ : Finset (Fin t.tag.rank)) :
      Set (Fin t.tag.rank)) u :=
  (coxeterSystem t.tag).isMinimalCosetRep_iff.2 fun i hi => absurd hi (by simp)

theorem inversionSet_inv_eq (u : WeylGroup t.tag) :
    inversionSet u⁻¹ = negRootSet t.tag (label t.tag (u • lam)) := by
  ext γ
  rw [mem_inversionSet_inv_iff (J := (Finset.univ : Finset (Fin t.tag.rank)))
    (J' := (∅ : Finset (Fin t.tag.rank))) hL.zero hL.pos (parabolic_univ_mem hL u)
    (isMinimalCosetRep_empty hL u) γ]
  simp [negRootSet, pairing_eq_labelPairing]

open Classical in
theorem sum_relWeylTwist_orbitsIn [Fintype (WeylGroup t.tag)] (hlam : permLattice t.perm lam = lam)
    (Q : ℕ) :
    ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), Q ^ orbitsIn t (inversionSet w) =
      ((L.filter fun c => decide (IsPermInvariant t c)).map fun c => Q ^ orbCnt t c).sum := by
  classical
  have h1 : ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), Q ^ orbitsIn t (inversionSet w) =
      ∑ u ∈ Finset.univ.filter (· ∈ relWeylTwist t), Q ^ orbitsIn t (inversionSet u⁻¹) := by
    refine Finset.sum_nbij' (fun w => w⁻¹) (fun u => u⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact inv_mem hw
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact inv_mem hu
    · intro w _
      simp
    · intro u _
      simp
    · intro w _
      simp
  rw [h1, ← List.sum_toFinset _ (hL.nodup.filter _)]
  refine Finset.sum_bij (fun u _ => label t.tag (u • lam)) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine List.mem_toFinset.2 (List.mem_filter.2 ⟨hL.label_smul_mem (parabolic_univ_mem hL u), ?_⟩)
    refine decide_eq_true fun i => ?_
    have h := (mem_relWeylTwist_iff_smul t).1 hu lam
    rw [hlam] at h
    conv_lhs => rw [h]
    exact label_permLattice _ i
  · intro u hu u' hu' h
    exact hL.eq_of_label_eq (parabolic_univ_mem hL u) (isMinimalCosetRep_empty hL u)
      (parabolic_univ_mem hL u') (isMinimalCosetRep_empty hL u') h
  · intro c hc
    obtain ⟨hcL, hcinv⟩ := List.mem_filter.1 (List.mem_toFinset.1 hc)
    obtain ⟨u, hu, hmin, rfl⟩ := hL.exists_eq_label hcL
    have hδ : weylTwist t u = u := by
      refine hL.eq_of_label_eq (parabolic_univ_mem hL _) (isMinimalCosetRep_empty hL _)
        (parabolic_univ_mem hL _) (isMinimalCosetRep_empty hL _) ?_
      conv_lhs => rw [← hlam, weylTwist_smul_permLattice]
      exact label_permLattice_eq (of_decide_eq_true hcinv)
    refine ⟨u, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_relWeylTwist t).2 hδ
  · intro u _
    rw [inversionSet_inv_eq hL u, orbCnt]

end OrbitList

theorem labelPairing_permLattice {τ : Tag} (π : Equiv.Perm (Fin τ.rank))
    (hsym : ∀ i, symDiag τ (π i) = symDiag τ i) {c : Fin τ.rank → ℤ} (hc : ∀ i, c (π i) = c i)
    (γ : Fin τ.rank → ℤ) :
    labelPairing τ (permLattice π γ) c = labelPairing τ γ c := by
  simp only [labelPairing, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp π]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply, hsym, hc]

theorem symDiag_D4_perm (i : Fin TwistTag.D4.tag.rank) :
    symDiag TwistTag.D4.tag (TwistTag.D4.perm i) = symDiag TwistTag.D4.tag i := by
  have h : ∀ j : Fin Tag.D4.rank, symDiag Tag.D4 j = 1 := by decide
  exact (h _).trans (h _).symm

theorem negRootSet_permLattice {c : Fin TwistTag.D4.tag.rank → ℤ}
    (hc : IsPermInvariant TwistTag.D4 c) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ ∈ negRootSet TwistTag.D4.tag c) :
    permLattice TwistTag.D4.perm γ ∈ negRootSet TwistTag.D4.tag c := by
  obtain ⟨hr, hpos, hneg⟩ := hγ
  refine ⟨hr.permLattice TwistTag.D4.cartan_perm, by rwa [height_permLattice], ?_⟩
  rw [labelPairing_permLattice TwistTag.D4.perm symDiag_D4_perm hc]
  exact hneg

theorem orbitsIn_eq_card_image (S : Set (Fin t.tag.rank → ℤ)) (Sfin : Finset (Fin t.tag.rank → ℤ))
    (hmem : ∀ γ, γ ∈ Sfin ↔ γ ∈ S) (hroot : ∀ γ ∈ S, IsRoot t.tag γ)
    (hρ : ∀ γ ∈ S, permLattice t.perm γ ∈ S) :
    orbitsIn t S = (Sfin.image t.diagramOrbit).card := by
  classical
  rw [orbitsIn, ← Set.ncard_coe_finset]
  congr 1
  ext O
  simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
    refine ⟨α, (hmem α).2 (hsub (t.self_mem_diagramOrbit α)), rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨⟨α, hroot α ((hmem α).1 hα), rfl⟩, diagramOrbit_subset hρ ((hmem α).1 hα)⟩

@[expose] def orbCntC (c : Fin TwistTag.D4.tag.rank → ℤ) : ℕ :=
  (((rootList TwistTag.D4.tag).filter fun γ =>
    decide (0 < height γ ∧ labelPairing TwistTag.D4.tag γ c < 0)).toFinset.image
      TwistTag.D4.diagramOrbit).card

theorem orbCnt_eq_orbCntC {c : Fin TwistTag.D4.tag.rank → ℤ}
    (hc : IsPermInvariant TwistTag.D4 c) : orbCnt TwistTag.D4 c = orbCntC c := by
  classical
  refine orbitsIn_eq_card_image _ _ (fun γ => ?_) (fun γ hγ => hγ.1)
    (fun γ hγ => negRootSet_permLattice hc hγ)
  simp [negRootSet, mem_rootList]

open Classical in
theorem sum_orbitsIn_D4 [Fintype (WeylGroup TwistTag.D4.tag)] (Q : ℕ) :
    ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist TwistTag.D4),
        Q ^ orbitsIn TwistTag.D4 (inversionSet w) =
      1 + 2 * Q + 2 * Q ^ 2 + 2 * Q ^ 3 + 2 * Q ^ 4 + 2 * Q ^ 5 + Q ^ 6 := by
  obtain ⟨hL, -⟩ := d4FullCert.isOrbitList (mJ := 15) (mJ' := 0)
    (by simp [maskSet_zero]) d4FullCert_check
  have e15 : maskSet TwistTag.D4.tag 15 = Finset.univ := by decide
  rw [e15, maskSet_zero] at hL
  have hlam : permLattice TwistTag.D4.perm (decodeVec (τ := TwistTag.D4.tag) d4FullCert.lam) =
      decodeVec d4FullCert.lam := by decide +kernel
  rw [sum_relWeylTwist_orbitsIn (t := TwistTag.D4) hL hlam Q]
  have hfilt : ((d4FullCert.pts.map decodeVec).filter fun c =>
      decide (IsPermInvariant TwistTag.D4 c)) =
      ((d4FullCert.pts.map decodeVec).filter fun c => isPermInvB TwistTag.D4 c) :=
    List.filter_congr fun c _ => (isPermInvB_eq_decide c).symm
  have hmap : (((d4FullCert.pts.map decodeVec).filter fun c =>
      decide (IsPermInvariant TwistTag.D4 c)).map fun c => Q ^ orbCnt TwistTag.D4 c) =
      (((d4FullCert.pts.map decodeVec).filter fun c => isPermInvB TwistTag.D4 c).map
        fun c => Q ^ orbCntC c) := by
    rw [hfilt]
    refine List.map_congr_left fun c hc => ?_
    rw [orbCnt_eq_orbCntC]
    have := (List.mem_filter.1 hc).2
    rw [isPermInvB_eq_decide] at this
    exact of_decide_eq_true this
  have key : (((d4FullCert.pts.map decodeVec).filter fun c => isPermInvB TwistTag.D4 c).map
      orbCntC) = [0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6] := by decide +kernel
  have hcomp : ∀ l : List (Fin TwistTag.D4.tag.rank → ℤ),
      l.map (fun c => Q ^ orbCntC c) = (l.map orbCntC).map (fun e => Q ^ e) := fun l => by
    rw [List.map_map]
    rfl
  rw [hmap, hcomp, key]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

end CFSG.HardMathSupport.Lang.Triality
