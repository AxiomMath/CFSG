module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Step3
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


namespace MElt

theorem symmetrizer_le_cθ (τ : Tag) : ∀ j : Fin τ.rank, τ.symmetrizer j j ≤ cθ τ := by
  cases τ <;> decide +kernel

theorem cθ_pos (τ : Tag) : 0 < cθ τ := by
  have h := iform_self_pos_of_isRoot (isRoot_highRoot τ)
  rw [iform_highRoot_apply, CoordAux.highRoot_degree] at h
  omega

variable {τ : Tag} {K : Type} [Field K]

theorem iform_self_le_highRoot {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    iform γ γ ≤ iform (highRoot τ) (highRoot τ) := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj, iform_highRoot_apply, CoordAux.highRoot_degree]
  have := symmetrizer_le_cθ τ j
  omega

theorem neg_two_le_deg {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : -2 ≤ β (iθ τ) := by
  have h := CoordAux.degree_le_two (IsRoot.neg hβ)
  simp only [Pi.neg_apply] at h
  omega

theorem eq_neg_highRoot_of_deg_neg_two {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (h : β (iθ τ) = -2) : β = -highRoot τ := by
  have h2 : -β = highRoot τ :=
    CoordAux.eq_highRoot_of_two_le (IsRoot.neg hβ) (by simp [h])
  exact neg_eq_iff_eq_neg.1 h2

theorem deg_cases {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    β (iθ τ) = 2 ∨ β (iθ τ) = 1 ∨ β (iθ τ) = 0 ∨ β (iθ τ) = -1 ∨ β (iθ τ) = -2 := by
  have h1 := CoordAux.degree_le_two hβ
  have h2 := neg_two_le_deg hβ
  omega

theorem iform_nsmul_add_nsmul (i j : ℕ) (x y : Fin τ.rank → ℤ) :
    iform (i • x + j • y) (i • x + j • y) =
      (i : ℤ) ^ 2 * iform x x + 2 * i * j * iform x y + (j : ℤ) ^ 2 * iform y y := by
  rw [← natCast_zsmul x i, ← natCast_zsmul y j]
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right, iform_comm y x]
  ring

theorem exists_special_data {β : Fin τ.rank → ℤ} (hw : ∃ w : WeylGroup τ, β = w • highRoot τ)
    (hneg : β (iθ τ) = -1) :
    IsRoot τ β ∧ IsLongRoot τ β ∧ ∃ w' : WeylGroup τ, w' • highRoot τ = highRoot τ + β ∧
      (w'⁻¹ • β) ∈ Deg1 τ ∧ (highRoot τ + β) ∈ Deg1 τ := by
  obtain ⟨w, rfl⟩ := hw
  have hθ := isRoot_highRoot τ
  have hβ : IsRoot τ (w • highRoot τ) := IsRoot.smul hθ w
  have hlong : IsLongRoot τ (w • highRoot τ) := isLongRoot_smul_highRoot τ w
  have hc := cθ_ne_zero τ
  have haa : iform (highRoot τ) (highRoot τ) = cθ τ * 2 := by
    rw [iform_highRoot_apply, CoordAux.highRoot_degree]
  have hab : iform (highRoot τ) (w • highRoot τ) = cθ τ * (-1) := by
    rw [iform_highRoot_apply, hneg]
  have hbb : iform (w • highRoot τ) (w • highRoot τ) = cθ τ * 2 := hlong.trans haa
  have hcop : corootPair (highRoot τ) (w • highRoot τ) = -1 := by
    have h := corootPair_mul hθ (w • highRoot τ)
    rw [haa, hab] at h
    refine mul_right_cancel₀ (mul_ne_zero hc two_ne_zero) ?_
    rw [h]
    ring
  have hw' : (rootReflection (highRoot τ) * w) • highRoot τ = highRoot τ + w • highRoot τ := by
    rw [mul_smul, rootReflection_smul hθ, hcop, neg_one_smul, sub_neg_eq_add, add_comm]
  refine ⟨hβ, hlong, rootReflection (highRoot τ) * w, hw', ?_, ?_⟩
  · refine CoordAux.mem_Deg1.2 ⟨IsRoot.smul hβ _, ?_⟩
    have h1 := iform_smul (rootReflection (highRoot τ) * w) (highRoot τ)
      ((rootReflection (highRoot τ) * w)⁻¹ • (w • highRoot τ))
    rw [smul_inv_smul, hw', iform_add_left, hab, hbb, iform_highRoot_apply] at h1
    refine mul_left_cancel₀ hc ?_
    linarith
  · refine CoordAux.mem_Deg1.2 ⟨hw' ▸ IsRoot.smul hθ _, ?_⟩
    simp [CoordAux.highRoot_degree, hneg]

theorem commPairs_special {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hlong : IsLongRoot τ β)
    (hneg : β (iθ τ) = -1) (hsum : IsRoot τ (highRoot τ + β)) :
    commPairs τ (highRoot τ) β = [(1, 1)] := by
  have hc := cθ_pos τ
  have haa : iform (highRoot τ) (highRoot τ) = cθ τ * 2 := by
    rw [iform_highRoot_apply, CoordAux.highRoot_degree]
  have hab : iform (highRoot τ) β = cθ τ * (-1) := by
    rw [iform_highRoot_apply, hneg]
  have hbb : iform β β = cθ τ * 2 := hlong.trans haa
  refine list_eq_singleton_of_forall_eq (a := ((1, 1) : ℕ × ℕ)) (fun p hp => ?_)
    (commPairs_nodup _ _) ?_
  · obtain ⟨hcand, hroot⟩ := mem_commPairs.1 hp
    obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := mem_commCandidates.1 hcand
    have hle := iform_self_le_highRoot hroot
    rw [iform_nsmul_add_nsmul, haa, hab, hbb] at hle
    obtain ⟨a, b⟩ := p
    simp only at h1 h1' h2 h2' hle
    interval_cases a <;> interval_cases b <;>
      first | rfl | (exfalso; push_cast at hle; nlinarith [hc])
  · rw [mem_commPairs]
    exact ⟨by simp [commCandidates], by simpa using hsum⟩

theorem commPairs_deg_zero {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (h0 : β (iθ τ) = 0) :
    commPairs τ (highRoot τ) β = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun p hp => ?_
  obtain ⟨hcand, hroot⟩ := mem_commPairs.1 hp
  obtain ⟨⟨h1, h1'⟩, h2, h2'⟩ := mem_commCandidates.1 hcand
  have hdeg : (p.1 • highRoot τ + p.2 • β) (iθ τ) = 2 * (p.1 : ℤ) := by
    simp [CoordAux.highRoot_degree, h0]
    ring
  have heq := CoordAux.eq_highRoot_of_two_le hroot (by rw [hdeg]; omega)
  have hd2 : 2 * (p.1 : ℤ) = 2 := by rw [← hdeg, heq, CoordAux.highRoot_degree]
  have hp1 : p.1 = 1 := by omega
  rw [hp1, one_smul] at heq
  have hz : p.2 • β = 0 := by simpa using heq
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hβ.ne_zero
  simp only [Pi.zero_apply] at hj
  have := congrFun hz j
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul, nsmul_eq_mul] at this
  rcases mul_eq_zero.1 this with h | h
  · omega
  · exact hj h

theorem commutator_special {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hlong : IsLongRoot τ β)
    (hneg : β (iθ τ) = -1) :
    ∃ C : K, ∀ s t : K, pinnedX τ K (highRoot τ) s * pinnedX τ K β t *
      pinnedX τ K (highRoot τ) (-s) * pinnedX τ K β (-t) =
        pinnedX τ K (highRoot τ + β) (C * s * t) := by
  have hθ := isRoot_highRoot τ
  have hc := cθ_pos τ
  have hne : highRoot τ ≠ β := fun h => by
    have := congrFun h (iθ τ)
    rw [CoordAux.highRoot_degree, hneg] at this
    omega
  have hne' : highRoot τ ≠ -β := fun h => by
    have := congrFun h (iθ τ)
    rw [CoordAux.highRoot_degree] at this
    simp [hneg] at this
  have hab : iform (highRoot τ) β = cθ τ * (-1) := by
    rw [iform_highRoot_apply, hneg]
  have hsum : IsRoot τ (highRoot τ + β) :=
    isRoot_add_of_iform_neg hθ hβ hne' (by rw [hab]; omega)
  obtain ⟨-, -, -, -, hF⟩ := root_commutator_formula.{0} τ hθ hβ hne hne'
  refine ⟨((commConst τ (highRoot τ) β (1, 1) : ℤ) : K), fun s t => ?_⟩
  have h1 := hF K s t
  rw [commPairs_special hβ hlong hneg hsum] at h1
  simpa using h1

theorem conjSub_Uθ_of_mem_Pθ {p : ModGL τ K} (hp : p ∈ Pθ τ K) :
    conjSub p (Uθ τ K) = Uθ τ K :=
  conjSub_eq_of_mem_normalizer (Pθ_le_normalizer_Uθ τ K hp)

theorem conjSub_canonicalRep_rootSubgroup (w : WeylGroup τ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    conjSub (canonicalRep (coxeterSystem τ) K w) (rootSubgroup τ K γ) =
      rootSubgroup τ K (w • γ) :=
  CFSG.RankThree.PartOne.KE.map_conj_rootSubgroup w hγ

theorem exists_ne_zero_ne_one_of_three_le (h3 : 3 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra! h
  haveI : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hsurj : Function.Surjective fun b : Bool => if b then (1 : K) else 0 := by
    intro s
    by_cases hs : s = 0
    · exact ⟨false, by simp [hs]⟩
    · exact ⟨true, by simp [h s hs]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [show Nat.card Bool = 2 by simp] at hle
  omega

theorem commute_Uθ_conjSub_of_deg_zero {p : ModGL τ K} (hp : p ∈ Pθ τ K)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (h0 : β (iθ τ) = 0) :
    ∀ x ∈ Uθ τ K, ∀ y ∈ conjSub p (rootSubgroup τ K β), x * y = y * x := by
  intro x hx y hy
  have hne : highRoot τ ≠ β := fun h => by
    have := congrFun h (iθ τ)
    rw [CoordAux.highRoot_degree, h0] at this
    omega
  have hne' : highRoot τ ≠ -β := fun h => by
    have := congrFun h (iθ τ)
    rw [CoordAux.highRoot_degree] at this
    simp [h0] at this
  have hx' : p⁻¹ * x * p ∈ Uθ τ K :=
    mem_conjSub_iff.1 (by rwa [conjSub_Uθ_of_mem_Pθ hp])
  obtain ⟨s, hs⟩ := mem_rootSubgroup.1 hx'
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 (mem_conjSub_iff.1 hy)
  have hc := (commute_pinnedX_of_commPairs_nil τ K (isRoot_highRoot τ) hβ hne hne'
    (commPairs_deg_zero hβ h0) s t).eq
  rw [hs, ht] at hc
  calc x * y = p * ((p⁻¹ * x * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
    _ = p * ((p⁻¹ * y * p) * (p⁻¹ * x * p)) * p⁻¹ := by rw [hc]
    _ = y * x := by group

theorem exists_M_of_le_Qθ {X₁ X₂ H B : Subgroup (ModGL τ K)} (hco : TwCoords X₁ X₂)
    (hBH : B ≤ H) (hBQ : B ≤ Qθ τ K) (hBX : ¬ B ≤ X₁ ⊔ X₂) :
    ∃ m ∈ H, m ∈ Qθ τ K ∧ heisCoord τ K m ∉ VS (X₁ ⊔ X₂) := by
  obtain ⟨b, hb, hbX⟩ := SetLike.not_le_iff_exists.1 hBX
  exact ⟨b, hBH hb, hBQ hb, fun hS => hbX (hco.inj b (hBQ hb) hS)⟩

theorem exists_mem_Rθ_of_mem_VS {X₁ X₂ : Subgroup (ModGL τ K)} (hb : TwBasic X₁ X₂)
    {u : (Fin τ.rank → ℤ) → K} (hu : u ∈ VS (X₁ ⊔ X₂)) :
    ∃ s ∈ Rθ (X₁ ⊔ X₂), heisCoord τ K s = u := by
  refine exists_of_mem_span_coord (Rθ (X₁ ⊔ X₂)) inf_le_right (fun a ha => ?_) hu
  obtain ⟨t, htS, -, hts⟩ := exists_scalarTorus τ K ha
  have htX₁ : t ∈ X₁ := sup_le hb.Uθ_le hb.Uneg_le htS
  have htX : t ∈ X₁ ⊔ X₂ := Subgroup.mem_sup_left htX₁
  exact ⟨t, fun y hy => ⟨⟨(X₁ ⊔ X₂).mul_mem ((X₁ ⊔ X₂).mul_mem htX hy.1)
    ((X₁ ⊔ X₂).inv_mem htX), (hts y hy.2).1⟩, (hts y hy.2).2⟩⟩

end MElt

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
