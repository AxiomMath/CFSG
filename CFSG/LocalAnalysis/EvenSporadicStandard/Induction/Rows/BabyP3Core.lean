module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP3Gen
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.InvolutionsN1
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFacts
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21Aut
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.IndexTwo
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22
public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.GSide.HSylowCenter
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentDefs
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide CFSG.Monster.B.CTIB CFSG.EvenSmallLie.TwoE6


theorem bFix_coe_mem_N1_of_mem_NE {n : Eam} (hn : n ∈ NE) : (n : Dfull) ∈ N1 := by
  obtain ⟨y, hy, rfl⟩ := hn
  exact hy

theorem bFix_xhatEam_mem_NE : xhatEam ∈ NE :=
  ⟨cV0 * lamW0H, Subgroup.mul_mem _ cV0_mem_NH lamW0H_mem_NH, vStabEam_cV0_mul_lamW0H⟩

theorem bFix_natCard_NE : Nat.card NE = 2 ^ 22 := by
  have h : Nat.card NE = Nat.card NH := Subgroup.card_map_of_injective vStabEam.injective
  rw [h, natCard_NH]

theorem bFix_NE_le_commutator : NE ≤ commutator Eam := by
  have h := Subgroup.map_mono (f := vStabEam.toMonoidHom) NH_le_commutator
  rw [map_commutator_vStabEam] at h
  exact h

theorem bFix_xhat_pow_val (a : ZMod 2) : xhat ^ a.val = 1 ∨ xhat ^ a.val = xhat := by
  have h := ZMod.val_lt a
  rcases (by omega : a.val = 0 ∨ a.val = 1) with h0 | h1
  · exact Or.inl (by rw [h0, pow_zero])
  · exact Or.inr (by rw [h1, pow_one])

theorem bFix_sq_or_of_mem_NE (n : NE) :
    n * n = 1 ∨ n * n = (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) := by
  have hn := N1_le_Ehat (bFix_coe_mem_N1_of_mem_NE n.2)
  rcases Ehat_sq_mem hn with h | h
  · exact Or.inl (Subtype.ext (Subtype.ext h))
  · exact Or.inr (Subtype.ext (Subtype.ext (h.trans coe_xhatEam.symm)))

theorem bFix_comm_or_of_mem_NE (n m : NE) :
    n * m * n⁻¹ * m⁻¹ = 1 ∨ n * m * n⁻¹ * m⁻¹ = (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) := by
  have hn := N1_le_Ehat (bFix_coe_mem_N1_of_mem_NE n.2)
  have hm := N1_le_Ehat (bFix_coe_mem_N1_of_mem_NE m.2)
  obtain ⟨a, ha⟩ : ∃ a : ZMod 2, ((n : Eam) : Dfull) * ((m : Eam) : Dfull) * ((n : Eam) : Dfull)⁻¹ *
      ((m : Eam) : Dfull)⁻¹ = xhat ^ a.val := ⟨_, Ehat_commutator hn hm⟩
  rcases bFix_xhat_pow_val a with h | h
  · exact Or.inl (Subtype.ext (Subtype.ext (ha.trans h)))
  · exact Or.inr (Subtype.ext (Subtype.ext (ha.trans (h.trans coe_xhatEam.symm))))

theorem bFix_NE_elem {g : Eam} (hg : g ∈ NE) :
    ∃ A : Subgroup Eam, A ≤ NE ∧ (∀ x ∈ A, g * x = x * g) ∧ (∀ x ∈ A, x * x = 1) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ 8 ≤ Nat.card A := by
  have : Finite NE := Nat.finite_of_card_ne_zero (by rw [bFix_natCard_NE]; norm_num)
  have hz : ∀ n : NE,
      n * (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) = ⟨xhatEam, bFix_xhatEam_mem_NE⟩ * n :=
    fun n => by
      have h := xhat_comm_of_mem_Jhat (Ehat_le_Jhat (N1_le_Ehat (bFix_coe_mem_N1_of_mem_NE n.2)))
      refine Subtype.ext (Subtype.ext ?_)
      show ((n : Eam) : Dfull) * ((xhatEam : Eam) : Dfull) =
        ((xhatEam : Eam) : Dfull) * ((n : Eam) : Dfull)
      rw [coe_xhatEam]
      exact h
  have hz2 : (⟨xhatEam, bFix_xhatEam_mem_NE⟩ : NE) * ⟨xhatEam, bFix_xhatEam_mem_NE⟩ = 1 :=
    Subtype.ext (Subtype.ext (by
      show ((xhatEam : Eam) : Dfull) * ((xhatEam : Eam) : Dfull) = 1
      rw [coe_xhatEam]
      exact xhat_mul_self))
  obtain ⟨A, hAc, hAsq, hAcomm, hA8⟩ := exists_elemAbelian_centralizer hz hz2 bFix_sq_or_of_mem_NE
    bFix_comm_or_of_mem_NE (by rw [bFix_natCard_NE]) (⟨g, hg⟩ : NE)
  refine ⟨A.map NE.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact a.2
  · rintro _ ⟨a, ha, rfl⟩
    exact (congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hAc ha))).symm
  · rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hAsq a ha)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hAcomm a ha b hb)
  · rw [Subgroup.card_map_of_injective NE.subtype_injective]
    exact hA8

theorem bFix_inner {g : Eam} (hg : g ∈ commutator Eam) (hg2 : g * g = 1) :
    ∃ A : Subgroup Eam, A ≤ commutator Eam ∧ (∀ x ∈ A, g * x = x * g) ∧ (∀ x ∈ A, x * x = 1) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ 8 ≤ Nat.card A := by
  obtain ⟨h, hh⟩ := involutionsIntoN1 ⟨g, hg⟩ (Subtype.ext hg2)
  obtain ⟨A₀, hA₀N, hA₀g, hA₀sq, hA₀c, hA₀8⟩ := bFix_NE_elem (g := h * g * h⁻¹) hh
  let f : Eam →* Eam := (MulAut.conj h⁻¹).toMonoidHom
  have hf : ∀ a, f a = h⁻¹ * a * h := fun a => by simp [f]
  refine ⟨A₀.map f, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [hf]
    have := (inferInstance : (commutator Eam).Normal).conj_mem a
      (bFix_NE_le_commutator (hA₀N ha)) h⁻¹
    simpa using this
  · rintro _ ⟨a, ha, rfl⟩
    rw [hf]
    calc g * (h⁻¹ * a * h) = h⁻¹ * ((h * g * h⁻¹) * a) * h := by group
      _ = h⁻¹ * (a * (h * g * h⁻¹)) * h := by rw [hA₀g a ha]
      _ = (h⁻¹ * a * h) * g := by group
  · rintro _ ⟨a, ha, rfl⟩
    rw [hf]
    calc h⁻¹ * a * h * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h := by group
      _ = 1 := by rw [hA₀sq a ha]; group
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [hf, hf]
    calc h⁻¹ * a * h * (h⁻¹ * b * h) = h⁻¹ * (a * b) * h := by group
      _ = h⁻¹ * (b * a) * h := by rw [hA₀c a ha b hb]
      _ = h⁻¹ * b * h * (h⁻¹ * a * h) := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hA₀8

theorem bFix_cE'_mul_cE' : cE' * cE' = 1 := by
  rw [← vStabEam_cV0, ← map_mul, cV0_mul_self, map_one]

theorem bFix_mul_cE'_comm : ∀ x : Eam, x * cE' = cE' * x := fun x =>
  Subgroup.mem_center_iff.1 cE'_mem_center x

theorem bFix_isConj_mul_of_central {Y : Type*} [Group Y] {c y w : Y} (hc : ∀ x : Y, x * c = c * x)
    (h : IsConj y w) : IsConj (c * y) (c * w) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨g, ?_⟩
  calc g * (c * y) * g⁻¹ = (g * c) * y * g⁻¹ := by group
    _ = (c * g) * y * g⁻¹ := by rw [hc g]
    _ = c * (g * y * g⁻¹) := by group
    _ = c * w := by rw [hg]

theorem bFix_isConj_of_mulEquiv_isConj {α β : Type*} [Group α] [Group β] (f : α ≃* β) {a b : α}
    (h : IsConj (f a) (f b)) : IsConj a b := by
  have := f.symm.toMonoidHom.map_isConj h
  simpa using this

theorem bFix_not_isConj_of_pair {a : vStab cv0} (hnc : ¬ IsConj a (cStab cv0 * a)) {y : Eam}
    (hc : IsConj (cE' * y) y)
    (h : IsConj y (vStabEam a) ∨ IsConj y (vStabEam (cStab cv0 * a))) : False := by
  have hcE : vStabEam (cStab cv0) = cE' := vStabEam_cV0
  rcases h with h | h
  · have h1 : IsConj (cE' * y) (cE' * vStabEam a) := bFix_isConj_mul_of_central bFix_mul_cE'_comm h
    have h2 : IsConj (cE' * vStabEam a) (vStabEam a) := h1.symm.trans (hc.trans h)
    have h3 : IsConj (vStabEam (cStab cv0 * a)) (vStabEam a) := by
      rw [map_mul, hcE]
      exact h2
    exact hnc (bFix_isConj_of_mulEquiv_isConj vStabEam h3).symm
  · have h1 : IsConj (cE' * y) (cE' * vStabEam (cStab cv0 * a)) :=
      bFix_isConj_mul_of_central bFix_mul_cE'_comm h
    have h2 : IsConj (cE' * vStabEam (cStab cv0 * a)) (vStabEam (cStab cv0 * a)) :=
      h1.symm.trans (hc.trans h)
    have h4 : cE' * vStabEam (cStab cv0 * a) = vStabEam a := by
      rw [map_mul, hcE, ← mul_assoc, bFix_cE'_mul_cE', one_mul]
    rw [h4] at h2
    exact hnc (bFix_isConj_of_mulEquiv_isConj vStabEam h2)

theorem bFix_not_isConj_cE'_mul_of_outer {y : Eam} (hy : y ∉ commutator Eam) (hy2 : y * y = 1) :
    ¬ IsConj (cE' * y) y := by
  intro hc
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨-, -, b, x, -, -, -, -, -, -, -, -, -, -, -, -, hcl1, hcl2, -, -, -, -, -, -, -, -, -, -,
    -, -, hnc1, hnc2, -⟩ := native_H_outer_involution_classes hρ
  rcases isConj_of_outer_involution hρ hcl1 hcl2 hy hy2 with h | h
  · exact bFix_not_isConj_of_pair hnc1 hc h
  · exact bFix_not_isConj_of_pair hnc2 hc h

theorem bFix_outer {g : Eam} (hg : g ∉ commutator Eam) (hg2 : g * g = 1) :
    ∃ A : Subgroup Eam, A ≤ commutator Eam ∧ (∀ x ∈ A, g * x = x * g) ∧ (∀ x ∈ A, x * x = 1) ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ 8 ≤ Nat.card A := by
  have : Finite Eam := Finite.of_equiv _ vStabEam.toEquiv
  obtain ⟨V, hVE, hV4, hVg, hVconj⟩ := exists_fours_group_of_outer_involution hg hg2
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    by_cases h1 : v = 1
    · rw [h1, one_mul]
    · exact bFix_mul_self_eq_one_of_isConj hg2 (mem_centralizer_singleton_iff.1 (hVg hv))
        (hVconj v hv h1)
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have h1 : (v * w) * (v * w) = 1 := hVsq _ (V.mul_mem hv hw)
    have h2 : (v * w)⁻¹ = v * w := inv_eq_of_mul_eq_one_right h1
    have h3 : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hVsq v hv)
    have h4 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hVsq w hw)
    calc v * w = (v * w)⁻¹ := h2.symm
      _ = w * v := by rw [mul_inv_rev, h3, h4]
  have hcV : cE' ∉ V := fun h =>
    bFix_not_isConj_cE'_mul_of_outer hg hg2 (hVconj cE' h cE'_ne_one)
  obtain ⟨A, hVA, hcA, hAcard, hAmem⟩ :=
    bFix_exists_sup_central (V := V) (c := cE') bFix_mul_cE'_comm bFix_cE'_mul_cE' hcV
  have hAsplit : ∀ a ∈ A, ∃ v ∈ V, a = v ∨ a = cE' * v := fun a ha => by
    rcases hAmem a ha with h | h
    · exact ⟨a, h, Or.inl rfl⟩
    · exact ⟨cE' * a, h, Or.inr (by rw [← mul_assoc, bFix_cE'_mul_cE', one_mul])⟩
  have Cc : ∀ y : Eam, Commute cE' y := fun y => (bFix_mul_cE'_comm y).symm
  have Cv : ∀ v ∈ V, ∀ w ∈ V, Commute v w := hVcomm
  have Cg : ∀ v ∈ V, Commute g v := fun v hv => (mem_centralizer_singleton_iff.1 (hVg hv)).symm
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨v, hv, h | h⟩ := hAsplit a ha
    · rw [h]
      exact hVE hv
    · rw [h]
      exact Subgroup.mul_mem _ (CFSG.Monster.B.TwoA.Amalgam.cE'_mem_commutator) (hVE hv)
  · intro a ha
    obtain ⟨v, hv, h | h⟩ := hAsplit a ha
    · rw [h]
      exact (Cg v hv).eq
    · rw [h]
      exact ((Cc g).symm.mul_right (Cg v hv)).eq
  · intro a ha
    obtain ⟨v, hv, h | h⟩ := hAsplit a ha
    · rw [h]
      exact hVsq v hv
    · rw [h]
      calc cE' * v * (cE' * v) = cE' * (v * cE') * v := by group
        _ = cE' * (cE' * v) * v := by rw [bFix_mul_cE'_comm v]
        _ = (cE' * cE') * (v * v) := by group
        _ = 1 := by rw [bFix_cE'_mul_cE', hVsq v hv, one_mul]
  · intro a ha b hb
    obtain ⟨v, hv, h1 | h1⟩ := hAsplit a ha <;> obtain ⟨w, hw, h2 | h2⟩ := hAsplit b hb
    · rw [h1, h2]
      exact (Cv v hv w hw).eq
    · rw [h1, h2]
      exact ((Cc v).symm.mul_right (Cv v hv w hw)).eq
    · rw [h1, h2]
      exact ((Cc w).mul_left (Cv v hv w hw)).eq
    · rw [h1, h2]
      exact ((Cc (cE' * w)).mul_left ((Cc v).symm.mul_right (Cv v hv w hw))).eq
  · rw [hAcard, hV4]

theorem bFix_commutator_Eam (α : MulAut (commutator Eam)) (_ : α ≠ 1) (hα2 : α * α = 1) :
    ∃ E : Subgroup (commutator Eam), (∀ x ∈ E, α x = x) ∧ (∀ x ∈ E, x * x = 1) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ 8 ≤ Nat.card E :=
  fixes_of_aut_conj (commutator Eam) bFix_cE'_mul_cE' centralizer_commutator_Eam mul_self_ne_cE'
    exists_eq_conj_of_mulAut (fun _ hg hg2 => bFix_inner hg hg2)
    (fun _ hg hg2 => bFix_outer hg hg2) α hα2

end CFSG.EvenSporadicStandard.Induction
