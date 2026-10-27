module

public import CFSG.CGT.Timmesfeld75.JLemmaQuot

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {R : Type} [Group R] [Finite R]

theorem lemma26Hyp_jQuot (h215 : Lemma215Stmt) {T : Subgroup R} (hT : IsWC T)
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤)
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet (classD T))
    (h4 : 4 ≤ Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 R))))
    (htrans : ∀ t ∈ T, t ∉ CFSG.pCore 2 R → ∀ t' ∈ T, t' ∉ CFSG.pCore 2 R →
      ∃ z ∈ Subgroup.normalizer (T : Set R), z * t * z⁻¹ = t') :
    IsSimpleGroup (jQuot R) ∧ (∃ x y : jQuot R, x * y ≠ y * x) ∧
      Lemma26Hyp (jQuot R) (T.map (jMap R)) := by
  classical
  set O := CFSG.pCore 2 R with hO
  set T₁ : Subgroup (R ⧸ O) := T.map (QuotientGroup.mk' O) with hT₁
  have hT₁wc : IsWC T₁ := isWC_map_pCore hT hcl
  have hcl₁ : Subgroup.normalClosure (T₁ : Set (R ⧸ O)) = ⊤ := by
    rw [hT₁, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _),
      hcl, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hO2 : ∀ N : Subgroup (R ⧸ O), N.Normal → IsPGroup 2 N → N = ⊥ :=
    normal_pGroup_quot_pCore_eq_bot
  have hnc₁ : ∃ a b : R ⧸ O, a * b ≠ b * a := exists_not_comm_quot_pCore hT hcl h4
  have hZodd := odd_card_center hO2
  set Z : Subgroup (R ⧸ O) := Subgroup.center (R ⧸ O) with hZ
  have hWCb : IsWC (T₁.map (QuotientGroup.mk' Z)) :=
    hT₁wc.map_quotient_central_odd Z le_rfl hZodd
  have hKb : Subgroup.normalClosure
      ((T₁.map (QuotientGroup.mk' Z) : Subgroup ((R ⧸ O) ⧸ Z)) : Set ((R ⧸ O) ⧸ Z)) = ⊤ := by
    rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hcl₁,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have h4b : 4 ≤ Nat.card (T₁.map (QuotientGroup.mk' Z)) :=
    four_le_card_map_central_odd hT₁wc.1 Z hZodd h4
  have hrad := solvable_radical_bot_quotient hT₁wc h4 hcl₁ hO2
  have hsimple : IsSimpleGroup ((R ⧸ O) ⧸ Z) := h215 _ _ hWCb h4b hKb hrad
  have hbot : T₁.map (QuotientGroup.mk' Z) ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h4b
    omega
  have hTmap : T.map (jMap R) = T₁.map (QuotientGroup.mk' Z) := by
    rw [hT₁, jMap, Subgroup.map_map]
  have htransK : ∀ x ∈ T.map (jMap R), x ≠ 1 → ∀ y ∈ T.map (jMap R), y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer ((T.map (jMap R) : Subgroup (jQuot R)) : Set (jQuot R)),
        g * x * g⁻¹ = y := by
    rintro _ ⟨t, ht, rfl⟩ hx _ ⟨t', ht', rfl⟩ hy
    have htO : t ∉ O := fun h => hx (MonoidHom.mem_ker.1 (pCore_le_ker_jMap h))
    have ht'O : t' ∉ O := fun h => hy (MonoidHom.mem_ker.1 (pCore_le_ker_jMap h))
    obtain ⟨z, hz, hzt⟩ := htrans t ht htO t' ht' ht'O
    refine ⟨jMap R z, ?_, ?_⟩
    · rw [mem_normalizer_iff_conjSubgroup_eq, ← map_conjSubgroup,
        mem_normalizer_iff_conjSubgroup_eq.1 hz]
    · rw [← map_mul, ← map_inv, ← map_mul, hzt]
  have hnab : ∃ x y : (R ⧸ O) ⧸ Z, x * y ≠ y * x := by
    by_contra hcomm
    push Not at hcomm
    have hsolv : Group.IsSolvable (⊤ : Subgroup ((R ⧸ O) ⧸ Z)) :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a b)
    have htop := hrad ⊤ inferInstance hsolv
    have hb : T₁.map (QuotientGroup.mk' Z) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      rw [← htop]
      exact Subgroup.mem_top x
    exact hbot hb
  rw [hTmap] at htransK
  rw [hTmap]
  refine ⟨hsimple, hnab, hWCb, lt_of_lt_of_le (by norm_num) h4b,
    exists_classD_eq_isConj_of_transitive hbot htransK, ?_, ?_⟩
  · rw [← hTmap]
    exact isRootInvolutionSet_classD_map jMap_surjective hroot
  · rw [closure_classD_eq_normalClosure, hKb]

end CFSG.CGT.T75M
