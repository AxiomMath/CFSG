module

public import CFSG.CGT.Timmesfeld75.JLemmaCore
public import CFSG.CGT.Timmesfeld75.JLemmaRoot
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.CGT.Timmesfeld75.Sec5NineGen
public import CFSG.CGT.Timmesfeld75.TheoremA1

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Quotient

variable {R : Type} [Group R] [Finite R]

omit [Finite R] in
theorem normal_pGroup_quot_pCore_eq_bot (P : Subgroup (R ⧸ CFSG.pCore 2 R)) (hP : P.Normal)
    (hP2 : IsPGroup 2 P) : P = ⊥ := by
  have hPc : IsPGroup 2 (P.comap (QuotientGroup.mk' (CFSG.pCore 2 R))) := by
    refine hP2.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hPn : (P.comap (QuotientGroup.mk' (CFSG.pCore 2 R))).Normal := hP.comap _
  have hle : P.comap (QuotientGroup.mk' (CFSG.pCore 2 R)) ≤ CFSG.pCore 2 R :=
    le_sSup ⟨hPn, hPc⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff k).2 (hle (Subgroup.mem_comap.2 hx))

theorem exists_not_comm_quot_pCore {T : Subgroup R} (hT : IsWC T)
    (hcl : Subgroup.normalClosure (T : Set R) = ⊤)
    (h4 : 4 ≤ Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 R)))) :
    ∃ a b : R ⧸ CFSG.pCore 2 R, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hT₁ := isWC_map_pCore hT hcl
  have hnorm : (T.map (QuotientGroup.mk' (CFSG.pCore 2 R))).Normal :=
    ⟨fun n _ g => by rwa [show g * n * g⁻¹ = n by rw [hcomm g n, mul_inv_cancel_right]]⟩
  have hbot := normal_pGroup_quot_pCore_eq_bot _ hnorm (isPGroup_two_of_isElemAbelian hT₁.1)
  rw [hbot, Subgroup.card_bot] at h4
  omega

theorem jCore {n : ℕ} (hInd : SimpleCaseUpTo n) (h215 : Lemma215Stmt) {T : Subgroup R}
    (hT : IsWC T) (hcl : Subgroup.normalClosure (T : Set R) = ⊤)
    (hroot : CFSG.Timmesfeld.IsRootInvolutionSet (classD T))
    (h4 : 4 ≤ Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 R))))
    (hn : Nat.card (R ⧸ CFSG.pCore 2 R) < n) :
    IsSimpleGroup (jQuot R) ∧ ListGroup (jQuot R) ∧ Lemma26Hyp (jQuot R) (T.map (jMap R)) ∧
      (∀ x ∈ T.map (jMap R), x ≠ 1 → ∀ y ∈ T.map (jMap R), y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer ((T.map (jMap R) : Subgroup (jQuot R)) : Set (jQuot R)),
          g * x * g⁻¹ = y) ∧
      T ⊓ (jMap R).ker = T ⊓ CFSG.pCore 2 R := by
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
  have hnab : ∃ a b : (R ⧸ O) ⧸ Z, a * b ≠ b * a := by
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
  have hlt : Nat.card ((R ⧸ O) ⧸ Z) < n :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective Z)) hn
  obtain ⟨hlist, htrans⟩ := hInd _ hlt hnab _ hWCb h4b
  have hTmap : T.map (jMap R) = T₁.map (QuotientGroup.mk' Z) := by
    rw [hT₁, jMap, Subgroup.map_map]
  rw [hTmap]
  refine ⟨hsimple, hlist, ⟨hWCb, lt_of_lt_of_le (by norm_num) h4b,
    exists_classD_eq_isConj_of_transitive hbot htrans, ?_, ?_⟩, htrans, ?_⟩
  · rw [← hTmap]
    exact isRootInvolutionSet_classD_map jMap_surjective hroot
  · rw [closure_classD_eq_normalClosure, hKb]
  · have hTZ : T₁ ⊓ Z = ⊥ := inf_center_eq_bot_of_not_comm hT₁wc hcl₁ hnc₁
    refine le_antisymm ?_ fun t ht => ⟨ht.1, pCore_le_ker_jMap ht.2⟩
    rintro t ⟨htT, htk⟩
    refine ⟨htT, ?_⟩
    have hz : QuotientGroup.mk' O t ∈ Z := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 htk)
    have hm : QuotientGroup.mk' O t ∈ T₁ ⊓ Z := ⟨Subgroup.mem_map_of_mem _ htT, hz⟩
    rw [hTZ, Subgroup.mem_bot] at hm
    exact (QuotientGroup.eq_one_iff t).1 hm

end Quotient

end CFSG.CGT.Timmesfeld75
