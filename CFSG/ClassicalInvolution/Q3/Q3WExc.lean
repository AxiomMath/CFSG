module

public import CFSG.ClassicalInvolution.Q3.Q3WSimply
public import CFSG.ClassicalInvolution.WeakCT.Exceptional

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT

theorem nonempty_ringEquiv_of_card {F G : Type} [Field F] [Finite F] [Field G] [Finite G]
    (h : Nat.card F = Nat.card G) : Nonempty (F ≃+* G) := by
  have := Fintype.ofFinite F
  have := Fintype.ofFinite G
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h])⟩

theorem card_galoisField_three_one : Nat.card (GaloisField 3 1) = 3 := by
  rw [GaloisField.card 3 1 one_ne_zero]
  norm_num

theorem nonempty_ringEquiv_F3 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    Nonempty (F ≃+* F3) :=
  nonempty_ringEquiv_of_card (by rw [hF, Nat.card_zmod])

theorem nonempty_ringEquiv_F3_galoisField : Nonempty (F3 ≃+* GaloisField 3 1) :=
  nonempty_ringEquiv_of_card (by rw [card_galoisField_three_one, Nat.card_zmod])

theorem weakCT3_e6 (hadm : StatedLieAdmissible .E6 0 3 1) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {X : Type} [Group X]
    (U : Fin 6 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 6, edgeE 6 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 3 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E6 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨eF⟩ := nonempty_ringEquiv_F3 hF
  obtain ⟨e⟩ := nonempty_ringEquiv_F3_galoisField
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum (GaloisField 3 1)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E6) (Or.inl rfl)
  have hroot : ∃ c : Fin 6, edgeE 6 ⟨0, by norm_num⟩ c ∨ edgeE 6 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  exact weakCT3_of_chevalleyExtras_of_equiv e
    (Steinberg.Minuscule.e6_chevalleyExtras (GaloisField 3 1) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField 3 1)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e6Data_valid.commC_natAbs (GaloisField 3 1) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e6Datum_steinbergExtras (GaloisField 3 1)).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.Minuscule.e6Datum_isCTGroupDatum (GaloisField 3 1)).sq_mem k
      have e := Steinberg.Minuscule.e6Data_valid.weylElement_xm (GaloisField 3 1) k 1
      rw [e]
      exact h)
    (CurtisTits.curtisTitsConclusion_e6 3 1 hadm) (leviConePresented_e6 _)
    (rootedTree_edgeE (r := 6) (by norm_num)) hroot hgen hcomm
    (fun i j h => (hpair i j h).imp fun W hW => LinearBlockStandardPair.of_ringEquiv eF hW)

theorem weakCT3_e7 (hadm : StatedLieAdmissible .E7 0 3 1) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E7 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Minuscule.e7Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨eF⟩ := nonempty_ringEquiv_F3 hF
  obtain ⟨e⟩ := nonempty_ringEquiv_F3_galoisField
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e7Datum (GaloisField 3 1)).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum (GaloisField 3 1)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))
  have hroot : ∃ c : Fin 7, edgeE 7 ⟨0, by norm_num⟩ c ∨ edgeE 7 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  exact weakCT3_of_chevalleyExtras_of_equiv e
    (Steinberg.Minuscule.e7_chevalleyExtras (GaloisField 3 1) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField 3 1)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e7Data_valid.commC_natAbs (GaloisField 3 1) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e7Datum_steinbergExtras (GaloisField 3 1)).torus_iSupIndep
    (fun (k : Fin 7) => by
      have h := (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField 3 1)).sq_mem k
      have e := Steinberg.Minuscule.e7Data_valid.weylElement_xm (GaloisField 3 1) k 1
      rw [e]
      exact h)
    (CurtisTits.curtisTitsConclusion_e7 3 1 hadm) (leviConePresented_e7 _)
    (rootedTree_edgeE (r := 7) (by norm_num)) hroot hgen hcomm
    (fun i j h => (hpair i j h).imp fun W hW => LinearBlockStandardPair.of_ringEquiv eF hW)

theorem weakCT3_e8 (hadm : StatedLieAdmissible .E8 0 3 1) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 3) {X : Type} [Group X]
    (U : Fin 8 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (adjointGroup .E8 (GaloisField 3 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (adjointGroup .E8 (GaloisField 3 1))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E8 0 3 1 ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.e8Datum (GaloisField 3 1)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨eF⟩ := nonempty_ringEquiv_F3 hF
  obtain ⟨e⟩ := nonempty_ringEquiv_F3_galoisField
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.e8Datum (GaloisField 3 1)).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum (GaloisField 3 1)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E8) (Or.inr (Or.inr rfl))
  have hroot : ∃ c : Fin 8, edgeE 8 ⟨0, by norm_num⟩ c ∨ edgeE 8 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  refine weakCT3_of_chevalleyExtras_of_equiv e
    (Steinberg.Adjoint.e8_chevalleyExtras (GaloisField 3 1) O _
      (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
        Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField 3 1)) O))
    rfl ?_ h1 h2 h3 h4 (Steinberg.Adjoint.e8_steinbergExtras (GaloisField 3 1)).torus_iSupIndep
    (fun (k : Fin 8) => by
      have h := (Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField 3 1)).sq_mem k
      rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .E8) k] at h
      exact h)
    (CurtisTits.curtisTitsConclusion_e8 3 1 hadm) (leviConePresented_e8 _)
    (rootedTree_edgeE (r := 8) (by norm_num)) hroot hgen hcomm
    (fun i j h => (hpair i j h).imp fun W hW => LinearBlockStandardPair.of_ringEquiv eF hW)
  intro α hα β hβ hr hd
  rw [Steinberg.Adjoint.mem_adjDatum_roots] at hα hβ hr hd
  have hne : α + β ≠ 0 := hr.ne_zero
  rw [Steinberg.Adjoint.commC_11 hα hβ hne, Steinberg.Adjoint.RootOperatorFamily'.coeff11,
    Steinberg.Adjoint.RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
      change β = -α at h
      rw [h, add_neg_cancel])) hr]
  exact Steinberg.Adjoint.stringNorm_of_not_isRoot hd

end CFSG.ClassicalInvolution.Q3.Q3W
