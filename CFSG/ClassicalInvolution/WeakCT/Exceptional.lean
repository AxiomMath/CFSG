module

public import CFSG.ClassicalInvolution.WeakCT.SimplyLaced
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.LieType.CurtisTits.Adjoint

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank

section Tree

@[expose] def parentE (r : ℕ) (hr : 4 ≤ r) (k : Fin r) : Fin r :=
  if k.val = 1 then ⟨3, by omega⟩ else if k.val = 2 then ⟨0, by omega⟩ else
    ⟨k.val - 1, by have := k.2; omega⟩

@[expose] def depthE (r : ℕ) (k : Fin r) : ℕ :=
  if k.val = 1 then 3 else if k.val = 2 then 1 else if k.val = 0 then 0 else k.val - 1

theorem val_parentE {r : ℕ} (hr : 4 ≤ r) (k : Fin r) :
    (parentE r hr k).val = if k.val = 1 then 3 else if k.val = 2 then 0 else k.val - 1 := by
  unfold parentE
  split_ifs <;> rfl

theorem rootedTree_edgeE {r : ℕ} (hr : 4 ≤ r) :
    RootedTree (edgeE r) (parentE r hr) (depthE r) ⟨0, by omega⟩ := by
  have hk0 : ∀ k : Fin r, k ≠ ⟨0, by omega⟩ → k.val ≠ 0 := fun k hk h => hk (Fin.ext h)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun i j hij hji => ?_, fun i j hij => ?_⟩
  · have h1 := hk0 k hk
    have h3 := val_parentE hr k
    unfold depthE
    split_ifs at h3 ⊢ <;> omega
  · have h1 := hk0 k hk
    have h3 := val_parentE hr k
    unfold edgeE
    split_ifs at h3 <;> omega
  · unfold edgeE at hij hji
    omega
  · unfold edgeE at hij
    have hi := val_parentE hr i
    have hj := val_parentE hr j
    have hne : ∀ k : Fin r, k.val ≠ 0 → k ≠ ⟨0, by omega⟩ := fun k hk h => hk (by rw [h])
    rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨hne j (by omega), Fin.ext ?_⟩
      split_ifs at hj <;> omega
    · right
      refine ⟨hne i (by omega), Fin.ext ?_⟩
      simp only [h1, ↓reduceIte] at hi
      omega
    · left
      refine ⟨hne j (by omega), Fin.ext ?_⟩
      split_ifs at hj <;> omega

@[expose] def cartanEntry (τ : Tag) (i j : Fin τ.rank) : ℤ := τ.cartan i j

theorem edgeE_orientation {τ : Tag} (h : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (∀ i j : Fin τ.rank, edgeE τ.rank i j → ¬ edgeE τ.rank j i) ∧
    (∀ i j : Fin τ.rank, edgeE τ.rank i j → cartanEntry τ i j = -1 ∧ cartanEntry τ j i = -1) ∧
    (∀ i j : Fin τ.rank, i ≠ j → ¬ edgeE τ.rank i j → ¬ edgeE τ.rank j i →
      cartanEntry τ i j = 0 ∧ cartanEntry τ j i = 0) ∧
    (∀ i j : Fin τ.rank, edgeE τ.rank i j → ∃ k, k ≠ i ∧ k ≠ j ∧
      ((edgeE τ.rank j k ∨ edgeE τ.rank k j) ∧ ¬ edgeE τ.rank i k ∧ ¬ edgeE τ.rank k i ∨
        (edgeE τ.rank i k ∨ edgeE τ.rank k i) ∧ ¬ edgeE τ.rank j k ∧ ¬ edgeE τ.rank k j)) := by
  rcases h with rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Tree

section Recognition

variable (p f : ℕ) [Fact p.Prime]

theorem weakCT_e6 (hadm : StatedLieAdmissible .E6 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {X : Type} [Group X]
    (U : Fin 6 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 6, edgeE 6 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E6 0 p f ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Minuscule.e6Datum (GaloisField p f)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e6Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e6Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E6) (Or.inl rfl)
  have hroot : ∃ c : Fin 6, edgeE 6 ⟨0, by norm_num⟩ c ∨ edgeE 6 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  exact weakCT_of_chevalleyExtras_of_equiv e
    (Steinberg.Minuscule.e6_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e6Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E6 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E6) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e6Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e6Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.Minuscule.e6Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e6Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
    (CurtisTits.curtisTitsConclusion_e6 p f hadm) (leviConePresented_e6 _) hq
    (rootedTree_edgeE (r := 6) (by norm_num)) hroot hgen hcomm hpair

theorem weakCT_e7 (hadm : StatedLieAdmissible .E7 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E7 0 p f ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Minuscule.e7Datum (GaloisField p f)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e7Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))
  have hroot : ∃ c : Fin 7, edgeE 7 ⟨0, by norm_num⟩ c ∨ edgeE 7 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  exact weakCT_of_chevalleyExtras_of_equiv e
    (Steinberg.Minuscule.e7_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField p f)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e7Data_valid.commC_natAbs (GaloisField p f) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e7Datum_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 7) => by
      have h := (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField p f)).sq_mem k
      have e := Steinberg.Minuscule.e7Data_valid.weylElement_xm (GaloisField p f) k 1
      rw [e]
      exact h)
    (CurtisTits.curtisTitsConclusion_e7 p f hadm) (leviConePresented_e7 _) hq
    (rootedTree_edgeE (r := 7) (by norm_num)) hroot hgen hcomm hpair

theorem weakCT_e8 (hadm : StatedLieAdmissible .E8 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {X : Type} [Group X]
    (U : Fin 8 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : (adjointGroup .E8 (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (adjointGroup .E8 (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E8 0 p f ∧
      ∀ k, (CurtisTits.rankOne (Steinberg.Adjoint.e8Datum (GaloisField p f)).rootGroup k).map Ψ =
        U k := by
  obtain ⟨e⟩ : Nonempty (F ≃+* GaloisField p f) := by
    have := Fintype.ofFinite F
    have := Fintype.ofFinite (GaloisField p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        GaloisField.card p f (by have := hadm.2.1; omega)])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Adjoint.e8Datum (GaloisField p f)).isFiniteType
    (Dv := (Steinberg.Adjoint.e8Datum (GaloisField p f)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E8) (Or.inr (Or.inr rfl))
  have hroot : ∃ c : Fin 8, edgeE 8 ⟨0, by norm_num⟩ c ∨ edgeE 8 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  refine weakCT_of_chevalleyExtras_of_equiv e
    (Steinberg.Adjoint.e8_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
        Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField p f)) O))
    rfl ?_ h1 h2 h3 h4 (Steinberg.Adjoint.e8_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 8) => by
      have h := (Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField p f)).sq_mem k
      rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .E8) k] at h
      exact h)
    (CurtisTits.curtisTitsConclusion_e8 p f hadm) (leviConePresented_e8 _) hq
    (rootedTree_edgeE (r := 8) (by norm_num)) hroot hgen hcomm hpair
  intro α hα β hβ hr hd
  rw [Steinberg.Adjoint.mem_adjDatum_roots] at hα hβ hr hd
  have hne : α + β ≠ 0 := hr.ne_zero
  rw [Steinberg.Adjoint.commC_11 hα hβ hne, Steinberg.Adjoint.RootOperatorFamily'.coeff11,
    Steinberg.Adjoint.RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
      change β = -α at h
      rw [h, add_neg_cancel])) hr]
  exact Steinberg.Adjoint.stringNorm_of_not_isRoot hd

end Recognition

end CFSG.ClassicalInvolution.WeakCT
