module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogD
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Transport

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}

theorem weakCT_of_frame_of_equiv {F₀ : Type} [Field F₀] (e : F₀ ≃+* F) {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) (k₀ : Fin D.rank) {X : Type} [Group X]
    {U : Fin D.rank → Subgroup X} (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin D.rank → SL(2, F₀) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j, adj i j → ∃ ψ : SL(3, F₀) →* X,
      ψ.comp (blk F₀ 0) = ρ i ∧ ψ.comp (blk F₀ 1) = ρ j) :
    ∃ Ψ : K →* X, Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center K).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) t n p f ∧
      ∀ k, (CurtisTits.rankOne D.rootGroup k).map Ψ = U k := by
  let φ₂ : SL(2, F) →* SL(2, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  let φ₃ : SL(3, F) →* SL(3, F₀) := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  have hφ₂inj : Function.Injective φ₂ := fun A B h => by
    have := congrArg (Matrix.SpecialLinearGroup.map e.toRingHom) h
    rwa [map_symm_map, map_symm_map] at this
  have hφ₂surj : ∀ A : SL(2, F₀), ∃ B : SL(2, F), φ₂ B = A := fun A =>
    ⟨Matrix.SpecialLinearGroup.map e.toRingHom A, map_map_symm e A⟩
  refine weakCT_of_frame hCT hL hD k₀ hgen hcomm (ρ := fun k => (ρ k).comp φ₂)
    (fun k => ⟨(hρ k).1.comp hφ₂inj, ?_⟩) (fun i j hij => ?_)
  · rw [← (hρ k).2]
    ext y
    constructor
    · rintro ⟨B, rfl⟩
      exact ⟨φ₂ B, rfl⟩
    · rintro ⟨A, rfl⟩
      obtain ⟨B, rfl⟩ := hφ₂surj A
      exact ⟨B, rfl⟩
  · obtain ⟨ψ, hψ0, hψ1⟩ := hψ i j hij
    refine ⟨ψ.comp φ₃, ?_, ?_⟩
    · ext A
      show ψ (φ₃ (blk F 0 A)) = ρ i (φ₂ A)
      rw [← hψ0, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 0 A)
    · ext A
      show ψ (φ₃ (blk F 1 A)) = ρ j (φ₂ A)
      rw [← hψ1, MonoidHom.comp_apply]
      exact congrArg ψ (map_blk e.symm.toRingHom 1 A)

end Transport

section Exceptional

variable (p f : ℕ) [Fact p.Prime]


theorem weakCT_e6_of_frame (hadm : StatedLieAdmissible .E6 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (U : Fin 6 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin 6 → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 6, edgeE 6 i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E6 0 p f := by
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
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
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
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, -⟩ := weakCT_of_frame_of_equiv e
    (CurtisTits.curtisTitsConclusion_e6 p f hadm) (leviConePresented_e6 _) hD
    (⟨0, by norm_num⟩ : Fin 6) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel⟩

theorem weakCT_e7_of_frame (hadm : StatedLieAdmissible .E7 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (U : Fin 7 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin 7 → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 7, edgeE 7 i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E7 0 p f := by
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
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
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
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, -⟩ := weakCT_of_frame_of_equiv e
    (CurtisTits.curtisTitsConclusion_e7 p f hadm) (leviConePresented_e7 _) hD
    (⟨0, by norm_num⟩ : Fin 7) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel⟩

theorem weakCT_e8_of_frame (hadm : StatedLieAdmissible .E8 0 p f) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {X : Type} [Group X] (U : Fin 8 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    {ρ : Fin 8 → SL(2, F) →* X} (hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k)
    (hψ : ∀ i j : Fin 8, edgeE 8 i j → ∃ ψ : SL(3, F) →* X,
      ψ.comp (blk F 0) = ρ i ∧ ψ.comp (blk F 1) = ρ j) :
    ∃ Ψ : (adjointGroup .E8 (GaloisField p f)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple X ∧
      Subgroup.center X = (Subgroup.center (adjointGroup .E8 (GaloisField p f))).map Ψ ∧
      LieModel (X ⧸ Subgroup.center X) .E8 0 p f := by
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
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Adjoint.e8_chevalleyExtras (GaloisField p f) O _
      (Steinberg.Adjoint.commutatorFormula_commC Steinberg.Adjoint.e8Data_valid
        Steinberg.Adjoint.noG2_E8 _ (Steinberg.Adjoint.adjDatum_roots _ (GaloisField p f)) O))
    rfl (fun α hα β hβ hr hd => by
      rw [Steinberg.Adjoint.mem_adjDatum_roots] at hα hβ hr hd
      have hne : α + β ≠ 0 := hr.ne_zero
      rw [Steinberg.Adjoint.commC_11 hα hβ hne, Steinberg.Adjoint.RootOperatorFamily'.coeff11,
        Steinberg.Adjoint.RootOperatorFamily'.bracketCoeff_natAbs _ _ (fun h => hne (by
          change β = -α at h
          rw [h, add_neg_cancel])) hr]
      exact Steinberg.Adjoint.stringNorm_of_not_isRoot hd) h1 h2 h3 h4
    (Steinberg.Adjoint.e8_steinbergExtras (GaloisField p f)).torus_iSupIndep
    (fun (k : Fin 8) => by
      have h := (Steinberg.Adjoint.e8_isCTGroupDatum (GaloisField p f)).sq_mem k
      rw [Steinberg.Adjoint.weylElement_eq_xPar (Chevalley.rootOperatorFamily .E8) k] at h
      exact h)
  obtain ⟨Ψ, hsurj, hker, hqs, hcent, hmodel, -⟩ := weakCT_of_frame_of_equiv e
    (CurtisTits.curtisTitsConclusion_e8 p f hadm) (leviConePresented_e8 _) hD
    (⟨0, by norm_num⟩ : Fin 8) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hqs, hcent, hmodel⟩

end Exceptional


section Recog

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.Yardstones.Md0ec50421ce4 TauCeti
  CFSG.ComponentClassification.CatLeaf


theorem lieModel_e6_chev {G : Type} [Group G] {p f : ℕ} (h : LieModel G .E6 0 p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h (by simp [lieSylowExponent]; omega)⟩
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨p, f, hp, hf⟩
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q (LieTypeIndex.valid_E6 q) K
      (by rw [hK, PrimePower.card_def])
    exact isChevSimple_of_lie ⟨.E6 q, LieTypeIndex.valid_E6 q⟩
      (LieTypeIndex.characteristic_E6 q) (e.trans b)
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem lieModel_e7_chev {G : Type} [Group G] {p f : ℕ} (h : LieModel G .E7 0 p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h (by simp [lieSylowExponent]; omega)⟩
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨p, f, hp, hf⟩
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q (LieTypeIndex.valid_E7 q) K
      (by rw [hK, PrimePower.card_def])
    exact isChevSimple_of_lie ⟨.E7 q, LieTypeIndex.valid_E7 q⟩
      (LieTypeIndex.characteristic_E7 q) (e.trans b)
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem innerRecog_E6 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 6 → ι)
    (hgram : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 6, edgeE 6 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecog p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 6) hgram hframe
  have hadm : StatedLieAdmissible .E6 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel⟩ := weakCT_e6_of_frame p f hadm hK U hgen hcomm hρ hψ
  obtain ⟨hchev, hA6⟩ := lieModel_e6_chev hmodel
  refine ⟨_, inferInstance, ⟨hqs.1.commutator_eq_top, hchev, fun ⟨e⟩ => (hA6.false e).elim⟩,
    ⟨fun e => hA6.false e⟩, MonoidHom.id _, Function.surjective_id, ?_⟩
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem innerRecog_E7 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 7 → ι)
    (hgram : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 7, edgeE 7 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecog p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 7) hgram hframe
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel⟩ := weakCT_e7_of_frame p f hadm hK U hgen hcomm hρ hψ
  obtain ⟨hchev, hA6⟩ := lieModel_e7_chev hmodel
  refine ⟨_, inferInstance, ⟨hqs.1.commutator_eq_top, hchev, fun ⟨e⟩ => (hA6.false e).elim⟩,
    ⟨fun e => hA6.false e⟩, MonoidHom.id _, Function.surjective_id, ?_⟩
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem lieModel_e8_chev {G : Type} [Group G] {p f : ℕ} (h : LieModel G .E8 0 p f) :
    IsChevSimple p G ∧ IsEmpty (G ≃* alternatingGroup (Fin 6)) := by
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  refine ⟨?_, isEmpty_alt6_of_lieModel_gen h (by simp [lieSylowExponent]; omega)⟩
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
    let q : PrimePower := ⟨p, f, hp, hf⟩
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv K
      (by rw [hK, PrimePower.card_def])
    exact isChevSimple_of_lie ⟨.E8 q, hv⟩
      (LieTypeIndex.characteristic_E8 q) (e.trans b)
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

theorem innerRecog_E8 {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = p ^ f)
    {ι : Type} [Fintype ι] (β : ι → Fin τ.rank → ℤ) (hroot : ∀ b, IsRoot τ (β b))
    (l : Fin 8 → ι)
    (hgram : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      iform (β (l i)) (β (l j)) = 0)
    (hframe : ∀ i j : Fin 8, edgeE 8 i j → ∃ θ : SL(3, K) →* ModGL τ K,
      θ.comp (blockSL K 3 2 0 (by omega)) = rootSL2 τ K (β (l i)) ∧
        θ.comp (blockSL K 3 2 1 (by omega)) = rootSL2 τ K (β (l j))) :
    InnerRecog p ↥(rootSpan τ K (rootsOfFam β (Set.range l))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, ρ, hgen, hcomm, hρ, hψ⟩ := weakCT_data hτ β hroot l (edgeE 8) hgram hframe
  have hadm : StatedLieAdmissible .E8 0 p f := ⟨hp, hf, rfl⟩
  obtain ⟨Ψ', hsurj, hker, hqs, hcent, hmodel⟩ := weakCT_e8_of_frame p f hadm hK U hgen hcomm hρ hψ
  obtain ⟨hchev, hA6⟩ := lieModel_e8_chev hmodel
  refine ⟨_, inferInstance, ⟨hqs.1.commutator_eq_top, hchev, fun ⟨e⟩ => (hA6.false e).elim⟩,
    ⟨fun e => hA6.false e⟩, MonoidHom.id _, Function.surjective_id, ?_⟩
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
  rw [hx]
  exact Subgroup.one_mem _

end Recog

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
