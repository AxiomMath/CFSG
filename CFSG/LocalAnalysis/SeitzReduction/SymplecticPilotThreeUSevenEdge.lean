module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeGraphNormalUnitaryOdd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignTwist
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryTransportOdd

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply)
open CFSG.LieType.CurtisTits (rankOne)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section Bar

variable {f m : ℕ} {K' : Type} [Field K'] [Finite K'] [CharP K'  2] (h : UnitaryFieldData 2 f K')
  {C₀ : GL (Fin (2 * m + 1)) K'}
  (hC₀ : ((C₀ : GL (Fin (2 * m + 1)) K') : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K') = 1)
  (hC : IsPrimeFormGram C₀) (P : GL (Fin (2 * m + 1)) h.fixedField)
  (hP : ((P : GL (Fin (2 * m + 1)) h.fixedField) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField) * antidiag (2 * m + 1) *
      ((P : GL (Fin (2 * m + 1)) h.fixedField) :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) h.fixedField)ᵀ = 1)

theorem ctuOddGramEquiv_ctuaBarAut (hF : Nat.card K' = (2 ^ f) ^ 2)
    (y : SU (unitaryInvolution K' 2 f) (2 * m + 1)) :
    ctuOddGramEquiv h hC₀ (RingEquiv.refl K') P hP
        (ctuaBarAut (unitaryInvolution K' 2 f) (unitaryInvolution_involutive hF) (2 * m + 1) y) =
      primeFormFieldSU h hC (UnitaryPilot.barRingEquiv h)
        (ctuOddGramEquiv h hC₀ (RingEquiv.refl K') P hP y) := by
  have htr : ∀ A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) K',
      transportMat ((RingEquiv.refl K' : K' ≃+* K') : K' →+* K') (Equiv.refl _) A = A := by
    intro A
    ext i j
    rfl
  apply Subtype.ext
  apply Units.ext
  rw [F4Pilot.coe_primeFormFieldSU]
  change oddTransportMat h (RingEquiv.refl K') P
      (mat (unitaryInvolution K' 2 f) (2 * m + 1) (ctuaBarAut (unitaryInvolution K' 2 f)
        (unitaryInvolution_involutive hF) (2 * m + 1) y)) =
    (oddTransportMat h (RingEquiv.refl K') P (mat (unitaryInvolution K' 2 f) (2 * m + 1) y)).map
      (UnitaryPilot.barRingEquiv h)
  rw [oddTransportMat, oddTransportMat, htr, htr, Matrix.map_mul, Matrix.map_mul]
  have h1 : (oddRi h P).map (UnitaryPilot.barRingEquiv h) = oddRi h P := map_bar_subtype h _
  have h2 : (oddR h P).map (UnitaryPilot.barRingEquiv h) = oddR h P := map_bar_subtype h _
  rw [h1, h2]
  congr 2

end Bar

section Normal

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def SpThreeUOddNormalized (e : L ≃* StatedSp 3 K) (t : G) (f : ℕ) (k : Fin 3)
    (b : Bool) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (hF : Nat.card F = (2 ^ f) ^ 2)
    (ι : K →+* F) (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c)
    (Φ : SU (unitaryInvolution F 2 f) (2 * 2 + 1) →* G),
    Φ.range = neighbourCore e k ∧
    Φ.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) ∧
    (∀ x : StatedSp 2 K,
      Φ (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι (cond b (tauSp x) x)) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G)) ∧
    ∀ y, t * Φ y * t⁻¹ = Φ (ctuaBarAut (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 2 + 1) y)

variable [Finite G] [Finite K]

theorem spThreeUOddNormalized_false_or_true
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryOdd) :
    SpThreeUOddNormalized e t f k false ∨ SpThreeUOddNormalized e t f k true := by
  obtain ⟨K', _, h, _, C₀, hC, hC₀, hβ⟩ :=
    exists_unitaryOddNeighbourParam_three hset hKc hf e htC ht k hk
  have : Finite K' := h.finite
  have : CharP K' 2 := h.charP
  have : Finite h.fixedField :=
    CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer.fixedField_finite h
  obtain ⟨P, hP⟩ := exists_mul_antidiag_mul_transpose_eq_one (k := h.fixedField)
    (n := 2 * 2 + 1) (i₀ := ⟨2, by omega⟩) (Fin.ext (by simp only [Fin.val_rev]))
  obtain ⟨ι', κ, Φ, hκ, hrange, hker, hN1, hN3⟩ := hβ (oddBeta P hP)
  have hF : Nat.card K' = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  set ι : K →+* K' := h.fixedField.subtype.comp (ι' : K →+* h.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K' 2 f (ι c) = ι c := fun c => by
    rw [unitaryInvolution_apply, ← h.bar_apply]
    exact (h.mem_fixedField.1 (ι' c).2)
  set E := ctuOddGramEquiv h hC₀ (RingEquiv.refl K') P hP with hE
  have hrange' : (Φ.comp E.toMonoidHom).range = neighbourCore e k := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, hrange]
  have hker' : (Φ.comp E.toMonoidHom).ker ≤
      center (SU (unitaryInvolution K' 2 f) (2 * 2 + 1)) := fun x hx =>
    mem_center_of_mulEquiv_mem_center E (hker hx)
  have hN1' : ∀ x : StatedSp 2 K, (Φ.comp E.toMonoidHom)
      (ctuEmbed 1 le_rfl (unitaryInvolution K' 2 f) ι hι (κ x)) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G) := by
    intro x
    change Φ (E (ctuEmbed 1 le_rfl (unitaryInvolution K' 2 f) ι hι (κ x))) = _
    rw [hE, ctuOddGramEquiv_ctuEmbed h hC₀ (RingEquiv.refl K') P hP hι ι' (fun _ => rfl)]
    exact hN1 x
  have hN3' : ∀ y, t * (Φ.comp E.toMonoidHom) y * t⁻¹ = (Φ.comp E.toMonoidHom)
      (ctuaBarAut (unitaryInvolution K' 2 f) (unitaryInvolution_involutive hF) (2 * 2 + 1) y) := by
    intro y
    change t * Φ (E y) * t⁻¹ = Φ (E _)
    rw [hN3, hE, ctuOddGramEquiv_ctuaBarAut h hC₀ hC P hP hF]
  rcases hκ with rfl | rfl
  · exact Or.inl ⟨K', inferInstance, inferInstance, inferInstance, hF, ι, hι,
      Φ.comp E.toMonoidHom, hrange', hker', hN1', hN3'⟩
  · exact Or.inr ⟨K', inferInstance, inferInstance, inferInstance, hF, ι, hι,
      Φ.comp E.toMonoidHom, hrange', hker', hN1', hN3'⟩

end Normal

section Edge

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

omit [Finite G] in
theorem map_ctuEmbed_eq_of_uodd_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {F : Type} [Field F]
    {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c} (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SU σ (2 * 2 + 1) →* G) (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl σ ι hι (β x)) =
      ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K)) :
    ((T₄.map β).map (ctuEmbed 1 le_rfl σ ι hι)).map (Φ.codRestrict _ hΦE) =
      (modelToG e (T₄.map ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom))).subgroupOf
        (neighbourCore e k) := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    rw [mem_subgroupOf]
    change Φ (ctuEmbed 1 le_rfl σ ι hι (β x)) ∈ _
    rw [hN1]
    exact symm_mem_modelToG e ⟨x, hx, rfl⟩
  · intro hy
    rw [mem_subgroupOf] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    refine ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ (ctuEmbed 1 le_rfl σ ι hι (β x)) = (y : G)
    rw [hN1, ← hxy]
    rfl

omit [Finite G] in
theorem map_ctuTorus_eq_of_uodd_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {F : Type} [Field F]
    {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c} (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SU σ (2 * 2 + 1) →* G) (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctuEmbed 1 le_rfl σ ι hι (β x)) =
      ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G)) :
    (((rootTorusSp K 0).map β).map (ctuEmbed 1 le_rfl σ ι hι)).map (Φ.codRestrict _ hΦE) =
      (modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf (neighbourCore e k) := by
  rw [map_ctuEmbed_eq_of_uodd_N1 e k β Φ hΦE hN1]
  congr 2
  ext x
  constructor
  · rintro ⟨_, ⟨κ, rfl⟩, rfl⟩
    refine ⟨κ, ?_⟩
    change rootTorusHom K 3 (k.succAbove 0) κ =
      ((complSpEquiv k (rootTorusHom K 2 0 κ) : complSp K k) : StatedSp 3 K)
    rw [coe_complSpEquiv_rootTorusHom]
  · rintro ⟨κ, rfl⟩
    exact ⟨rootTorusHom K 2 0 κ, ⟨κ, rfl⟩, coe_complSpEquiv_rootTorusHom k 0 κ⟩

theorem not_sq_add_one_dvd_natCard_edgeCoreSp_of_uodd_std {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3}
    (hn : SpThreeUOddNormalized e t f k false) :
    ¬ (Nat.card K ^ 2 + 1) ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨F, _, _, _, hF, ι, hι, Φ, hrange, hker, hN1, -⟩ := hn
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hTY := map_ctuTorus_eq_of_uodd_N1 e k (MonoidHom.id _) Φ hΦE (fun x => hN1 x)
  rw [Subgroup.map_id, ← hΦ'] at hTY
  have hQ := le_map_perfectCore_centralizer Φ' hΦ's hker'
    ((rootTorusSp K 0).map (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι))
    (Q := perfectCore (centralizer (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf
      (neighbourCore e k) : Subgroup (neighbourCore e k)) : Set (neighbourCore e k))))
    (perfectCore_perfect _) (by rw [hTY]; exact perfectCore_le _)
  rw [perfectCore_centralizer_ctuEmbed_rootTorus_eq hF le_rfl hι hK4 (l := (0 : Fin 2))
    (by decide) (fun h3 => by
      have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega)] at hQ
  have h1 := (Subgroup.card_dvd_of_le hQ).trans (Subgroup.card_map_dvd _ _)
  rw [natCard_ctuBlock_zero_two hF, ← hKc] at h1
  have hq2 : 2 ∣ Nat.card K := by
    rw [hKc]
    exact dvd_pow_self 2 (by omega)
  exact fun h2 => not_sq_add_one_dvd_card_SU_three hq2 (by omega) (h2.trans h1)

theorem sq_add_one_dvd_natCard_edgeCoreSp_of_uodd_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3}
    (hn : SpThreeUOddNormalized e t f k true) :
    (Nat.card K ^ 2 + 1) ∣ Nat.card (edgeCoreSp e k (k.succAbove 0)) := by
  obtain ⟨F, _, _, _, hF, ι, hι, Φ, hrange, hker, hN1, -⟩ := hn
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hle := modelToG_rootTorusSp_le_neighbourCore_three hK4 e (k := k) (a := 0) rfl
  rw [natCard_edgeCoreSp_eq e k _ hle]
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hker' : Φ'.ker ≤ center (SU (unitaryInvolution F 2 f) (2 * 2 + 1)) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  have hTY := map_ctuTorus_eq_of_uodd_N1 e k tauSp Φ hΦE (fun x => hN1 x)
  rw [← hΦ'] at hTY
  have h1 : (rankOne (rootGroup (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF)
      (2 * 2 + 1)) (⟨0, by norm_num⟩ : Fin ((2 * 2 + 1) / 2))).map Φ' ≤
        perfectCore (centralizer (((modelToG e (rootTorusSp K (k.succAbove 0))).subgroupOf
          (neighbourCore e k) : Subgroup (neighbourCore e k)) : Set (neighbourCore e k))) := by
    refine (Subgroup.map_mono (rankOne_zero_le_perfectCore_centralizer_twTorus hF hf hι)).trans ?_
    have h2 := map_perfectCore_centralizer_le Φ'
      (((rootTorusSp K 0).map tauSp).map (ctuEmbed 1 le_rfl (unitaryInvolution F 2 f) ι hι))
    rw [hTY] at h2
    exact h2
  have h3 := Subgroup.card_dvd_of_le h1
  rw [natCard_map_rankOne_zero hF hker', CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    hF, ← hKc] at h3
  exact (sq_add_one_dvd_ordSL_two_sq (Nat.card K)).trans h3

end Edge

section Orient

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def SpThreeUOddStandard (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → ¬ (Nat.card K ^ 2 + 1) ∣ Nat.card (edgeCoreSp e k l)

@[expose] def SpThreeUOddTwisted (e : L ≃* StatedSp 3 K) : Prop :=
  ∀ k l : Fin 3, k ≠ l → (Nat.card K ^ 2 + 1) ∣ Nat.card (edgeCoreSp e k l)

theorem spThreeUOddStandard_or_twisted (e : L ≃* StatedSp 3 K) :
    SpThreeUOddStandard e ∨ SpThreeUOddTwisted e := by
  by_cases h : (Nat.card K ^ 2 + 1) ∣ Nat.card (edgeCoreSp e 0 1)
  · exact Or.inr fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h
  · exact Or.inl fun k l hkl => by rw [natCard_edgeCoreSp_eq_zero_one e hkl]; exact h

variable [Finite K] [CharP K 2]

theorem spThreeUOddNormalized_of_standard
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryOdd) (hstd : SpThreeUOddStandard e) :
    SpThreeUOddNormalized e t f k false := by
  rcases spThreeUOddNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact h
  · exact absurd (sq_add_one_dvd_natCard_edgeCoreSp_of_uodd_twisted hKc hf h)
      (hstd k _ (ne_succAbove_zero_three k))

theorem spThreeUOddNormalized_of_twisted
    {f : ℕ}
    (hset : SeitzSetting G L) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp 3 K) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (k : Fin 3) (hk : RootKindSp e t f k .unitaryOdd) (htw : SpThreeUOddTwisted e) :
    SpThreeUOddNormalized e t f k true := by
  rcases spThreeUOddNormalized_false_or_true hset hKc hf e htC ht k hk with h | h
  · exact absurd (htw k _ (ne_succAbove_zero_three k))
      (not_sq_add_one_dvd_natCard_edgeCoreSp_of_uodd_std hKc hf h)
  · exact h

end Orient

@[expose] def SpThreeUnitaryOddStandardInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) → SpThreeUOddStandard e →
        SpGlobalCoverType e f .unitaryOdd

@[expose] def SpThreeUnitaryOddTwistedFalseInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryOdd) → SpThreeUOddTwisted e → False

theorem spThreeKindCoverInput_unitaryOdd_of_oriented (hs : SpThreeUnitaryOddStandardInput)
    (ht : SpThreeUnitaryOddTwistedFalseInput) : SpThreeKindCoverInput .unitaryOdd := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot
  rcases spThreeUOddStandard_or_twisted e with h | h
  · exact hs G L hset f K hKc hf e t hto hKt hroot h
  · exact (ht G L hset f K hKc hf e t hto hKt hroot h).elim

end CFSG.SeitzReduction.SymplecticPilot
