module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeCoverMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogOmega

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair)
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_finite)

section Images

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem map_uModelSU_eq_of_N1 (e : L ≃* StatedSp 3 K) (k : Fin 3) {f : ℕ} {K' : Type} [Field K']
    (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2] {C₀ : GL (Fin (2 * 2)) K'}
    (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)
    (ι : K ≃+* h.fixedField) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* G)
    (hΦE : ∀ x, Φ x ∈ neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K,
      Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) =
        ((e.symm ((complSpEquiv k x : complSp K k) : StatedSp 3 K) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K)) :
    (((T₄.map β).map (statedSpMap (ι : K →+* h.fixedField) 2)).map (uModelSU h hC₀)).map
        (Φ.codRestrict _ hΦE) =
      (modelToG e (T₄.map (complSpHom k))).subgroupOf (neighbourCore e k) := by
  ext y
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rw [mem_subgroupOf]
    change Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) ∈ _
    rw [hN1]
    exact symm_mem_modelToG e ⟨x, hx, rfl⟩
  · intro hy
    rw [mem_subgroupOf] at hy
    obtain ⟨_, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    refine ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    change Φ (uModelSU h hC₀ (statedSpMap (ι : K →+* h.fixedField) 2 (β x))) = (y : G)
    rw [hN1, ← hxy]
    rfl

variable [Finite K] [CharP K 2] {k : Type} [Field k] [CharP k 2]

omit [CharP k 2] in
theorem map_tauSp_siegelTorus_eq (ι : K ≃+* k) :
    ((siegelTorus K 2).map tauSp).map (statedSpMap (ι : K →+* k) 2) = rootTorusSp k 0 := by
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩
    refine ⟨Units.map (ι : K →+* k) (s * s), ?_⟩
    change _ = statedSpMap (ι : K →+* k) 2 (tauSp (diagSp K 2 (fun _ => s)))
    rw [tauSp_diagSp_const, statedSpMap_rootTorusHom]
  · rintro ⟨μ, rfl⟩
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((ι.symm : k →+* K) (μ : k))
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact μ.ne_zero (by simpa using congrArg ι hr)
    set s : Kˣ := Units.mk0 r hr0 with hs
    refine ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, ?_⟩
    change statedSpMap (ι : K →+* k) 2 (tauSp (diagSp K 2 (fun _ => s))) = _
    rw [tauSp_diagSp_const, statedSpMap_rootTorusHom]
    congr 1
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, hs, Units.val_mk0]
    rw [← hr]
    simp

end Images

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] in
theorem natCard_pieceCore_dvd_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3} {J : Finset (Fin 3)}
    (hk : k ∉ spSupport J)
    (hfact : leviTorusSp K J ≤ rootTorusSp K k ⊔ (siegelTorus K 2).map (complSpHom (K := K) k))
    (hT₄ : (siegelTorus K 2).map (complSpHom (K := K) k) ≤ leviTorusSp K J)
    (hn : SpThreeUnitaryNormalized e t f k true) :
    Nat.card (pieceCore e J) ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨K', _, h, _, C₀, -, hC₀, ι, Φ, hrange, hker, hN1, -⟩ := hn
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have : Finite K' := h.finite
  have : Finite h.fixedField := fixedField_finite h
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  have hkK : Nat.card h.fixedField = Nat.card K := (Nat.card_congr ι.toEquiv).symm
  have hk4 : 4 ≤ Nat.card h.fixedField := hkK ▸ hK4
  have hΦE : ∀ x, Φ x ∈ neighbourCore e k := fun x => hrange ▸ ⟨x, rfl⟩
  set Φ' := Φ.codRestrict _ hΦE with hΦ'
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hker' : Φ'.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) := by
    rw [hΦ', MonoidHom.ker_codRestrict]
    exact hker
  set Y := modelToG e ((siegelTorus K 2).map (complSpHom (K := K) k)) with hYdef
  have hY : Y ≤ neighbourCore e k := by
    refine (UnitaryPilot.modelToG_mono e ?_).trans
      (modelToG_complSp_le_neighbourCore e hK4 (by norm_num) k)
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv k x).2
  rw [pieceCore_eq e hk, inf_centralizer_eq_of_le_sup (H := neighbourCore e k)
    (X := modelToG e (rootTorusSp K k)) (Y := Y) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e hT₄)
    (by rw [← UnitaryPilot.modelToG_sup]; exact UnitaryPilot.modelToG_mono e hfact),
    perfectCore_inf_centralizer_eq_map hY,
    Subgroup.card_map_of_injective (neighbourCore e k).subtype_injective]
  have hTY := map_uModelSU_eq_of_N1 e k h hC₀ ι tauSp Φ hΦE (fun x => hN1 x) (siegelTorus K 2)
  rw [map_tauSp_siegelTorus_eq ι, ← hΦ'] at hTY
  have hQ := le_map_perfectCore_centralizer Φ' hΦ's hker' (uStdTorus h hC₀)
    (Q := perfectCore (centralizer ((Y.subgroupOf (neighbourCore e k) :
      Subgroup (neighbourCore e k)) : Set (neighbourCore e k))))
    (perfectCore_perfect _) (by rw [uStdTorus, hTY]; exact perfectCore_le _)
  refine (Subgroup.card_dvd_of_le hQ).trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [← natCard_SL_two_congr ι]
  exact natCard_perfectCore_centralizer_uStdTorus_dvd h hC₀ hk4

omit [Finite K] in
theorem pieceCore_eq_modelToG_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) {e : L ≃* StatedSp 3 K} {t : G} {k : Fin 3} {J : Finset (Fin 3)} {j : Fin 3}
    (hj : j ∈ J) (hk : k ∉ spSupport J)
    (hfact : leviTorusSp K J ≤ rootTorusSp K k ⊔ (siegelTorus K 2).map (complSpHom (K := K) k))
    (hT₄ : (siegelTorus K 2).map (complSpHom (K := K) k) ≤ leviTorusSp K J)
    (hn : SpThreeUnitaryNormalized e t f k true) :
    pieceCore e J = modelToG e (simpleRootSL2 K j) := by
  have : Finite K := LinearPilot.finite_of_card_eq_two_pow hKc
  have hK4 : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  symm
  apply Subgroup.eq_of_le_of_card_ge (modelToG_simpleRootSL2_le_pieceCore e hK4 hj)
  rw [natCard_modelToG_simpleRootSL2]
  exact Nat.le_of_dvd Nat.card_pos (natCard_pieceCore_dvd_of_unitary_twisted hKc hf hk hfact hT₄ hn)

omit [Finite K] in
theorem pieceCore_zero_eq_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} (hn : SpThreeUnitaryNormalized e t f 2 true) :
    pieceCore e ({0} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 0) :=
  pieceCore_eq_modelToG_of_unitary_twisted hKc hf (Finset.mem_singleton_self 0) (by decide)
    leviTorusSp_zero_le_sup map_siegelTorus_two_le_leviTorusSp_zero hn

omit [Finite K] in
theorem pieceCore_one_eq_of_unitary_twisted {f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    {e : L ≃* StatedSp 3 K} {t : G} (hn : SpThreeUnitaryNormalized e t f 0 true) :
    pieceCore e ({1} : Finset (Fin 3)) = modelToG e (simpleRootSL2 K 1) :=
  pieceCore_eq_modelToG_of_unitary_twisted hKc hf (Finset.mem_singleton_self 1) (by decide)
    leviTorusSp_one_le_sup map_siegelTorus_zero_le_leviTorusSp_one hn

end Pieces

section Row


@[expose] def SpThreeOmegaMinusPairInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
    ∀ (e : L ≃* StatedSp 3 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin 3, RootKindSp e t f k .unitaryEven) → SpThreeTwisted e →
        modelToG e (simpleRootSL2 K 0) ≤
            centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) ∧
          ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
            TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K 1))
              (pieceCore e ({2} : Finset (Fin 3)))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem spOmegaMinusPieces_of_unitary_twisted {f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin 3, RootKindSp e t f k .unitaryEven) (htw : SpThreeTwisted e)
    (horth : modelToG e (simpleRootSL2 K 0) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G))
    (hpair : ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (W : Subgroup G),
      TwistedB2BlockStandardPair hirr W (modelToG e (simpleRootSL2 K 1))
        (pieceCore e ({2} : Finset (Fin 3)))) :
    SpOmegaMinusPieces (m := 1) e := by
  refine ⟨?_, ?_, hpair⟩
  · intro j hj
    fin_cases j
    · exact pieceCore_zero_eq_of_unitary_twisted hKc hf
        (spThreeUnitaryNormalized_of_twisted hset hKc hf e htC ht 2 (hroot 2) htw)
    · exact pieceCore_one_eq_of_unitary_twisted hKc hf
        (spThreeUnitaryNormalized_of_twisted hset hKc hf e htC ht 0 (hroot 0) htw)
    · exact absurd hj (by decide)
  · intro i hi
    have hi0 : i = 0 := by
      ext
      simp only [Fin.val_zero]
      omega
    subst hi0
    exact horth

theorem spThreeUnitaryEvenTwistedInput_of_pairInput (hp : SpThreeOmegaMinusPairInput) :
    SpThreeUnitaryEvenTwistedInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t hto hKt hroot htw
  have htC : t ∈ centralizer (L : Set G) := by
    have h1 : t ∈ zpowers t := mem_zpowers t
    rw [← hKt] at h1
    exact h1.1
  obtain ⟨horth, hpair⟩ := hp G L hset f K hKc hf e t hto hKt hroot htw
  exact sp2mKindType_omegaMinus_three_of_pieces hKc hf e
    (spOmegaMinusPieces_of_unitary_twisted hset hKc hf e htC hto hroot htw horth hpair)

theorem spThreeUnitaryEvenRecognitionInput_of_inputs (hs : SpThreeUnitaryEvenStandardInput)
    (hp : SpThreeOmegaMinusPairInput) : SpThreeUnitaryEvenRecognitionInput :=
  spThreeUnitaryEvenRecognitionInput_of_oriented hs (spThreeUnitaryEvenTwistedInput_of_pairInput hp)

end Row

end CFSG.SeitzReduction.SymplecticPilot
