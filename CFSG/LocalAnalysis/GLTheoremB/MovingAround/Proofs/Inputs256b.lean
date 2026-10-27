module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116d
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)

@[expose] def Concl256 (K : Type) [Group K] (x : MulAut K) (y : K) (L : Subgroup K) : Prop :=
  ∃ S : MulAut K → Set (Subgroup K),
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) ∧
    (∀ Y : Subgroup K, CFSG.Open.IsSubnormal Y (Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S) → L ≤ Y →
      ¬ IsAltType 5 (barOf 3 Y)) ∧
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, Prop1310a5b.IsAltOrChev (barOf 3 J) ∧
      ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H →
        GLAPPrimeCore 3 H = ⊥ → Prop1310a5b.IsPumpupOrSelf (barOf 3 J) H → Prop1310a5b.Good2319 H) ∧
    L ≤ ⨆ (J : Subgroup K) (_ : J ∈ S x), J

@[expose] def InputSporDownChev3 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ s : TauCeti.SporadicName, IsSporType s S →
    ∀ α : MulAut S, α ^ 3 = 1 → ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ 3 → IsChevSimple q (PSimple 3 I) →
      α ≠ 1 ∧ Claims1116c.SporDownCase s 3 (PSimple 3 I)

@[expose] def Clause2W (J : Type) [Group J] : Prop :=
  IsAltType 5 J ∨ (Prop1310a5b.IsAltOrChev J ∧
    ∀ (H : Type) [Group H] [Finite H], CFSG.LocalAnalysis.GLTheoremA.IsKHat H →
      GLAPPrimeCore 3 H = ⊥ → Prop1310a5b.IsPumpupOrSelf J H → Prop1310a5b.Good2319 H)

@[expose] def Concl256W (K : Type) [Group K] (x : MulAut K) (y : K) (L : Subgroup K) : Prop :=
  ∃ S : MulAut K → Set (Subgroup K),
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, GLAPComponent 3 (Prop1310a5.fixedSub a) J) ∧
    (∀ Y : Subgroup K, CFSG.Open.IsSubnormal Y (Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) S) → L ≤ Y →
      ¬ IsAltType 5 (barOf 3 Y)) ∧
    (∀ a ∈ Prop1310a5b.Agrp x y, a ≠ 1 → ∀ J ∈ S a, Clause2W (barOf 3 J)) ∧
    L ≤ ⨆ (J : Subgroup K) (_ : J ∈ S x), J

@[expose] def Input25_6A5Chev2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K →
    GLAPPrimeCore 3 K = ⊥ → ¬ IsPiGroup 3 K → (¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) →
    IsLieChar (· = 2) K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Concl256W K x y L

@[expose] def chev5Comps {K : Type} [Group K] (a : MulAut K) : Set (Subgroup K) :=
  {J | GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ IsChevSimple 5 (PSimple 3 J)}

@[expose] def InputGen2311Five : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 3 K = ⊥ →
    IsLieChar (· = 5) K →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 →
        Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) chev5Comps = ⊤

@[expose] def a5Comps {K : Type} [Group K] (a : MulAut K) : Set (Subgroup K) :=
  {J | GLAPComponent 3 (Prop1310a5.fixedSub a) J ∧ IsAltType 5 (barOf 3 J)}

@[expose] def InputGen2324c : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → GLAPPrimeCore 3 K = ⊥ →
    (IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K)) →
    ∀ x : MulAut K, orderOf x = 3 → ∀ L : Subgroup K, GLAPComponent 3 (Prop1310a5.fixedSub x) L →
      IsAltType 5 (barOf 3 L) → ∀ y ∈ L, orderOf y = 3 → Prop1310a5b.Kstar (Prop1310a5b.Agrp x y) a5Comps = ⊤

section Generic

theorem fixedSub_eq {K : Type} [Group K] (x : MulAut K) : Prop1310a5.fixedSub x = fixSubgroup x :=
  Subgroup.ext fun _ => Iff.rfl

theorem alt5_noncomm : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  decide

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isAltType_pSimple {K : Type} [Group K] {L : Subgroup K} (h : IsAltType 5 (barOf 3 L)) :
    IsAltType 5 (PSimple 3 L) :=
  Lemma1315b.isAltType_center_quot le_rfl h

theorem not_alt5_of_subnormal_top {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hcore : GLAPPrimeCore 3 K = ⊥) {x : MulAut K} (hx : x ≠ 1) {L : Subgroup K}
    (hLx : L ≤ fixSubgroup x) (hL5 : IsAltType 5 (barOf 3 L)) {Y : Subgroup K}
    (hY : CFSG.Open.IsSubnormal Y ⊤) (hLY : L ≤ Y) : ¬ IsAltType 5 (barOf 3 Y) := by
  intro hY5
  obtain ⟨eL⟩ := hL5
  have hqt : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K).symm hq
  rcases SporFacts.eq_or_le_center_of_isSubnormal hqt hY with rfl | hZ
  ·
    obtain ⟨eY⟩ := hY5
    have hct : GLAPPrimeCore 3 ↥(⊤ : Subgroup K) = ⊥ := by
      rw [← glaPPrimeCore_map_iso 3 (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K).symm, hcore,
        Subgroup.map_bot]
    have hK60 : Nat.card K = 60 := by
      rw [← Subgroup.card_top, ← Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hct).trans
        QuotientGroup.quotientBot).toEquiv, Nat.card_congr eY.toEquiv, card_alt5]
    have hdvd : Nat.card (barOf 3 L) ∣ Nat.card L :=
      Subgroup.index_dvd_card (H := GLAPPrimeCore 3 ↥L)
    rw [Nat.card_congr eL.toEquiv, card_alt5] at hdvd
    have hLtop : L = ⊤ :=
      Subgroup.eq_top_of_le_card (H := L) (by rw [hK60]; exact Nat.le_of_dvd Nat.card_pos hdvd)
    apply hx
    ext k
    rw [MulAut.one_apply]
    have hk : k ∈ L := by rw [hLtop]; exact Subgroup.mem_top k
    exact mem_fixSubgroup.1 (hLx hk)
  ·
    have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
      intro a ha b hb
      obtain ⟨a', -, rfl⟩ := hZ (hLY ha)
      obtain ⟨b', hb', rfl⟩ := hZ (hLY hb)
      have h1 : a' * b' = b' * a' := Subgroup.mem_center_iff.1 hb' a'
      exact congrArg Subtype.val h1
    have key : ∀ u v : barOf 3 L, u * v = v * u := by
      intro u v
      obtain ⟨u0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) u
      obtain ⟨v0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) v
      rw [← map_mul, ← map_mul, show u0 * v0 = v0 * u0 from Subtype.ext (hcomm _ u0.2 _ v0.2)]
    obtain ⟨a, b, hab⟩ := alt5_noncomm
    apply hab
    have h2 := congrArg eL (key (eL.symm a) (eL.symm b))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

end Generic

section Types

theorem type_split (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K)
    (hAlt : ¬ ∃ n : ℕ, IsAltType n (K ⧸ Subgroup.center K)) {x : MulAut K} (hx : orderOf x = 3)
    {L : Subgroup K} (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) :
    IsLieChar (· = 2) K ∨ IsLieChar (· = 5) K ∨
      IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K) := by
  have hq := hK.1
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hL' : GLAPComponent 3 (fixSubgroup x) L := by rwa [fixedSub_eq] at hL
  obtain ⟨hJ', ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three x hL'
  obtain ⟨eA⟩ := isAltType_pSimple hL5
  have eI : PSimple 3 (L.map (QuotientGroup.mk' (Subgroup.center K))) ≃* alternatingGroup (Fin 5) :=
    eJ.symm.trans eA
  obtain ⟨i, ⟨f⟩⟩ := hK.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact absurd ⟨n, ⟨f⟩⟩ hAlt
  | lie idx =>
    have hchev : IsChevSimple idx.1.characteristic (K ⧸ Subgroup.center K) :=
      Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
    have hI := hKD idx.1.characteristic (K ⧸ Subgroup.center K) inferInstance hnab hchev
      (centerQuotientHom K x) (Inputs1415.centerQuotientHom_pow_eq_one hx3) _ hJ'
    by_cases h2 : idx.1.characteristic = 2
    · exact Or.inl ⟨idx, ⟨f⟩, h2⟩
    · rcases Prop1116Design.alt_chev_cases hnl h2 le_rfl ⟨eI⟩ hI with ⟨-, h5⟩ | ⟨h6, -⟩
      · exact Or.inr (Or.inl ⟨idx, ⟨f⟩, h5⟩)
      · omega
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (K ⧸ Subgroup.center K) inferInstance hnab s
      ⟨f⟩ (centerQuotientHom K x) (Inputs1415.centerQuotientHom_pow_eq_one hx3) _ hJ' 5 Nat.prime_five
      (by norm_num) (by norm_num) (Claims1116c.isChevSimple_five_of_A5 eI)
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · rcases hs with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr ⟨f⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨f⟩))
    · exfalso
      have h168 := Prop1116Design.card_statedProj_two_seven h7
      rw [Nat.card_congr eI.toEquiv, card_alt5] at h168
      omega
    · omega
    · omega

theorem good2319_of_pumpup_alt5 (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    {J : Type} [Group J] (hJ5 : IsAltType 5 J) (H : Type) [Group H] [Finite H]
    (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H) (hP : Prop1310a5b.IsPumpupOrSelf J H) : Prop1310a5b.Good2319 H := by
  obtain ⟨σ, hσ3, J₁, hJ₁, ⟨e⟩⟩ := hP
  obtain ⟨e5⟩ := hJ5
  have hq := hH.1
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hq
  have hJ₁' : GLAPComponent 3 (fixSubgroup σ) J₁ := by rwa [fixedSub_eq] at hJ₁
  obtain ⟨hI, ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three σ hJ₁'
  obtain ⟨eA⟩ := isAltType_pSimple (L := J₁) ⟨e.trans e5⟩
  have eI : PSimple 3 (J₁.map (QuotientGroup.mk' (Subgroup.center H))) ≃* alternatingGroup (Fin 5) :=
    eJ.symm.trans eA
  obtain ⟨i, ⟨f⟩⟩ := hH.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨f⟩⟩
  | lie idx =>
    by_cases h3 : idx.1.characteristic = 3
    · exfalso
      have hchev : IsChevSimple idx.1.characteristic (H ⧸ Subgroup.center H) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
      have hI3 := hKD idx.1.characteristic (H ⧸ Subgroup.center H) inferInstance hnab hchev
        (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI
      rw [h3] at hI3
      rcases Prop1116Design.alt_chev_cases hnl (by norm_num) le_rfl ⟨eI⟩ hI3 with ⟨-, h⟩ | ⟨h, -⟩ <;>
        omega
    · exact Or.inr (Or.inl ⟨idx.1.characteristic, h3, idx, ⟨f⟩, rfl⟩)
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (H ⧸ Subgroup.center H) inferInstance hnab s
      ⟨f⟩ (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI 5 Nat.prime_five
      (by norm_num) (by norm_num) (Claims1116c.isChevSimple_five_of_A5 eI)
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · refine Or.inr (Or.inr fun A _ => ?_)
      by_contra hA
      have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut H)) :=
        le_trans (by omega) (CFSG.SectionRank.pRank_mono (by norm_num) (le_top (a := A)))
      have hpair := Inputs256.onePair_of_three_le Nat.prime_three (by norm_num) hOut hbr hOff hq f h3'
      rcases hs with rfl | rfl <;> revert hpair <;> decide
    · exfalso
      have h168 := Prop1116Design.card_statedProj_two_seven h7
      rw [Nat.card_congr eI.toEquiv, card_alt5] at h168
      omega
    · omega
    · omega

end Types

section HSM23

theorem concl_hsM23 (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hGen : InputGen2324c) {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K)
    (hcore : GLAPPrimeCore 3 K = ⊥)
    (hs : IsSporType .HS (K ⧸ Subgroup.center K) ∨ IsSporType .M23 (K ⧸ Subgroup.center K))
    {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K} (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L)
    (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L) (hy : orderOf y = 3) : Concl256 K x y L := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hLx : L ≤ fixSubgroup x := by
    rw [← fixedSub_eq]
    exact hL.1
  refine ⟨a5Comps, fun a _ _ J hJ => hJ.1, fun Y hY hLY => ?_, fun a _ _ J hJ => ?_, ?_⟩
  · rw [hGen K hq hcore hs x hx L hL hL5 y hyL hy] at hY
    exact not_alt5_of_subnormal_top hq hcore hx1 hLx hL5 hY hLY
  · exact ⟨Or.inl ⟨5, isAltType_pSimple hJ.2⟩, fun H _ _ hH _ hP =>
      good2319_of_pumpup_alt5 hnl hKD hSD hOut hbr hOff hJ.2 H hH hP⟩
  · exact le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ a5Comps x) => J) L ⟨hL, hL5⟩ le_rfl

end HSM23

section Chev5

theorem isAltOrChev_of_chev5 {J : Type} [Group J] (h : IsChevSimple 5 (J ⧸ Subgroup.center J)) :
    Prop1310a5b.IsAltOrChev J := by
  rcases h with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      have h5 : idx.1.characteristic = 5 := hi
      exact Or.inr ⟨idx, ⟨e⟩, (by rw [h5]; norm_num : idx.1.characteristic ≠ 3)⟩
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
  · cases i with
    | alternating n hn =>
      rcases hi with ⟨rfl, -⟩ | ⟨-, h | h⟩ | ⟨-, h⟩
      · exact Or.inl ⟨5, ⟨e⟩⟩
      all_goals omega
    | lie d =>
      exfalso
      obtain ⟨d1, hv⟩ := d
      cases d1 with
      | A k q' =>
        rcases k with _ | _ | k <;> simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | twistedA k q' =>
        rcases k with _ | _ | _ | _ | k <;> simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
      | _ => simp [CFSG.Yardstones.Md0ec50421ce4.ambiguousChev] at hi
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim

theorem isChevSimple_seven_of_isLpType {T : Type} [Group T] (h : IsLpType 2 7 T) : IsChevSimple 7 T := by
  obtain ⟨F, hF, hFin, hc, ⟨f⟩⟩ := h
  exact CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv f
    (CFSG.LocalAnalysis.GLTheoremA.KDSpor.He7.isChevSimple_seven_L2 F hc)

theorem good2319_of_pumpup_chev5 (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) {J : Type} [Group J]
    (hJ : IsChevSimple 5 (J ⧸ Subgroup.center J)) (H : Type) [Group H] [Finite H]
    (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H) (hP : Prop1310a5b.IsPumpupOrSelf J H) :
    Prop1310a5b.Good2319 H := by
  obtain ⟨σ, hσ3, J₁, hJ₁, ⟨e⟩⟩ := hP
  have hq := hH.1
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian H hq
  have hJ₁' : GLAPComponent 3 (fixSubgroup σ) J₁ := by rwa [fixedSub_eq] at hJ₁
  obtain ⟨hI, ⟨eJ⟩⟩ := Inputs1415.center_transfer Nat.prime_three σ hJ₁'
  have eZ : PSimple 3 J₁ ≃* J ⧸ Subgroup.center J :=
    QuotientGroup.congr (Subgroup.center (barOf 3 J₁)) (Subgroup.center J) e (Subgroup.map_center_eq e)
  have hX : IsChevSimple 5 (PSimple 3 (J₁.map (QuotientGroup.mk' (Subgroup.center H)))) :=
    CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv (eJ.symm.trans eZ) hJ
  obtain ⟨i, ⟨f⟩⟩ := hH.2
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply f.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn => exact Or.inl ⟨n, ⟨f⟩⟩
  | lie idx =>
    by_cases h3 : idx.1.characteristic = 3
    · exfalso
      have hchev : IsChevSimple idx.1.characteristic (H ⧸ Subgroup.center H) :=
        Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩
      have hI3 := hKD idx.1.characteristic (H ⧸ Subgroup.center H) inferInstance hnab hchev
        (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI
      rw [h3] at hI3
      rcases hcc _ 3 5 hI3 hX (by norm_num) with h | h <;> omega
    · exact Or.inr (Or.inl ⟨idx.1.characteristic, h3, idx, ⟨f⟩, rfl⟩)
  | sporadic s =>
    obtain ⟨-, h⟩ := hSD (H ⧸ Subgroup.center H) inferInstance hnab s
      ⟨f⟩ (centerQuotientHom H σ) (Inputs1415.centerQuotientHom_pow_eq_one hσ3) _ hI 5 Nat.prime_five
      (by norm_num) (by norm_num) hX
    rcases h with ⟨-, hs, -⟩ | ⟨-, -, h7⟩ | ⟨h35, -⟩ | ⟨h313, -⟩
    · refine Or.inr (Or.inr fun A _ => ?_)
      by_contra hA
      have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut H)) :=
        le_trans (by omega) (CFSG.SectionRank.pRank_mono (by norm_num) (le_top (a := A)))
      have hpair := Inputs256.onePair_of_three_le Nat.prime_three (by norm_num) hOut hbr hOff hq f h3'
      rcases hs with rfl | rfl <;> revert hpair <;> decide
    · exfalso
      rcases hcc _ 7 5 (isChevSimple_seven_of_isLpType h7) hX (by norm_num) with h | h <;> omega
    · omega
    · omega

theorem concl_chev5 (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) (hGen5 : InputGen2311Five) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hcore : GLAPPrimeCore 3 K = ⊥)
    (h5 : IsLieChar (· = 5) K) {x : MulAut K} (hx : orderOf x = 3) {L : Subgroup K}
    (hL : GLAPComponent 3 (Prop1310a5.fixedSub x) L) (hL5 : IsAltType 5 (barOf 3 L)) {y : K} (hyL : y ∈ L)
    (hy : orderOf y = 3) : Concl256 K x y L := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  have hLx : L ≤ fixSubgroup x := by
    rw [← fixedSub_eq]
    exact hL.1
  obtain ⟨eL⟩ := isAltType_pSimple hL5
  refine ⟨chev5Comps, fun a _ _ J hJ => hJ.1, fun Y hY hLY => ?_, fun a _ _ J hJ => ?_, ?_⟩
  · rw [hGen5 K hK hcore h5 x hx L hL hL5 y hyL hy] at hY
    exact not_alt5_of_subnormal_top hK.1 hcore hx1 hLx hL5 hY hLY
  · exact ⟨isAltOrChev_of_chev5 (J := barOf 3 J) hJ.2, fun H _ _ hH _ hP =>
      good2319_of_pumpup_chev5 hKD hSD hOut hbr hOff hcc (J := barOf 3 J) hJ.2 H hH hP⟩
  · exact le_iSup₂_of_le (f := fun (J : Subgroup K) (_ : J ∈ chev5Comps x) => J) L
      ⟨hL, Claims1116c.isChevSimple_five_of_A5 eL⟩ le_rfl

end Chev5

section Assembly

theorem inputSporDownChev3_of_input (h : Claims1116b.InputSporDownChev) : InputSporDownChev3 := by
  intro S _ _ hS hnc s hs α hα I hI q hq hq2 hq3 hc
  exact h S hS hnc 3 Nat.prime_three (by norm_num) s hs α hα I hI q hq hq2 hq3 hc

theorem concl_of_weak (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    {K : Type} [Group K] {x : MulAut K} {y : K} {L : Subgroup K} (h : Concl256W K x y L) :
    Concl256 K x y L := by
  obtain ⟨S, h0, h1, h2, h3⟩ := h
  refine ⟨S, h0, h1, fun a ha ha1 J hJ => ?_, h3⟩
  rcases h2 a ha ha1 J hJ with h5 | h
  · exact ⟨Or.inl ⟨5, Lemma1315b.isAltType_center_quot le_rfl h5⟩, fun H _ _ hH _ hP =>
      good2319_of_pumpup_alt5 hnl hKD hSD hOut hbr hOff h5 H hH hP⟩
  · exact h

theorem input25_6A5NonAlt_of_facts (hnl : Prop1116Design.InputAltNotLie)
    (hKD : ∀ r : ℕ, CFSG.LocalAnalysis.GLTheoremA.KDChevDownQ 3 r)
    (hSD : InputSporDownChev3)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOff : ∀ s : TauCeti.SporadicName,
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.OffPair s (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hcc : Claims1116.Input3_3_OddChar) (hGen : InputGen2324c) (hGen5 : InputGen2311Five)
    (h2 : Input25_6A5Chev2) : InputsSeitz2.Input25_6A5NonAlt := by
  intro K _ _ hK hcore hnotPi hAlt x hx L hL hL5 y hyL hy
  rcases type_split hnl hKD hSD hK hAlt hx hL hL5 with h | h | h | h
  · exact concl_of_weak hnl hKD hSD hOut hbr hOff (h2 K hK hcore hnotPi hAlt h x hx L hL hL5 y hyL hy)
  · exact concl_chev5 hKD hSD hOut hbr hOff hcc hGen5 hK hcore h hx hL hL5 hyL hy
  · exact concl_hsM23 hnl hKD hSD hOut hbr hOff hGen hK.1 hcore (Or.inl h) hx hL hL5 hyL hy
  · exact concl_hsM23 hnl hKD hSD hOut hbr hOff hGen hK.1 hcore (Or.inr h) hx hL hL5 hyL hy

end Assembly

section Holds


theorem good2319_of_pumpup_alt5_holds (hSD : InputSporDownChev3) {J : Type} [Group J]
    (hJ5 : IsAltType 5 J) (H : Type) [Group H] [Finite H] (hH : CFSG.LocalAnalysis.GLTheoremA.IsKHat H)
    (hP : Prop1310a5b.IsPumpupOrSelf J H) : Prop1310a5b.Good2319 H :=
  good2319_of_pumpup_alt5 AltFacts4.inputAltNotLie_holds
    (fun r => PumpDefChar.kdChevDownQ_odd Nat.prime_three (by norm_num) r) hSD
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
      CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds) hJ5 H hH hP

theorem input25_6A5NonAlt_of_residuals (hSD : InputSporDownChev3) (hGen : InputGen2324c)
    (hGen5 : InputGen2311Five) (h2 : Input25_6A5Chev2) : InputsSeitz2.Input25_6A5NonAlt :=
  input25_6A5NonAlt_of_facts AltFacts4.inputAltNotLie_holds
    (fun r => PumpDefChar.kdChevDownQ_odd Nat.prime_three (by norm_num) r) hSD
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.offPair_carrier
      CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicBMData_holds)
    CrossCharOdd.input3_3_OddChar_holds hGen hGen5 h2

theorem input25_6A5_of_residuals (hSD : InputSporDownChev3) (hGen : InputGen2324c)
    (hGen5 : InputGen2311Five) (h2 : Input25_6A5Chev2) : Prop1310a5b.Input25_6A5 :=
  InputsSeitz2.input25_6A5_of_nonAlt (input25_6A5NonAlt_of_residuals hSD hGen hGen5 h2)

end Holds

section Rows


theorem inputSporDownChev3_of_rows
    (hB : Claims1116c.SporDownRow .B 3)
    (hM : Claims1116c.SporDownRow .M 3) : InputSporDownChev3 := by
  intro S _ _ hS hnc s hs α hα I hI q hq hq2 hq3 hchev
  haveI := hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [Claims1116b.fixSubgroup_one_eq_top] at hI
    obtain ⟨f⟩ := CFSG.LocalAnalysis.GLTheoremA.chevQ_pSimple_top_equiv Nat.prime_three hnc hI
    exact Claims1116c.not_isChevSimple_of_isSporType (Claims1116.isSporType_congr f.symm hs) hq hq2 hchev
  refine ⟨hα1, ?_⟩
  obtain ⟨x, rfl, hxp⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three
    (by norm_num) (Claims1116b.center_eq_bot_of_simple hnc)
    (CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds S hS hnc s hs) α hα
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj] at hI
  have hcard : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr hs.some.toEquiv).trans
      (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s)
  by_cases h2 : 3 ^ 2 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s
  · have hrow : Claims1116c.SporDownRow s 3 := by
      have hdvd' : 3 ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic s).Group := by
        rw [CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s]
        exact h2
      rcases CFSG.HardMathSupport.Solomon.Coordinator.sporadicP2Table_holds s 3 Nat.prime_three
          (by norm_num) hdvd' with h1 | h1
      · rcases h1 with ⟨-, hs'⟩ | ⟨h35, -⟩ | ⟨h37, -⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
          rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl
          exacts [Claims1116c.sporDownRow_J3_three, Claims1116c.sporDownRow_McL_three,
            Claims1116c.sporDownRow_Suz_three, Claims1116c.sporDownRow_ON_three,
            Claims1116c.sporDownRow_Co3_three, Claims1116c.sporDownRow_Co2_three,
            Claims1116d.sporDownRow_Co1_three, Claims1116c.sporDownRow_Fi22_three,
            Claims1116c.sporDownRow_Fi23_three, Claims1116c.sporDownRow_Fi24Prime_three,
            Claims1116c.sporDownRow_HN_three, Claims1116c.sporDownRow_Ly_three,
            Claims1116c.sporDownRow_Th_three, hB, hM]
        · omega
        · omega
      · rcases h1 with ⟨-, hs'⟩ | ⟨h35, -⟩ | ⟨h37, -⟩ | ⟨h311, -⟩ | ⟨h313, -⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
          rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          exacts [Claims1116c.sporDownRow_M11_three, Claims1116c.sporDownRow_M12_three,
            Claims1116c.sporDownRow_M22_three, Claims1116c.sporDownRow_M23_three,
            Claims1116d.sporDownRow_M24_three, Claims1116d.sporDownRow_J2_three,
            Claims1116c.sporDownRow_J4_three, Claims1116c.sporDownRow_HS_three,
            Claims1116d.sporDownRow_Ru_three, Claims1116c.sporDownRow_He_three]
        all_goals omega
    exact hrow S hS hs x hxo I hI q hq hq2 hq3 hchev
  · exact (CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact Nat.prime_three hxo
      (by rw [hcard]; exact h2) hI).elim

theorem input25_6A5NonAlt_of_rows
    (hB : Claims1116c.SporDownRow .B 3) (hM : Claims1116c.SporDownRow .M 3)
    (hGen : InputGen2324c) (hGen5 : InputGen2311Five) (h2 : Input25_6A5Chev2) :
    InputsSeitz2.Input25_6A5NonAlt :=
  input25_6A5NonAlt_of_residuals (inputSporDownChev3_of_rows hB hM) hGen hGen5 h2


@[expose] def Input25_6A5Rest : Prop :=
  InputGen2324c ∧ InputGen2311Five ∧ Input25_6A5Chev2

end Rows

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256b

end
