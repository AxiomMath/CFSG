module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Weak

variable {K K' : Type*} [Group K] [Group K'] {p k : ℕ}

theorem i1910_weak_of_strong {A : Subgroup (MulAut K)}
    (h : IsLocallyBalanced p k A) : IsWeaklyLocallyBalanced p k A := by
  intro D hD H hH hAH
  have h0 := h D hD H hH (hD.1.trans hAH)
  rw [h0]
  exact Subgroup.commutator_bot_left _

theorem i1910_compWeak_of_comp {G : Type*} [Group G] {B L : Subgroup G}
    (h : IsCompLocallyBalanced p k B L) : IsCompWeaklyLocallyBalanced p k B L :=
  i1910_weak_of_strong h

@[expose] def IsWeaklyLocallyBalancedAbs (p k : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ A : Subgroup (MulAut K), IsElemAbelian p A → IsWeaklyLocallyBalanced p k A

theorem i1910_weakAbs_of_abs (h : IsLocallyBalancedAbs p k K) :
    IsWeaklyLocallyBalancedAbs p k K :=
  fun A _ => i1910_weak_of_strong (h.isLocallyBalanced A)

theorem i1910_isElemAbelian_map {M M' : Type*} [Group M] [Group M'] (ψ : M →* M')
    {D : Subgroup M} (hD : IsElemAbelian p D) :
    IsElemAbelian p (D.map ψ) := CFSG.Open.IsElemAbelian.map hD _

theorem i1910_weakAbs_of_injective (ψ : MulAut K →* MulAut K')
    (hψ : Function.Injective ψ) (hinn : innerAut K' ≤ (innerAut K).map ψ)
    (h : IsWeaklyLocallyBalancedAbs p k K') : IsWeaklyLocallyBalancedAbs p k K := by
  intro A hA D hD H hH hAH
  have hD' : IsEkIn p k (A.map ψ) (D.map ψ) :=
    ⟨Subgroup.map_mono hD.1, i1910_isElemAbelian_map ψ hD.2.1, by
      rw [Subgroup.card_map_of_injective hψ, hD.2.2]⟩
  have hH' : innerAut K' ≤ H.map ψ := hinn.trans (Subgroup.map_mono hH)
  have hAH' : A.map ψ ≤ Subgroup.normalizer ((H.map ψ : Subgroup (MulAut K')) : Set (MulAut K')) :=
    (Subgroup.map_mono hAH).trans (Subgroup.le_normalizer_map ψ)
  have h0 := h (A.map ψ) (i1910_isElemAbelian_map ψ hA) (D.map ψ) hD' (H.map ψ) hH' hAH'
  have hle := map_localDeltaIn_le p ψ hψ H D
  have hc : (⁅localDeltaIn p H D, A⁆).map ψ = ⊥ := by
    rw [Subgroup.map_commutator]
    exact le_bot_iff.1 (h0 ▸ Subgroup.commutator_mono hle le_rfl)
  exact (Subgroup.map_eq_bot_iff_of_injective _ hψ).1 hc

theorem i1910_weakAbs_of_quotient_center (hK : commutator K = ⊤)
    (h : IsWeaklyLocallyBalancedAbs p k (K ⧸ Subgroup.center K)) :
    IsWeaklyLocallyBalancedAbs p k K :=
  i1910_weakAbs_of_injective _ (autCenterQuot_injective_of_perfect hK)
    innerAut_le_map_autCenterQuot h

end Weak

theorem i1910_isExtremalType_of_lpEpsIndex {S : Type} [Group S] (idx : TauCeti.ValidLieTypeIndex)
    (hidx : IsLpEpsIndex 3 idx.1)
    (hne : ∀ Q : TauCeti.PrimePower, idx.1 = .twistedA 2 Q → Q.card ≠ 8)
    (g : S ≃* (TauCeti.CFSGIndex.lie idx).Group) : IsExtremalType S := by
  obtain ⟨d, hv⟩ := idx
  change IsLpEpsIndex 3 d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hcardF : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
      rw [GaloisField.card _ _ Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    refine Or.inl ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance,
      by rw [hcardF]; exact hQ, ⟨?_⟩⟩
    exact (g.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (3 - 1) Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (3 - 1 + 1) _))).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (3 - 1 + 1) _)
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (3 - 1) Q hv g
    obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hm
    refine Or.inr ⟨K, inferInstance, inferInstance, Q.p ^ Q.exponent, hK, ?_, ?_, ⟨eT⟩⟩
    · rw [← TauCeti.PrimePower.card_def]
      omega
    · rw [← TauCeti.PrimePower.card_def]
      exact hne Q rfl

@[expose] def LocalTwoBalanceAltLow : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L → ∀ n : ℕ,
        Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) →
          IsCompLocallyBalanced p 2 B L

@[expose] def U3EightTwoBalanceThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex,
      (∃ Q : TauCeti.PrimePower, idx.1 = .twistedA 2 Q ∧ Q.card = 8) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → IsLocallyBalancedAbs 3 2 S

@[expose] def WeakLThreeEpsThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → IsWeaklyLocallyBalancedAbs 3 2 S

@[expose] def LocalTwoBalanceDefCharFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic = 5 → IsLocallyBalancedAbs 5 2 S

@[expose] def LocalTwoBalanceCrossCharFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic ≠ 5 →
        (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 5 idx'.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)) → IsLocallyBalancedAbs 5 2 S

@[expose] def SporadicTwoBalanceFive (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → IsLocallyBalancedAbs 5 2 S

@[expose] def SporadicOneBalanceFive (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → IsLocallyBalancedAbs 5 1 S

@[expose] def LocalTwoBalanceSporadicFive : Prop :=
  ∀ name : TauCeti.SporadicName, name ≠ TauCeti.SporadicName.Fi22 → SporadicTwoBalanceFive name

theorem SporadicTwoBalanceFive.of_one {name : TauCeti.SporadicName}
    (h : SporadicOneBalanceFive name) : SporadicTwoBalanceFive name :=
  fun S _ _ hS hnab he => i196_two_of_one Nat.prime_five (h S hS hnab he)

@[expose] def LocalTwoBalanceSimpleFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → (∀ n : ℕ, IsEmpty (S ≃* ↥(alternatingGroup (Fin n)))) →
      (∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 5 idx.1 →
        IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) →
      IsEmpty (S ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) →
        IsLocallyBalancedAbs 5 2 S

theorem localTwoBalanceSimpleFive_of_families (hD : LocalTwoBalanceDefCharFive)
    (hC : LocalTwoBalanceCrossCharFive) (hSp : LocalTwoBalanceSporadicFive) :
    LocalTwoBalanceSimpleFive := by
  intro S _ _ hsimple hnab hcat hnalt hnexc hnFi
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    exact ((hnalt n).false e).elim
  | lie idx =>
    by_cases hch : idx.1.characteristic = 5
    · exact hD S hsimple hnab idx ⟨e⟩ hch
    · exact hC S hsimple hnab idx ⟨e⟩ hch hnexc
  | sporadic name =>
    have hne : name ≠ TauCeti.SporadicName.Fi22 := fun h => hnFi.false (h ▸ e)
    exact hSp name hne S hsimple hnab ⟨e⟩

@[expose] def DefCharOuterRankTwoFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic = 5 →
        ∀ D : Subgroup (MulAut S), IsElemAbelian 5 D → Nat.card D = 5 ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

theorem localTwoBalanceDefCharFive_of (hOut : DefCharOuterRankTwoFive)
    (hCore : DefCharInnerCoreFree) : LocalTwoBalanceDefCharFive := by
  intro S _ _ hS hnab idx hidx hch D hD hcard H hH hDH
  obtain ⟨x, ⟨hxD, hxI⟩, hx1⟩ := hOut S hS hnab idx hidx hch D hD hcard
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxp : orderOf x = 5 := orderOf_eq_prime (hD.2 x hxD) hx1
  have hle : localDeltaIn 5 H D ≤
      GLAPPrimeCoreOf 5 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
    unfold localDeltaIn
    exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
  rw [hCore S hS hnab idx hidx 5 Nat.prime_five (by norm_num) hch x hxI hxp H hH] at hle
  exact le_bot_iff.1 hle

@[expose] def WeakLFiveEpsFive : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 5 idx.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → IsWeaklyLocallyBalancedAbs 5 2 S

@[expose] def WeakFi22Five : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsFiTwentyTwo S → IsWeaklyLocallyBalancedAbs 5 2 S

@[expose] def Fi22CoverFive : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    IsFiTwentyTwo (Y ⧸ Subgroup.center Y) → GLAPPrimeCore 5 Y = ⊥ → IsFiTwentyTwo Y

@[expose] def Input19_10ClauseC {G : Type*} [Group G] [Finite G] (X B L : Subgroup G) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (q n : ℕ), q = 2 ^ n ∧ n % 4 = 2 ∧
      Nat.card K = q ^ 2 ∧
      Nonempty ((↥L ⧸ oPrimeP 5 ↥L) ≃* StatedProj (StatedSU 5 q K))) ∧
    Odd (Nat.card ↥(X ⊓ Subgroup.centralizer (B : Set G))) ∧
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ (B₀.subgroupOf B).index = 25 ∧
      CFSG.Open.pRank 5 B < CFSG.Open.pRank 5 (X ⊓ Subgroup.centralizer (B₀ : Set G))

@[expose] def LFiveEpsFiveTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian 5 B →
      GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B → 2 ≤ CFSG.Open.pRank 5 B →
      ∀ L : Subgroup G, GLAPComponent 5 X L → ∀ idx : TauCeti.ValidLieTypeIndex,
        IsLpEpsIndex 5 idx.1 →
        Nonempty ((barOf 5 L ⧸ Subgroup.center (barOf 5 L)) ≃*
          (TauCeti.CFSGIndex.lie idx).Group) →
          IsCompLocallyBalanced 5 2 B L ∨ Input19_10ClauseC X B L

@[expose] def Input19_10Low : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) →
    ∀ X : Subgroup G, X ≠ ⊤ → ∀ B : Subgroup G, B ≤ X → IsElemAbelian p B →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → 2 ≤ CFSG.Open.pRank p B →
      ∀ L : Subgroup G, GLAPComponent p X L →
        IsCompWeaklyLocallyBalanced p 2 B L ∧
        (IsCompLocallyBalanced p 2 B L ∨
          (p = 5 ∧ IsFiTwentyTwo (barOf 5 L)) ∨
          (p = 3 ∧ IsExtremalType (↥L ⧸ oPrimeP 3 ↥L)) ∨
          (p = 5 ∧ Input19_10ClauseC X B L))

theorem input19_10Low_of_parts (hAlt : LocalTwoBalanceAltLow) (hS3 : LocalTwoBalanceSimpleThree)
    (hS5 : LocalTwoBalanceSimpleFive) (hU38 : U3EightTwoBalanceThree)
    (hW3 : WeakLThreeEpsThree) (hFi : Fi22CoverFive) (hWFi : WeakFi22Five)
    (hWL5 : WeakLFiveEpsFive) (hE5 : LFiveEpsFiveTwo) : Input19_10Low := by
  intro G _ _ hG p hp hp35 X hX B hBX hB hrank h2 L hL
  obtain ⟨hsimple, hnabS, hcat⟩ := isCatalogGroup_quotient_center_barOf hp hG hX hL
  have hq : CFSG.Open.IsQuasisimple (barOf p L) := isQuasisimple_barOf hp hL
  have hperf : commutator (barOf p L) = ⊤ := hq.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases halt : ∃ n : ℕ,
      Nonempty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n)))
  · obtain ⟨n, hn⟩ := halt
    have h := hAlt G hG p hp hp35 X hX B hBX hB hrank h2 L hL n hn
    exact ⟨i1910_compWeak_of_comp h, Or.inl h⟩
  · have hnalt : ∀ n : ℕ,
        IsEmpty ((barOf p L ⧸ Subgroup.center (barOf p L)) ≃* ↥(alternatingGroup (Fin n))) :=
      fun n => not_nonempty_iff.1 fun h => halt ⟨n, h⟩
    obtain ⟨e⟩ := i196_exists_mulEquiv_quot_oPrimeP p (H := ↥L) hsimple hnabS
    rcases hp35 with rfl | rfl
    ·
      by_cases hexc : ∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx.1 ∧
          Nonempty ((barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃*
            (TauCeti.CFSGIndex.lie idx).Group)
      · obtain ⟨idx, hidx, ⟨g⟩⟩ := hexc
        have hweak : IsCompWeaklyLocallyBalanced 3 2 B L :=
          i1910_weakAbs_of_quotient_center hperf
            (hW3 _ hsimple hnabS idx hidx ⟨g⟩) _
            (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hB L)
        refine ⟨hweak, ?_⟩
        by_cases hq8 : ∃ Q : TauCeti.PrimePower, idx.1 = .twistedA 2 Q ∧ Q.card = 8
        · refine Or.inl ?_
          exact (IsLocallyBalancedAbs.of_quotient_center hperf
            (hU38 _ hsimple hnabS idx hq8 ⟨g⟩)).isLocallyBalanced _
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, i1910_isExtremalType_of_lpEpsIndex idx hidx
            (fun Q h hc => hq8 ⟨Q, h, hc⟩) (e.symm.trans g)⟩))
      · have hnexc : ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx.1 →
            IsEmpty ((barOf 3 L ⧸ Subgroup.center (barOf 3 L)) ≃*
              (TauCeti.CFSGIndex.lie idx).Group) :=
          fun idx hidx => ⟨fun f => hexc ⟨idx, hidx, ⟨f⟩⟩⟩
        have h := (IsLocallyBalancedAbs.of_quotient_center hperf
          (hS3 _ hsimple hnabS hcat hnalt hnexc)).isLocallyBalanced (autBar 3 B L)
        exact ⟨i1910_weak_of_strong h, Or.inl h⟩
    ·
      by_cases hFi22 : IsFiTwentyTwo (barOf 5 L ⧸ Subgroup.center (barOf 5 L))
      · have hY : IsFiTwentyTwo (barOf 5 L) := hFi (barOf 5 L) hq hFi22
          (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 5)
        have hweak : IsCompWeaklyLocallyBalanced 5 2 B L :=
          i1910_weakAbs_of_quotient_center hperf
            (hWFi _ hsimple hnabS hFi22) _
            (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hB L)
        exact ⟨hweak, Or.inr (Or.inl ⟨rfl, hY⟩)⟩
      · by_cases hexc : ∃ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 5 idx.1 ∧
            Nonempty ((barOf 5 L ⧸ Subgroup.center (barOf 5 L)) ≃*
              (TauCeti.CFSGIndex.lie idx).Group)
        · obtain ⟨idx, hidx, hg⟩ := hexc
          have hweak : IsCompWeaklyLocallyBalanced 5 2 B L :=
            i1910_weakAbs_of_quotient_center hperf
              (hWL5 _ hsimple hnabS idx hidx hg) _
              (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hB L)
          refine ⟨hweak, ?_⟩
          rcases hE5 G hG X hX B hBX hB hrank h2 L hL idx hidx hg with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
        · have hnexc : ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 5 idx.1 →
              IsEmpty ((barOf 5 L ⧸ Subgroup.center (barOf 5 L)) ≃*
                (TauCeti.CFSGIndex.lie idx).Group) :=
            fun idx hidx => ⟨fun f => hexc ⟨idx, hidx, ⟨f⟩⟩⟩
          have hnFi : IsEmpty ((barOf 5 L ⧸ Subgroup.center (barOf 5 L)) ≃*
              (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.Fi22).Group) :=
            ⟨fun f => hFi22 ⟨f⟩⟩
          have h := (IsLocallyBalancedAbs.of_quotient_center hperf
            (hS5 _ hsimple hnabS hcat hnalt hnexc hnFi)).isLocallyBalanced (autBar 5 B L)
          exact ⟨i1910_weak_of_strong h, Or.inl h⟩

theorem input19_10_of_low (h3 : LocalThreeBalance) (h2 : LocalTwoBalanceGtFive)
    (hLow : Input19_10Low) : Input19_10 := by
  intro G _ _ _ hnab hG p hp hp2 X hX B hBX hB hrank L hL
  refine ⟨fun h3B => h3 G hG p hp hp2 X hX B hBX hB hrank h3B L hL, ?_⟩
  have hcases : p = 3 ∨ p = 5 ∨ 5 < p := by
    have h2' := hp.two_le
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  rcases hcases with rfl | rfl | h5
  · have h := hLow G hG 3 hp (Or.inl rfl) X hX B hBX hB hrank
    refine ⟨fun h2B => (h h2B L hL).1, fun h2B => (h h2B L hL).2⟩
  · have h := hLow G hG 5 hp (Or.inr rfl) X hX B hBX hB hrank
    refine ⟨fun h2B => (h h2B L hL).1, fun h2B => (h h2B L hL).2⟩
  · refine ⟨fun h2B => i1910_compWeak_of_comp
      (h2 G hG p hp h5 X hX B hBX hB hrank h2B L hL), fun h2B => Or.inl
      (h2 G hG p hp h5 X hX B hBX hB hrank h2B L hL)⟩

theorem input19_10_of_parts (h3 : LocalThreeBalance) (h2 : LocalTwoBalanceGtFive)
    (hAlt : LocalTwoBalanceAltLow) (hS3 : LocalTwoBalanceSimpleThree)
    (hS5 : LocalTwoBalanceSimpleFive) (hU38 : U3EightTwoBalanceThree)
    (hW3 : WeakLThreeEpsThree) (hFi : Fi22CoverFive) (hWFi : WeakFi22Five)
    (hWL5 : WeakLFiveEpsFive) (hE5 : LFiveEpsFiveTwo) : Input19_10 :=
  input19_10_of_low h3 h2
    (input19_10Low_of_parts hAlt hS3 hS5 hU38 hW3 hFi hWFi hWL5 hE5)

end CFSG.HardMathSupport.Solomon.Coordinator
