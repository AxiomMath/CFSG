module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.Reduction
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefChar
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Center

variable {Q : Type*} [Group Q] [Finite Q]

theorem i196_isPGroup_center_of_pPrimeCore_eq_bot (p : ℕ) [hp : Fact p.Prime]
    (h : CFSG.pPrimeCore p Q = ⊥) : IsPGroup p (Subgroup.center Q) := by
  rintro ⟨z, hz⟩
  have hn : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
  refine ⟨a, Subtype.ext ?_⟩
  show z ^ p ^ a = 1
  have hdvd : p ^ a ∣ orderOf z := ⟨m, hnm⟩
  have hwo : orderOf (z ^ p ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a hp.out.ne_zero) hdvd, hnm]
    exact Nat.mul_div_cancel_left m (pow_pos hp.out.pos a)
  have hwc : z ^ p ^ a ∈ Subgroup.center Q := Subgroup.pow_mem _ hz _
  have hle : Subgroup.zpowers (z ^ p ^ a) ≤ Subgroup.center Q := by
    rw [Subgroup.zpowers_le]; exact hwc
  have hnorm : (Subgroup.zpowers (z ^ p ^ a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' := hle hn
    rw [Subgroup.mem_center_iff.1 hn' g, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z ^ p ^ a))) := by
    rw [Nat.card_zpowers, hwo]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm
  have hle2 : Subgroup.zpowers (z ^ p ^ a) ≤ CFSG.pPrimeCore p Q :=
    le_sSup ⟨hnorm, hcop⟩
  rw [h] at hle2
  exact Subgroup.mem_bot.1 (hle2 (Subgroup.mem_zpowers _))

theorem i196_pCore_eq_center_of_quasisimple (p : ℕ) [Fact p.Prime]
    (hS : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (hnc : ∃ a b : Q ⧸ Subgroup.center Q, a * b ≠ b * a)
    (h : CFSG.pPrimeCore p Q = ⊥) : CFSG.pCore p Q = Subgroup.center Q := by
  apply le_antisymm
  · have hPn : (CFSG.pCore p Q).Normal := CFSG.pCore_normal
    have hP : IsPGroup p (CFSG.pCore p Q) := CFSG.pCore_isPGroup
    have hmapn : ((CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
      hPn.map _ (QuotientGroup.mk'_surjective _)
    have := hmapn
    rcases hS.eq_bot_or_eq_top_of_normal ((CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q)))
      with hbot | htop
    · intro x hx
      have : QuotientGroup.mk' (Subgroup.center Q) x ∈
          (CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q)) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    · exfalso
      have hSp : IsPGroup p (Q ⧸ Subgroup.center Q) := by
        intro s
        have hs : s ∈ (CFSG.pCore p Q).map (QuotientGroup.mk' (Subgroup.center Q)) := by
          rw [htop]; trivial
        obtain ⟨x, hx, rfl⟩ := hs
        obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
        refine ⟨k, ?_⟩
        have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
        change (QuotientGroup.mk' (Subgroup.center Q) x) ^ p ^ k = 1
        rw [← map_pow, hk', map_one]
      have := hS.toNontrivial
      have hnt := hSp.center_nontrivial
      have hcn : (Subgroup.center (Q ⧸ Subgroup.center Q)).Normal := inferInstance
      have := hcn
      rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with hb | ht
      · obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center (Q ⧸ Subgroup.center Q))
        apply hz
        apply Subtype.ext
        have h2 := (SetLike.ext_iff.1 hb (z : Q ⧸ Subgroup.center Q)).1 z.2
        exact Subgroup.mem_bot.1 h2
      · obtain ⟨a, b, hab⟩ := hnc
        have : a ∈ Subgroup.center (Q ⧸ Subgroup.center Q) := by rw [ht]; trivial
        exact hab (Subgroup.mem_center_iff.1 this b).symm
  · intro z hz
    exact le_sSup (show Subgroup.center Q ∈ {K : Subgroup Q | K.Normal ∧ IsPGroup p K} from
      ⟨inferInstance, i196_isPGroup_center_of_pPrimeCore_eq_bot p h⟩) hz

end Center

section Quotient

variable {H : Type*} [Group H] [Finite H]

theorem i196_exists_mulEquiv_quot_oPrimeP (p : ℕ) [Fact p.Prime]
    (hS : IsSimpleGroup ((H ⧸ GLAPPrimeCore p H) ⧸ Subgroup.center (H ⧸ GLAPPrimeCore p H)))
    (hnc : ∃ a b : (H ⧸ GLAPPrimeCore p H) ⧸ Subgroup.center (H ⧸ GLAPPrimeCore p H),
      a * b ≠ b * a) :
    Nonempty (((H ⧸ GLAPPrimeCore p H) ⧸ Subgroup.center (H ⧸ GLAPPrimeCore p H)) ≃*
      (H ⧸ oPrimeP p H)) := by
  set N := GLAPPrimeCore p H with hN
  have hbot : CFSG.pPrimeCore p (H ⧸ N) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  have hcore : CFSG.pCore p (H ⧸ N) = Subgroup.center (H ⧸ N) :=
    i196_pCore_eq_center_of_quasisimple p hS hnc hbot
  have hop : oPrimeP p H = (Subgroup.center (H ⧸ N)).comap (QuotientGroup.mk' N) := by
    unfold oPrimeP
    rw [hcore]
  have hNle : N ≤ oPrimeP p H := by
    intro x hx
    rw [hop]
    change QuotientGroup.mk' N x ∈ Subgroup.center (H ⧸ N)
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact Subgroup.one_mem _
  have hmap : (oPrimeP p H).map (QuotientGroup.mk' N) = Subgroup.center (H ⧸ N) := by
    rw [hop]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (oPrimeP p H) hNle)⟩

end Quotient

section Models

theorem i196_isLThreeEps_of_lpEpsIndex {S : Type} [Group S] (idx : TauCeti.ValidLieTypeIndex)
    (hidx : IsLpEpsIndex 3 idx.1) (g : S ≃* (TauCeti.CFSGIndex.lie idx).Group) :
    Lemma25Ns.IsLThreeEps S := by
  obtain ⟨d, hv⟩ := idx
  change IsLpEpsIndex 3 d at hidx
  rcases hidx with ⟨Q, hd, hQ⟩ | ⟨Q, hd, hQ⟩
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hcardF : Nat.card (GaloisField Q.p Q.exponent) = Q.card := by
      rw [GaloisField.card _ _ Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
    refine Or.inl ⟨GaloisField Q.p Q.exponent, inferInstance, inferInstance, by rw [hcardF]; exact hQ,
      ⟨?_⟩⟩
    exact (g.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL (3 - 1) Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        (3 - 1 + 1) _))).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj (3 - 1 + 1) _)
  · subst hd
    have : Fact Q.p.Prime := ⟨Q.prime_p⟩
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA (3 - 1) Q hv g
    obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hm
    refine Or.inr ⟨K, inferInstance, inferInstance, Q.p ^ Q.exponent, hK, ?_, ⟨eT⟩⟩
    rw [← TauCeti.PrimePower.card_def]
    omega

end Models

@[expose] def LocalTwoBalanceSimpleThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → (∀ n : ℕ, IsEmpty (S ≃* ↥(alternatingGroup (Fin n)))) →
      (∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx.1 →
        IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) → IsLocallyBalancedAbs 3 2 S

@[expose] def LocalTwoBalanceDefCharThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic = 3 → IsLocallyBalancedAbs 3 2 S

@[expose] def LocalTwoBalanceCrossCharThree : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      idx.1.characteristic ≠ 3 →
        (∀ idx' : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx'.1 →
          IsEmpty (S ≃* (TauCeti.CFSGIndex.lie idx').Group)) → IsLocallyBalancedAbs 3 2 S

@[expose] def SporadicTwoBalanceThree (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → IsLocallyBalancedAbs 3 2 S

@[expose] def SporadicOneBalanceThree (name : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → IsLocallyBalancedAbs 3 1 S

@[expose] def LocalTwoBalanceSporadicThree : Prop :=
  ∀ name : TauCeti.SporadicName, SporadicTwoBalanceThree name

section OneToTwo

variable {K : Type*} [Group K] {p : ℕ}

theorem i196_exists_line_le_of_card_eq_sq {G : Type*} [Group G] (hp : p.Prime) {D : Subgroup G}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) :
    ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) p (n := 1)
    (by rw [hcard]; exact pow_dvd_pow p (by norm_num))
  refine ⟨E'.map D.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
    apply Subtype.ext
    change (x : G) * y = y * x
    exact congrArg (fun z : D => (z : G)) (hD.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hD.2 x x.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hE']

theorem i196_two_of_one (hp : p.Prime) (h : IsLocallyBalancedAbs p 1 K) :
    IsLocallyBalancedAbs p 2 K := by
  intro D hD hcard H hH hDH
  obtain ⟨E, hED, hE, hEc⟩ := i196_exists_line_le_of_card_eq_sq hp hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (h E hE hEc H hH (hED.trans hDH)).le)

end OneToTwo

theorem SporadicTwoBalanceThree.of_one {name : TauCeti.SporadicName}
    (h : SporadicOneBalanceThree name) : SporadicTwoBalanceThree name :=
  fun S _ _ hS hnab he => i196_two_of_one Nat.prime_three (h S hS hnab he)

theorem localTwoBalanceSimpleThree_of_families (hD : LocalTwoBalanceDefCharThree)
    (hC : LocalTwoBalanceCrossCharThree) (hSp : LocalTwoBalanceSporadicThree) :
    LocalTwoBalanceSimpleThree := by
  intro S _ _ hsimple hnab hcat hnalt hnexc
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
    by_cases hch : idx.1.characteristic = 3
    · exact hD S hsimple hnab idx ⟨e⟩ hch
    · exact hC S hsimple hnab idx ⟨e⟩ hch hnexc
  | sporadic name =>
    exact hSp name S hsimple hnab ⟨e⟩

theorem input19_6_9_of_simple (hS : LocalTwoBalanceSimpleThree) : Lemma25Ns.Input19_6_9 := by
  intro G _ _ _ hnab hG X J D hX hJ hDN hD hnot
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hL3, hAlt⟩ := hcon
  apply hnot
  obtain ⟨hsimple, hnabS, hcat⟩ := isCatalogGroup_quotient_center_barOf Nat.prime_three hG hX hJ
  have hq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_barOf Nat.prime_three hJ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := i196_exists_mulEquiv_quot_oPrimeP 3 (H := ↥J) hsimple hnabS
  have hnalt : ∀ n : ℕ,
      IsEmpty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃* ↥(alternatingGroup (Fin n))) :=
    fun n => ⟨fun f => hAlt ⟨n, ⟨e.symm.trans f⟩⟩⟩
  have hnexc : ∀ idx : TauCeti.ValidLieTypeIndex, IsLpEpsIndex 3 idx.1 →
      IsEmpty ((barOf 3 J ⧸ Subgroup.center (barOf 3 J)) ≃*
        (TauCeti.CFSGIndex.lie idx).Group) :=
    fun idx hidx => ⟨fun f => hL3 (i196_isLThreeEps_of_lpEpsIndex idx hidx (e.symm.trans f))⟩
  have hperf : commutator (barOf 3 J) = ⊤ := hq.1
  exact (IsLocallyBalancedAbs.of_quotient_center hperf
    (hS _ hsimple hnabS hcat hnalt hnexc)).isLocallyBalanced _

theorem input19_6_9_of_families (hD : LocalTwoBalanceDefCharThree)
    (hC : LocalTwoBalanceCrossCharThree) (hSp : LocalTwoBalanceSporadicThree) :
    Lemma25Ns.Input19_6_9 :=
  input19_6_9_of_simple (localTwoBalanceSimpleThree_of_families hD hC hSp)

@[expose] def DefCharOuterRankTwoThreeNonD4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, (¬ ∃ q : TauCeti.PrimePower, idx.1 = .D 4 q) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → idx.1.characteristic = 3 →
        ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
          ∃ x ∈ D ⊓ innerAut S, x ≠ 1

@[expose] def DefCharThreeD4Outer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, idx.1 = .D 4 q) →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) → idx.1.characteristic = 3 →
        ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
          D ⊓ innerAut S = ⊥ → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
            D ≤ Subgroup.normalizer (H : Set (MulAut S)) → localDeltaIn 3 H D = ⊥

theorem localTwoBalanceDefCharThree_of (hOut : DefCharOuterRankTwoThreeNonD4)
    (hD4 : DefCharThreeD4Outer) (hCore : DefCharInnerCoreFree) : LocalTwoBalanceDefCharThree := by
  intro S _ _ hS hnab idx hidx hch D hD hcard H hH hDH
  by_cases hD4' : ∃ q : TauCeti.PrimePower, idx.1 = .D 4 q
  · by_cases hmeet : D ⊓ innerAut S = ⊥
    · exact hD4 S hS hnab idx hD4' hidx hch D hD hcard hmeet H hH hDH
    · obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hmeet)
      have hxD : x ∈ D := hx.1
      have hxI : x ∈ innerAut S := hx.2
      have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 _ hxD) hx1'
      have hle : localDeltaIn 3 H D ≤
          GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
        unfold localDeltaIn
        exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1' le_rfl)
      rw [hCore S hS hnab idx hidx 3 Nat.prime_three (by norm_num) hch _ hxI hxp H hH] at hle
      exact le_bot_iff.1 hle
  · obtain ⟨x, ⟨hxD, hxI⟩, hx1⟩ := hOut S hS hnab idx hD4' hidx hch D hD hcard
    have hxp : orderOf x = 3 := orderOf_eq_prime (hD.2 x hxD) hx1
    have hle : localDeltaIn 3 H D ≤
        GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
      unfold localDeltaIn
      exact iInf₂_le_of_le x hxD (iInf_le_of_le hx1 le_rfl)
    rw [hCore S hS hnab idx hidx 3 Nat.prime_three (by norm_num) hch x hxI hxp H hH] at hle
    exact le_bot_iff.1 hle

end CFSG.HardMathSupport.Solomon.Coordinator
