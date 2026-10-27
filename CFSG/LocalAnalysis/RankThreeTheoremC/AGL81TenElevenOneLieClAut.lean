module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneLieClCases
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Linear
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairA6Atlas
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankOne
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.LocalAnalysis.RankThreeUC.S15
  Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  (autThreePowInner_of_not_three_dvd_outer autThreePowInner_of_mulEquiv)

@[expose] def KFactTenElevenOneLieAutRes : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → Open.IsQuasisimple ↥L →
    CFSG.pCore 2 Y = ⊥ → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
    (RankTwoList d.1 ∨ RankThreeList d.1) → (∀ q : TauCeti.PrimePower, d.1 ≠ .A 2 q) →
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) →
    (∃ T J : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (L : Set Y)) →
    Open.pRank 3 (⊤ : Subgroup Y) = 3 →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      Open.pRank 3 (Subgroup.centralizer (E : Set Y)) ≤ 2) →
    (∃ N : Subgroup Y, N.Normal ∧ N.index = 3) → False

namespace LieClAut

theorem center_quotient_eq_bot {Q : Type*} [Group Q] (hq : Open.IsQuasisimple Q) :
    center (Q ⧸ center Q) = ⊥ := by
  haveI := hq.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with h | h
  · exact h
  · exfalso
    have hker : commutator Q ≤ (QuotientGroup.mk' (center Q)).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (h ▸ mem_top _) _).symm
    rw [hq.1] at hker
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ center Q)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ∀ g : Q, (g : Q ⧸ center Q) = 1 := fun g => hker (mem_top g)
    exact hxy (by rw [h1 x, h1 y])

variable {X : Type} [Group X] [Finite X]

theorem pRank_mulAut_le (hc : center X = ⊥) (hX : AutThreePowInner X) :
    Open.pRank 3 (⊤ : Subgroup (MulAut X)) ≤ Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ center X := mem_center_iff.2 fun h => by
      have h1 := DFunLike.congr_fun hg h
      rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [hc, mem_bot] at hgc
    exact hgc
  obtain ⟨E, -, hE, hEc⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (MulAut X))
  have hEr : E ≤ (MulAut.conj : X →* MulAut X).range := fun ψ hψ => by
    have h3 : ψ ^ 3 = 1 := hE.2 ψ hψ
    obtain ⟨a, ha⟩ := hX ψ 1 fun x => by
      have := congrArg (fun τ : MulAut X => τ x) h3
      simpa [pow_succ, MulAut.mul_apply] using this
    exact ⟨a, MulEquiv.ext fun x => by rw [MulAut.conj_apply, ha]⟩
  set f : ↥E →* X :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (Subgroup.inclusion hEr) with hfdef
  have hf : Function.Injective f :=
    (MonoidHom.ofInjective hinj).symm.injective.comp (Subgroup.inclusion_injective hEr)
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun a b => hE.1.is_comm.comm a b)
    (fun a => Subtype.ext (hE.2 _ a.2)) hEc f hf le_top

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]

theorem pRank_top_le_of_autThreePowInner (hq : Open.IsQuasisimple ↥L)
    (hC3 : ¬ 3 ∣ Nat.card (centralizer (L : Set Y)))
    (hX : AutThreePowInner (↥L ⧸ center ↥L)) :
    Open.pRank 3 (⊤ : Subgroup Y) ≤ Open.pRank 3 (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  obtain ⟨E, -, hE, hEc⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup Y)
  set φ : ↥E →* MulAut (↥L ⧸ center ↥L) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
      ((MulAut.conjNormal : Y →* MulAut ↥L).comp E.subtype) with hφdef
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (MulAut.conjNormal (x : Y) : MulAut ↥L) = 1 :=
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥L
        (by rw [map_one]; exact hx)
    have hxC : (x : Y) ∈ centralizer (L : Set Y) := mem_centralizer_iff.2 fun l hl => by
      have h2 := congrArg (fun τ : MulAut ↥L => ((τ ⟨l, hl⟩ : ↥L) : Y)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
      calc l * (x : Y) = (x : Y) * l * (x : Y)⁻¹ * x := by rw [h2]
        _ = (x : Y) * l := by group
    have hoE : orderOf x ∣ 3 ^ Open.pRank 3 (⊤ : Subgroup Y) := hEc ▸ orderOf_dvd_natCard x
    have hoC : orderOf x ∣ Nat.card (centralizer (L : Set Y)) := by
      have := orderOf_dvd_natCard (⟨x, hxC⟩ : centralizer (L : Set Y))
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at this
    have hcop : Nat.Coprime (3 ^ Open.pRank 3 (⊤ : Subgroup Y))
        (Nat.card (centralizer (L : Set Y))) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hoE) hoC)
  have hle := CFSG.SectionRank.le_pRank_of_injective (by norm_num)
    (fun a b => hE.1.is_comm.comm a b)
    (fun a => Subtype.ext (hE.2 _ a.2)) hEc φ hφ (le_top : φ.range ≤ ⊤)
  exact hle.trans (pRank_mulAut_le (center_quotient_eq_bot hq) hX)

theorem pRank_le_of_not_dvd {m : ℕ} (h : ¬ 3 ^ (m + 1) ∣ Nat.card X) :
    Open.pRank 3 (⊤ : Subgroup X) ≤ m := by
  obtain ⟨E, -, -, hEc⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  by_contra hlt
  apply h
  have h1 : 3 ^ (m + 1) ∣ 3 ^ Open.pRank 3 (⊤ : Subgroup X) :=
    Nat.pow_dvd_pow 3 (by omega)
  exact h1.trans (hEc ▸ E.card_subgroup_dvd_card)

theorem small_autThreePowInner_pRank (h : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
      Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group))) :
    AutThreePowInner X ∧ Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩, ⟨e⟩⟩
  · refine ⟨autThreePowInner_of_mulEquiv
      e (CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.autThreePowInner_alt_of_five_le
        (by omega)), pRank_le_of_not_dvd ?_⟩
    rw [Nat.card_congr e.toEquiv]
    rcases hn with rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;> decide
  · simp only at hd
    subst hd
    obtain ⟨hp7, hf1⟩ : q.p = 7 ∧ q.exponent = 1 := by
      have hq' : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      exact (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
    have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hcard : Nat.card X = 168 := by
      rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hM, hp7, hf1]
      decide +kernel
    rw [hp7, hf1] at hM
    refine ⟨CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.autThreePowInner_of_psl_two hM
      (by norm_num) ?_, pRank_le_of_not_dvd (by rw [hcard]; decide)⟩
    rw [hcard, show (168 : ℕ) = 3 ^ 1 * 56 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 56)]
    simp
  · refine ⟨?_, a6a_pRank_top_le_two_of_isUThreeThree ⟨⟨d, hv⟩, ⟨q, hq, hd⟩, ⟨e⟩⟩⟩
    simp only at hd
    subst hd
    obtain ⟨hp3, hf1⟩ : q.p = 3 ∧ q.exponent = 1 := by
      have hq' : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      exact (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
    have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    rw [hp3, hf1] at hM
    have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) le_rfl Nat.prime_three le_rfl hM).1
    refine autThreePowInner_of_not_three_dvd_outer fun h3 => ?_
    have h2 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 2 := by
      simpa [CFSG.RankThree.OuterOrder.determinantParameter] using hout
    have := h3.trans h2
    omega

theorem index_cases (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1) :
    IsRankTwoPlus d.1 ∨ (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .twistedA 2 q) := by
  obtain ⟨d, hv⟩ := d
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A l q =>
    by_cases hl : 2 ≤ l
    · exact Or.inl ⟨hd, hl⟩
    · exact Or.inr (Or.inl ⟨q, hd, by simp only; congr 1; have := hr.1; omega⟩)
  | twistedA l q =>
    by_cases hl : 3 ≤ l
    · exact Or.inl ⟨hd, hl⟩
    · exact Or.inr (Or.inr ⟨q, hd, by simp only; congr 1; have := hr.1; omega⟩)
  | B l q => exact Or.inl ⟨hd, hr.1⟩
  | D l q => exact Or.inl ⟨hd, hr⟩
  | twistedD l q => exact Or.inl ⟨hd, hr⟩
  | G2 q => exact Or.inl hd
  | _ => exact hd.elim

theorem exists_eq_of_rankOneList {d : TauCeti.LieTypeIndex} (h : RankOneList d) :
    ∃ q : TauCeti.PrimePower, d = .A 2 q := by
  unfold RankOneList at h
  split at h
  · exact ⟨_, rfl⟩
  · exact h.elim

theorem false_of_borelMaximal (hmax : LieOut.BorelMaximal X)
    (hJ : ∃ T J : Subgroup X, IsSylowTwoOf T ⊤ ∧
      Subgroup.normalizer (T : Set _) ≤ J ∧ J ≠ Subgroup.normalizer (T : Set _) ∧ J ≠ ⊤) :
    False := by
  obtain ⟨T, J, ⟨-, hT2, hTi⟩, hTJ, hJT, hJt⟩ := hJ
  change ¬ 2 ∣ T.relIndex ⊤ at hTi
  rw [Subgroup.relIndex_top_right] at hTi
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hmax (hT2.toSylow hTi) J (by rw [IsPGroup.toSylow_coe]; exact hTJ) hJt
  rw [IsPGroup.toSylow_coe] at h
  exact hJT h

end LieClAut

open LieClAut in
theorem kFactTenElevenOneLieAut_of_res (hChev : LieOddRankChev)
    (hR : KFactTenElevenOneLieAutRes) : KFactTenElevenOneLieAut := by
  intro Y _ _ L hLn hq hO hcl hJ hC3 hrk hE hN
  haveI := hLn
  rcases hcl with ⟨d, hdi, ⟨e⟩⟩ | hsmall | hsmall
  · rcases index_cases d hdi with hd2 | ⟨q, hq2, hd⟩ | ⟨q, hq2, hd⟩
    · by_cases hA2 : ∃ q : TauCeti.PrimePower, d.1 = .A 2 q
      · obtain ⟨q, hq'⟩ := hA2
        have hq2 : q.p = 2 := by
          have := hdi
          rw [hq'] at this
          exact this
        exact ⟨q.exponent, d, ⟨q, hq2, rfl, hq'⟩, ⟨e⟩⟩
      push Not at hA2
      have hr := hChev ↥L hq d hdi ⟨e⟩ 3 Nat.prime_three (by norm_num)
      have hLr : Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := by
        have h1 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L
        have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (le_top : L ≤ ⊤)
        omega
      obtain ⟨-, -, -, h4⟩ := mRank3_cases hd2 (Nat.card (Subgroup.center ↥L))
      rcases h4 with h | h | h | h
      · obtain ⟨q, hq'⟩ := exists_eq_of_rankOneList h
        exact absurd hq' (hA2 q)
      · exact (hR Y L hLn hq hO d hd2 (Or.inl h) hA2 ⟨e⟩ hJ hC3 hrk hE hN).elim
      · exact (hR Y L hLn hq hO d hd2 (Or.inr h) hA2 ⟨e⟩ hJ hC3 hrk hE hN).elim
      · omega
    · exfalso
      obtain ⟨d, hv⟩ := d
      obtain rfl : d = .A 1 q := hd
      have hM := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
      rw [hq2] at hM
      exact false_of_borelMaximal (LieOut.borelMaximal_of_model_psl_two hM) hJ
    · exfalso
      obtain ⟨d, hv⟩ := d
      obtain rfl : d = .twistedA 2 q := hd
      have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      rw [hq2] at hM
      exact false_of_borelMaximal (LieOut.borelMaximal_of_model_psu_three hM) hJ
  all_goals
    exfalso
    obtain ⟨hX, hX2⟩ := small_autThreePowInner_pRank (X := ↥L ⧸ center ↥L)
      (by first | exact Or.inl hsmall | exact Or.inr hsmall)
    have := pRank_top_le_of_autThreePowInner hq hC3 hX
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
