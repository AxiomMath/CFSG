module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TitsFiveLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32Loc
import CFSG.Sporadic.Recognition.JankoWongPSLNine
import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.Maximal

open Subgroup

theorem isCoatom_of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K] {p : ℕ}
    [Fact p.Prime] (e : K ≃* K')
    (h : ∀ S' : Sylow p K', IsCoatom (normalizer ((S' : Subgroup K') : Set K')))
    (S : Sylow p K) : IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  have hS : ((Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S : Sylow p K') :
      Subgroup K') = (S : Subgroup K).map e.toMonoidHom := rfl
  have h1 : IsCoatom ((normalizer ((S : Subgroup K) : Set K)).map e.toMonoidHom) := by
    rw [map_equiv_normalizer_eq, ← hS]
    exact h _
  exact (OrderIso.isCoatom_iff e.mapSubgroup _).1 h1

theorem normalizer_ne_top_of_simple {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    {p k : ℕ} [Fact p.Prime] (hk : 2 ≤ k) (S : Sylow p K)
    (hS : Nat.card (S : Subgroup K) = p ^ k) :
    normalizer ((S : Subgroup K) : Set K) ≠ ⊤ := by
  intro h
  haveI : (S : Subgroup K).Normal := normalizer_eq_top_iff.mp h
  have hp : p.Prime := Fact.out
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S : Subgroup K) with h0 | h1
  · rw [h0, Subgroup.card_bot] at hS
    have := Nat.one_lt_pow (by omega : k ≠ 0) hp.one_lt
    omega
  · have hsurj : Function.Surjective (S : Subgroup K).subtype := fun x =>
      ⟨⟨x, by rw [h1]; trivial⟩, rfl⟩
    have hpg : IsPGroup p K := S.isPGroup'.of_surjective _ hsurj
    have h2 : Nat.card K = p := hpg.isSimpleGroup_iff_card_eq.1 inferInstance
    rw [h1, Subgroup.card_top] at hS
    have := Nat.pow_lt_pow_right hp.one_lt (by omega : 1 < k)
    rw [pow_one] at this
    omega

theorem center_eq_bot_of_simple {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (h : ¬ (Nat.card K).Prime) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h0 | h1
  · exact h0
  · refine absurd ?_ h
    have hcomm : ∀ a b : K, a * b = b * a := fun a b =>
      (mem_center_iff.1 (h1 ▸ mem_top a) b).symm
    letI : CommGroup K := { ‹Group K› with mul_comm := hcomm }
    exact IsSimpleGroup.prime_card (α := K)

theorem isCoatom_of_forall_le {K : Type*} [Group K] {N : Subgroup K} (hne : N ≠ ⊤)
    (hmax : ∀ Y : Subgroup K, N ≤ Y → Y = N ∨ Y = ⊤) : IsCoatom N := by
  refine ⟨hne, fun Y hY => ?_⟩
  rcases hmax Y hY.le with h | h
  · exact absurd h hY.ne'
  · exact h

section Borel

open CFSG.AGLEmbedding

theorem isCoatom_a6 {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 6))
    (S : Sylow 3 K) : IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨φ⟩ :=
    CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine hF
  exact isCoatom_of_mulEquiv (e.trans φ.symm)
    (fun S' => psl2GF_borelCoatom 3 2 (by norm_num) (by norm_num) S') S

private theorem isCoatom_l225 {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hd : IsLinTwoIndex 5 2 d) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (S : Sylow 5 K) :
    IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  exact isCoatom_of_mulEquiv (e.trans φ)
    (fun S' => psl2GF_borelCoatom 5 2 (by norm_num) (by norm_num) S') S

private theorem isCoatom_unitary {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (S : Sylow p K) :
    IsCoatom (normalizer ((S : Subgroup K) : Set K)) :=
  kFactUnitaryBorelMaximal K p d hd ⟨e⟩ S

end Borel

section L28

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs

private theorem isCoatom_l28 {K : Type} [Group K] [Finite K] (hL : IsCaseTwoGroup 3 K)
    (T : Sylow 3 K) : IsCoatom (normalizer ((T : Subgroup K) : Set K)) := by
  obtain ⟨ε₀⟩ := L28Local.nonempty_equiv_G8 hL
  have hD := L28Local.l28Data_of_equiv ε₀ T
  refine isCoatom_of_forall_le (fun h => ?_) fun Y hY => hD.maximal hY
  have h1 := hD.card_normalizer
  rw [h, Subgroup.card_top, hD.card_group] at h1
  omega

end L28

section Sz32

open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor


private theorem isCoatom_sz32 {K : Type} [Group K] [Finite K] (hK : IsSz32Type 5 K)
    (T : Sylow 5 K) : IsCoatom (normalizer ((T : Subgroup K) : Set K)) := by
  have hD := sz32_data K hK T
  refine isCoatom_of_forall_le (fun h => ?_) fun Y hY => hD.maximal hY
  have h1 := hD.card_normalizer
  rw [h, Subgroup.card_top, hD.card_group] at h1
  omega

end Sz32

section Tits

open CFSG.AGLEmbeddingD2 CFSG.Sporadic.Schreier.Tits


private theorem isCoatom_tits {K : Type} [Group K] [Finite K]
    (hK : ∃ hv : TauCeti.LieTypeIndex.tits.Valid,
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group)) (S : Sylow 5 K) :
    IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hv, ⟨e⟩⟩ := hK
  obtain ⟨eD⟩ := CFSG.AGLEmbedding.KFactProofs.SmallIdent.nonempty_equiv_tits (K := K)
    ⟨⟨.tits, hv⟩, rfl, ⟨e⟩⟩
  haveI : IsSimpleGroup K := by
    haveI := titsD_simple
    exact eD.isSimpleGroup
  have hcard : Nat.card K = 17971200 := by rw [Nat.card_congr eD.toEquiv, card_titsD]
  have hKc : centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [coe_top, centralizer_univ, center_eq_bot_of_simple (by rw [hcard]; norm_num)]
  obtain ⟨-, hS, hmax, -⟩ := d2TorusLocalAt_tits ⟨.tits, hv⟩ rfl K ⊤ inferInstance hKc
    ⟨topEquiv.trans e⟩ 5 rfl S
  exact isCoatom_of_forall_le (normalizer_ne_top_of_simple (by norm_num) S hS) hmax

end Tits

section McL

open CFSG.AGLEmbeddingD2


private theorem isCoatom_mcl {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group)) (S : Sylow 5 K) :
    IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have e' : K ≃* CFSG.Blueprint.NativeSporadic.McL := e.trans eC.symm
  haveI : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup K _ CFSG.Blueprint.NativeSporadic.McL _
      CFSG.Sporadic.McL.isSimpleGroup_McL e'
  have hcard : Nat.card K = 898128000 := by
    rw [Nat.card_congr e'.toEquiv, CFSG.Sporadic.McL.card_McL]
  have hKc : centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [coe_top, centralizer_univ, center_eq_bot_of_simple (by rw [hcard]; norm_num)]
  obtain ⟨-, hS, hmax, -⟩ := d2HeisLocalAt_mcl K ⊤ inferInstance hKc ⟨topEquiv.trans e⟩ 5 rfl S
  exact isCoatom_of_forall_le (normalizer_ne_top_of_simple (by norm_num) S hS) hmax

end McL

section M11

open CFSG.AGLEmbeddingD2


private theorem isCoatom_m11 {K : Type} [Group K] [Finite K]
    (hL : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M11).Group)) (S : Sylow 3 K) :
    IsCoatom (normalizer ((S : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hL
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have e' : K ≃* CFSG.Blueprint.NativeSporadic.M11 := e.trans eC.symm
  haveI : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup K _ CFSG.Blueprint.NativeSporadic.M11 _
      CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2 e'
  obtain ⟨R₀, hR₀⟩ := m11_three_localData
  have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_three (by norm_num)
  have h := torusLocal_sylow e' hT (by
    rw [hT.1, CFSG.Sporadic.Mathieu.card_M11, factorization_eq_of_pow_dvd Nat.prime_three
      (k := 2) (by norm_num) (by norm_num) (by norm_num)]) S
  exact isCoatom_of_forall_le (normalizer_ne_top_of_simple (by norm_num) S h.1) h.2.1

end M11

section L34


private theorem isCoatom_l34 {K : Type} [Group K] [Finite K] (hL : IsRankThreeL34 K)
    (T : Sylow 3 K) : IsCoatom (normalizer ((T : Subgroup K) : Set K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, -, hmax, -⟩ := kFactL34Three K hL T
  obtain ⟨q, -, -, hv, ⟨e⟩⟩ := hL
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (2 + 1))
      (GaloisField q.p q.exponent)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField q.p q.exponent) (n := 3)
      (by norm_num) (Or.inl le_rfl)).2.1
  haveI : IsSimpleGroup K := e'.isSimpleGroup
  exact isCoatom_of_forall_le (normalizer_ne_top_of_simple (by norm_num) T hcard) hmax

end L34

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.Maximal

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open Maximal

theorem kFactStepThreeMaximal_holds :
    KFactStepThreeMaximal := by
  intro p K _ _ hK hA10 S
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n hn =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isCoatom_a6 e S
    · exact (hA10.false e).elim
  | lie d =>
    obtain ⟨d, hdv⟩ := d
    rcases hi with ⟨rfl, hi⟩ | ⟨rfl, hi⟩
    · rcases hi with ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hqe, hd⟩
      · obtain rfl : d = .twistedA 2 q := hd
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact isCoatom_unitary ⟨q, hqp, rfl⟩ e S
      · exact isCoatom_l28 ⟨⟨d, hdv⟩, Or.inl ⟨rfl, q, hqp, hqe, hd⟩, ⟨e⟩⟩ S
      · obtain rfl : d = .A 2 q := hd
        exact isCoatom_l34 ⟨q, hqp, hqe, hdv, ⟨e⟩⟩ S
    · rcases hi with ⟨q, hqp, hqe, hd⟩ | ⟨q, hqp, hqe, hd⟩ | hd | hd
      · obtain rfl : d = .A 1 q := hd
        exact isCoatom_l225 ⟨q, rfl, hqp, hqe⟩ e S
      · obtain rfl : d = .twistedA 2 q := hd
        haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
        exact isCoatom_unitary ⟨q, hqp, rfl⟩ e S
      · obtain rfl : d = .suzuki 2 := hd
        exact isCoatom_sz32 ⟨rfl, hdv, ⟨e⟩⟩ S
      · obtain rfl : d = .tits := hd
        exact isCoatom_tits ⟨hdv, ⟨e⟩⟩ S
  | sporadic s =>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact isCoatom_m11 ⟨e⟩ S
    · exact isCoatom_mcl ⟨e⟩ S

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

