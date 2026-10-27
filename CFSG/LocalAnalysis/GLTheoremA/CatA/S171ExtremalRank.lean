module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalTorus
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171ExtremalE6
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartOne.CentralCoverThree

theorem exists_cubeRoot_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : Odd f) :
    ∃ ω : Kˣ, orderOf ω = 3 ∧ ω ^ (2 ^ f + 1) = 1 := by
  have h3 : 3 ∣ Nat.card Kˣ := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 f
    rw [one_pow] at h
    have h4 : Nat.card Kˣ = 4 ^ f - 1 := by
      rw [Nat.card_units, hK, ← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h4]
    exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨ω, hω, ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one, hω]
  simpa using hf.nat_add_dvd_pow_add_pow 2 1

theorem extremalRank_of_statedProj {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) {K : Type} [Field K] [Finite K] {Q f : ℕ}
    (θ : PSimple 3 L ≃* StatedProj (StatedSU 6 Q K)) (hK : Nat.card K = Q ^ 2) (hQ : Q = 2 ^ f)
    (hf : Odd f) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
      3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E := by
  classical
  subst hQ
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have h2 : (-1 : K) = 1 := CharTwo.neg_eq 1
  obtain ⟨ω, hω, hQ⟩ := exists_cubeRoot_two_pow hK hf
  have hQ0 : 2 ^ f ≠ 0 := pow_ne_zero _ two_ne_zero
  have hntX : Nontrivial (StatedProj (StatedSU 6 (2 ^ f) K)) := by
    refine nontrivial_of_ne (S171Extremal.torusHom hω hQ0 hQ (Multiplicative.ofAdd (dvec 1))) 1
      fun h => ?_
    obtain ⟨k, hk⟩ := (S171Extremal.torusHom_eq_one_iff hω hQ0 hQ _).1 h
    have h01 := (hk 0).trans (hk 1).symm
    rw [dvec_apply, dvec_apply] at h01
    exact absurd h01 (by decide)
  haveI : Nontrivial (PSimple 3 L) := θ.toEquiv.nontrivial
  obtain ⟨eL⟩ := HSubT.psimple_nonempty_equiv_quotCenter 3 L hL inferInstance
  let ψ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 6 (2 ^ f) K) := eL.symm.trans θ
  let φ : ↥L →* StatedProj (StatedSU 6 (2 ^ f) K) :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  obtain ⟨U, hU, hcard⟩ := S171Extremal.exists_elemAbelian_card_map_eq h2 hω hQ0 hQ φ hφs hker.le
  exact S171Extremal.exists_of_map_card φ hker hU hcard.ge

theorem extremalRank_u6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid} (hq2 : q.p = 2) (hn : Odd q.exponent)
    (θ : PSimple 3 L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
      3 ^ 4 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv θ
  exact extremalRank_of_statedProj hL e hK (by rw [hq2]) hn

section TwE6


theorem extremalRank_twE6 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : CFSG.Open.IsQuasisimple ↥L) {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid} (hq2 : q.p = 2) (hn : Odd q.exponent)
    (θ : PSimple 3 L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧
      3 ^ 5 * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E := by
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group :=
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_twistedE6 hv).2
  haveI : Nontrivial (PSimple 3 L) := θ.toEquiv.nontrivial
  obtain ⟨eL⟩ := HSubT.psimple_nonempty_equiv_quotCenter 3 L hL inferInstance
  have h3 : 3 ∣ q.p ^ q.exponent + 1 := by
    rw [hq2]
    simpa using hn.nat_add_dvd_pow_add_pow 2 1
  obtain ⟨R, hR, hcard⟩ := S171ExtremalE6.exists_card_map_mk_twE6 h3 (eL.symm.trans θ)
  exact S171Extremal.exists_of_map_card _ (QuotientGroup.ker_mk' _) hR hcard

theorem I171ExtremalRankFact_holds : I171ExtremalRankFact := by
  intro G _ _ L hL n hn
  constructor
  · rintro ⟨i, hi, ⟨θ⟩⟩
    cases i with
    | cyclic p hp => simp [isU6n, onLie] at hi
    | alternating m hm => simp [isU6n, onLie] at hi
    | sporadic s => simp [isU6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [isU6n, onLie] at hi
      split at hi
      · rename_i q
        exact extremalRank_u6 hL hi.1 (hi.2 ▸ hn) θ
      · exact absurd hi id
  · rintro ⟨i, hi, ⟨θ⟩⟩
    cases i with
    | cyclic p hp => simp [isTE6n, onLie] at hi
    | alternating m hm => simp [isTE6n, onLie] at hi
    | sporadic s => simp [isTE6n, onLie] at hi
    | lie j =>
      obtain ⟨d, hv⟩ := j
      simp only [isTE6n, onLie] at hi
      split at hi
      · rename_i q
        exact extremalRank_twE6 hL hi.1 (hi.2 ▸ hn) θ
      · exact absurd hi id

end TwE6

end CFSG.LocalAnalysis.GLTheoremA.S171
