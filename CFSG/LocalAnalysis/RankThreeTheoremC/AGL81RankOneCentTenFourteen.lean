module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
import CFSG.Quasithin.Vol2.Ch3Sec3InspWalterHolds
import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def IsTenFourteenOneIndex (p : ℕ) : TauCeti.CFSGIndex → Prop
  | .cyclic _ _ => False
  | .alternating n _ => (p = 3 ∧ n = 6) ∨ (p = 5 ∧ n = 10)
  | .lie d =>
    (∃ q : TauCeti.PrimePower, q.p = p ∧ 2 ≤ q.exponent ∧ d.1 = .A 1 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = p ∧ d.1 = .twistedA 2 q) ∨
    (p = 3 ∧ ((∃ m : ℕ, d.1 = .reeG2 m) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
      (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q))) ∨
    (p = 5 ∧ (d.1 = .suzuki 2 ∨ d.1 = .tits))
  | .sporadic s => (p = 3 ∧ s = .M11) ∨ (p = 5 ∧ s = .McL) ∨ (p = 11 ∧ s = .J4)

@[expose] def TenFourteenOneGroup (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ i : TauCeti.CFSGIndex, IsTenFourteenOneIndex p i ∧ Nonempty (K ≃* i.Group)

structure TenFourteenCentAt (p : ℕ) (M C : Subgroup G) : Prop where
  core_le : (primeComplementCore (G := C) p).map C.subtype ≤ M
  cyclic : d1KBar p M C = ⊥ → ∀ B : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p B (C ⊓ M) →
    3 ≤ Open.pRank p B → IsCyclic ↥(Subgroup.center ↥B)
  nineThree : d1KBar p M C ≠ ⊥ → Hyp111NineThree p M C (d1KBar p M C)
  rank : d1KBar p M C ≠ ⊥ → Open.pRank p (d1PlusCore p C (d1KBar p M C)) ≤ 1
  center : d1KBar p M C ≠ ⊥ → Subgroup.center ↥(d1KBar p M C) = ⊥
  list : d1KBar p M C ≠ ⊥ → TenFourteenOneGroup p ↥(d1KBar p M C)

variable (G) in
@[expose] def AGL81TenFourteenCentCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ a : G, a ∈ M → orderOf a = p →
    ¬ Subgroup.centralizer ({a} : Set G) ≤ M →
    (∃ U : Subgroup G, U ≤ Subgroup.centralizer ({a} : Set G) ∧ IsAGLQ p M U) →
    TenFourteenCentAt p M (Subgroup.centralizer ({a} : Set G))

section List

variable {S : Type} [Group S] [Finite S]

theorem le_pRank_of_linTwo {p : ℕ} {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.p = p) (hd : d.1 = .A 1 q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    q.exponent ≤ Open.pRank p (⊤ : Subgroup S) := by
  subst hq
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨b⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) ⟨q, hd, rfl, rfl⟩
  have h := CFSG.Quasithin.H13.S3320.le_pRank_of_psl2 q.exponent_pos (e.trans b)
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h

theorem le_pRank_of_unitary {p : ℕ} (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    {q : TauCeti.PrimePower} (hq : q.p = p) (hd : d.1 = .twistedA 2 q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    2 * q.exponent ≤ Open.pRank p (⊤ : Subgroup S) ∨ 4 ≤ Open.pRank p (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .twistedA 2 q := hd
  have hC := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  subst hq
  obtain ⟨-, -, h⟩ := CFSG.SectionRank.classical_model_rank hp2 hC
  rcases h with ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | ⟨h, -⟩ | h
  · exact absurd h (by decide)
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (by decide)
  · exact Or.inr h


theorem six_le_pRank_of_reeGTwo {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (hd : d.1 = .reeG2 m)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : 6 ≤ Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = .reeG2 m := hd
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, -, hK⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 3),
      Nat.card K = 3 ^ (2 * m + 1) :=
    ⟨GaloisField 3 (2 * m + 1), inferInstance, inferInstance, inferInstance,
      GaloisField.card 3 (2 * m + 1) (by omega)⟩
  obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge m hv K hK
  have hmodel : CFSG.Blueprint.ReeTitsModel S .twistedG2 3 (2 * m + 1) :=
    ⟨⟨Nat.prime_three, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl, K, inferInstance,
      inferInstance, hK, ⟨e.trans b.symm⟩⟩
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmodel
  omega

theorem stepThreeGroup_of_tenFourteenOne {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hS : TenFourteenOneGroup p S) (hr : Open.pRank p (⊤ : Subgroup S) ≤ 2) :
    StepThreeGroup p S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  refine ⟨i, ?_, ⟨e⟩⟩
  have hp2 : p ≠ 2 := by omega
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating n _ => exact hi
  | sporadic s =>
    rcases hi with h | h | ⟨rfl, -⟩
    · exact Or.inl h
    · exact Or.inr h
    · omega
  | lie d =>
    obtain ⟨x, hv⟩ := d
    rcases hi with ⟨q, hq, h2, hd⟩ | ⟨q, hq, hd⟩ | ⟨rfl, h3⟩ | ⟨rfl, h5⟩
    ·
      have hn := le_pRank_of_linTwo hq hd e
      have hn2 : q.exponent = 2 := by omega
      simp only at hd
      subst hd
      rcases hp with rfl | rfl
      · exfalso
        have := ((TauCeti.LieTypeIndex.valid_iff _).mp hv).2
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at this
        refine this (Or.inl ⟨rfl, ?_⟩)
        rw [TauCeti.PrimePower.card_def, hq, hn2]
        norm_num
      · exact Or.inr ⟨rfl, Or.inl ⟨q, hq, hn2, rfl⟩⟩
    ·
      have hn := le_pRank_of_unitary hp2 hq hd e
      have hn1 : q.exponent = 1 := by have := q.exponent_pos; omega
      rcases hp with rfl | rfl
      · exact Or.inl ⟨rfl, Or.inl ⟨q, hq, hn1, hd⟩⟩
      · exact Or.inr ⟨rfl, Or.inr (Or.inl ⟨q, hq, hn1, hd⟩)⟩
    · rcases h3 with ⟨m, hd⟩ | h | h
      · have := six_le_pRank_of_reeGTwo hd e
        omega
      · exact Or.inl ⟨rfl, Or.inr (Or.inl h)⟩
      · exact Or.inl ⟨rfl, Or.inr (Or.inr h)⟩
    · exact Or.inr ⟨rfl, Or.inr (Or.inr h5)⟩

end List

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
