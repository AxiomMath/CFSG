module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma36E

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

structure Lemma36ruDataQ (S : List TauCeti.SporadicName) (s : TauCeti.SporadicName)
    (Q : PairClass) (m e : ℕ) : Prop where
  m_le : m ≤ 2
  data : ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover s L →
    Q H L K u →
      orderOf u = 2 ∧ u ∈ L ∧ u ∉ K ∧ K ≤ L ⊓ centralizer ({u} : Set H) ∧
        (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic ∧
        CFSG.IsQuasisimple ↥K ∧ Group.IsSolvable ↥(autCentralizer L K) ∧
        twoAdic (autCentralizer L K) ≤ m ∧ ElemBound e (autCentralizer L K) ∧
        (∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) ∧
        InvolutionFixesNotLam ↥K (2 * e)
  noOther : ∀ (H : Type) [Group H] [Finite H], Balance.UHered H →
    ∀ (N L K : Subgroup H) (t u : H), FStarSimple N →
    N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover s L → Q H L K u →
    SolStd L → (∃ P : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥P) →
    (∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) → t ∈ centralizer (L : Set H) →
    orderOf t = 2 → BTheoremAt u → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → (∃ s' ∈ S, OddCover s' M) →
      (∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2) → False

inductive Rec36 (S : List TauCeti.SporadicName) (s : TauCeti.SporadicName) (Q : PairClass)
    (m : ℕ) : Prop
  | new (e : ℕ) : Lemma36eDataQ s Q m e → Rec36 S s Q m
  | old (n : ℕ) : Lemma36DataQ s Q m n → Rec36 S s Q m
  | ru (e : ℕ) : Lemma36ruDataQ S s Q m e → Rec36 S s Q m

theorem Rec36.local_facts {S : List TauCeti.SporadicName} {s : TauCeti.SporadicName}
    {Q : PairClass} {m : ℕ} (hd : Rec36 S s Q m) {H : Type} [Group H] [Finite H]
    {L K : Subgroup H} {u : H} (hL : OddCover s L) (hQ : Q H L K u) :
    orderOf u = 2 ∧ u ∈ L ∧ K ≤ L ⊓ centralizer ({u} : Set H) ∧
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic ∧ CFSG.IsQuasisimple ↥K := by
  rcases hd with ⟨e, hd⟩ | ⟨n, hd⟩ | ⟨e, hd⟩
  · obtain ⟨hu2, huL, hKX, hchar, hKq, -⟩ := hd.data H L K u hL hQ
    exact ⟨hu2, huL, hKX, hchar, hKq⟩
  · obtain ⟨hu2, huK, hKX, hchar, hKq, -⟩ := hd.data H L K u hL hQ
    exact ⟨hu2, (hKX huK).1, hKX, hchar, hKq⟩
  · obtain ⟨hu2, huL, -, hKX, hchar, hKq, -⟩ := hd.data H L K u hL hQ
    exact ⟨hu2, huL, hKX, hchar, hKq⟩

theorem componentProduct_eq_of_rec36 {H : Type} [Group H] [Finite H]
    {S : List TauCeti.SporadicName} {s : TauCeti.SporadicName} {Q : PairClass} {m : ℕ}
    (hH : Balance.UHered H) (hd : Rec36 S s Q m) (hout : OutTwoCovers S)
    {N L K : Subgroup H} {t u : H}
    (hN : FStarSimple N) (hidx : N.index ≤ 2)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (hL : OddCover s L) (hQ : Q H L K u) (hstd : SolStd L)
    (hcyc : ∃ P : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥P)
    (hCL2 : u ∉ K → ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2)
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (hB : BTheoremAt u)
    (htypeL : ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      K ≤ M ⊔ CFSG.conjugate M t → M ≠ K → ∃ s' ∈ S, OddCover s' M)
    (hC2 : u ∉ K → ∀ M : Subgroup H, IsCompIn M (centralizer ({u} : Set H)) →
      (∃ s' ∈ S, OddCover s' M) → ∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2) :
    K = componentProduct K u := by
  rcases hd with ⟨e, hd⟩ | ⟨n, hd⟩ | ⟨e, hd⟩
  · exact componentProduct_eq_of_lemma36e hd hout hN hkp hL hQ hstd hcyc ht ht2 hB htypeL hC2
  · exact componentProduct_eq_of_lemma36Data hd hN hkp hL hQ hstd hcyc ht ht2 hB
      fun M hM hKM hMK => (htypeL M hM hKM hMK).choose_spec.2.odd_center
  · obtain ⟨hu2, huL, huK, hKX, hchar, hKq, hAs, hA, he, hin, hfix⟩ := hd.data H L K u hL hQ
    exact componentProduct_eq_of_localData hd.m_le hN hkp hL hstd hcyc ht ht2 hB hu2 huL hKX
      hchar hKq hAs hA he hin hfix fun M hM hKM hMK =>
        hd.noOther H hH N L K t u hN hidx hkp hL hQ hstd hcyc (hCL2 huK) ht ht2 hB M hM hKM hMK
          (htypeL M hM hKM hMK) (hC2 huK M hM (htypeL M hM hKM hMK))

end CFSG.EvenSporadicStandard.Induction
