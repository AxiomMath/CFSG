module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXIVac
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHard2Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def AdjSelQ2 : Prop :=
  ∀ {τ : Tag}, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = 2 → ∀ p : ℕ, p.Prime → (p = 5 ∨ p = 7) → ModelSelQ2 p ↥(adjointGroup τ K)

private theorem p_eq_two_of_card_two {q : TauCeti.PrimePower} (h : q.card = 2) : q.p = 2 := by
  have hdvd : q.p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact dvd_pow_self _ q.exponent_pos.ne'
  rw [h] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd


private theorem exists_modelSelH_untw_cat_two (hQ : AdjSelQ2)
    (hT : ∀ {τ : Tag}, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K ^ 2 - 1 →
        CompTriv p ↥(adjointGroup τ K))
    {p : ℕ} (hp : p.Prime) (hp57 : p = 5 ∨ p = 7) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {c : TauCeti.PrimePower → TauCeti.LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : TauCeti.PrimePower)
    (hv : (c q).Valid) (hq : q.card = 2)
    {X : Type} [Group X] (e : X ≃* (TauCeti.CFSGIndex.lie ⟨c q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSelH p T := by
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  have hK2 : Nat.card K = 2 := hK.trans hq
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  have hpq : ¬ p ∣ Nat.card K ^ 2 - 1 := by
    rw [hK2]
    rcases hp57 with rfl | rfl <;> norm_num
  exact ⟨↥(adjointGroup τ K), inferInstance, inferInstance, ⟨e.trans φ⟩,
    modelSelH_of_q2 (hQ hτ K hK2 p hp hp57) (hT hτ K hK2 p hp hp2 hpq)⟩

theorem t263SelWP_hard2Small_of (hQ : AdjSelQ2)
    (hT : ∀ {τ : Tag}, (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = 2 → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card K ^ 2 - 1 →
        CompTriv p ↥(adjointGroup τ K)) :
    T263SelWP t263GHard2Small := by
  refine t263SelWP_of_modelH (fun p hp hp2 X _ h => ?_)
    (fun p hp hp2 Ω _ _ S x hSn hSq hSp hcat hxp hInn => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | E6 q =>
        obtain ⟨hq, hp57⟩ := hi
        exact exists_modelSelH_untw_cat_two hQ hT hp hp57 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv hq e
      | E7 q =>
        obtain ⟨hq, hp57⟩ := hi
        exact exists_modelSelH_untw_cat_two hQ hT hp hp57 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv hq e
      | E8 q =>
        obtain ⟨hq, hp57⟩ := hi
        exact exists_modelSelH_untw_cat_two hQ hT hp hp57 (by simp)
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv hq e
      | _ => exact hi.elim
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · obtain ⟨i, hi, he⟩ := hcat
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | E6 q =>
        obtain ⟨hq, hp57⟩ := hi
        exact inducesInnerMod_e6Inner hp hp2 hSn hSq hSp
          ⟨_, (show t263GE6Inner p (.lie ⟨.E6 q, hv⟩) from
            ⟨p_eq_two_of_card_two hq, fun h3 => by rcases hp57 with rfl | rfl <;> omega⟩), he⟩
          hxp hInn
      | E7 q =>
        exact inducesInnerMod_excInner hp hp2 hSn hSq hSp
          ⟨_, (show t263GExcInner p (.lie ⟨.E7 q, hv⟩) from p_eq_two_of_card_two hi.1), he⟩
          hxp hInn
      | E8 q =>
        exact inducesInnerMod_excInner hp hp2 hSn hSq hSp
          ⟨_, (show t263GExcInner p (.lie ⟨.E8 q, hv⟩) from p_eq_two_of_card_two hi.1), he⟩
          hxp hInn
      | _ => exact hi.elim
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
