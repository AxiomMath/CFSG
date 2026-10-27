module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXFSelQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXHardExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyModelTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def TwE6CompTriv : Prop :=
  ∀ (f : ℕ), 4 ≤ 2 ^ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ (2 ^ f) ^ 2 - 1 →
        CompTriv p ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)

private theorem exists_modelSelH_twE6_cat
    (hT : TwE6CompTriv) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) (hq2 : q.p = 2) (hq4 : 4 ≤ q.card)
    (hpq : ¬ p ∣ q.card ^ 2 - 1) {X : Type} [Group X]
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSelH p T := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨ψ⟩⟩ := exists_native_model_twisted
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv
  have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
  have hK2 : Nat.card K = (2 ^ q.exponent) ^ 2 := by
    rw [hq2] at hK
    exact hK
  have hσ2 : ∀ c, σ c = c ^ (2 ^ q.exponent) := by
    rw [hq2] at hσ
    exact hσ
  rw [hqc] at hq4 hpq
  exact ⟨↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), inferInstance, inferInstance,
    ⟨e.trans ψ⟩, modelSelH_of_triv (modelSelQ_twistedE6 q.exponent_pos hK2 σ hσ2 hq4 hp hp2)
      (hT q.exponent hq4 K hK2 σ hσ2 p hp hp2 hpq)⟩

theorem t263SelWP_e6THard4_of
    (hT : TwE6CompTriv) : T263SelWP t263GE6THard4 := by
  refine t263SelWP_of_modelH (fun p hp hp2 X _ h => ?_)
    (fun p hp hp2 Ω _ _ S x hSn hSq hSp hcat hxp hInn => ?_)
  · obtain ⟨i, hi, ⟨e⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | twistedE6 q =>
        obtain ⟨hq2, hq4, hpq⟩ := hi
        exact exists_modelSelH_twE6_cat hT hp hp2 q hv hq2 hq4 hpq e
      | _ => exact hi.elim
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  · refine inducesInnerMod_e6Inner hp hp2 hSn hSq hSp (S10.catalogIs_imp ?_ hcat) hxp hInn
    intro i hi
    cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d <;> simp only [t263GE6THard4, t263GE6Inner, onLie] at hi ⊢ <;>
        first
          | exact hi.elim
          | exact ⟨hi.1, fun h3 => hi.2.2 (h3.1 ▸ three_dvd_card_sq_sub_one hi.1)⟩
    | cyclic r hr => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
