module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
public import CFSG.Yardstones.Md42047359a2a.Definitions

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open TauCeti CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem congr_pow_ne_one {S T : Type*} [Group S] [Group T] (e : S ≃* T) {β : MulAut S} {p : ℕ}
    (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    MulAut.congr e β ^ p = 1 ∧ MulAut.congr e β ≠ 1 := by
  refine ⟨by rw [← map_pow, hβ, map_one], fun h => hβ1 ?_⟩
  exact (MulAut.congr e).injective (h.trans (map_one _).symm)

theorem perfectInLayer_untw_cat {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {c : PrimePower → LieTypeIndex}
    (hB : CFSG.TauCetiBridge.Even.UntwistedBridgeAll τ c) (q : PrimePower) (hv : (c q).Valid)
    (hG2 : τ = .G2 → 3 ≤ q.card) {p : ℕ} (hmon : MonomialToralAt τ p) {S : Type} [Group S]
    (e : S ≃* (CFSGIndex.lie ⟨c q, hv⟩).Group) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p)
    (β : MulAut S) (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : PerfectInLayer β := by
  obtain ⟨K, _, _, hK, -, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup hB q hv
  let e' := e.trans eK
  refine perfectInLayer_of_congr e' β ?_
  obtain ⟨hβ', hβ1'⟩ := congr_pow_ne_one e' hβ hβ1
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK, PrimePower.card_def]
    intro h
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h))
  rcases hτ with rfl | rfl | h | h | h
  · exact perfectInLayer_exc_FG (Or.inr rfl) (fun _ => hK ▸ hG2 rfl) hp hp2 hpK hmon _ hβ' hβ1'
  · exact perfectInLayer_exc_FG (Or.inl rfl) (fun h => absurd h (by decide)) hp hp2 hpK hmon _
      hβ' hβ1'
  · exact perfectInLayer_exc_E (Or.inl h) hp hp2 hpK hmon _ hβ' hβ1'
  · exact perfectInLayer_exc_E (Or.inr (Or.inl h)) hp hp2 hpK hmon _ hβ' hβ1'
  · exact perfectInLayer_exc_E (Or.inr (Or.inr h)) hp hp2 hpK hmon _ hβ' hβ1'

theorem lieSemisimpleCentExceptional_of_five (h65 : MonomialToralAt Tag.E6 5)
    (h75 : MonomialToralAt Tag.E7 5) :
    CFSG.Yardstones.Md42047359a2a.LieSemisimpleCentExceptional := by
  intro S _ _ _ _ idx hF he p hp hp2 hpc β hβp hβ1
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  have hmon : ∀ {τ : Tag}, (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      MonomialToralAt τ p := fun hτ => monomialToralAt_exc h65 h75 hτ hp hp2
  cases d with
  | E6 q =>
    exact perfectInLayer_untw_cat (Or.inr (Or.inr (Or.inl rfl)))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv (fun h => absurd h (by decide))
      (hmon (by simp)) e hp hp2 ((LieTypeIndex.characteristic_E6 q) ▸ hpc) β hβp hβ1
  | E7 q =>
    exact perfectInLayer_untw_cat (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv (fun h => absurd h (by decide))
      (hmon (by simp)) e hp hp2 ((LieTypeIndex.characteristic_E7 q) ▸ hpc) β hβp hβ1
  | E8 q =>
    exact perfectInLayer_untw_cat (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv (fun h => absurd h (by decide))
      (hmon (by simp)) e hp hp2 ((LieTypeIndex.characteristic_E8 q) ▸ hpc) β hβp hβ1
  | F4 q =>
    exact perfectInLayer_untw_cat (Or.inr (Or.inl rfl))
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv (fun h => absurd h (by decide))
      (hmon (by simp)) e hp hp2 ((LieTypeIndex.characteristic_F4 q) ▸ hpc) β hβp hβ1
  | G2 q =>
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    exact perfectInLayer_untw_cat (Or.inl rfl)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv (fun _ => hr)
      (hmon (by simp)) e hp hp2 ((LieTypeIndex.characteristic_G2 q) ▸ hpc) β hβp hβ1
  | twistedE6 q =>
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
    let e' := e.trans eK
    refine perfectInLayer_of_congr e' β ?_
    obtain ⟨hβ', hβ1'⟩ := congr_pow_ne_one e' hβp hβ1
    exact perfectInLayer_exc_twE6 q.prime_p q.exponent_pos hK σ hσ hp hp2
      ((LieTypeIndex.characteristic_twistedE6 q) ▸ hpc) (hmon (by simp)) _ hβ' hβ1'
  | trialityD4 q =>
    obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
    let e' := e.trans eK
    refine perfectInLayer_of_congr e' β ?_
    obtain ⟨hβ', hβ1'⟩ := congr_pow_ne_one e' hβp hβ1
    exact perfectInLayer_exc_triD4 q.prime_p q.exponent_pos hK σ hσ hp hp2
      ((LieTypeIndex.characteristic_trialityD4 q) ▸ hpc) (hmon (by simp)) _ hβ' hβ1'
  | _ => simp [CFSG.Yardstones.Md42047359a2a.lieFamily] at hF

theorem lieSemisimpleCentExceptional :
    CFSG.Yardstones.Md42047359a2a.LieSemisimpleCentExceptional :=
  lieSemisimpleCentExceptional_of_five monomialToralAt_E6_five monomialToralAt_E7_five

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
