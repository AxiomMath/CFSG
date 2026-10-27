module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Sylow
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Spor

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem i1431SporSurv_of_noOrders
    (hZ : ∀ s : TauCeti.SporadicName, SporL2Pair s 5 →
      Subgroup.center (NativeSporadic.Carrier s) = ⊥)
    (hInn : ∀ s : TauCeti.SporadicName, SporL2Pair s 5 →
      ∀ ψ : MulAut (NativeSporadic.Carrier s), ψ ^ 3 = 1 →
        ∃ x : NativeSporadic.Carrier s, MulAut.conj x = ψ)
    (h65 : ∀ s : TauCeti.SporadicName, SporL2Pair s 4 → NoOrder 65 (NativeSporadic.Carrier s))
    (h186 : ∀ s : TauCeti.SporadicName, SporL2Pair s 5 →
      NoOrder 186 (NativeSporadic.Carrier s)) : I1431SporSurv := by
  intro name q0 hpair S _ _ ⟨e⟩ ψ hψ3 hψ1 A hA hL2
  rcases hpair with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact not_typeL2_four_of_noOrder65
      (noOrder_of_mulEquiv e (h65 name (Or.inl ⟨rfl, hn⟩))) A hL2
  · have hZS : Subgroup.center S = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have : e z ∈ Subgroup.center (NativeSporadic.Carrier name) := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        obtain ⟨g', rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul, hz g']
      rw [hZ name (Or.inr ⟨rfl, hn⟩), Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (e.injective (this.trans (map_one e).symm))
    have hψ' : (MulAut.congr e ψ) ^ 3 = 1 := by rw [← map_pow, hψ3, map_one]
    obtain ⟨x', hx'⟩ := hInn name (Or.inr ⟨rfl, hn⟩) _ hψ'
    have hinn : ∃ x : S, MulAut.conj x = ψ := by
      refine ⟨e.symm x', ?_⟩
      apply (MulAut.congr e).injective
      rw [← hx']
      ext g
      simp [MulAut.congr_apply, MulAut.conj_apply]
    exact not_typeL2_five_of_noOrder186 hZS (noOrder_of_mulEquiv e (h186 name (Or.inr ⟨rfl, hn⟩)))
      hψ3 hψ1 hinn A hA.1 hL2

end CFSG.HardMathSupport.Dickson.Sec6.I1431
