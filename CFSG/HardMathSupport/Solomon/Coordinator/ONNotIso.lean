module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma56
public import CFSG.Sporadic.ON
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem card_onan_group :
    Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group = 460815505920 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b' : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.ONan).Group := b
  rw [← Nat.card_congr b'.toEquiv]
  exact CFSG.Sporadic.ON.card_ON

theorem inputONNotIso_holds :
    LocalBalance.Lemma56Ns.InputONNotIso := by
  have h := card_onan_group
  have hA : ∀ n : ℕ, 2 ≤ n →
      Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    intro n hn
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e⟩
    have := Nat.card_congr e.toEquiv
    rw [h, hA 6 (by norm_num)] at this
    norm_num [Nat.factorial] at this
  · rintro ⟨e⟩
    have := Nat.card_congr e.toEquiv
    rw [h, hA 7 (by norm_num)] at this
    norm_num [Nat.factorial] at this
  · rintro ⟨e⟩
    have hc := Nat.card_congr e.toEquiv
    have hle := CFSG.Sporadic.Bridge.M22.tauCeti_finite_card_le.2
    rw [h] at hc
    have : (460815505920 : ℕ) ≤ 443520 := hc ▸ hle
    norm_num at this

end CFSG.HardMathSupport.Solomon.Coordinator
