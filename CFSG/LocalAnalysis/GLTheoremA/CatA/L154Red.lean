module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K155XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def L154NIDOn (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K J : Subgroup Γ) (x y : Γ),
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → IsChevSimple 2 (PSimple p K) → catalogIs (PSimple p K) Q →
    x ∈ X → x ^ p = 1 → y ^ p = 1 → x * y = y * x → y ∉ Subgroup.zpowers x →
    x ∈ Subgroup.normalizer (K : Set Γ) → y ∈ Subgroup.normalizer (K : Set Γ) → ¬ CentMod p K x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    y ∈ Subgroup.normalizer (J : Set Γ) → NonInnDiag p y J

@[expose] def L154TD4On (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Γ : Type) [Group Γ] [Finite Γ] (X K J : Subgroup Γ) (x y : Γ),
    CFSG.Open.IsKGroup ↥X → GLAPComponent p X K → IsChevSimple 2 (PSimple p K) → catalogIs (PSimple p K) Q →
    x ∈ X → x ^ p = 1 → y ^ p = 1 → x * y = y * x → y ∉ Subgroup.zpowers x →
    x ∈ Subgroup.normalizer (K : Set Γ) → y ∈ Subgroup.normalizer (K : Set Γ) → ¬ CentMod p K x →
    InnDiagOn p (Subgroup.zpowers x) K → FieldOn p y K →
    GLAPComponent p (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J →
    y ∈ Subgroup.normalizer (J : Set Γ) → ¬ (p = 3 ∧ IsTD4 3 J)

theorem l154NIDOn_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i) (h : L154NIDOn Q') :
    L154NIDOn Q := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := hQ
  exact h p hp hp2 Γ X K J x y hXk hK hKc ⟨i, hsub i hi, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField
    hJ hyJ

theorem l154TD4On_mono {Q Q' : TauCeti.CFSGIndex → Prop} (hsub : ∀ i, Q i → Q' i) (h : L154TD4On Q') :
    L154TD4On Q := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := hQ
  exact h p hp hp2 Γ X K J x y hXk hK hKc ⟨i, hsub i hi, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField
    hJ hyJ

theorem l154NIDOn_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : L154NIDOn Q₁) (h₂ : L154NIDOn Q₂) :
    L154NIDOn (fun i => Q₁ i ∨ Q₂ i) := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact h₂ p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ

theorem l154TD4On_or {Q₁ Q₂ : TauCeti.CFSGIndex → Prop} (h₁ : L154TD4On Q₁) (h₂ : L154TD4On Q₂) :
    L154TD4On (fun i => Q₁ i ∨ Q₂ i) := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hQ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := hQ
  rcases hi with h | h
  · exact h₁ p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact h₂ p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ

@[expose] def l154Lin : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A _ q => q.p = 2 | _ => False

@[expose] def l154Uni : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA _ q => q.p = 2 | _ => False

@[expose] def l154Symp : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B _ q => q.p = 2 | .C _ q => q.p = 2 | _ => False

@[expose] def l154Orth : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D _ q => q.p = 2 | _ => False

@[expose] def l154TwOrth : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedD _ q => q.p = 2 | _ => False

@[expose] def l154Exc : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .E6 q => q.p = 2 | .E7 q => q.p = 2 | .E8 q => q.p = 2 | .F4 q => q.p = 2 | .G2 q => q.p = 2
    | .twistedE6 q => q.p = 2 | .trialityD4 q => q.p = 2
    | .suzuki _ => True | .reeF4 _ => True | .tits => True
    | _ => False

@[expose] def l154AmbU33 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 3 | _ => False

@[expose] def l154AmbAlt (i : TauCeti.CFSGIndex) : Prop :=
  ambiguousChev 2 i ∧ ¬ l154AmbU33 i

@[expose] def l154Chev2 : TauCeti.CFSGIndex → Prop :=
  fun i => (onLie fun d => d.characteristic = 2) i ∨ ambiguousChev 2 i

theorem catalogIs_l154Chev2 {S : Type} [Group S] (h : IsChevSimple 2 S) : catalogIs S l154Chev2 := by
  rcases h with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
  · exact ⟨i, Or.inl hi, e⟩
  · exact ⟨i, Or.inr hi, e⟩

theorem l154_cover (i : TauCeti.CFSGIndex) (h : l154Chev2 i) :
    l154Lin i ∨ l154Uni i ∨ l154Symp i ∨ l154Orth i ∨ l154TwOrth i ∨ l154Exc i ∨ l154AmbAlt i ∨
      l154AmbU33 i := by
  rcases h with h | h
  · cases i with
    | cyclic p hp => simp [onLie] at h
    | alternating n hn => simp [onLie] at h
    | sporadic s => simp [onLie] at h
    | lie d =>
      obtain ⟨t, ht⟩ := d
      cases t <;>
        simp_all [onLie, l154Lin, l154Uni, l154Symp, l154Orth, l154TwOrth, l154Exc]
  · by_cases hu : l154AmbU33 i
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hu))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hu⟩))))))

theorem l154NonInnDiag_of_families (hLin : L154NIDOn l154Lin) (hUni : L154NIDOn l154Uni)
    (hSymp : L154NIDOn l154Symp) (hOrth : L154NIDOn l154Orth) (hTwOrth : L154NIDOn l154TwOrth)
    (hExc : L154NIDOn l154Exc) (hAmbAlt : L154NIDOn l154AmbAlt) (hAmbU33 : L154NIDOn l154AmbU33) :
    L154NonInnDiag := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := catalogIs_l154Chev2 hKc
  rcases l154_cover i hi with h | h | h | h | h | h | h | h
  · exact hLin p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hUni p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hSymp p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hOrth p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hTwOrth p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ
  · exact hExc p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hAmbAlt p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ
  · exact hAmbU33 p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ

theorem l154NotTD4_of_families (hLin : L154TD4On l154Lin) (hUni : L154TD4On l154Uni)
    (hSymp : L154TD4On l154Symp) (hOrth : L154TD4On l154Orth) (hTwOrth : L154TD4On l154TwOrth)
    (hExc : L154TD4On l154Exc) (hAmbAlt : L154TD4On l154AmbAlt) (hAmbU33 : L154TD4On l154AmbU33) :
    L154NotTD4 := by
  intro p hp hp2 Γ _ _ X K J x y hXk hK hKc hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  obtain ⟨i, hi, e⟩ := catalogIs_l154Chev2 hKc
  rcases l154_cover i hi with h | h | h | h | h | h | h | h
  · exact hLin p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hUni p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hSymp p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hOrth p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hTwOrth p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ
  · exact hExc p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ hyJ
  · exact hAmbAlt p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ
  · exact hAmbU33 p hp hp2 Γ X K J x y hXk hK hKc ⟨i, h, e⟩ hxX hxp hyp hcomm hyx hxN hyN hcm hInn hField hJ
      hyJ

end CFSG.LocalAnalysis.GLTheoremA.K155X
