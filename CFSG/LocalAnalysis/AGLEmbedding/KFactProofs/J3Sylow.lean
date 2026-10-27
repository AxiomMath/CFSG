module

public import CFSG.Sporadic.Bridge.J3Surj
public import Certificates.Certificate9435

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Sylow

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native

theorem sylow_check : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∀ T : Sylow 3 J, ∃ (H : Subgroup J) (t₁ t₂ s : J)
        (Z : Fin 9 → J) (w₁ w₂ : List Bool), Subgroup.closure ({t₁, t₂} : Set J) = T ∧
          IsCoatom H ∧ LocalData H t₁ t₂ s Z w₁ w₂ :=
  Certificates.certificate9435

end CFSG.AGLEmbedding.KFactProofs.J3Sylow

namespace CFSG.AGLEmbedding

open KFactProofs.J3Sylow CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen

theorem kFactJ3Sylow :
    KFactJ3Sylow := by
  intro J _ _ ⟨eJ⟩ T
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let f := eJ.trans b.symm
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup J := MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) f
  have hJcard : Nat.card J = 50232960 := by
    rw [Nat.card_congr f.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  obtain ⟨H, t₁, t₂, s, Z, w₁, w₂, hT, hH, D⟩ := sylow_check J ⟨eJ⟩ hsimple hJcard T
  have hfacts := D.facts hH
  rw [hT] at hfacts
  exact hfacts

end CFSG.AGLEmbedding
