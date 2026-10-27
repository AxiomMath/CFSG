module

public import CFSG.GF2Type.Smith1979W3.SuzInput
public import CFSG.Sporadic.SuzRecog.SuzL34.StandardData
public import CFSG.Sporadic.SuzRecog.SuzL34.LocalDataOf

public section

namespace CFSG.GF2Type.Smith1979W3

open CFSG.Sporadic.SuzRecog.SuzL34Cert

theorem suzL34DataInput_of (hF1 : F1Prop) (hF1M : F1MProp) (hF2 : F2Prop)
    (hF3 : F3Prop) (hF4 : F4Prop) (hF5 : F5Prop) (hF6 : F6Prop) (hF6b : F6bProp)
    (hF7 : F7Prop) (hF8 : F8Prop) (hF9 : F9Prop) (hF11 : F11Prop) :
    SuzL34DataInput := by
  intro G _ _ _ hKP S hw hE hΩ hNWC
  obtain ⟨D⟩ := CFSG.Sporadic.SuzRecog.SuzL34.exists_localData S hw hE hΩ hNWC
  exact D.suzL34Data hF1 hF1M hF2 hF3 hF4 hF5 hF6 hF6b hF7 hF8 hF9 hF11

end CFSG.GF2Type.Smith1979W3
