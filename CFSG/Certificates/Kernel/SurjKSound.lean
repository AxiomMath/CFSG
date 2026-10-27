module

public import Certificates.Data.Kernel.SurjK
public import Certificates.Data.CFSGNative.Bridge.SurjD
import CFSG.Certificates.Kernel.SurjKWordsProved

public section

namespace CFSG.KC.SurjK

open CFSG.Sporadic.Bridge.SurjD.Native

theorem wordsK_sound {cs : List Char} {L : List (List Int)} (h : wordsK cs L = true) :
    parseWords (String.ofList cs) = L.toArray :=
  wordsK_sound_proved h

end CFSG.KC.SurjK

end
