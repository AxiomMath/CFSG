module

public import Certificates.Data.Kernel.Co2Eleven
public import CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenInputs
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Co2ElevenSnd.Main

public section

namespace CFSG.KC.Co2Eleven

open CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

theorem elevenK_sound {D : Co2ElevenData} {m bound A B : Nat} {WV WVI R : Nat → Nat}
    {szs : List Nat}
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : CFSG.Sporadic.Fi23.Native.slpOK D.words = true)
    (h : elevenK A B WV WVI R D.words.toList D.is D.ih D.chain.toList m 11 bound szs = true) :
    co2ElevenOK D m bound = true := by
  exact Snd.co2ElevenOK_of hA hB hs h

theorem sevenK_sound {D : Co2SevenData} {m bound A B : Nat} {WV WVI R : Nat → Nat}
    {szs : List Nat}
    (hA : co2T 0 = (CFSG.KS.Raw.unpack 2300 12 A).map UInt32.ofNat)
    (hB : co2T 1 = (CFSG.KS.Raw.unpack 2300 12 B).map UInt32.ofNat)
    (hs : CFSG.Sporadic.Fi23.Native.slpOK D.words = true) (hid : D.id.size = 8)
    (h : elevenK A B WV WVI R D.words.toList D.is D.ih D.chain.toList m 7 bound szs = true)
    (hc : centK WV D.words.toList D.id.toList D.is D.ih 7 = true) :
    co2SevenOK D m bound = true := by
  exact Snd.co2SevenOK_of hA hB hs hid h hc

end CFSG.KC.Co2Eleven

end
