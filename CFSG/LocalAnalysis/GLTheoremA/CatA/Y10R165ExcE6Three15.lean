module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.LieType.Steinberg.Isogeny


theorem e6Model165At_three : E6Model165At 3 := by
  intro F hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  by_cases hqZ : q ∣ Nat.card (e6Isogeny F).ker
  · exact e6Model165At_three_of_dvd F n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv hqZ
  · exact e6Model165At_three_of_coprime F n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv hqZ

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
