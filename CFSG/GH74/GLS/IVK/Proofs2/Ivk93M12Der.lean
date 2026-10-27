module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12XLevel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Core

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

theorem ivk93M12Der_proved : Ivk93M12Der := by
  intro X _ _ x hx hxJ hs hn hT P _ _ zc hP ρ hρ hodd hρx
  obtain ⟨hy, ⟨ρJ, hoddJ, hρJy, hN⟩, haut⟩ := xlevel x hx hxJ hs hn hT zc hP ρ hρ hodd hρx
  exact data_of_core hs hn hy hP ρJ hoddJ hρJy hN haut

end CFSG.GH74.GLS.IVK.Proofs2
