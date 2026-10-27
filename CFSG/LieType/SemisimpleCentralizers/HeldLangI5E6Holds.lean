module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5E6Tw

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

section Certificates

theorem kd264I5UniversalExc_holds : KD264I5UniversalExc := by
  intro e k hk hexc L _ _ hL β hβ3 hout
  obtain ⟨d, hd⟩ := e
  cases d with
  | E6 q =>
    obtain ⟨h3q, rfl⟩ := hk
    exact kd264I5Universal_E6 q hd h3q L hL β hβ3 hout
  | twistedE6 q =>
    obtain ⟨h3q, rfl⟩ := hk
    exact kd264I5Universal_twE6 q hd h3q L hL β hβ3 hout
  | _ => exact absurd hexc (by rintro ⟨q', h | h⟩ <;> simp at h)

end Certificates

end CFSG.LieType.SemisimpleCentralizers.HeldLang
