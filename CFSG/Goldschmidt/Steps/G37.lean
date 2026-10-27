module

public import CFSG.Goldschmidt.Steps.G37Lift1
public import CFSG.Goldschmidt.Steps.G3aFStar
public import CFSG.Goldschmidt.Steps.G32Q
public import CFSG.Goldschmidt.Steps.G3b34
public import CFSG.Goldschmidt.Steps.G3b35

public section

namespace CFSG.Goldschmidt

theorem G37_of (h31 : S_G31) (h32Q : S_G32Q) (h33 : S_G33) (h34 : S_G34) (h35 : S_G35) :
    S_G37 := by
  intro G _ _ H A hS hE a haA ha1 X hXH hXa hXE
  exact ⟨G37.part1 h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE ha1,
    fun K hK hKO => G37.part2 h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE hK hKO,
    G37.part3a h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE,
    fun L hL hYL => G37.part3b h31 h32Q h33 h34 h35 hS hE haA hXH hXa hXE hL hYL⟩

theorem G37 :
    S_G37 :=
  G37_of G31 G32Q G33 G34 G35

end CFSG.Goldschmidt
