module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightPlus
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem aschbacherTwoEight_holds : AschbacherTwoEight := by
  intro V _ _ hV2 E A n hn hAN hoff hnat hZ
  rcases hnat with h | h
  · exact TwoEight.twoEight_plus n hV2 hn hAN hoff h hZ
  · have : NeZero n := ⟨by omega⟩
    exact TwoEight.twoEight_minus n hn hAN hoff h hZ

end CFSG.CGT.PushingUpLit.CGT6
