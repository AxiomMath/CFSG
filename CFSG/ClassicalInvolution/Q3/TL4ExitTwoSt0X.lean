module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0D
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0E
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0Q
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0K
public import CFSG.ClassicalInvolution.Q3.TL4Res2FXDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem socleType_of_exitSec {n : ℕ} (h6 : Thm6RBelow 3 n) (hG : Nat.card G < n)
    (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤)
    (hWg : (⨆ x : W, conjSub (x : G) K) = W)
    (hex : PhilipHall.Frame.Thm4Twin.F2.ExitSec W K hKW z hz) :
    SocleType (↥L₀ ⧸ Subgroup.center ↥L₀) := by
  have hLW := le_of_subnormal hc hK hz hKW hWs
  rcases exitShape_of_exitSec hc hK hz hKW hWs hWg hex with
    h4 | ⟨S, hd, hcl, hE2, ⟨he, h3⟩ | hm | ⟨-, h4⟩⟩
  · exact socleType_of_twinE4 hc hWs hLW h4
  · exact socleType_of_e3a h6 hG hc hLW hd hcl hE2 he h3
  · exact socleType_of_center_M12 hc hLW hm
  · exact socleType_of_center_E4 hc hLW h4

theorem exitTwoClassR_of_rows {n : ℕ} (h6 : Thm6RBelow 3 n) (hL2 : SocleTransitive IsL2Sq)
    (hL3 : SocleTransitive IsL3Ge5) (hU3 : SocleTransitive IsU3Ge5)
    (hU33 : SocleTransitive IsU33) (hM12 : SocleTransitive IsM12)
    (hSp6 : SocleTransitive IsSp62) (hO8 : SocleTransitive IsO8p2) : ExitTwoClassR n := by
  intro G _ _ hG J L L₀ hc K hK z hz W hKW hWs hWg hex
  rcases socleType_of_exitSec h6 hG hc hK hz hKW hWs hWg hex with h | h | h | h | h | h | h
  · exact false_of_socle (fun e hA => IsL2Sq.of_mulEquiv e hA) hL2 hc h
  · exact false_of_socle (fun e hA => IsL3Ge5.of_mulEquiv e hA) hL3 hc h
  · exact false_of_socle (fun e hA => IsU3Ge5.of_mulEquiv e hA) hU3 hc h
  · exact false_of_socle (fun e hA => IsU33.of_mulEquiv e hA) hU33 hc h
  · exact false_of_socle (fun e hA => IsM12.of_mulEquiv e hA) hM12 hc h
  · exact false_of_socle (fun e hA => IsSp62.of_mulEquiv e hA) hSp6 hc h
  · exact false_of_socle (fun e hA => IsO8p2.of_mulEquiv e hA) hO8 hc h

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
