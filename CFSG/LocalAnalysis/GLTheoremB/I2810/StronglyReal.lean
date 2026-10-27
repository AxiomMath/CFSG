module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
public import CFSG.LieType.ChevTwo.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealV
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealAut
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealInd
import CFSG.LocalAnalysis.GLTheoremB.I2810.StronglyRealFour
import CFSG.Assembly.ComponentTypeDefs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.LieType.ChevTwo
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section ActionOnV
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem strongly_real_small {V : Type} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a)
    (h2 : ∀ v : V, v * v = 1) {τ y : MulAut V} (hτ : τ * τ = 1) (hinv : τ * y * τ⁻¹ = y⁻¹)
    (hy : Odd (orderOf y)) (hidx : (fixV' (Subgroup.zpowers τ)).index ≤ 4) :
    orderOf y = 1 ∨ orderOf y = 3 ∨ orderOf y = 5 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  exact strongly_real_small_comm h2 hτ hinv hy hidx

theorem inverts_to_aut (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S) (ha2 : a ^ 2 = 1)
    {P : ℕ → Prop} (hinv : Inverts W K a P) :
    ∃ y : MulAut ↥(vOf W K S), Odd (orderOf y) ∧ (∃ m, Odd m ∧ P m ∧ m ∣ orderOf y) ∧
      vAct hR ⟨a, Subgroup.mem_sup_right haS⟩ * y * (vAct hR ⟨a, Subgroup.mem_sup_right haS⟩)⁻¹ =
        y⁻¹ :=
  SRAut.inverts_to_aut_aux h hR haS ha2 hinv

theorem offender_fix_index (h : Setup28 W K S) (hR : Red28 W K S) {A : Subgroup X}
    (hA : Off28 W K S A) (hc : Nat.card ↥(indAut W K A) = 4) {a : X} (haA : a ∈ A) :
    (fixV' (Subgroup.zpowers (vAct hR ⟨a, Subgroup.mem_sup_right (hA.isMax.1 haA)⟩))).index ≤ 4 :=
  SRAut.offender_fix_index_aux h hR hA hc haA

end ActionOnV

section CaseFour
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem hyp4_inverts_five (h : Setup28 W K S) (h4 : Hyp28Four W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) : Inverts W K a (fun m => m = 5) :=
  SRFour.hyp4_inverts_five_aux h h4 haS hna

theorem inverts_five_contra (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (ha2 : a ^ 2 = 1) (htr : TransvOn (vOf W K S) a) (hinv : Inverts W K a (fun m => m = 5)) :
    False :=
  SRAut.inverts_five_contra_aux h hR haS ha2 htr hinv

end CaseFour

section CaseOneRank
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem hyp1_inverts_big (hInv : Chev2RankTwoInverts) (h : Setup28 W K S) (h1 : Hyp28One W K S)
    {A : Subgroup X} (hA : Off28 W K S A) (hc : Nat.card ↥(indAut W K A) = 4) :
    ∃ a ∈ A, a ∉ kerAct W K S ∧ Inverts W K a (fun m => 5 < m) :=
  SRInd.hyp1_inverts_big_aux hInv h h1 hA hc

end CaseOneRank

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
