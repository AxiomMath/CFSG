module

public import CFSG.ClassicalInvolution.Q3.TL4S289Z
public import CFSG.ClassicalInvolution.Q3.TL4S289L2
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3MW
public import CFSG.ClassicalInvolution.Q3.TL4Thm6
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.Q3.TL4MF165A

public section

namespace CFSG.ComponentClassification.QuaternionComponent

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.MilestoneAssembly
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

section Wired

theorem thm6RBelow_of_large₃₃
    (hGH : GH74SectionalModels) {n : ℕ} {Y : Type} [Group Y]
    [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} (hL : Q3.TightLargeHypR 3 n Y R S t) :
    Q3.TL4.Thm6RBelow 3 n :=
  Q3.TL4.Induct.thm6RBelow_mono (Nat.le_succ n) (Q3.TL4.thm6RBelow_three_of_simple
    (Q3.TL4.thm6SimpleLe_of_leaves hGH Q3.TL4.smallLeaves6_holds hL.below hL.tbelow))

theorem star289ZFree₃₃
    (hGH : GH74SectionalModels) (hTw : Q3.TL4.SecIdE3S3NoTwist) :
    ∀ n, Q3.TL4.TightStar289ZFreeR 3 n := fun n Y _ _ R S t hL =>
  Q3.TL4.tightStar289ZFreeR_of
    (fun M _ _ hM => Q3.TL4.model165Aut_proved M (hM.imp (fun h => ⟨h.1, Or.inl h.2⟩) id))
    (Q3.TL4.secIdExitS3Ident_of (Q3.TL4.secIdE3MuS3_of Q3.TL4.secIdE3S3M12Center_proved hTw)
      Q3.TL4.secIdE3L2NoStar_proved n (thm6RBelow_of_large₃₃ hGH hL)) Y R S t hL

end Wired

end CFSG.ComponentClassification.QuaternionComponent
