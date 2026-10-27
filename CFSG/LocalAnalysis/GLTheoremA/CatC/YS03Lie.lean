module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Two2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def KD1912TwoLieAt (p : ℕ) (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, k2Lie p d.1 → P d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ A : Subgroup (MulAut S),
        IsElemAbelian p A → IsTwoPrimaryWeaklyLocallyBalanced p 1 A

theorem kd1912TwoLieAt_union {p : ℕ} {P Q : TauCeti.LieTypeIndex → Prop}
    (hP : KD1912TwoLieAt p P) (hQ : KD1912TwoLieAt p Q) : KD1912TwoLieAt p (fun d => P d ∨ Q d) := by
  intro S _ _ hS hnc d hd hPQ e A hA
  rcases hPQ with h | h
  · exact hP S hS hnc d hd h e A hA
  · exact hQ S hS hnc d hd h e A hA

theorem kd1912TwoLie_of_cover {p : ℕ} {P : TauCeti.LieTypeIndex → Prop}
    (hcov : ∀ d, k2Lie p d → P d) (h : KD1912TwoLieAt p P) : KD1912TwoLie p := by
  intro S _ _ hS hnc d hd e A hA
  exact h S hS hnc d hd (hcov _ hd) e A hA

@[expose] def LieL2 : TauCeti.LieTypeIndex → Prop
  | .A 1 _ => True
  | _ => False

@[expose] def LieL3 : TauCeti.LieTypeIndex → Prop
  | .A 2 _ => True
  | _ => False

@[expose] def LieU3 : TauCeti.LieTypeIndex → Prop
  | .twistedA 2 _ => True
  | _ => False

@[expose] def LieRows3 : TauCeti.LieTypeIndex → Prop
  | .B 2 _ | .B 3 _ | .D 4 _ | .G2 _ | .twistedA 3 _ | .twistedA 4 _ | .twistedA 5 _
  | .trialityD4 _ | .tits | .reeF4 _ => True
  | _ => False

@[expose] def LieRows5 : TauCeti.LieTypeIndex → Prop
  | .tits | .reeF4 _ | .suzuki _ => True
  | _ => False

@[expose] def KD1912TwoL2 : Prop := KD1912TwoLieAt 3 LieL2

@[expose] def KD1912TwoL3 : Prop := KD1912TwoLieAt 3 LieL3

@[expose] def KD1912TwoU3 : Prop := KD1912TwoLieAt 3 LieU3

@[expose] def KD1912TwoRows3 : Prop := KD1912TwoLieAt 3 LieRows3

@[expose] def KD1912TwoRows5 : Prop := KD1912TwoLieAt 5 LieRows5

@[expose] def KD1912TwoL33 : Prop := KD1912TwoLieAt 13 LieL3

theorem lieCover_three {d : TauCeti.LieTypeIndex} (h : k2Lie 3 d) :
    LieL2 d ∨ LieL3 d ∨ LieU3 d ∨ LieRows3 d := by
  unfold k2Lie at h
  split at h <;> simp_all [LieL2, LieL3, LieU3, LieRows3]

theorem lieCover_five {d : TauCeti.LieTypeIndex} (h : k2Lie 5 d) : LieRows5 d := by
  unfold k2Lie at h
  split at h <;> simp_all [LieRows5]

theorem lieCover_thirteen {d : TauCeti.LieTypeIndex} (h : k2Lie 13 d) : LieL3 d := by
  unfold k2Lie at h
  split at h <;> simp_all [LieL3]

theorem kd1912TwoLie_three (h2 : KD1912TwoL2) (h3 : KD1912TwoL3) (hu : KD1912TwoU3)
    (hr : KD1912TwoRows3) : KD1912TwoLie 3 :=
  kd1912TwoLie_of_cover (fun _ hd => lieCover_three hd)
    (kd1912TwoLieAt_union h2 (kd1912TwoLieAt_union h3 (kd1912TwoLieAt_union hu hr)))

theorem kd1912TwoLie_five (h : KD1912TwoRows5) : KD1912TwoLie 5 :=
  kd1912TwoLie_of_cover (fun _ hd => lieCover_five hd) h

theorem kd1912TwoLie_thirteen (h : KD1912TwoL33) : KD1912TwoLie 13 :=
  kd1912TwoLie_of_cover (fun _ hd => lieCover_thirteen hd) h

end CFSG.LocalAnalysis.GLTheoremA
