module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.F18a

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

set_option quotPrecheck false in
local notation "D5" => (t5G ()).tab
local notation "I5" => idx5

theorem G23LCtx.F_GL3 (X : G23LCtx m) :
    SecProp (g23T5 m) (frameOf m).F
      (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :=
  X.f5.F_GL3

theorem G23LCtx.S_sylow_T5 (X : G23LCtx m) : IsSylowIn 2 (g23T5 m) (frameOf m).S :=
  X.f5.S_sylow

theorem G23LCtx.F_normal_T5 (X : G23LCtx m) :
    ((frameOf m).F.subgroupOf (g23T5 m)).Normal :=
  X.f5.F_normal

theorem G23LCtx.S_no_complement (X : G23LCtx m) :
    ∀ P : Subgroup G, P ≤ (frameOf m).S → P ⊓ (frameOf m).F = ⊥ →
      Nat.card P * Nat.card (frameOf m).F ≠ Nat.card (frameOf m).S :=
  X.f5.S_no_complement

theorem G23LCtx.F_nonsplit (X : G23LCtx m) : ¬ SplitsOver (g23T5 m) (frameOf m).F :=
  not_splitsOver_of_sylow X.F_normal_T5 X.S_sylow_T5 (F_le_S (frameOf m).toSFrame)
    X.S_no_complement

theorem G23LCtx.normIn_A_inf_F (X : G23LCtx m) :
    normIn m.L (frameOf m).A ⊓ normIn m.L (frameOf m).F =
      centEl (g23T5 m) (frameOf m).z := by
  rw [X.normIn_A, X.normIn_F, ← X.centEl_z]
  exact centEl_inf_eq _ (g23T5_le m)

theorem G23LCtx.F_S3 (X : G23LCtx m) :
    SecProp (centEl (g23T5 m) (frameOf m).z) (frameOf m).A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) :=
  X.f5.F_S3

theorem G23LCtx.F_sylow (X : G23LCtx m) :
    ∀ T : Subgroup G, IsSylowIn 3 (centEl (g23T5 m) (frameOf m).z) T →
      ActsRegularly T (frameOf m).F (frameOf m).Z ∧
        ActsRegularly T (frameOf m).A (frameOf m).F :=
  X.f5.F_sylow

theorem G23LCtx.fact18_5 (X : G23LCtx m) :
    centIn m.L (frameOf m).F = (frameOf m).F ∧
      SecProp (normIn m.L (frameOf m).F) (frameOf m).F
        (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∧
      ¬ SplitsOver (normIn m.L (frameOf m).F) (frameOf m).F ∧
      SecProp (normIn m.L (frameOf m).A ⊓ normIn m.L (frameOf m).F) (frameOf m).A
        (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∧
      ∀ T : Subgroup G, IsSylowIn 3 (normIn m.L (frameOf m).A ⊓ normIn m.L (frameOf m).F) T →
        ActsRegularly T (frameOf m).F (frameOf m).Z ∧
          ActsRegularly T (frameOf m).A (frameOf m).F := by
  rw [X.normIn_A_inf_F, X.normIn_F]
  exact ⟨X.centIn_F, X.F_GL3, X.F_nonsplit, X.F_S3, X.F_sylow⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
