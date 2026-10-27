module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.LBase

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {m : G23Model G}

theorem G23LCtx.cen_S (X : G23LCtx m) : cen (frameOf m).S = (frameOf m).Z := X.f1.cen_S

theorem G23LCtx.cen_A (X : G23LCtx m) : cen (frameOf m).A = (frameOf m).Z := X.f1.cen_A

theorem G23LCtx.normIn_A (X : G23LCtx m) : normIn m.L (frameOf m).A = g23H m := by
  have hcen : cen (frameOf m).A = zpowers (frameOf m).z := by
    rw [X.cen_A, SFrame.Z]
  have hn : normIn m.L (frameOf m).A
      = normIn (centEl m.L (frameOf m).z) (frameOf m).A :=
    normIn_eq_normIn_centEl hcen X.z_ne_one X.z_sq
  rw [X.centEl_z] at hn
  rw [hn]
  exact X.f1.normIn_H_A

theorem G23LCtx.normIn_S (X : G23LCtx m) : normIn m.L (frameOf m).S = (frameOf m).S := by
  have hcen : cen (frameOf m).S = zpowers (frameOf m).z := by
    rw [X.cen_S, SFrame.Z]
  have hn : normIn m.L (frameOf m).S
      = normIn (centEl m.L (frameOf m).z) (frameOf m).S :=
    normIn_eq_normIn_centEl hcen X.z_ne_one X.z_sq
  rw [X.centEl_z] at hn
  rw [hn]
  exact X.f1.normIn_H_S

theorem G23LCtx.normIn_A_inf_B (X : G23LCtx m) :
    normIn m.L (frameOf m).A ⊓ normIn m.L (frameOf m).B = (frameOf m).S := by
  rw [X.normIn_A]
  have hH : g23H m ⊓ normIn m.L (frameOf m).B = normIn (g23H m) (frameOf m).B := by
    rw [normIn, normIn, ← inf_assoc, inf_eq_left.mpr (g23H_le m)]
  rw [hH]
  exact X.f1.normIn_H_B

theorem G23LCtx.A_frob (X : G23LCtx m) :
    SecProp (g23H m) (frameOf m).A (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) := X.f1.A_frob

theorem G23LCtx.A_orbits (X : G23LCtx m) :
    ∀ T : Subgroup G, IsSylowIn 3 (g23H m) T →
      IsOrbitMod T (frameOf m).Z
        ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) \ ((frameOf m).Z : Set G)) ∧
      IsOrbitMod T (frameOf m).Z
        ((closure {(frameOf m).a₂, (frameOf m).b₂} : Set G) \ ((frameOf m).Z : Set G)) ∧
      IsOrbitMod T (frameOf m).Z ((frameOf m).A \
        ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
          (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G))) := X.f1.A_orbits

theorem G23LCtx.fact18_1 (X : G23LCtx m) :
    normIn m.L (frameOf m).S = normIn m.L (frameOf m).A ⊓ normIn m.L (frameOf m).B ∧
      normIn m.L (frameOf m).S = (frameOf m).S :=
  ⟨by rw [X.normIn_A_inf_B, X.normIn_S], X.normIn_S⟩

theorem G23LCtx.fact18_2 (X : G23LCtx m) :
    normIn m.L (frameOf m).A = centEl m.L (frameOf m).z ∧
      SecProp (normIn m.L (frameOf m).A) (frameOf m).A
        (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y) ∧
      ∀ T : Subgroup G, IsSylowIn 3 (normIn m.L (frameOf m).A) T →
        IsOrbitMod T (frameOf m).Z
          ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) \ ((frameOf m).Z : Set G)) ∧
        IsOrbitMod T (frameOf m).Z
          ((closure {(frameOf m).a₂, (frameOf m).b₂} : Set G) \ ((frameOf m).Z : Set G)) ∧
        IsOrbitMod T (frameOf m).Z ((frameOf m).A \
          ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
            (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G))) := by
  rw [X.normIn_A, X.centEl_z]
  exact ⟨rfl, X.A_frob, X.A_orbits⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
