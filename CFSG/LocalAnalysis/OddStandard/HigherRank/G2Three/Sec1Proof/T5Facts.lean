module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.Words5

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def g23T5 (m : G23Model G) : Subgroup G := closure (gen5 m '' {s | s < 7})

structure G23T5Facts (m : G23Model G) : Prop where
  F_normal : ((frameOf m).F.subgroupOf (g23T5 m)).Normal
  F_isE : IsE 3 (frameOf m).F
  card_T5 : Nat.card (g23T5 m) = 1344
  cen_B : cen (frameOf m).B = closure {(frameOf m).b₁ * (frameOf m).b₂, (frameOf m).z}
  cen_B_isE : IsE 2 (cen (frameOf m).B)
  card_B : Nat.card (frameOf m).B = 32
  card_normIn_B : Nat.card (normIn (g23T5 m) (frameOf m).B) = 192
  B_S3 : SecProp (normIn (g23T5 m) (frameOf m).B) (frameOf m).B
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
  B_sylow : ∀ T : Subgroup G, IsSylowIn 3 (normIn (g23T5 m) (frameOf m).B) T →
    ActsRegularly T (cen (frameOf m).B) ⊥ ∧
      ActsRegularly T (closure {(frameOf m).b₁, (frameOf m).a₁ * (frameOf m).a₂ * (frameOf m).h₀})
        (cen (frameOf m).B)
  F_GL3 : SecProp (g23T5 m) (frameOf m).F
    (fun Y _ _ _ => Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
  S_sylow : IsSylowIn 2 (g23T5 m) (frameOf m).S
  S_no_complement : ∀ P : Subgroup G, P ≤ (frameOf m).S → P ⊓ (frameOf m).F = ⊥ →
    Nat.card P * Nat.card (frameOf m).F ≠ Nat.card (frameOf m).S
  F_S3 : SecProp (centEl (g23T5 m) (frameOf m).z) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
  F_sylow : ∀ T : Subgroup G, IsSylowIn 3 (centEl (g23T5 m) (frameOf m).z) T →
    ActsRegularly T (frameOf m).F (frameOf m).Z ∧ ActsRegularly T (frameOf m).A (frameOf m).F
  Y1_conj : ∃ t ∈ g23T5 m,
    cen (frameOf m).B ⊔ closure {(frameOf m).h₀} = conjSub t (frameOf m).E
  nine_conj_E : ∃ Ws : List (Subgroup G), Ws.Nodup ∧ Ws.length = 9 ∧
    ∀ W ∈ Ws, (∃ t ∈ g23T5 m, W = conjSub t (frameOf m).E) ∧ (frameOf m).z ∈ W

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
