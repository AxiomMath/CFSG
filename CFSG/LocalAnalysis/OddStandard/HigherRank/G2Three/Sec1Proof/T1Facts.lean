module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def g23H (m : G23Model G) : Subgroup G :=
  (frameOf m).K₁ ⊔ (frameOf m).K₂ ⊔ closure {(frameOf m).h₀}

@[expose] def g23T1 (m : G23Model G) : Subgroup G :=
  closure {(frameOf m).u₁, (frameOf m).b₁, (frameOf m).u₂, (frameOf m).b₂, (frameOf m).h₀,
    (frameOf m).σ}

structure G23T1Facts (m : G23Model G) : Prop where
  z_order : orderOf (frameOf m).z = 2
  card_H : Nat.card (g23H m) = 576
  H_cent_z : ∀ h ∈ g23H m, h * (frameOf m).z = (frameOf m).z * h
  centIn_H_F : centIn (g23H m) (frameOf m).F = (frameOf m).F
  K1_iso : Nonempty (↥(frameOf m).K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  K2_iso : Nonempty (↥(frameOf m).K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
  K1_normal : (frameOf m).K₁ ≤ g23H m ∧ ((frameOf m).K₁.subgroupOf (g23H m)).Normal
  K2_normal : (frameOf m).K₂ ≤ g23H m ∧ ((frameOf m).K₂.subgroupOf (g23H m)).Normal
  K_comm : ∀ u ∈ (frameOf m).K₁, ∀ v ∈ (frameOf m).K₂, u * v = v * u
  K_inter : (frameOf m).K₁ ⊓ (frameOf m).K₂ = (frameOf m).Z
  pCore1 : pCoreOf 2 (frameOf m).K₁ = closure {(frameOf m).a₁, (frameOf m).b₁}
  pCore2 : pCoreOf 2 (frameOf m).K₂ = closure {(frameOf m).a₂, (frameOf m).b₂}
  X1_sylow : IsSylowIn 3 (frameOf m).K₁ (frameOf m).X₁
  X2_sylow : IsSylowIn 3 (frameOf m).K₂ (frameOf m).X₂
  h0_inv1 : ∀ y ∈ (frameOf m).X₁, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹
  h0_inv2 : ∀ y ∈ (frameOf m).X₂, (frameOf m).h₀ * y * (frameOf m).h₀⁻¹ = y⁻¹
  sigma_K1 : conjSub (frameOf m).σ (frameOf m).K₁ = (frameOf m).K₂
  F_cent_sigma : ∀ f ∈ (frameOf m).F, (frameOf m).σ * f = f * (frameOf m).σ
  cen_S : cen (frameOf m).S = (frameOf m).Z
  cen_A : cen (frameOf m).A = (frameOf m).Z
  normIn_H_A : normIn (g23H m) (frameOf m).A = g23H m
  normIn_H_S : normIn (g23H m) (frameOf m).S = (frameOf m).S
  normIn_H_B : normIn (g23H m) (frameOf m).B = (frameOf m).S
  A_frob : SecProp (g23H m) (frameOf m).A (fun Y _ _ _ => IsFrobeniusOfOrder 18 Y)
  A_orbits : ∀ T : Subgroup G, IsSylowIn 3 (g23H m) T →
    IsOrbitMod T (frameOf m).Z
      ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) \ ((frameOf m).Z : Set G)) ∧
    IsOrbitMod T (frameOf m).Z
      ((closure {(frameOf m).a₂, (frameOf m).b₂} : Set G) \ ((frameOf m).Z : Set G)) ∧
    IsOrbitMod T (frameOf m).Z ((frameOf m).A \
      ((closure {(frameOf m).a₁, (frameOf m).b₁} : Set G) ∪
        (closure {(frameOf m).a₂, (frameOf m).b₂} : Set G)))
  centIn_H_cen_B : centIn (g23H m) (cen (frameOf m).B) = (frameOf m).B
  card_E : Nat.card (frameOf m).E = 8
  elemAb_E : IsElemAbelian 2 (frameOf m).E
  centIn_H_E : centIn (g23H m) (frameOf m).E = (frameOf m).E
  card_normIn_H_E : Nat.card (normIn (g23H m) (frameOf m).E) = 192
  fix_E : ∀ e ∈ (frameOf m).E, e ∉ zpowers (frameOf m).z →
    ∃ k ∈ normIn (g23H m) (frameOf m).E, k * e ≠ e * k
  E_S3 : SecProp (normIn (g23H m) (frameOf m).E) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
  E_trans : ∀ u ∈ (frameOf m).E, u ∉ (frameOf m).Z → ∀ v ∈ (frameOf m).E, v ∉ (frameOf m).Z →
    ∃ k ∈ normIn (g23H m) (frameOf m).E, k * u * k⁻¹ = v
  E_sylow : ∀ T : Subgroup G, IsSylowIn 3 (normIn (g23H m) (frameOf m).E) T →
    ActsRegularly T (frameOf m).E (frameOf m).Z ∧ ActsRegularly T (frameOf m).A (frameOf m).E
  Y2_conj : ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂, (frameOf m).b₁ * (frameOf m).a₂,
    (frameOf m).z} = conjSub h (frameOf m).E
  Y3_conj : ∃ h ∈ g23H m, closure {(frameOf m).a₁ * (frameOf m).b₂,
    (frameOf m).a₁ * (frameOf m).b₁ * (frameOf m).a₂, (frameOf m).z} = conjSub h (frameOf m).F
  card_T1 : Nat.card (g23T1 m) = 1152
  T1_le_cent : g23T1 m ≤ centEl ⊤ (frameOf m).z
  T1_S3S3 : SecProp (g23T1 m) (frameOf m).A
    (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
  commMod_A : {g : G | g ∈ g23T1 m ∧ ∀ a ∈ (frameOf m).A, ⁅a, g⁆ ∈ (frameOf m).Z} =
    ((frameOf m).A : Set G)
  commMod_EF : {g : G | g ∈ g23T1 m ∧ ∀ y ∈ (frameOf m).E ⊔ (frameOf m).F, ⁅y, g⁆ ∈ (frameOf m).Z} =
    ((frameOf m).A : Set G)

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab
