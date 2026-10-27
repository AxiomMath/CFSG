module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndNat

public section

namespace CFSG.CGT.PushingUpLit.CGT6.OmegaPlus

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

variable {V : Type} [CommGroup V]

structure PlusSide (G Y D B : Subgroup (MulAut V)) (n : ℕ) : Prop where
  hn : 2 ≤ n
  yg : Y ≤ G
  dy : D ≤ Y
  by_ : B ≤ Y
  sup : D ⊔ B = Y
  inf : D ⊓ B = ⊥
  comm : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d
  dsl : Nonempty (↥D ≃* SLq n)
  bsl : Nonempty (↥B ≃* SLq n)
  vsup : fixV Y ⊔ commV Y = ⊤
  vinf : fixV Y ⊓ commV Y = ⊥
  cD : commV D = commV Y
  fD : fixV D = fixV Y
  cdec : ∀ x ∈ G ⊓ Subgroup.centralizer (D : Set (MulAut V)),
    ∃ β ∈ B, ∃ c ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), x = β * c
  ctriv : ∀ c ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), (∃ k : ℕ, c ^ 2 ^ k = 1) →
    ∀ u ∈ commV Y, c u = u
  faith : ∀ y ∈ Y, (∀ u ∈ commV Y, y u = u) → y = 1
  rootfix : ∀ b ∈ B, b ^ 2 = 1 → b ≠ 1 → ∀ β ∈ B, β * b = b * β →
    ∀ v ∈ fixV (Subgroup.zpowers b), β v = v
  fixb : ∀ b ∈ B, b ^ 2 = 1 → b ≠ 1 →
    fixV (Subgroup.zpowers b) = commV (Subgroup.zpowers b) ⊔ fixV Y ∧
      commV (Subgroup.zpowers b) ⊓ fixV Y = ⊥ ∧ commV (Subgroup.zpowers b) ≤ commV Y
  natE : ∀ b ∈ B, b ^ 2 = 1 → b ≠ 1 →
    IsNatSectionBy (slAct n) D (commV (Subgroup.zpowers b)) ⊥

end CFSG.CGT.PushingUpLit.CGT6.OmegaPlus
