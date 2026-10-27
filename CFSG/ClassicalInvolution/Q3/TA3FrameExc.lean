module

public import CFSG.ClassicalInvolution.Q3.TA3FrameLayer
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.Blueprint CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem layerExcludesQ8_of_shape (hF : TwoSubgroupsFourGenerated X) {t : X} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hF₁ : Odd (Nat.card F₁))
    (hF₂ : Odd (Nat.card F₂)) (h4₁ : 4 ≤ Nat.card F₁) (h4₂ : 4 ≤ Nat.card F₂)
    (Sh : Shape ↥(Subgroup.centralizer ({t} : Set X)) F₁ F₂) : LayerExcludesQ8 X t := by
  set C := Subgroup.centralizer ({t} : Set X)
  let e₁ : ↥(Sh.I₁.map C.subtype) ≃* SL(2, F₁) :=
    (Sh.I₁.equivMapOfInjective C.subtype C.subtype_injective).symm.trans Sh.e₁
  let e₂ : ↥(Sh.I₂.map C.subtype) ≃* SL(2, F₂) :=
    (Sh.I₂.equivMapOfInjective C.subtype C.subtype_injective).symm.trans Sh.e₂
  have hn₁ : ((Sh.I₁.map C.subtype).subgroupOf C).Normal := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact Sh.normal₁
  have hn₂ : ((Sh.I₂.map C.subtype).subgroupOf C).Normal := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
    exact Sh.normal₂
  refine layerExcludesQ8_of_sl2Pair hF
    (isComponentOf_of_normal (Subgroup.map_subtype_le _) hn₁ (isQuasisimple_of_equiv_sl2 h4₁ e₁))
    (isComponentOf_of_normal (Subgroup.map_subtype_le _) hn₂ (isQuasisimple_of_equiv_sl2 h4₂ e₂))
    le_rfl le_rfl ?_ hF₁ hF₂ e₁ e₂
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact congrArg Subtype.val (Sh.comm a ha b hb)

theorem layerExcludesQ8_g2 (hF : TwoSubgroupsFourGenerated X) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hm : LieModel X .G2 0 p f) (t : X) (ht : orderOf t = 2) :
    LayerExcludesQ8 X t := by
  obtain ⟨F, _, _, Sh, hcard, -⟩ := GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hm t ht
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  exact layerExcludesQ8_of_shape hF hodd hodd (by omega) (by omega) Sh

theorem layerExcludesQ8_d4 (hF : TwoSubgroupsFourGenerated X) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hm : LieModel X .trialityD4 0 p f) (t : X)
    (ht : orderOf t = 2) : LayerExcludesQ8 X t := by
  obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, -⟩ :=
    GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hm t ht
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h₁ : Odd (Nat.card F₁) := by rw [hc₁]; exact hq.pow
  have h₂ : Odd (Nat.card F₂) := by rw [hc₂]; exact hq
  have h4₁ : 4 ≤ Nat.card F₁ := by
    rw [hc₁]
    calc 4 ≤ p ^ f := by omega
      _ ≤ (p ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  exact layerExcludesQ8_of_shape hF h₁ h₂ h4₁ (by rw [hc₂]; omega) Sh

end CFSG.ClassicalInvolution.Q3.TA3.Frame
