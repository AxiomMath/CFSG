module

public import CFSG.CGT.T75A.OuterConj
public import CFSG.CGT.T75A.Transitive
public import CFSG.CGT.T75A.KleinFour
public import CFSG.CGT.Timmesfeld75.BenderInputs3

public section

namespace CFSG.CGT.T75A

open CFSG.BenderSuzuki (PSU3Model)
open CFSG.CGT.Timmesfeld75 (statedClassicalModel_psu3_of_mulEquiv conjSubgroup)

theorem outer_involution_root_pair_of_mulEquiv {D : Type} [Group D] [Finite D] {f : ℕ}
    (hf : 2 ≤ f) (e : D ≃* PSU3Model f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) {S : Sylow 2 D}
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    (∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype, α x = x) ∧
      ∃ S' : Sylow 2 D, (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
          (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype ∧
        ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype, α x = x :=
  outer_involution_root_pair hf (statedClassicalModel_psu3_of_mulEquiv hf e) α hα hαout hαT

theorem outer_involutions_conj_of_mulEquiv {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (e : D ≃* PSU3Model f) {α β : MulAut D} (hα : orderOf α = 2) (hβ : orderOf β = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range)
    (hβout : β ∉ (MulAut.conj : D →* MulAut D).range) : IsConj α β :=
  outer_involutions_conj hf (statedClassicalModel_psu3_of_mulEquiv hf e) hα hβ hαout hβout

theorem inner_involution_eq_conj_root_of_mulEquiv {D : Type} [Group D] [Finite D] {f : ℕ}
    (hf : 2 ≤ f) (e : D ≃* PSU3Model f) {S : Sylow 2 D} (α : MulAut D) (hαα : α * α = 1)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    ∃ t ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α = MulAut.conj t :=
  inner_involution_eq_conj_root_map hf (statedClassicalModel_psu3_of_mulEquiv hf e) α hαα hin hαT

theorem exists_normalizer_conj_root_of_mulEquiv {D : Type} [Group D] [Finite D] {f : ℕ}
    (hf : 2 ≤ f) (e : D ≃* PSU3Model f) {S S' S'' : Sylow 2 D}
    (h' : (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (h'' : (Subgroup.center (S'' : Subgroup D)).map (S'' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    ∃ g ∈ (S : Subgroup D), g ∈ Subgroup.normalizer
        (((Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype : Subgroup D) : Set D) ∧
      conjSubgroup g ((Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype) =
        (Subgroup.center (S'' : Subgroup D)).map (S'' : Subgroup D).subtype :=
  exists_normalizer_conj_root hf (statedClassicalModel_psu3_of_mulEquiv hf e) h' h''

theorem klein_four_root_pair_of_mulEquiv {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (e : D ≃* PSU3Model f) {S S' : Sylow 2 D}
    (hTT' : (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
      (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    {α β : MulAut D} (hα : α * α = 1) (hβ : β * β = 1) (hc : α * β = β * α)
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (hαT' : ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype)
    (hβT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      β x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype)
    (hβT' : ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype,
      β x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype) :
    α = 1 ∨ β = 1 ∨ α = β :=
  klein_four_root_pair hf (statedClassicalModel_psu3_of_mulEquiv hf e) hTT' hα hβ hc hαT hαT'
    hβT hβT'

end CFSG.CGT.T75A
