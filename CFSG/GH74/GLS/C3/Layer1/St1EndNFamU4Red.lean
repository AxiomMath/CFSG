module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFamQ3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Single

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Lem711Cfg

variable {X : Type} [Group X] [Finite X] {L K : Subgroup X} {x y : X}

theorem u4_rowS {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h : Lem711Cfg X L K x y)
    (hL : LieModel ↥L .PSU 4 p f) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = (p ^ f) ^ 2 ∧
      Nonempty (↥K ≃* projectiveSL 2 E) := by
  have := h.normal
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSU hL
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hst
  have hc := h.isComponentOf_centralizer
  have hcomp : CFSG.Assembly.IsComponentOf K (L ⊓ centralizer ({x} : Set X)) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hc (le_inf h.K_le hc.1) inf_le_right
  exact IVK.su4_single_rowS h.soc.simple h.exists_noncomm h.centralizer_eq_bot h.hx
    h.x_mem_commutator hcomp h.smallSource hp hp2 hf hF e

end Lem711Cfg

theorem lem711_u4_of_three (h43 : Lem711Empty (fun X _ => LieModel X .PSU 4 3 1))
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    Lem711Empty (fun X _ => LieModel X .PSU 4 p f) := by
  intro X _ _ L K x y h hL
  obtain ⟨E, _, _, hE, ⟨eK⟩⟩ := h.u4_rowS hp hp2 hf hL
  obtain ⟨rfl, rfl⟩ := h.q_eq_three_of_proj2 hp hp2 hf hE eK
  exact h43 X L K x y h hL

end CFSG.GH74.GLS
