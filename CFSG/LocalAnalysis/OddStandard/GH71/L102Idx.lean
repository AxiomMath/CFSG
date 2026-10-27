module

public import CFSG.LocalAnalysis.OddStandard.GH71.Thompson
public import CFSG.LocalAnalysis.OddStandard.GH71.CUFacts

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG

variable {G : Type} [Group G]

theorem isMulCommutative_sup {A B : Subgroup G} (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  rintro x (hx | hx) y (hy | hy) -
  · exact hA x hx y hy
  · exact hAB x hx y hy
  · exact (hAB y hy x hx).symm
  · exact hB x hx y hy

theorem relIndex_sup_eq_of_le_normalizer' {A N : Subgroup G}
    (h : A ≤ normalizer (N : Set G)) : N.relIndex (A ⊔ N) = N.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A N h).toEquiv.symm

theorem comm_of_isMulCommutative {D : Subgroup G} (hD : IsMulCommutative ↥D) :
    ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (hD.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem relIndex_map_conj {D₀ E : Subgroup G} {h : G} (hh : h ∈ normalizer (E : Set G)) :
    (D₀.map (MulAut.conj h).toMonoidHom).relIndex E = D₀.relIndex E := by
  conv_lhs => rw [← map_conj_eq_of_mem_normalizer hh]
  exact relIndex_map_map_of_injective _ _ (MulAut.conj h).injective

variable [Finite G]

theorem relIndex_le_three {P D D₀ E : Subgroup G} (hD : IsMaxAbelianIn P D) (hD₀D : D₀ ≤ D)
    (hidx : D₀.relIndex D = 3) (hEP : E ≤ P) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hED₀ : ∀ e ∈ E, ∀ d ∈ D₀, e * d = d * e) : D₀.relIndex E ≤ 3 := by
  have hDab := comm_of_isMulCommutative hD.2.1
  have hA : IsMulCommutative ↥(E ⊔ D₀) := isMulCommutative_sup hEab
    (fun a ha b hb => hDab a (hD₀D ha) b (hD₀D hb)) hED₀
  have hAP : E ⊔ D₀ ≤ P := sup_le hEP (hD₀D.trans hD.1)
  have hle : Nat.card ↥(E ⊔ D₀) ≤ Nat.card D := hD.2.2 _ hAP hA
  have hEN : E ≤ normalizer (D₀ : Set G) := fun e he =>
    Ctx71.centralizer_le_normalizer' D₀ (mem_centralizer_iff.mpr fun d hd => (hED₀ e he d hd).symm)
  have h1 : D₀.relIndex D * Nat.card ↥(D₀ ⊓ D) = Nat.card D := relIndex_mul_card D₀ D
  have h2 : D₀.relIndex (E ⊔ D₀) * Nat.card ↥(D₀ ⊓ (E ⊔ D₀)) = Nat.card ↥(E ⊔ D₀) :=
    relIndex_mul_card D₀ (E ⊔ D₀)
  rw [inf_of_le_left hD₀D, hidx] at h1
  rw [inf_of_le_left le_sup_right, relIndex_sup_eq_of_le_normalizer' hEN] at h2
  have hpos : 0 < Nat.card D₀ := Nat.card_pos
  have : D₀.relIndex E * Nat.card D₀ ≤ 3 * Nat.card D₀ := by rw [h2, h1]; exact hle
  exact Nat.le_of_mul_le_mul_right this hpos

end CFSG.OddStandard.GH71
