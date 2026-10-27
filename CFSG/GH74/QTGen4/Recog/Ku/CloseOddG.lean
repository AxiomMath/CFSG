module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseOddE
public import CFSG.GH74.QTGen4.Recog.Ku.CloseOddF

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

theorem KuA6Model.frame_product_bound [Finite G] {E W V2 N : Subgroup G} {z : G}
    (Ψ : KuA6Model E W V2 N z) (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x w δ₁ δ₂ : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3)
    (hw : orderOf w = 3) (hwx : w * x = x * w) (hwX : w ∉ Subgroup.zpowers x)
    (hδ₁ : δ₁ * δ₁ = 1) (hδ₁x : δ₁ * x * δ₁⁻¹ = x⁻¹)
    (hδ₂ : δ₂ * δ₂ = 1) (hδ₂x : δ₂ * x * δ₂⁻¹ = x⁻¹) :
    (δ₁ * δ₂) ^ 2 ∈ Subgroup.zpowers x ∨ (δ₁ * δ₂) ^ 3 = 1 := by
  classical
  have hp : δ₁ * δ₂ ∈ Subgroup.centralizer ({x} : Set G) :=
    mul_mem_centralizer_of_inverts hδ₁x hδ₂x
  have hQ := Ψ.cenQuot_alt hHN hxH hx hw hwx hwX
  set p : cenQuot x := QuotientGroup.mk
    (⟨δ₁ * δ₂, hp⟩ : ↥(Subgroup.centralizer ({x} : Set G))) with hpdef
  have key : p * p = 1 ∨ p ^ 3 = 1 :=
    alt_four_five_odd_product hQ (cenConj hδ₁x) (cenConj hδ₂x) (cenConj_cenConj hδ₁x hδ₁)
      (cenConj_cenConj hδ₂x hδ₂) (Ψ.cenConj_not_inner hHN hxH hx hδ₁x)
      (Ψ.cenConj_not_inner hHN hxH hx hδ₂x) (cenConj_cenConj_mul hδ₁x hδ₂x hp)
  have h27 : ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
    rw [card_centralizer_eq_three_mul hx]
    rcases hQ with h4 | h5
    · obtain ⟨e⟩ := h4
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    · obtain ⟨e⟩ := h5
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
  have hpx : δ₁ * δ₂ * x = x * (δ₁ * δ₂) :=
    Subgroup.mem_centralizer_singleton_iff.mp hp
  rcases key with h | h
  · left
    have h' : (QuotientGroup.mk (⟨δ₁ * δ₂, hp⟩ * ⟨δ₁ * δ₂, hp⟩ :
        ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x) = 1 := by
      rw [QuotientGroup.mk_mul]; exact h
    rw [cenQuot_mk_eq_one_iff] at h'
    rw [pow_two]
    exact h'
  · right
    have h' : (QuotientGroup.mk (⟨δ₁ * δ₂, hp⟩ ^ 3 :
        ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x) = 1 := by
      rw [QuotientGroup.mk_pow]; exact h
    rw [cenQuot_mk_eq_one_iff] at h'
    exact cube_eq_one_of_mem_zpowers hx hw hwx hwX hpx h27 h'

end CFSG.GH74.QTGen4.Ku
