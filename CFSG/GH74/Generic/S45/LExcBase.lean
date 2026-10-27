module

public import CFSG.GH74.Generic.S45.LOrd
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def Q8Order (X : Type) [Group X] : Prop :=
  ∃ q : ℕ, 5 ≤ q ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ Nat.card X * 2 = q * (q ^ 2 - 1)

@[expose] def SmallQ8 (X : Type) [Group X] : Prop :=
  SmallType X ∧ Q8Order X

theorem q8Order_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) : Q8Order X ↔ Q8Order Y := by
  have h : Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv
  unfold Q8Order
  rw [h]

theorem smallQ8_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) : SmallQ8 X ↔ SmallQ8 Y :=
  and_congr (smallType_congr e) (q8Order_congr e)

theorem not_smallQ8_of_not_smallType {X : Type} [Group X] (h : ¬ SmallType X) : ¬ SmallQ8 X :=
  fun hs => h hs.1

theorem not_q8Order_of_card_dvd {X : Type} [Group X] {c : ℕ} (hdvd : Nat.card X ∣ c)
    (hc : CFSG.GH74.Generic.S45.OrdClosable c) : ¬ Q8Order X := by
  rintro ⟨q, hq5, hq8, hcard⟩
  refine hc q hq5 hq8 ?_
  have h : q * (q ^ 2 - 1) / 2 = Nat.card X := by omega
  rwa [h]

variable {C : Type} [Group C]

theorem not_smallQ8_of_conj {ψ β γ : MulAut C} (hψ : ψ * β * ψ⁻¹ = γ)
    (h : ∀ K : Subgroup C, Assembly.IsComponentOf K (fixedSubgroup γ) → ¬ SmallQ8 K)
    {K : Subgroup C} (hK : Assembly.IsComponentOf K (fixedSubgroup β)) : ¬ SmallQ8 K := by
  have hc : MulAut.congr ψ β = ψ * β * ψ⁻¹ := MulEquiv.ext fun _ => rfl
  have hfix := fixedSubgroup_congr ψ β
  rw [hc] at hfix
  have h1 : Assembly.IsComponentOf (K.map ψ.toMonoidHom) (fixedSubgroup (ψ * β * ψ⁻¹)) :=
    hfix ▸ isComponentOf_map_of_equiv ψ hK
  rw [hψ] at h1
  intro hs
  exact h _ h1 ((smallQ8_congr (ψ.subgroupMap K)).1 hs)

@[expose] def NoSmallQ8Component (C : Type) [Group C] : Prop :=
  ∀ α : MulAut C, α ^ 2 = 1 → α ≠ 1 → ∀ K : Subgroup C,
    Assembly.IsComponentOf K (fixedSubgroup α) → ¬ SmallQ8 K

theorem noSmallQ8Component_of_equiv {C' : Type} [Group C'] (e : C ≃* C')
    (h : NoSmallQ8Component C') : NoSmallQ8Component C := by
  intro α hα hα1 K hK
  set α' := MulAut.congr e α with hα'
  have hfix := fixedSubgroup_congr e α
  have hα'2 : α' ^ 2 = 1 := by rw [hα', ← map_pow, hα, map_one]
  have hα'1 : α' ≠ 1 := fun h1 => hα1 ((MulAut.congr e).injective (by rw [← hα', h1, map_one]))
  have hK' : Assembly.IsComponentOf (K.map e.toMonoidHom) (fixedSubgroup α') := by
    rw [hfix]
    exact isComponentOf_map_of_equiv e hK
  intro hs
  exact h α' hα'2 hα'1 _ hK' ((smallQ8_congr (e.subgroupMap K)).1 hs)

end CFSG.ComponentClassification.ExcSelector
