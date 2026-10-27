module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitElem
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup
open CFSG.ComponentClassification.HSFLit (ElemAbelianTwo eq_one_or_eq_of_mem_zpowers)

variable {G : Type} [Group G] [Finite G]

theorem elem_sup_zpowers {V : Subgroup G} (hV : ElemAbelianTwo V) {g : G} (hg2 : g ^ 2 = 1)
    (hgc : ∀ a ∈ V, g * a = a * g) : ElemAbelianTwo (V ⊔ zpowers g) := by
  by_cases hgV : g ∈ V
  · rwa [sup_eq_left.mpr (zpowers_le.mpr hgV)]
  · exact (hV.sup_zpowers hg2 hgV hgc).1

theorem elem_zpowers {a : G} (ha : a ^ 2 = 1) : ElemAbelianTwo (zpowers a) := by
  have := elem_sup_zpowers (ElemAbelianTwo.bot (G := G)) ha
    (fun x hx => by rw [mem_bot.mp hx, one_mul, mul_one])
  rwa [bot_sup_eq] at this

omit [Finite G] in
theorem commute_of_mem_sup {g a b : G} (ha : g * a = a * g) (hb : g * b = b * g) {x : G}
    (hx : x ∈ zpowers a ⊔ zpowers b) : g * x = x * g := by
  have hle : zpowers a ⊔ zpowers b ≤ centralizer ({g} : Set G) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ha.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hb.symm))
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem elem_E4 {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    ElemAbelianTwo (zpowers a ⊔ zpowers b) :=
  elem_sup_zpowers (elem_zpowers ha) hb fun x hx => by
    rcases eq_one_or_eq_of_mem_zpowers ha hx with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hab.symm

theorem elem_E8 {a b c : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) :
    ElemAbelianTwo (zpowers a ⊔ zpowers b ⊔ zpowers c) :=
  elem_sup_zpowers (elem_E4 ha hb hab) hc fun _ hx => commute_of_mem_sup hac.symm hbc.symm hx

theorem mem_E4_cases {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    {x : G} (hx : x ∈ zpowers a ⊔ zpowers b) : x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  by_cases hba : b ∈ zpowers a
  · rw [sup_eq_left.mpr (zpowers_le.mpr hba)] at hx
    rcases eq_one_or_eq_of_mem_zpowers ha hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb])
    rcases ((elem_zpowers ha).sup_zpowers hb hba fun y hy => by
        rcases eq_one_or_eq_of_mem_zpowers ha hy with rfl | rfl
        · rw [one_mul, mul_one]
        · exact hab.symm).2.1 x hx with h | h
    · rcases eq_one_or_eq_of_mem_zpowers ha h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases eq_one_or_eq_of_mem_zpowers ha h with h' | h'
      · right; right; left
        rw [← hbinv]
        exact eq_inv_of_mul_eq_one_left h'
      · right; right; right
        calc x = x * b * b⁻¹ := by group
          _ = a * b := by rw [h', hbinv]

theorem card_E8 {a b c : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hba : b ≠ a) (hcE : c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧ c ≠ a * b) :
    Nat.card (zpowers a ⊔ zpowers b ⊔ zpowers c : Subgroup G) = 8 := by
  have h1 : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  have hbn : b ∉ zpowers a := fun h =>
    (eq_one_or_eq_of_mem_zpowers ha h).elim hb1 hba
  have h2 := ((elem_zpowers ha).sup_zpowers hb hbn fun y hy => by
    rcases eq_one_or_eq_of_mem_zpowers ha hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hab.symm).2.2
  have hcn : c ∉ zpowers a ⊔ zpowers b := fun h => by
    rcases mem_E4_cases ha hb hab h with h' | h' | h' | h'
    · exact hcE.1 h'
    · exact hcE.2.1 h'
    · exact hcE.2.2.1 h'
    · exact hcE.2.2.2 h'
  have h3 := ((elem_E4 ha hb hab).sup_zpowers hc hcn fun _ hx =>
    commute_of_mem_sup hac.symm hbc.symm hx).2.2
  rw [h3, h2, h1]

theorem card_E4 {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hba : b ≠ a) : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = 4 := by
  have h1 : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  have hbn : b ∉ zpowers a := fun h =>
    (eq_one_or_eq_of_mem_zpowers ha h).elim hb1 hba
  have h2 := ((elem_zpowers ha).sup_zpowers hb hbn fun y hy => by
    rcases eq_one_or_eq_of_mem_zpowers ha hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact hab.symm).2.2
  rw [h2, h1]

omit [Finite G] in
theorem mem_E8_left {a b c : G} : a ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
  mem_sup_left (mem_sup_left (mem_zpowers a))

omit [Finite G] in
theorem mem_E8_mid {a b c : G} : b ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
  mem_sup_left (mem_sup_right (mem_zpowers b))

omit [Finite G] in
theorem mem_E8_right {a b c : G} : c ∈ zpowers a ⊔ zpowers b ⊔ zpowers c :=
  mem_sup_right (mem_zpowers c)

omit [Finite G] in
theorem E8_le {a b c : G} {H : Subgroup G} (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    zpowers a ⊔ zpowers b ⊔ zpowers c ≤ H :=
  sup_le (sup_le (zpowers_le.mpr ha) (zpowers_le.mpr hb)) (zpowers_le.mpr hc)

end CFSG.ComponentClassification.HSDihedral
