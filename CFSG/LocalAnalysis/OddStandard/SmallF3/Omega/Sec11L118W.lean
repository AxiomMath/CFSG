module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11_isD8_card {C : Subgroup G} (h : IsD8 C) : Nat.card C = 8 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]

theorem sec11_isD8_nonabelian {C : Subgroup G} (h : IsD8 C) :
    ∃ a ∈ C, ∃ b ∈ C, a * b ≠ b * a := by
  obtain ⟨e⟩ := h
  have hne : (DihedralGroup.r 1 * DihedralGroup.sr 0 : DihedralGroup 4) ≠
      DihedralGroup.sr 0 * DihedralGroup.r 1 := by decide
  refine ⟨(e.symm (DihedralGroup.r 1) : G), (e.symm (DihedralGroup.r 1)).2,
    (e.symm (DihedralGroup.sr 0) : G), (e.symm (DihedralGroup.sr 0)).2, fun hab => hne ?_⟩
  have hab' : e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.sr 0) =
      e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.r 1) := Subtype.ext hab
  have := congrArg e hab'
  simpa using this

private theorem sec11_d8_centralizer_aux :
    ∀ T Z c : DihedralGroup 4, T * T = 1 → Z * Z = 1 → (∀ x : DihedralGroup 4, x * Z = Z * x) →
      T ≠ 1 → Z ≠ 1 → T ≠ Z → c * T = T * c → c = 1 ∨ c = T ∨ c = Z ∨ c = T * Z := by
  decide +kernel

theorem sec11_isD8_centralizer {C : Subgroup G} (hC : IsD8 C) {t z : G} (htC : t ∈ C)
    (hzC : z ∈ C) (ht2 : t * t = 1) (hz2 : z * z = 1) (hzc : ∀ c ∈ C, c * z = z * c)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (htz : t ≠ z) {c : G} (hc : c ∈ C) (hct : c * t = t * c) :
    c ∈ zpowers t ⊔ zpowers z := by
  obtain ⟨e⟩ := hC
  set t' : ↥C := ⟨t, htC⟩ with ht'
  set z' : ↥C := ⟨z, hzC⟩ with hz'
  set c' : ↥C := ⟨c, hc⟩ with hc'
  have h1 : e t' * e t' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext ht2
  have h2 : e z' * e z' = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    exact Subtype.ext hz2
  have h3 : ∀ x : DihedralGroup 4, x * e z' = e z' * x := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc y y.2)
  have h4 : e t' ≠ 1 := fun h => ht1 (by simpa [ht'] using e.injective (h.trans (map_one e).symm))
  have h5 : e z' ≠ 1 := fun h => hz1 (by simpa [hz'] using e.injective (h.trans (map_one e).symm))
  have h6 : e t' ≠ e z' := fun h => htz (by simpa [ht', hz'] using e.injective h)
  have h7 : e c' * e t' = e t' * e c' := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hct
  rcases sec11_d8_centralizer_aux (e t') (e z') (e c') h1 h2 h3 h4 h5 h6 h7 with h | h | h | h
  · have : c' = 1 := e.injective (h.trans (map_one e).symm)
    have hc1 : c = 1 := congrArg Subtype.val this
    rw [hc1]
    exact Subgroup.one_mem _
  · have : c' = t' := e.injective h
    have hct' : c = t := congrArg Subtype.val this
    rw [hct']
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  · have : c' = z' := e.injective h
    have hcz' : c = z := congrArg Subtype.val this
    rw [hcz']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  · have : c' = t' * z' := e.injective (h.trans (map_mul e t' z').symm)
    have hctz : c = t * z := congrArg Subtype.val this
    rw [hctz]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

private theorem sec11_inf_Q_eq {A Q : Subgroup G} {z : G}
    (hAQ : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a)
    (hQz : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c ∈ zpowers z) (hzA : z ∈ A) (hzQ : z ∈ Q) :
    A ⊓ Q = zpowers z := by
  apply le_antisymm
  · intro c hc
    exact hQz c hc.2 (fun q hq => hAQ c hc.1 q hq)
  · rw [Subgroup.zpowers_le]
    exact ⟨hzA, hzQ⟩

theorem sec11_card_CQ_le_card_XQ [Finite G] {C X Q : Subgroup G} {z : G}
    (hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c) (hXQ : ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x)
    (hQz : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c ∈ zpowers z) (hzC : z ∈ C) (hzX : z ∈ X)
    (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hC8 : Nat.card C = 8)
    (hX8 : 8 ≤ Nat.card X) :
    Nat.card ↥(C ⊔ Q) ≤ Nat.card ↥(X ⊔ Q) := by
  have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hC := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute C Q hCQ).1
  have hX := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute X Q hXQ).1
  rw [sec11_inf_Q_eq hCQ hQz hzC hzQ, hzcard, hC8] at hC
  rw [sec11_inf_Q_eq hXQ hQz hzX hzQ, hzcard] at hX
  have h8 : 8 * Nat.card Q ≤ Nat.card X * Nat.card Q := Nat.mul_le_mul_right _ hX8
  omega

end CFSG.OddStandard.SmallF3.Omega
