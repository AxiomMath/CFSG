module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44Two
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import all CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open scoped MatrixGroups commutatorElement

theorem pSL_mem_ZK_iff {a₁ a₂ a₃ a₄ a₅ a₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ ∈ ZK ↔ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ a₄ = 0 ∧ a₅ = 0 := by
  constructor
  · rintro ⟨a, b, c, d, z, ⟨rfl, rfl, rfl, rfl⟩, h⟩
    obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := pSL_eq_pSL_iff.1 h
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact pSL_mem_mSub ⟨rfl, rfl, rfl, rfl⟩

theorem pSL_mul_inv_mem_ZK_iff {c₁ c₂ c₃ c₄ c₅ c₈ d₁ d₂ d₃ d₄ d₅ d₈ : F4} :
    pSL c₁ c₂ c₃ c₄ c₅ c₈ * (pSL d₁ d₂ d₃ d₄ d₅ d₈)⁻¹ ∈ ZK ↔
      c₁ = d₁ ∧ c₂ = d₂ ∧ c₃ = d₃ ∧ c₄ = d₄ ∧ c₅ = d₅ := by
  constructor
  · intro h
    obtain ⟨a, b, c, d, w, ⟨rfl, rfl, rfl, rfl⟩, hw⟩ := h
    rw [mul_inv_eq_iff_eq_mul, pSL_mul, pSL_eq_pSL_iff] at hw
    obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := hw
    exact ⟨by rw [h₁, zero_add], by rw [h₂, zero_add], by rw [h₃, zero_add],
      by rw [h₄]; ring, by rw [h₅]; ring⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨0, 0, 0, 0, c₈ - d₈, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    rw [mul_inv_eq_iff_eq_mul, pSL_mul, pSL_eq_pSL_iff]
    exact ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

theorem pSL_comm_mem_ZK_iff {a₁ a₂ a₃ a₄ a₅ a₈ b₁ b₂ b₃ b₄ b₅ b₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL b₁ b₂ b₃ b₄ b₅ b₈ * (pSL a₁ a₂ a₃ a₄ a₅ a₈)⁻¹ *
        (pSL b₁ b₂ b₃ b₄ b₅ b₈)⁻¹ ∈ ZK ↔ a₂ * b₁ = b₂ * a₁ ∧ a₃ * b₂ = b₃ * a₂ := by
  have e : ∀ x y : SL(4, F4), x * y * x⁻¹ * y⁻¹ = x * y * (y * x)⁻¹ := fun x y => by group
  rw [e, pSL_mul, pSL_mul, pSL_mul_inv_mem_ZK_iff]
  constructor
  · rintro ⟨-, -, -, h₄, h₅⟩
    exact ⟨by linear_combination h₄, by linear_combination h₅⟩
  · rintro ⟨h₄, h₅⟩
    exact ⟨add_comm _ _, add_comm _ _, add_comm _ _, by linear_combination h₄,
      by linear_combination h₅⟩

theorem pSL_mul_self_mem_ZK_iff {a₁ a₂ a₃ a₄ a₅ a₈ : F4} :
    pSL a₁ a₂ a₃ a₄ a₅ a₈ * pSL a₁ a₂ a₃ a₄ a₅ a₈ ∈ ZK ↔ a₂ * a₁ = 0 ∧ a₃ * a₂ = 0 := by
  rw [pSL_mul_self, pSL_mem_ZK_iff]
  simp

theorem comm_of_mem_ZK {z h : SL(4, F4)} (hz : z ∈ ZK) (hh : h ∈ PK) : h * z = z * h := by
  obtain ⟨a, b, c, d, w, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hz
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₈, rfl⟩ := hh
  exact pSL_mul_comm_iff.2 ⟨by ring, by ring, by ring⟩

theorem mem_MK_of_mem_PK {x : SL(4, F4)} (hx : x ∈ PK) (h : x 2 1 = 0) : x ∈ MK := by
  rw [eq_pSL_of_mem_PK hx, h]
  exact mem_MK.2 ⟨_, _, _, _, _, rfl⟩

theorem mem_YK_of_mem_PK {x : SL(4, F4)} (hx : x ∈ PK) (h₁ : x 1 0 = 0) (h₃ : x 3 2 = 0) :
    x ∈ YK := by
  rw [eq_pSL_of_mem_PK hx, h₁, h₃]
  exact ⟨_, _, _, _, rfl⟩

theorem le_MK_or_le_YK {E : Subgroup SL(4, F4)} (hE : E ≤ PK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x 2 1 * y 1 0 = y 2 1 * x 1 0 ∧ x 3 2 * y 2 1 = y 3 2 * x 2 1)
    (hs : ∀ x ∈ E, x 2 1 * x 1 0 = 0 ∧ x 3 2 * x 2 1 = 0) : E ≤ MK ∨ E ≤ YK := by
  by_cases h : ∀ x ∈ E, x 2 1 = 0
  · exact Or.inl fun x hx => mem_MK_of_mem_PK (hE hx) (h x hx)
  simp only [not_forall, exists_prop] at h
  obtain ⟨x, hx, h21⟩ := h
  have h10 : x 1 0 = 0 := (mul_eq_zero.1 (hs x hx).1).resolve_left h21
  have h32 : x 3 2 = 0 := (mul_eq_zero.1 (hs x hx).2).resolve_right h21
  refine Or.inr fun y hy => mem_YK_of_mem_PK (hE hy) ?_ ?_
  · have e := (hc x hx y hy).1
    rw [h10, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_left h21
  · have e := (hc x hx y hy).2
    rw [h32, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right h21

theorem le_MK_or_le_YK_of_elemAb {E : Subgroup SL(4, F4)} (hE : E ≤ PK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : E ≤ MK ∨ E ≤ YK := by
  refine le_MK_or_le_YK hE (fun x hx y hy => ?_) fun x hx => ?_
  · have h := hc x hx y hy
    rw [eq_pSL_of_mem_PK (hE hx), eq_pSL_of_mem_PK (hE hy)] at h
    obtain ⟨h₁, h₂, -⟩ := pSL_mul_comm_iff.1 h
    exact ⟨h₁, h₂⟩
  · have h := hs x hx
    rw [eq_pSL_of_mem_PK (hE hx)] at h
    obtain ⟨h₁, h₂, -⟩ := pSL_mul_self_eq_one_iff.1 h
    exact ⟨h₁, h₂⟩

theorem elemAb_YK : (∀ x ∈ YK, ∀ y ∈ YK, x * y = y * x) ∧ ∀ x ∈ YK, x * x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a₂, a₄, a₅, a₈, rfl⟩ _ ⟨b₂, b₄, b₅, b₈, rfl⟩
    exact pSL_mul_comm_iff.2 ⟨by ring, by ring, by ring⟩
  · rintro _ ⟨a₂, a₄, a₅, a₈, rfl⟩
    exact pSL_mul_self_eq_one_iff.2 ⟨by ring, by ring, by ring⟩

theorem elemAb_mod_MK : (∀ x ∈ MK, ∀ y ∈ MK, x * y * x⁻¹ * y⁻¹ ∈ ZK) ∧ ∀ x ∈ MK, x * x ∈ ZK := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨a, b, c, d, z, rfl⟩ := mem_MK.1 hx
    obtain ⟨a', b', c', d', z', rfl⟩ := mem_MK.1 hy
    exact pSL_comm_mem_ZK_iff.2 ⟨by ring, by ring⟩
  · obtain ⟨a, b, c, d, z, rfl⟩ := mem_MK.1 hx
    exact pSL_mul_self_mem_ZK_iff.2 ⟨by ring, by ring⟩

theorem ZK_le_YK : ZK ≤ YK := by
  rintro _ ⟨a, b, c, d, z, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
  exact ⟨0, 0, 0, z, rfl⟩

theorem eq_YK_of_elemAb {E : Subgroup SL(4, F4)} (hE : E ≤ PK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1)
    (h8 : 2 ^ 8 ≤ Nat.card E) : E = YK := by
  rcases le_MK_or_le_YK_of_elemAb hE hc hs with h | h
  · exact absurd (h8.trans (card_le_of_elemAb h hc hs)) (by norm_num)
  · exact Subgroup.eq_of_le_of_card_ge h (card_YK ▸ h8)

theorem commutator_pSL (w : F4) : ⁅pSL 1 0 0 0 0 0, pSL 0 0 0 0 w 0⁆ = pSL 0 0 0 0 0 w := by
  rw [commutatorElement_def]
  simp only [pSL_inv, pSL_mul]
  rw [pSL_eq_pSL_iff]
  revert w
  decide

theorem commutator_MK : ⁅MK, MK⁆ = ZK := by
  refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) fun z hz => ?_
  · rw [commutatorElement_def]
    exact elemAb_mod_MK.1 x hx y hy
  · obtain ⟨a, b, c, d, w, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hz
    rw [← commutator_pSL]
    exact commutator_mem_commutator (mem_MK.2 ⟨1, 0, 0, 0, 0, rfl⟩)
      (mem_MK.2 ⟨0, 0, w, 0, 0, rfl⟩)

theorem mem_Z₂K_iff {x : SL(4, F4)} :
    x ∈ Z₂K ↔ x ∈ PK ∧ ∀ y ∈ PK, x * y * x⁻¹ * y⁻¹ ∈ ZK := by
  constructor
  · rintro ⟨a, b, c, d, z, ⟨rfl, rfl⟩, rfl⟩
    refine ⟨pSL_mem_PK _ _ _ _ _ _, fun y hy => ?_⟩
    obtain ⟨b₁, b₂, b₃, b₄, b₅, b₈, rfl⟩ := hy
    exact pSL_comm_mem_ZK_iff.2 ⟨by ring, by ring⟩
  · rintro ⟨⟨a₁, a₂, a₃, a₄, a₅, a₈, rfl⟩, h⟩
    obtain ⟨h₁, -⟩ := pSL_comm_mem_ZK_iff.1 (h _ (pSL_mem_PK 1 0 0 0 0 0))
    obtain ⟨h₂, h₂'⟩ := pSL_comm_mem_ZK_iff.1 (h _ (pSL_mem_PK 0 1 0 0 0 0))
    have e₂ : a₂ = 0 := by linear_combination h₁
    have e₁ : a₁ = 0 := by linear_combination -h₂
    have e₃ : a₃ = 0 := by linear_combination h₂'
    subst e₁ e₂ e₃
    exact pSL_mem_mSub ⟨rfl, rfl⟩

theorem exists_sylow_PK : ∃ S : Sylow 2 SL(4, F4), (S : Subgroup SL(4, F4)) = PK := by
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := F4) 2 (n := 4) (by norm_num)
  have h : Nat.card (U : Subgroup SL(4, F4)) = 2 ^ (Nat.card SL(4, F4)).factorization 2 :=
    U.card_eq_multiplicity
  rw [hU, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_unitriangular,
    Nat.card_eq_fintype_card (α := F4), F4.card] at h
  refine ⟨Sylow.ofCard PK ?_, Sylow.coe_ofCard _ _⟩
  rw [card_PK, ← h]
  norm_num

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
