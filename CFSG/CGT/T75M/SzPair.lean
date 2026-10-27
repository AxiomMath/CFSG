module

public import CFSG.CGT.T75M.SzLemma
public import CFSG.CGT.T75M.SzModule
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.CGT.T75M

open CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open scoped commutatorElement

variable {G : Type} [Group G]

structure SzData (T T₁ : Subgroup G) (a : ℕ) : Prop where
  sec3 : Sec3 T T₁
  ha : 1 ≤ a
  iso : ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
    Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* Sz a)


theorem SzData.conj {T T₁ : Subgroup G} {a : ℕ} (hD : SzData T T₁ a) (g : G) :
    SzData (conjSubgroup g T) (conjSubgroup g T₁) a := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.iso
  have hS' : Sec3 (conjSubgroup g T) (conjSubgroup g T₁) := hD.sec3.conj_gen g
  have hX' : conjSubgroup g T ⊔ conjSubgroup g T₁ = conjSubgroup g (T ⊔ T₁) :=
    (conjSubgroup_sup_eq_sup g T T₁).symm
  have hM' : cfgM (conjSubgroup g T) (conjSubgroup g T₁) = conjSubgroup g (cfgM T T₁) :=
    cfgM_conj g T T₁
  let E : ↥(T ⊔ T₁) ≃* ↥(conjSubgroup g T ⊔ conjSubgroup g T₁) :=
    { toFun := fun x => ⟨g * x * g⁻¹, mem_conjSubgroup_sup.2 (by simp [mul_assoc])⟩
      invFun := fun y => ⟨g⁻¹ * y * g, mem_conjSubgroup_sup.1 y.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hN' := hS'.normal_cfgM_subgroupOf
  have hmap : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).map E.toMonoidHom =
      (cfgM (conjSubgroup g T) (conjSubgroup g T₁)).subgroupOf
        (conjSubgroup g T ⊔ conjSubgroup g T₁) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_subgroupOf, hM', mem_conjSubgroup]
      show g⁻¹ * (g * (z : G) * g⁻¹) * g ∈ cfgM T T₁
      have e1 : g⁻¹ * (g * (z : G) * g⁻¹) * g = z := by group
      rw [e1]
      exact Subgroup.mem_subgroupOf.1 hz
    · intro hy
      refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have h1 := Subgroup.mem_subgroupOf.1 hy
      rw [hM', mem_conjSubgroup] at h1
      exact h1
  exact ⟨hS', hD.ha, hN', ⟨(QuotientGroup.congr _ _ E hmap).symm.trans e⟩⟩

section Wrappers

variable [Finite G] {T T₁ : Subgroup G} {a : ℕ}

theorem SzData.exists_comm_of_normalizes (hD : SzData T T₁ a)
    {u : G} (huX : u ∈ Subgroup.normalizer ((T ⊔ T₁ : Subgroup G) : Set G))
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (huT : u ∈ Subgroup.normalizer (T : Set G)) (hu2 : u * u = 1) :
    ∃ y ∈ T, (∀ x ∈ T ⊔ T₁, ⁅y * u, x⁆ ∈ cfgM T T₁) ∧
      (u ∈ Subgroup.normalizer (T₁ : Set G) → y ∈ cfgM T T₁) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.iso
  exact _root_.CFSG.CGT.T75M.exists_comm_of_normalizes hD.sec3 hD.ha e huX huM huT hu2

theorem SzData.comm_of_index_le (hD : SzData T T₁ a) {u : G}
    (huM : u ∈ Subgroup.normalizer ((cfgM T T₁ : Subgroup G) : Set G))
    (hX : ∀ x ∈ T ⊔ T₁, ⁅x, u⁆ ∈ cfgM T T₁)
    (hc : Nat.card T ≤ 2 ^ (2 * a + 1) * Nat.card ↥(T ⊓ Subgroup.centralizer ({u} : Set G))) :
    ∀ m ∈ cfgM T T₁, m * u = u * m := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.iso
  exact _root_.CFSG.CGT.T75M.comm_of_index_le hD.sec3 hD.ha e huM hX hc

theorem SzData.two_pow_le_card_normIn (hD : SzData T T₁ a) :
    2 ^ (2 * (2 * a + 1)) ≤ Nat.card (normIn T T₁) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.iso
  exact _root_.CFSG.CGT.T75M.two_pow_le_card_normIn hD.sec3 hD.ha e

theorem SzData.card_eq_mul (hD : SzData T T₁ a) :
    Nat.card T = Nat.card (normIn T T₁) * 2 ^ (2 * a + 1) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD.iso
  exact _root_.CFSG.CGT.T75M.card_eq_mul_sz hD.sec3 hD.ha e

end Wrappers

end CFSG.CGT.T75M
