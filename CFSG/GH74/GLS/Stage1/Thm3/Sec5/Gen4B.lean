module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Gen4Q
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Stages

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

theorem mem_normalizer_inf {G : Type} [Group G] {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX x, hY x]

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem false_of_L53_gen4 (hgen4 : Gen4 G) (hII : II4_4_4_center)
    (hq : CFSG.GH74.GLS.Stage1.Thm3.Sec6.II4_4_quat) {a : G} {Y A : Subgroup G}
    (h : Std4 G z S K₁ K₂) (haa : a * a = 1) (hYA : L53Data z S K₁ K₂ a Y A) : False := by
  have hM := m4_of_std hII h
  have hK₁ : K₁ = K₁ ∨ K₁ = K₂ := Or.inl rfl
  have hK₂ : K₂ = K₁ ∨ K₂ = K₂ := Or.inr rfl
  obtain ⟨n₁, hn₁⟩ :=
    hq G h.simple z h.orderOf_z S K₁ h.sylow (h.comp_isPCompIn hK₁) (h.comp_pRank hK₁)
  obtain ⟨n₂, hn₂⟩ :=
    hq G h.simple z h.orderOf_z S K₂ h.sylow (h.comp_isPCompIn hK₂) (h.comp_pRank hK₂)
  have hcomm : ∀ x ∈ S ⊓ K₁, ∀ y ∈ S ⊓ K₂, x * y = y * x := fun x hx y hy =>
    hM.comm_of_S hx.2 hy.2 hx.1 hy.1
  have hPeq : Pz S z = (S ⊓ K₁) ⊔ (S ⊓ K₂) := by
    rw [Pz_eq h]
    have e₁ : M.Pm S K₁ K₂ ⊓ K₁ = S ⊓ K₁ := by
      unfold M.Pm; rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
    have e₂ : M.Pm S K₁ K₂ ⊓ K₂ = S ⊓ K₂ := by
      unfold M.Pm; rw [inf_assoc, inf_eq_right.2 (le_sup_right : K₂ ≤ K₁ ⊔ K₂)]
    have := hM.P_eq
    rw [e₁, e₂] at this
    exact this
  obtain ⟨c, hcA, hAc⟩ := hYA.A_cyclic
  have hAS : A ≤ S := fun u hu => (hYA.A_le hu).1
  have hAK₁ : ∀ u ∈ A, u ∈ Subgroup.normalizer (K₁ : Set G) := fun u hu => (hYA.A_le hu).2
  have hAK₂ : ∀ u ∈ A, u ∈ Subgroup.normalizer (K₂ : Set G) := fun u hu =>
    normalizer_other hM h.ne (S_le_Cz hM (hAS hu)) (hAK₁ u hu)
  have hPA : Pz S z ≤ A := by rw [hAc]; exact le_sup_left
  have hnormP : ∀ u ∈ A, u ∈ Subgroup.normalizer (Pz S z : Set G) := by
    intro u hu
    have hS : u ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hAS hu)
    have hKK : u ∈ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_sup K₁ K₂ ⟨hAK₁ u hu, hAK₂ u hu⟩
    rw [Pz_eq h]
    exact mem_normalizer_inf hS hKK
  obtain ⟨d, hdA, q, hqP, haeq⟩ := exists_sq_mul_of_cyclic hPA (fun u hu => hnormP u hu) hcA hAc
    (hM.S_pgroup.to_le hAS) hYA.A_order hYA.a_mem haa
  obtain ⟨k, hk⟩ := hM.S_pgroup (⟨d, hAS hdA⟩ : ↥S)
  have hdk : d ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hAS hdA)
  have hd₁ : d ∈ Subgroup.normalizer ((S ⊓ K₁ : Subgroup G) : Set G) :=
    mem_normalizer_inf hdS (hAK₁ d hdA)
  have hd₂ : d ∈ Subgroup.normalizer ((S ⊓ K₂ : Subgroup G) : Set G) :=
    mem_normalizer_inf hdS (hAK₂ d hdA)
  have ha_sq : (d * d * q) * (d * d * q) = 1 := by rw [← haeq]; exact haa
  have haP : d * d * q ∉ (S ⊓ K₁) ⊔ (S ⊓ K₂) := by
    rw [← haeq]
    intro hmem
    have hle : (S ⊓ K₁) ⊔ (S ⊓ K₂) ≤ K₁ ⊔ K₂ := sup_le_sup inf_le_right inf_le_right
    exact hYA.a_not_K (hle hmem)
  have hqP' : q ∈ (S ⊓ K₁) ⊔ (S ⊓ K₂) := by rw [← hPeq]; exact hqP
  exact false_of_quat_pair hgen4 hn₁ hn₂ hcomm hd₁ hd₂ hdk hqP' ha_sq haP

theorem false_of_ctr5_L53_gen4 (hgen4 : Gen4 G) (hII : II4_4_4_center)
    (hq : CFSG.GH74.GLS.Stage1.Thm3.Sec6.II4_4_quat) {a x : G}
    (hctr : Ctr5 G z S K₁ K₂ a x) (h53 : L53 z S K₁ K₂ a) : False := by
  obtain ⟨Y, A, hYA⟩ := h53
  exact false_of_L53_gen4 hgen4 hII hq hctr.cfg.std
    (mul_self_eq_one_of_orderOf_eq_two hctr.elt.inv) hYA

end CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5
