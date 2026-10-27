module

public import CFSG.CGT.Timmesfeld75.Sec215Local

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

theorem cfg_eq_one_of_comm (c : Cfg T T₁) {t y : G} (ht : t ∈ T) (htL : t ∉ normIn T T₁)
    (hy : y ∈ normIn T₁ T) (h : ⁅y, t⁆ = 1) : y = 1 := by
  have htM : t ∉ cfgM T T₁ := fun hM => htL (by rw [← c.inf_cfgM]; exact ⟨ht, hM⟩)
  have hyM : y ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hy
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h)
  have hyL : y ∈ normIn T T₁ := by
    rw [← c.cfgM_inf_centralizer ht htM]
    exact ⟨hyM, hyC⟩
  have h1 : y ∈ T ⊓ T₁ := ⟨normIn_le _ _ hyL, normIn_le _ _ hy⟩
  rw [c.inf, Subgroup.mem_bot] at h1
  exact h1

theorem cfg_exists_comm_eq [Finite G] (c : Cfg T T₁) (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    {x : G} (hx : x ∈ T) (hxL : x ∉ normIn T T₁) {l : G} (hl : l ∈ normIn T T₁) :
    ∃ y ∈ normIn T₁ T, ⁅x, y⁆ = l := by
  let f : ↥(normIn T₁ T) → ↥(normIn T T₁) := fun y =>
    ⟨⁅x, (y : G)⁆, c.comm_mem_normIn hx y.2⟩
  have hinj : Function.Injective f := by
    intro y y' h
    have h1 : ⁅x, (y : G)⁆ = ⁅x, (y' : G)⁆ := congrArg Subtype.val h
    have hw : (y' : G)⁻¹ * y ∈ normIn T₁ T :=
      (normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem y'.2) y.2
    have hcomm : ⁅x, (y' : G)⁻¹ * y⁆ = 1 := by
      have e : ⁅x, (y' : G)⁻¹ * y⁆ = (x * (y' : G)⁻¹ * x⁻¹) * ⁅x, (y : G)⁆ * y' := by
        simp only [commutatorElement_def]
        group
      have e' : (x * (y' : G)⁻¹ * x⁻¹) * ⁅x, (y' : G)⁆ * y' = 1 := by
        simp only [commutatorElement_def]
        group
      rw [e, h1, e']
    have hcomm' : ⁅(y' : G)⁻¹ * y, x⁆ = 1 := by
      rw [← commutatorElement_inv, hcomm, inv_one]
    have := cfg_eq_one_of_comm c hx hxL hw hcomm'
    exact Subtype.ext (inv_mul_eq_one.1 this).symm
  have hcard : Nat.card (normIn T T₁) ≤ Nat.card (normIn T₁ T) := (c.card_normIn_eq hconj).le
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨l, hl⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

end CFSG.CGT.PushingUpLit.T2KR
