module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIKernel
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB5

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Elementary

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a x : G}

omit [Finite G] in
theorem Sec4Hyp.sec4N_le_normalizer_conj (_h : Sec4Hyp T T₁ a T₂) {g : G}
    (hg : g ∈ Subgroup.normalizer (sec4N T T₁ T₂ : Set G)) :
    sec4N T T₁ T₂ ≤ Subgroup.normalizer (conjSubgroup g T : Set G) := by
  intro y hy
  rw [mem_normalizer_conjSubgroup_iff]
  apply sec4N_le_normalizer_left
  have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hg) y).1 hy
  simpa using this

theorem Sec4ActsTriv.mem_normalizer_of_le (h : Sec4Hyp T T₁ a T₂) {U : Subgroup G} (hU : IsWC U)
    (hUY : U ≤ sec4Y T T₁ T₂) (hx : Sec4ActsTriv T T₁ T₂ x) :
    x ∈ Subgroup.normalizer (U : Set G) := by
  have hUN : U ≤ Subgroup.normalizer (sec4N T T₁ T₂ : Set G) := hUY.trans h.sec4Y_le_normalizer
  have hS : IsPGroup 2 ↥(U ⊔ sec4N T T₁ T₂) :=
    (isPGroup_two_of_isElemAbelian hU.1).to_sup_of_normal_right' h.isPGroup_sec4N hUN
  have hle : conjSubgroup x U ≤ U ⊔ sec4N T T₁ T₂ := by
    rintro _ ⟨u, hu, rfl⟩
    have e : x * u * x⁻¹ = ⁅x, u⁆ * u := by
      simp only [commutatorElement_def]
      group
    show x * u * x⁻¹ ∈ U ⊔ sec4N T T₁ T₂
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hx u (hUY hu))) (Subgroup.mem_sup_left hu)
  exact mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hU hS le_sup_left hle)

end Elementary

section Centralizers

theorem conjSubgroup_normIn_eq_of_mem_normalizer {G : Type} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    conjSubgroup x (normIn A B) = normIn A B := by
  have h := normIn_conj x A B
  rwa [mem_normalizer_iff_conjSubgroup_eq.1 hA, mem_normalizer_iff_conjSubgroup_eq.1 hB,
    eq_comm] at h

theorem exists_ne_one_mem_centralizer_of_involution {G : Type} [Group G] [Finite G]
    {V : Subgroup G} (hV : IsElemAbelian 2 V) (hVne : V ≠ ⊥) {a : G} (haa : a * a = 1)
    (haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V) : ∃ v ∈ V, v ≠ 1 ∧ a * v = v * a := by
  by_contra hcon
  push Not at hcon
  have hbot : V ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    by_contra hv1
    exact hv1 (by
      by_contra hne
      exact hcon v hv.1 hne (Subgroup.mem_centralizer_singleton_iff.1 hv.2).symm)
  have h := card_le_sq_centralizer hV haa haV
  rw [hbot, Subgroup.card_bot] at h
  have h1 : Nat.card V ≤ 1 := by simpa using h
  exact hVne (Subgroup.card_eq_one.1 (le_antisymm h1 Nat.card_pos))

end Centralizers

section Trivial

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a x : G}

theorem Sec4Hyp.mem_sec4N_of_conj_le (h : Sec4Hyp T T₁ a T₂) {g : G}
    (hxg : x ∈ conjSubgroup g T) (hle : conjSubgroup g T ≤ sec4Y T T₁ T₂)
    (hx : Sec4ActsTriv T T₁ T₂ x) : x ∈ sec4N T T₁ T₂ := by
  obtain ⟨k, hk, hkg⟩ := exists_mem_conj_eq_of_le h.pair.wc left_le_sec4Y hle
  rw [hkg] at hxg
  have ht : k⁻¹ * x * k ∈ T := mem_conjSubgroup.1 hxg
  have hk' : k⁻¹ ∈ sec4Y T T₁ T₂ := (sec4Y T T₁ T₂).inv_mem hk
  have hker : k⁻¹ * x * k ∈ sec4Ker T T₁ T₂ := by
    have := h.conj_mem_sec4Ker (show x ∈ sec4Ker T T₁ T₂ from hx) hk'
    simpa using this
  have hL : k⁻¹ * x * k ∈ normIn T T₁ := by
    rw [← h.inf_sec4Ker_eq]
    exact ⟨ht, hker⟩
  have hN := normIn_le_sec4N_left (T₂ := T₂) hL
  have hN' := (Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer hk) _).1 hN
  have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
  rwa [e] at hN'

theorem Sec4Hyp.actsTriv_of_commutators (h : Sec4Hyp T T₁ a T₂) {w : G}
    (hT : ∀ t ∈ T, ⁅w, t⁆ ∈ sec4N T T₁ T₂) (hT₁ : ∀ t ∈ T₁, ⁅w, t⁆ ∈ sec4N T T₁ T₂)
    (hT₂ : ∀ t ∈ T₂, ⁅w, t⁆ ∈ sec4N T T₁ T₂) : Sec4ActsTriv T T₁ T₂ w := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ sec4Y T T₁ T₂ ∧ ⁅w, y⁆ ∈ sec4N T T₁ T₂}
      mul_mem' := fun {y₁ y₂} h₁ h₂ => by
        refine ⟨(sec4Y T T₁ T₂).mul_mem h₁.1 h₂.1, ?_⟩
        have e : ⁅w, y₁ * y₂⁆ = ⁅w, y₁⁆ * (y₁ * ⁅w, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (sec4N T T₁ T₂).mul_mem h₁.2
          ((Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer h₁.1) _).1 h₂.2)
      one_mem' := ⟨(sec4Y T T₁ T₂).one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := fun {y} hy => by
        refine ⟨(sec4Y T T₁ T₂).inv_mem hy.1, ?_⟩
        have e : ⁅w, y⁻¹⁆ = y⁻¹ * ⁅w, y⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have hyi := (Subgroup.normalizer (sec4N T T₁ T₂ : Set G)).inv_mem
          (h.sec4Y_le_normalizer hy.1)
        have := (Subgroup.mem_normalizer_iff.1 hyi _).1 ((sec4N T T₁ T₂).inv_mem hy.2)
        simpa using this }
  have hCY : sec4Y T T₁ T₂ ≤ C :=
    sup_le (sup_le (fun t ht => ⟨left_le_sec4Y ht, hT t ht⟩)
      (fun t ht => ⟨mid_le_sec4Y ht, hT₁ t ht⟩)) (fun t ht => ⟨right_le_sec4Y ht, hT₂ t ht⟩)
  exact fun y hy => (hCY hy).2

end Trivial

end CFSG.CGT.Timmesfeld75
