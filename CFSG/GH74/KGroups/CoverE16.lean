module

public import CFSG.GH74.Filter.ElemAbelian

public section

namespace CFSG.GH74.KGroups

open Subgroup
open scoped IsMulCommutative

@[expose] noncomputable def elemPow2 {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 2 = 1) : (Fin r → Multiplicative (ZMod 2)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

theorem exists_E16 {G : Type*} [Group G] (e : Fin 4 → G) (hsq : ∀ i, e i * e i = 1)
    (hcomm : ∀ i j, e i * e j = e j * e i)
    (hker : ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => e i ^ (a i : ℕ)).prod ≠ 1)
    (hconj : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
      ∃ g : G, g * e 0 * g⁻¹ = (List.ofFn fun i => e i ^ (a i : ℕ)).prod) :
    ∃ E : Subgroup G, Nat.card E = 16 ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ (∀ i, e i ∈ E) ∧
      ∀ x ∈ E, x ≠ 1 → ∃ g : G, g * e 0 * g⁻¹ = x := by
  have hsq' : ∀ i, e i ^ 2 = 1 := fun i => by rw [sq]; exact hsq i
  set C := Subgroup.closure (Set.range e) with hC
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin 4 → C := fun i => ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 2 = 1 := fun i => Subtype.ext (by simpa [v] using hsq' i)
  let φ : (Fin 4 → Multiplicative (ZMod 2)) →* G := C.subtype.comp (elemPow2 v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => e i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, elemPow2, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ] at ha
    rw [Subgroup.mem_bot]
    by_contra hne
    refine hker (fun i => ⟨(Multiplicative.toAdd (a i)).val, ZMod.val_lt _⟩) (fun h0 => hne ?_) ha
    funext i
    have h1 := congrFun h0 i
    have h2 : (Multiplicative.toAdd (a i)).val = 0 := by simpa using congrArg Fin.val h1
    exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h2)
  have hsqa : ∀ a : Fin 4 → Multiplicative (ZMod 2), a * a = 1 := by
    intro a
    funext i
    rw [Pi.mul_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    exact CharTwo.add_self_eq_zero _
  refine ⟨φ.range, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, CFSG.GH74.Filter.card_pi_zmod_two]
    norm_num
  · rintro _ ⟨a, rfl⟩
    rw [sq, ← map_mul, hsqa, map_one]
  · intro i
    refine ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), ?_⟩
    rw [hφ]
    have : ∀ j, e j ^ (Multiplicative.toAdd ((Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2)) :
        Fin 4 → Multiplicative (ZMod 2)) j)).val = if j = i then e i else 1 := by
      intro j
      by_cases hj : j = i
      · subst hj
        have h1 : ((1 : ZMod 2)).val = 1 := rfl
        simp [h1]
      · simp [hj]
    simp only [this]
    fin_cases i <;> simp
  · rintro _ ⟨a, rfl⟩ hx
    have ha : a ≠ 1 := fun h => hx (by rw [h, map_one])
    have hne : (fun i => (⟨(Multiplicative.toAdd (a i)).val, ZMod.val_lt _⟩ : Fin 2)) ≠ 0 := by
      intro h0
      apply ha
      funext i
      have h1 := congrFun h0 i
      have h2 : (Multiplicative.toAdd (a i)).val = 0 := by simpa using congrArg Fin.val h1
      exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 h2)
    obtain ⟨g, hg⟩ := hconj _ hne
    exact ⟨g, by rw [hg, hφ]⟩

end CFSG.GH74.KGroups
