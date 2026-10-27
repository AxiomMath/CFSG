module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem permVec_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := rfl

theorem permVec_one {n : ℕ} (v : Fin n → ZMod 2) : permVec (1 : Equiv.Perm (Fin n)) v = v := rfl

theorem mem_sup_zpowers_iff_of_commute {G : Type} [Group G] {B : Subgroup G} {t : G}
    (hc : ∀ b ∈ B, b * t = t * b) {x : G} :
    x ∈ B ⊔ zpowers t ↔ ∃ b ∈ B, ∃ i : ℤ, x = b * t ^ i := by
  constructor
  · intro hx
    let D : Subgroup G :=
      { carrier := {x | ∃ b ∈ B, ∃ i : ℤ, x = b * t ^ i}
        one_mem' := ⟨1, B.one_mem, 0, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨b, hb, i, rfl⟩ ⟨b', hb', j, rfl⟩
          refine ⟨b * b', B.mul_mem hb hb', i + j, ?_⟩
          have hcomm : (t ^ i) * b' = b' * t ^ i :=
            ((Commute.zpow_left (show Commute t b' from (hc b' hb').symm) i)).eq
          rw [zpow_add]
          calc b * t ^ i * (b' * t ^ j) = b * (t ^ i * b') * t ^ j := by group
            _ = b * (b' * t ^ i) * t ^ j := by rw [hcomm]
            _ = b * b' * (t ^ i * t ^ j) := by group
        inv_mem' := by
          rintro _ ⟨b, hb, i, rfl⟩
          refine ⟨b⁻¹, B.inv_mem hb, -i, ?_⟩
          have hcomm : (t ^ (-i)) * b⁻¹ = b⁻¹ * t ^ (-i) :=
            ((Commute.zpow_left (show Commute t b⁻¹ from
              ((Commute.inv_right (show Commute t b from (hc b hb).symm)))) (-i))).eq
          calc (b * t ^ i)⁻¹ = t ^ (-i) * b⁻¹ := by group
            _ = b⁻¹ * t ^ (-i) := hcomm }
    have hle : B ⊔ zpowers t ≤ D := by
      refine sup_le (fun b hb => ⟨b, hb, 0, by simp⟩) ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨1, B.one_mem, i, by simp⟩
    exact hle hx
  · rintro ⟨b, hb, i, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers t) i))

theorem permVec_injective_five {σ σ' : Equiv.Perm (Fin 5)}
    (h : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec σ v = permVec σ' v) : σ = σ' := by
  let ev : Fin 5 → Fin 5 → Fin 5 → ZMod 2 := fun a b x => if x = a ∨ x = b then 1 else 0
  have hev : ∀ a b : Fin 5, a ≠ b → IsEvenVec (ev a b) := by
    unfold IsEvenVec
    decide
  have key : ∀ a b : Fin 5, a ≠ b → ∀ x : Fin 5,
      (σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b) ↔ (x = a ∨ x = b) := by
    intro a b hab x
    have h1 := congrFun (h _ (hev a b hab)) (σ x)
    simp only [permVec, Function.comp_apply, Equiv.symm_apply_apply, ev] at h1
    by_cases hx : x = a ∨ x = b
    · simp only [hx, if_true] at h1
      by_cases hy : σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b
      · simp [hx, hy]
      · simp [hy] at h1
    · simp only [hx, if_false] at h1
      by_cases hy : σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b
      · simp [hy] at h1
      · simp [hx, hy]
  refine Equiv.ext fun i => ?_
  have hne : ∀ i : Fin 5, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by decide
  obtain ⟨h1, h2, h3⟩ := hne i
  have e1 := (key i (i + 1) h1 i).2 (Or.inl rfl)
  have e2 := (key i (i + 2) h2 i).2 (Or.inl rfl)
  have : σ'.symm (σ i) = i := by
    rcases e1 with e1 | e1
    · exact e1
    · rcases e2 with e2 | e2
      · exact e2
      · exact absurd (e1.symm.trans e2) h3
  have := congrArg σ' this
  simpa using this

theorem eq_alt_or_top_five {X : Subgroup (Equiv.Perm (Fin 5))}
    (h : alternatingGroup (Fin 5) ≤ X) : X = alternatingGroup (Fin 5) ∨ X = ⊤ := by
  have h2 : (alternatingGroup (Fin 5)).index = 2 := alternatingGroup.index_eq_two
  have key := Subgroup.relIndex_mul_index h
  rw [h2] at key
  have hd : X.index ∣ 2 := ⟨(alternatingGroup (Fin 5)).relIndex X, by rw [← key, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · rw [h1] at key
    have h3 : (alternatingGroup (Fin 5)).relIndex X = 1 := by omega
    exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.1 h3) h)

end CFSG.OddStandard.SmallF3.Omega
