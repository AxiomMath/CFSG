module

public import CFSG.HardMathSupport.Foote.SPLScalar.CasesCore

public section

namespace CFSG.HardMathSupport.Foote.SPLScalar

open Equiv CFSG.HardMathSupport.Foote.SPLScalar.Core


private abbrev A6 := alternatingGroup (Fin 6)

private def a6a : A6 := ⟨swap 0 1 * swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
private def a6b : A6 := ⟨swap 3 4 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem a6_comm : a6a * a6b = a6b * a6a := by decide
private theorem a6a_cube : a6a ^ 3 = 1 := by decide
private theorem a6b_cube : a6b ^ 3 = 1 := by decide
private theorem a6_t : ∃ t : A6, t * a6a * t⁻¹ = a6b ∧ t * a6b * t⁻¹ = a6a⁻¹ := by decide +kernel
private theorem sq_conj (t x : A6) : t ^ 2 * x * (t ^ 2)⁻¹ = t * (t * x * t⁻¹) * t⁻¹ := by
  simp [pow_two, mul_assoc]

private theorem a6_card9 :
    (Finset.univ.image fun p : Fin 3 × Fin 3 => a6a ^ (p.1 : ℕ) * a6b ^ (p.2 : ℕ)).card = 9 := by
  decide +kernel


private theorem a6_exists_sq_inv_sylow (U : Sylow 3 A6) :
    ∃ t ∈ Subgroup.normalizer ((U : Subgroup A6) : Set A6), ∀ x ∈ (U : Subgroup A6), t ^ 2 * x * (t ^ 2)⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommS : ∀ x ∈ ({a6a, a6b} : Set A6), ∀ y ∈ ({a6a, a6b} : Set A6), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | rfl | exact a6_comm | exact a6_comm.symm
  have hPcomm : ∀ x ∈ Subgroup.closure ({a6a, a6b} : Set A6),
      ∀ y ∈ Subgroup.closure ({a6a, a6b} : Set A6), x * y = y * x := by
    intro x hx y hy
    have hPW : ({a6a, a6b} : Set A6).Pairwise Commute := fun x hx y hy _ => hcommS x hx y hy
    have := Subgroup.isMulCommutative_closure hPW
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨x, hx⟩ : Subgroup.closure ({a6a, a6b} : Set A6)) ⟨y, hy⟩)
  have hP3 : ∀ x ∈ Subgroup.closure ({a6a, a6b} : Set A6), x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl; exacts [a6a_cube, a6b_cube]
    | one => simp
    | mul x y hx hy hx3 hy3 => rw [Commute.mul_pow (show Commute x y from hPcomm x hx y hy), hx3, hy3, one_mul]
    | inv x hx hx3 => rw [inv_pow, hx3, inv_one]
  have hPG : IsPGroup 3 (Subgroup.closure ({a6a, a6b} : Set A6)) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h3 : (g : A6) ^ 3 = 1 := hP3 g g.2
    have hd : orderOf (g : A6) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [← Subgroup.orderOf_coe]
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hcard9 : 9 ≤ Nat.card (Subgroup.closure ({a6a, a6b} : Set A6)) := by
    have hsub : ((Finset.univ.image fun p : Fin 3 × Fin 3 => a6a ^ (p.1 : ℕ) * a6b ^ (p.2 : ℕ)) :
        Set A6) ⊆ Subgroup.closure ({a6a, a6b} : Set A6) := by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨p, rfl⟩ := hx
      exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, a6_card9] at this
    have e : Nat.card (Subgroup.closure ({a6a, a6b} : Set A6)) =
        ((Subgroup.closure ({a6a, a6b} : Set A6) : Subgroup A6) : Set A6).ncard :=
      Nat.card_coe_set_eq _
    omega
  obtain ⟨Q, hQ⟩ := hPG.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup A6) = 9 := (altSix_sylow ⟨MulEquiv.refl _⟩ Q).1
  have hPQ : Subgroup.closure ({a6a, a6b} : Set A6) = (Q : Subgroup A6) :=
    Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard]; exact hcard9)
  obtain ⟨t0, h1, h2⟩ := a6_t
  have h3 : t0⁻¹ * a6b * t0 = a6a := by rw [← h1]; group
  have h4 : t0⁻¹ * a6a * t0 = a6b⁻¹ := by
    have : a6a = t0 * a6b⁻¹ * t0⁻¹ := by rw [← inv_inv a6a, ← h2]; group
    rw [this]; group
  have hP := Subgroup.closure ({a6a, a6b} : Set A6)
  have hc1 : ∀ x ∈ Subgroup.closure ({a6a, a6b} : Set A6),
      t0 * x * t0⁻¹ ∈ Subgroup.closure ({a6a, a6b} : Set A6) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [h1]; exact Subgroup.subset_closure (by simp)
      · rw [h2]; exact inv_mem (Subgroup.subset_closure (by simp))
    | one => simp [one_mem]
    | mul x y hx hy hx' hy' =>
      have : t0 * (x * y) * t0⁻¹ = (t0 * x * t0⁻¹) * (t0 * y * t0⁻¹) := by group
      rw [this]; exact mul_mem hx' hy'
    | inv x hx hx' =>
      have : t0 * x⁻¹ * t0⁻¹ = (t0 * x * t0⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx'
  have hc2 : ∀ x ∈ Subgroup.closure ({a6a, a6b} : Set A6),
      t0⁻¹ * x * t0 ∈ Subgroup.closure ({a6a, a6b} : Set A6) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [h4]; exact inv_mem (Subgroup.subset_closure (by simp))
      · rw [h3]; exact Subgroup.subset_closure (by simp)
    | one => simp [one_mem]
    | mul x y hx hy hx' hy' =>
      have : t0⁻¹ * (x * y) * t0 = (t0⁻¹ * x * t0) * (t0⁻¹ * y * t0) := by group
      rw [this]; exact mul_mem hx' hy'
    | inv x hx hx' =>
      have : t0⁻¹ * x⁻¹ * t0 = (t0⁻¹ * x * t0)⁻¹ := by group
      rw [this]; exact inv_mem hx'
  have hinv : ∀ x ∈ Subgroup.closure ({a6a, a6b} : Set A6), t0 ^ 2 * x * (t0 ^ 2)⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [sq_conj, h1, h2]
      · rw [sq_conj, h2]
        have : t0 * a6a⁻¹ * t0⁻¹ = (t0 * a6a * t0⁻¹)⁻¹ := by group
        rw [this, h1]
    | one => simp
    | mul x y hx hy hx' hy' =>
      have : t0 ^ 2 * (x * y) * (t0 ^ 2)⁻¹ = (t0 ^ 2 * x * (t0 ^ 2)⁻¹) * (t0 ^ 2 * y * (t0 ^ 2)⁻¹) := by
        simp [pow_two, mul_assoc]
      rw [this, hx', hy', mul_inv_rev, hPcomm x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)]
    | inv x hx hx' =>
      have : t0 ^ 2 * x⁻¹ * (t0 ^ 2)⁻¹ = (t0 ^ 2 * x * (t0 ^ 2)⁻¹)⁻¹ := by
        simp [pow_two, mul_assoc]
      rw [this, hx']
  have hcn : ∀ x : A6, x ∈ (Q : Subgroup A6) ↔ t0 * x * t0⁻¹ ∈ (Q : Subgroup A6) := by
    intro x
    rw [← hPQ]
    constructor
    · exact hc1 x
    · intro hx
      have := hc2 _ hx
      simpa [mul_assoc] using this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6 Q U
  have hgm : ∀ x : A6, x ∈ (U : Subgroup A6) ↔ g⁻¹ * x * g ∈ (Q : Subgroup A6) := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul]
    simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
  refine ⟨g * t0 * g⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hgm x, hgm (g * t0 * g⁻¹ * x * (g * t0 * g⁻¹)⁻¹), hcn (g⁻¹ * x * g)]
    have : g⁻¹ * (g * t0 * g⁻¹ * x * (g * t0 * g⁻¹)⁻¹) * g = t0 * (g⁻¹ * x * g) * t0⁻¹ := by group
    rw [this]
  · intro x hx
    have hy : g⁻¹ * x * g ∈ (Q : Subgroup A6) := (hgm x).mp hx
    have := hinv _ (hPQ ▸ hy)
    have e : (g * t0 * g⁻¹) ^ 2 * x * ((g * t0 * g⁻¹) ^ 2)⁻¹ =
        g * (t0 ^ 2 * (g⁻¹ * x * g) * (t0 ^ 2)⁻¹) * g⁻¹ := by
      simp [pow_two, mul_assoc]
    rw [e, this]; group


theorem exists_sq_inv_of_altSix {L : Type} [Group L]
    (hL : Nonempty (L ≃* alternatingGroup (Fin 6))) (TL : Sylow 3 L) :
    ∃ t ∈ Subgroup.normalizer ((TL : Subgroup L) : Set L),
      ∀ a ∈ (TL : Subgroup L), t ^ 2 * a * (t ^ 2)⁻¹ = a⁻¹ := by
  obtain ⟨e⟩ := hL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  have hfs : Function.Surjective (e : L →* A6) := e.surjective
  let U : Sylow 3 A6 := TL.mapSurjective hfs
  have hUT : (U : Subgroup A6) = (TL : Subgroup L).map (e : L →* A6) :=
    Sylow.coe_mapSurjective hfs TL
  have hmem : ∀ x : L, x ∈ (TL : Subgroup L) ↔ e x ∈ (U : Subgroup A6) := by
    intro x
    rw [hUT]
    change _ ↔ e x ∈ (TL : Subgroup L).map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
    simp
  obtain ⟨t', ht', hinv⟩ := a6_exists_sq_inv_sylow U
  refine ⟨e.symm t', ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have h := Subgroup.mem_normalizer_iff.mp ht' (e x)
    rw [hmem x, hmem (e.symm t' * x * (e.symm t')⁻¹)]
    simpa [map_mul, map_inv] using h
  · intro a ha
    have h := hinv (e a) ((hmem a).mp ha)
    apply e.injective
    simpa [map_mul, map_inv, map_pow] using h

end CFSG.HardMathSupport.Foote.SPLScalar
