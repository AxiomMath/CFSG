module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbedding

open Equiv

def a6T0perm : Finset (Perm (Fin 6)) :=
  {1, swap 0 2 * swap 0 1, swap 0 1 * swap 0 2, swap 3 5 * swap 3 4, swap 3 4 * swap 3 5,
    swap 0 2 * swap 0 1 * (swap 3 5 * swap 3 4), swap 0 2 * swap 0 1 * (swap 3 4 * swap 3 5),
    swap 0 1 * swap 0 2 * (swap 3 5 * swap 3 4), swap 0 1 * swap 0 2 * (swap 3 4 * swap 3 5)}

def a6nperm : Perm (Fin 6) := swap 0 1 * swap 3 4

theorem a6T0perm_card : a6T0perm.card = 9 := by decide +kernel

theorem a6T0perm_inv : ∀ a ∈ a6T0perm, a⁻¹ ∈ a6T0perm := by decide +kernel

theorem a6T0perm_sign : ∀ a ∈ a6T0perm, Perm.sign a = 1 := by decide +kernel

theorem a6T0perm_mul : ∀ a ∈ a6T0perm, ∀ b ∈ a6T0perm, a * b ∈ a6T0perm := by decide +kernel

theorem a6nperm_inv : ∀ a ∈ a6T0perm, a6nperm * a * a6nperm⁻¹ = a⁻¹ := by decide +kernel

theorem a6nperm_sign : Perm.sign a6nperm = 1 := by decide +kernel

def a6T0 : Subgroup (alternatingGroup (Fin 6)) where
  carrier := {x | (x : Perm (Fin 6)) ∈ a6T0perm}
  mul_mem' := fun ha hb => a6T0perm_mul _ ha _ hb
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ a6T0perm
    simp [a6T0perm]
  inv_mem' := fun ha => a6T0perm_inv _ ha

theorem a6T0_card : Nat.card a6T0 = 9 := by
  have e : a6T0 ≃ (a6T0perm : Set (Perm (Fin 6))) :=
    { toFun := fun x => ⟨((x : alternatingGroup (Fin 6)) : Perm (Fin 6)), x.2⟩
      invFun := fun σ => ⟨⟨σ, Perm.mem_alternatingGroup.mpr (a6T0perm_sign σ σ.2)⟩, σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset, a6T0perm_card]

theorem card_altSix : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem card_sylow_altSix_le (S : Sylow 3 (alternatingGroup (Fin 6))) : Nat.card S ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hdvd : Nat.card S ∣ 360 := card_altSix ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd ⊢
  by_contra h
  push Not at h
  have hk3 : 3 ≤ k := by
    by_contra h'
    push Not at h'
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h27 : 3 ^ 3 ∣ 360 := (Nat.pow_dvd_pow 3 hk3).trans hdvd
  norm_num at h27

theorem exists_inv_of_sylow_altSix {K : Type*} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 6)) (T : Sylow 3 K) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
      ∀ t ∈ (T : Subgroup K), n * t * n⁻¹ = t⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : Nat.card a6T0 = 3 ^ 2 := by rw [a6T0_card]; norm_num
  obtain ⟨S, hS⟩ := (IsPGroup.of_card h9).exists_le_sylow
  have hST : (S : Subgroup (alternatingGroup (Fin 6))) = a6T0 :=
    (Subgroup.eq_of_le_of_card_ge hS (by rw [a6T0_card]; exact card_sylow_altSix_le S)).symm
  set T' : Sylow 3 (alternatingGroup (Fin 6)) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) S T'
  have hmemT' : ∀ y, y ∈ (T' : Subgroup (alternatingGroup (Fin 6))) ↔ g⁻¹ * y * g ∈ a6T0 := by
    intro y
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hST,
      ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  set n₀ : alternatingGroup (Fin 6) := ⟨a6nperm, Perm.mem_alternatingGroup.mpr a6nperm_sign⟩
  have hn₀ : ∀ s ∈ a6T0, n₀ * s * n₀⁻¹ = s⁻¹ := fun s hs =>
    Subtype.ext (a6nperm_inv _ hs)
  set n : alternatingGroup (Fin 6) := g * n₀ * g⁻¹
  have hn : ∀ y ∈ (T' : Subgroup (alternatingGroup (Fin 6))), n * y * n⁻¹ = y⁻¹ := by
    intro y hy
    have h1 := hn₀ _ ((hmemT' y).mp hy)
    calc n * y * n⁻¹ = g * (n₀ * (g⁻¹ * y * g) * n₀⁻¹) * g⁻¹ := by simp only [n]; group
      _ = g * (g⁻¹ * y * g)⁻¹ * g⁻¹ := by rw [h1]
      _ = y⁻¹ := by group
  have hT'K : ∀ t ∈ (T : Subgroup K), e t ∈ (T' : Subgroup (alternatingGroup (Fin 6))) :=
    fun t ht => ⟨t, ht, rfl⟩
  refine ⟨e.symm n, ?_, fun t ht => ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have h1 := hn _ (hT'K t ht)
    have h2 : e.symm n * t * (e.symm n)⁻¹ = t⁻¹ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, h1]
    rw [h2]
    exact (T : Subgroup K).inv_mem ht
  · have h1 := hn _ (hT'K t ht)
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

end CFSG.AGLEmbedding
