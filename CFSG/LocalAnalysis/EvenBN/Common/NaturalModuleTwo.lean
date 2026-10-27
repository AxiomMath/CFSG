module

public import CFSG.LocalAnalysis.EvenBN.Common.NaturalModule
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open scoped MatrixGroups

variable {G : Type*} [Group G] {k : Type*} [Field k] [Finite k] [CharP k 2]

theorem inf_centralizer_conj_eq_map_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) (e : G) :
    X ⊓ centralizer ({x * e * x⁻¹} : Set G) =
      (X ⊓ centralizer ({e} : Set G)).map (MulAut.conj x).toMonoidHom := by
  ext y
  simp only [mem_inf, mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hyX, hy⟩
    refine ⟨x⁻¹ * y * x, ⟨mul_mem (mul_mem (inv_mem hx) hyX) hx, ?_⟩, by group⟩
    calc x⁻¹ * y * x * e = x⁻¹ * (y * (x * e * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * e * x⁻¹) * y) * x := by rw [hy]
      _ = e * (x⁻¹ * y * x) := by group
  · rintro ⟨z, ⟨hzX, hz⟩, rfl⟩
    refine ⟨mul_mem (mul_mem hx hzX) (inv_mem hx), ?_⟩
    calc x * z * x⁻¹ * (x * e * x⁻¹) = x * (z * e) * x⁻¹ := by group
      _ = x * (e * z) * x⁻¹ := by rw [hz]
      _ = x * e * x⁻¹ * (x * z * x⁻¹) := by group

theorem eq_of_conj_eq_of_inf_centralizer_eq {X S J : Subgroup G} (hJX : J ≤ X)
    (hJinf : J ⊓ S = ⊥) {a : G} (hstab : X ⊓ centralizer ({a} : Set G) = S) {j j' : G}
    (hj : j ∈ J) (hj' : j' ∈ J) (h : j * a * j⁻¹ = j' * a * j'⁻¹) : j = j' := by
  have hmem : j'⁻¹ * j ∈ J ⊓ S := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hj') hj, ?_⟩
    rw [← hstab]
    refine mem_inf.2 ⟨mul_mem (inv_mem (hJX hj')) (hJX hj), mem_centralizer_singleton_iff.2 ?_⟩
    calc j'⁻¹ * j * a = j'⁻¹ * (j * a * j⁻¹) * j := by group
      _ = j'⁻¹ * (j' * a * j'⁻¹) * j := by rw [h]
      _ = a * (j'⁻¹ * j) := by group
  rw [hJinf, mem_bot] at hmem
  exact (inv_mul_eq_one.1 hmem).symm

theorem exists_conj_eq_of_stab {X A S J : Subgroup G} (hXA : X ≤ normalizer (A : Set G))
    (hJX : J ≤ X) (hJS : J ≤ normalizer (S : Set G)) (hJinf : J ⊓ S = ⊥)
    (hJcard : Nat.card J + 1 = Nat.card (A ⊓ centralizer (S : Set G) : Subgroup G)) {a b : G}
    (ha : a ∈ A ⊓ centralizer (S : Set G)) (hb : b ∈ A ⊓ centralizer (S : Set G)) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hstab : X ⊓ centralizer ({a} : Set G) = S) : ∃ j ∈ J, j * a * j⁻¹ = b := by
  set B := A ⊓ centralizer (S : Set G) with hB
  set T : Set G := (B : Set G) \ {1} with hT
  obtain ⟨haA, haS⟩ := mem_inf.1 ha
  have hmaps : Set.MapsTo (fun j => j * a * j⁻¹) (J : Set G) T := by
    intro j hj
    refine ⟨mem_inf.2 ⟨(mem_normalizer_iff.1 (hXA (hJX hj)) a).1 haA,
      mem_centralizer_iff.2 fun t ht => ?_⟩, fun h => ha1 ?_⟩
    · have ht' : j⁻¹ * t * j ∈ S := by
        have := (mem_normalizer_iff.1 (inv_mem (hJS hj)) t).1 ht
        rwa [inv_inv] at this
      have hc := mem_centralizer_iff.1 haS _ ht'
      calc t * (j * a * j⁻¹) = j * ((j⁻¹ * t * j) * a) * j⁻¹ := by group
        _ = j * (a * (j⁻¹ * t * j)) * j⁻¹ := by rw [hc]
        _ = j * a * j⁻¹ * t := by group
    · have h' : j * a * j⁻¹ = 1 := h
      calc a = j⁻¹ * (j * a * j⁻¹) * j := by group
        _ = 1 := by rw [h']; group
  have hinj : Set.InjOn (fun j => j * a * j⁻¹) (J : Set G) := fun j hj j' hj' h =>
    eq_of_conj_eq_of_inf_centralizer_eq hJX hJinf hstab hj hj' h
  have hBcard : (B : Set G).ncard = Nat.card B := (Nat.card_coe_set_eq _).symm
  have hTfin : T.Finite :=
    (Set.finite_of_ncard_ne_zero (s := (B : Set G)) (by rw [hBcard]; omega)).sdiff
  have himg : (fun j => j * a * j⁻¹) '' (J : Set G) = T := by
    refine Set.eq_of_subset_of_ncard_le hmaps.image_subset ?_ hTfin
    rw [hinj.ncard_image, hT, Set.ncard_sdiff_singleton_of_mem (one_mem B), hBcard,
      ← Nat.card_coe_set_eq]
    change Nat.card B - 1 ≤ Nat.card J
    omega
  obtain ⟨j, hj, hjb⟩ := himg.symm ▸ (show b ∈ T from ⟨hb, hb1⟩)
  exact ⟨j, hj, hjb⟩

theorem inf_centralizer_eq_of_stab {X A S : Subgroup G} (ψ : X ≃* SL(2, k)) (hSX : S ≤ X)
    (hS : Nat.card S = Nat.card k)
    (htrans : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ x ∈ X, x * a * x⁻¹ = b)
    (hstab : ∀ a ∈ A ⊓ centralizer (S : Set G), a ≠ 1 → X ⊓ centralizer ({a} : Set G) = S)
    {e : G} (he : e ∈ A ⊓ centralizer (S : Set G)) (he1 : e ≠ 1) {s : G} (hs : s ∈ S)
    (hs1 : s ≠ 1) : A ⊓ centralizer ({s} : Set G) = A ⊓ centralizer (S : Set G) := by
  refine le_antisymm (fun a ha => ?_)
    (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.2 hs)))
  obtain ⟨haA, has⟩ := mem_inf.1 ha
  refine mem_inf.2 ⟨haA, ?_⟩
  by_cases ha1 : a = 1
  · rw [ha1]
    exact one_mem _
  obtain ⟨x, hx, rfl⟩ := htrans e (mem_inf.1 he).1 a haA he1 ha1
  have hsa : s ∈ X ⊓ centralizer ({x * e * x⁻¹} : Set G) :=
    mem_inf.2 ⟨hSX hs, mem_centralizer_singleton_iff.2 (mem_centralizer_singleton_iff.1 has).symm⟩
  have hcard : Nat.card (X ⊓ centralizer ({x * e * x⁻¹} : Set G) : Subgroup G) = Nat.card k := by
    rw [inf_centralizer_conj_eq_map_of_mem hx, hstab e he he1,
      card_map_of_injective (MulAut.conj x).injective, hS]
  have hSeq := eq_of_mem_of_card ψ hSX inf_le_left hS hcard hs hsa hs1
  refine mem_centralizer_iff.2 fun t ht => ?_
  rw [SetLike.mem_coe, hSeq] at ht
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 ht).2

theorem natural_module_inf_centralizer_of_ne_one {n : ℕ} (hk : Nat.card k = 2 ^ n)
    {X A S : Subgroup G} (ψ : X ≃* SL(2, k)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : X ≤ normalizer (A : Set G)) (hcard : Nat.card A = (2 ^ n) ^ 2)
    (hfix : A ⊓ centralizer (X : Set G) = ⊥) (hSX : S ≤ X) (hS : Nat.card S = Nat.card k)
    (hfixS : Nat.card (A ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ n) {s : G} (hs : s ∈ S)
    (hs1 : s ≠ 1) : A ⊓ centralizer ({s} : Set G) = A ⊓ centralizer (S : Set G) := by
  obtain ⟨htrans, hstab, -⟩ := natural_module_of_card hk ψ hcomm hXA hcard hfix hSX hS hfixS
  obtain ⟨e, he, he1⟩ := (A ⊓ centralizer (S : Set G)).bot_or_exists_ne_one.resolve_left
    fun h => by
      have h1 : 1 < Nat.card k := Finite.one_lt_card
      rw [h, card_bot] at hfixS
      omega
  exact inf_centralizer_eq_of_stab ψ hSX hS htrans hstab he he1 hs hs1

theorem natural_module_exists_conj_of_le_normalizer {n : ℕ} (hk : Nat.card k = 2 ^ n)
    {X A S : Subgroup G} (ψ : X ≃* SL(2, k)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hXA : X ≤ normalizer (A : Set G)) (hcard : Nat.card A = (2 ^ n) ^ 2)
    (hfix : A ⊓ centralizer (X : Set G) = ⊥) (hSX : S ≤ X) (hS : Nat.card S = Nat.card k)
    (hfixS : Nat.card (A ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ n) {J : Subgroup G}
    (hJX : J ≤ X) (hJS : J ≤ normalizer (S : Set G)) (hJcard : Nat.card J = Nat.card k - 1)
    (hJinf : J ⊓ S = ⊥) {a b : G} (ha : a ∈ A ⊓ centralizer (S : Set G))
    (hb : b ∈ A ⊓ centralizer (S : Set G)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ j ∈ J, j * a * j⁻¹ = b := by
  obtain ⟨-, hstab, -⟩ := natural_module_of_card hk ψ hcomm hXA hcard hfix hSX hS hfixS
  have hq : 1 ≤ Nat.card k := Nat.card_pos
  exact exists_conj_eq_of_stab hXA hJX hJS hJinf (by rw [hJcard, hfixS, ← hk]; omega) ha hb ha1
    hb1 (hstab a ha ha1)

end CFSG.LocalAnalysis.EvenBN.Common
