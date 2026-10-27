module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84h_exists_two_part {M A : Type} [Group M] [Finite M] [Group A] (θ : M →* A)
    (m : M) (h : θ m * θ m = 1) :
    ∃ m' : M, (∃ a : ℕ, m' ^ 2 ^ a = 1) ∧ θ m' = θ m := by
  obtain ⟨a, k, hk, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  obtain ⟨j, rfl⟩ := hk
  refine ⟨m ^ (2 * j + 1), ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm (2 * j + 1) (2 ^ a), ← hord, pow_orderOf_eq_one]
  · rw [map_pow,
      show (θ m) ^ (2 * j + 1) = ((θ m) ^ 2) ^ j * θ m by rw [pow_succ, pow_mul]]
    rw [pow_two, h, one_pow, one_mul]

theorem sec8t84h_exists_conj_into_sylow2 {G : Type} [Group G] [Finite G] {S N K : Subgroup G}
    (hS : IsSylow2Of S N) (hKN : K ≤ N) (hK : IsPGroup 2 K) :
    ∃ g ∈ N, ∀ k ∈ K, g * k * g⁻¹ ∈ S := by
  obtain ⟨S', hS', hKS'⟩ := exists_isSylow2Of_ge hK hKN
  obtain ⟨a, haN, ha⟩ := IsSylow2Of.exists_conj_mem hS hS'
  exact ⟨a⁻¹, N.inv_mem haN, fun k hk => by
    rw [inv_inv]
    exact (ha k).mp (hKS' hk)⟩

theorem sec8t84h_isSylow2Of_map_subtype {X : Type} [Group X] (K : Subgroup X)
    {P : Subgroup ↥K} (hP : IsSylow2Of P ⊤) : IsSylow2Of (P.map K.subtype) K := by
  refine ⟨Subgroup.map_subtype_le P, hP.2.1.map K.subtype, ?_⟩
  have hsub : (P.map K.subtype).subgroupOf K = P :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K) P
  rw [Subgroup.relIndex, hsub]
  simpa [Subgroup.relIndex_top_right] using hP.2.2

theorem sec8t84h_omega1_of_map_subtype {X : Type} [Group X] (K : Subgroup X) {P : Subgroup ↥K}
    (h : omega1 (P.map K.subtype) = P.map K.subtype) : omega1 P = P := by
  have hset : K.subtype '' {x : ↥K | x ∈ P ∧ x ^ 2 = 1}
      = {y : X | y ∈ P.map K.subtype ∧ y ^ 2 = 1} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxP, hx2⟩, rfl⟩
      exact ⟨⟨x, hxP, rfl⟩, by rw [← map_pow, hx2, map_one]⟩
    · rintro ⟨hyP, hy2⟩
      obtain ⟨w, hwP, hwy⟩ := Subgroup.mem_map.mp hyP
      subst hwy
      exact ⟨w, ⟨hwP, by
        apply K.subtype_injective
        rw [map_one, map_pow, hy2]⟩, rfl⟩
  have h1 : (omega1 P).map K.subtype = omega1 (P.map K.subtype) := by
    unfold omega1
    rw [MonoidHom.map_closure, hset]
  exact Subgroup.map_injective (Subgroup.subtype_injective K) (h1.trans h)

theorem sec8t84h_mem_normalizer_of_map {A B : Type} [Group A] [Group B] (ι : A →* B)
    (hι : Function.Injective ι) {P : Subgroup A} {x : A}
    (hx : ι x ∈ Subgroup.normalizer ((P.map ι : Subgroup B) : Set B)) :
    x ∈ Subgroup.normalizer (P : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · intro hh
    have h1 : ι h ∈ P.map ι := (Subgroup.mem_map_iff_mem hι).mpr hh
    have h2 : ι x * ι h * (ι x)⁻¹ ∈ P.map ι := (hx (ι h)).mp h1
    rw [← map_mul, ← map_inv, ← map_mul] at h2
    exact (Subgroup.mem_map_iff_mem hι).mp h2
  · intro hh
    have h1 : ι (x * h * x⁻¹) ∈ P.map ι := (Subgroup.mem_map_iff_mem hι).mpr hh
    rw [map_mul, map_mul, map_inv] at h1
    exact (Subgroup.mem_map_iff_mem hι).mp ((hx (ι h)).mpr h1)

theorem sec8t84h_isElemAb2_subgroupOf {X : Type} [Group X] {K B : Subgroup X} (hBK : B ≤ K)
    {k : ℕ} (h : IsElemAb2 B k) : IsElemAb2 (B.subgroupOf K) k := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsMulCommutative ↥B := h.1.1
    infer_instance
  · intro x hx
    have hxB : (x : X) ∈ B := (Subgroup.mem_subgroupOf).mp hx
    apply Subtype.ext
    simpa using h.1.2 (x : X) hxB
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, h.2]

end CFSG.OddStandard.SmallF3.Omega
