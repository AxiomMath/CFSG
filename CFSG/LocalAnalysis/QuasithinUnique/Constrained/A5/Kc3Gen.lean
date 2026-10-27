module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.Subnormal
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.QuasithinUnique.A5.Kc3Gen

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem isSubnormal_le {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B :=
  h.le

theorem isSubnormal_map {Γ Γ' : Type*} [Group Γ] [Group Γ'] (f : Γ →* Γ') {A B : Subgroup Γ}
    (h : IsSubnormal A B) : IsSubnormal (A.map f) (B.map f) :=
  h.map f

theorem isSubnormal_subgroupOf {A B : Subgroup G} (N : Subgroup G) (h : IsSubnormal A B) :
    IsSubnormal (A.subgroupOf N) (B.subgroupOf N) :=
  h.comap N.subtype

theorem exists_pow_mem {K T₀ : Subgroup G} (hT : IsPGroup 2 T₀)
    (hTK : T₀ ≤ Subgroup.normalizer (K : Set G)) {c : G} (hc : c ∈ K ⊔ T₀) :
    ∃ m : ℕ, c ^ (2 ^ m) ∈ K := by
  rw [sup_comm] at hc
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right T₀ K hTK
  have hc' : c ∈ ((T₀ ⊔ K : Subgroup G) : Set G) := hc
  rw [hmul] at hc'
  obtain ⟨t, ht, k, hk, rfl⟩ := hc'
  obtain ⟨m, hm⟩ := hT ⟨t, ht⟩
  refine ⟨m, ?_⟩
  have hm' : t ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  have key : ∀ n : ℕ, ∃ k' ∈ K, (t * k) ^ n = t ^ n * k' := by
    intro n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', h⟩ := ih
      have hconj : t⁻¹ * k' * t ∈ K := by
        have := (Subgroup.mem_normalizer_iff.1 (hTK (T₀.inv_mem ht)) k').1 hk'
        simpa using this
      refine ⟨t⁻¹ * k' * t * k, K.mul_mem hconj hk, ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨k', hk', h⟩ := key (2 ^ m)
  rw [h, hm', one_mul]
  exact hk'

theorem charTwo_normalizer [Finite G] {K T₀ R : Subgroup G} (hT : IsPGroup 2 T₀)
    (hTK : T₀ ≤ Subgroup.normalizer (K : Set G)) (hR : IsPGroup 2 R) (hRK : R ≤ K)
    (hC : K ⊓ Subgroup.centralizer (R : Set G) ≤ R) :
    CharTwo ((K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := (K ⊔ T₀) ⊓ Subgroup.normalizer (R : Set G) with hX
  have hRX : R ≤ X := le_inf (hRK.trans le_sup_left) Subgroup.le_normalizer
  have hRD : R ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRX inf_le_right hR
  set D : Subgroup G := pCoreOf 2 X with hD
  have hXD : X ≤ Subgroup.normalizer (D : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  set C : Subgroup G := X ⊓ Subgroup.centralizer (D : Set G) with hCdef
  have hconj : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro x hx c hc
    refine ⟨X.mul_mem (X.mul_mem hx hc.1) (X.inv_mem hx), ?_⟩
    show x * c * x⁻¹ ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : x⁻¹ * d * x ∈ D := by
      have := (Subgroup.mem_normalizer_iff.1 (hXD (X.inv_mem hx)) d).1 hd
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hd'
    calc d * (x * c * x⁻¹) = x * ((x⁻¹ * d * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * d * x)) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * d := by group
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun h => hconj x hx c h, fun h => ?_⟩
    have := hconj x⁻¹ (X.inv_mem hx) _ h
    simpa [mul_assoc] using this
  have hC2 : IsPGroup 2 C := by
    intro c
    obtain ⟨m, hm⟩ := exists_pow_mem hT hTK (c.2.1.1 : (c : G) ∈ K ⊔ T₀)
    have hcent : (c : G) ^ (2 ^ m) ∈ Subgroup.centralizer (R : Set G) :=
      Subgroup.centralizer_le (s := (R : Set G)) (t := (D : Set G)) hRD
        (Subgroup.pow_mem _ c.2.2 _)
    have hmem : (c : G) ^ (2 ^ m) ∈ R := hC ⟨hm, hcent⟩
    obtain ⟨j, hj⟩ := hR ⟨_, hmem⟩
    refine ⟨m + j, Subtype.ext ?_⟩
    have hj' : ((c : G) ^ (2 ^ m)) ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    rw [← pow_mul, ← pow_add] at hj'
    exact hj'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXC hC2

theorem exists_sylowTwoOf_le [Finite G] {X S₀ : Subgroup G} (hSX : S₀ ≤ X)
    (hS : IsPGroup 2 S₀) : ∃ S₁ : Subgroup G, S₀ ≤ S₁ ∧ IsSylowTwoOf S₁ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW' : IsPGroup 2 ↥(S₀.subgroupOf X) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  obtain ⟨P', hP'⟩ := hW'.exists_le_sylow
  refine ⟨(P' : Subgroup ↥X).map X.subtype, ?_, Subgroup.map_subtype_le _, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hSX hx⟩, hP' (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · exact P'.isPGroup'.map X.subtype
  · have e : ((P' : Subgroup ↥X).map X.subtype).subgroupOf X = (P' : Subgroup ↥X) := by
      show (((P' : Subgroup ↥X).map X.subtype).comap X.subtype) = _
      rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    rw [e]
    exact P'.not_dvd_index' (Subgroup.index_ne_zero_of_finite)

end CFSG.QuasithinUnique.A5.Kc3Gen
