module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPositive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRootGen

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

section SetMul

variable {G : Type*} [Group G]

theorem mem_mul_singleton_mul {S T : Set G} {x g : G} :
    g ∈ S * {x} * T ↔ ∃ s ∈ S, ∃ t ∈ T, g = s * x * t := by
  simp only [Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨s, hs, _, rfl, rfl⟩, t, ht, rfl⟩
    exact ⟨s, hs, t, ht, rfl⟩
  · rintro ⟨s, hs, t, ht, rfl⟩
    exact ⟨_, ⟨s, hs, x, rfl, rfl⟩, t, ht, rfl⟩

theorem mem_mul_singleton_mul_singleton_mul {S T U : Set G} {x y g : G} :
    g ∈ S * {x} * T * {y} * U ↔ ∃ s ∈ S, ∃ t ∈ T, ∃ u ∈ U, g = s * x * t * y * u := by
  simp only [Set.mem_mul, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨s, hs, _, rfl, rfl⟩, t, ht, rfl⟩, _, rfl, rfl⟩, u, hu, rfl⟩
    exact ⟨s, hs, t, ht, u, hu, rfl⟩
  · rintro ⟨s, hs, t, ht, u, hu, rfl⟩
    exact ⟨_, ⟨_, ⟨_, ⟨s, hs, x, rfl, rfl⟩, t, ht, rfl⟩, y, rfl, rfl⟩, u, hu, rfl⟩

end SetMul

section Conj

variable (hr : 2 ≤ r)
include hr

theorem inv_mul_torus_mul_mem {n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hn : n ∈ torusWeyl r K) {t : (Fin r ⊕ Fin r → K) ≃ₗ[K] _} (ht : t ∈ torus r K) :
    n⁻¹ * t * n ∈ torus r K := by
  have htN : t ∈ torusWeyl r K := torus_le_torusWeyl ht
  have hker : (⟨t, htN⟩ : torusWeyl r K) ∈ (torusWeylNu r K hr).ker := by
    rw [torusWeylNu_ker hr, Subgroup.mem_subgroupOf]
    exact ht
  have hker' : (⟨n, hn⟩ : torusWeyl r K)⁻¹ * ⟨t, htN⟩ * ⟨n, hn⟩ ∈ (torusWeylNu r K hr).ker := by
    rw [MonoidHom.mem_ker] at hker ⊢
    rw [map_mul, map_mul, hker, mul_one, map_inv, inv_mul_cancel]
  rw [torusWeylNu_ker hr, Subgroup.mem_subgroupOf] at hker'
  exact hker'

theorem inv_mul_rootElt_mul_mem {n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hn : n ∈ torusWeyl r K) {β : Fin r → ℤ} (hβ : β ∈ roots r) (s : K) :
    n⁻¹ * rootElt r K β s * n ∈
      rootSubgroup r K ((((torusWeylNu r K hr ⟨n, hn⟩)⁻¹ : weylGroup r) :
        (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) β) := by
  have h := map_conj_rootSubgroup_torusWeyl hr (⟨n, hn⟩ : torusWeyl r K)⁻¹ hβ
  rw [map_inv] at h
  rw [← h]
  refine ⟨rootElt r K β s, rootElt_mem_rootSubgroup _ _, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv, inv_inv]

end Conj

section Exchange

variable (hr : 3 ≤ r)
include hr

theorem exists_borel_weylElt_rootElt {n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hn : n ∈ torusWeyl r K) (i : Fin r)
    {b₁ b₂ b₃ : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (h1 : b₁ ∈ borel r K)
    (h2 : b₂ ∈ borel r K) (h3 : b₃ ∈ borel r K) :
    ∃ c₁ ∈ borel r K, ∃ s : K, ∃ c₂ ∈ borel r K,
      b₁ * weylElt r K i * b₂ * n * b₃ =
        c₁ * weylElt r K i * rootElt r K (simpleRoot r i) s * n * c₂ := by
  have hr2 : 2 ≤ r := by omega
  obtain ⟨-, -, hUT, hUi⟩ := orthogonal_geometry_split_positive_root_factorization (K := K) hr
  obtain ⟨-, -, hfac, -, hconj⟩ := hUi i
  have hb2 : b₂ ∈ (unipotent r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
      (torus r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) := by
    rw [← hUT]
    exact h2
  obtain ⟨u₀, hu₀, t, ht, rfl⟩ := hb2
  have hu₀' : u₀ ∈
      (unipotentExcept r K i : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) *
        (rootSubgroup r K (simpleRoot r i) : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)))
      := by
    rw [← hfac]
    exact hu₀
  obtain ⟨u, hu, x, ⟨s, rfl⟩, rfl⟩ := hu₀'
  have hc₁ : b₁ * (weylElt r K i * u * (weylElt r K i)⁻¹) ∈ borel r K :=
    mul_mem h1 (unipotent_le_borel (hconj ⟨u, hu, rfl⟩))
  have hc₂ : (n⁻¹ * t * n) * b₃ ∈ borel r K :=
    mul_mem (torus_le_borel (inv_mul_torus_mul_mem hr2 hn ht)) h3
  exact ⟨_, hc₁, s, _, hc₂, by group⟩

theorem borel_weylElt_mul_mem {n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    (hn : n ∈ torusWeyl r K) (i : Fin r)
    {b₁ b₂ b₃ : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (h1 : b₁ ∈ borel r K)
    (h2 : b₂ ∈ borel r K) (h3 : b₃ ∈ borel r K) :
    ((((torusWeylNu r K (by omega) ⟨n, hn⟩)⁻¹ : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
        (simpleRoot r i) ∈ posRoots r →
      ∃ c₁ ∈ borel r K, ∃ c₂ ∈ borel r K,
        b₁ * weylElt r K i * b₂ * n * b₃ = c₁ * (weylElt r K i * n) * c₂) ∧
    ((∃ c₁ ∈ borel r K, ∃ c₂ ∈ borel r K,
        b₁ * weylElt r K i * b₂ * n * b₃ = c₁ * (weylElt r K i * n) * c₂) ∨
      ∃ c₁ ∈ borel r K, ∃ c₂ ∈ borel r K, b₁ * weylElt r K i * b₂ * n * b₃ = c₁ * n * c₂) := by
  have hr2 : 2 ≤ r := by omega
  obtain ⟨c₁, hc₁, s, c₂, hc₂, he⟩ := exists_borel_weylElt_rootElt hr hn i h1 h2 h3
  have hα : simpleRoot r i ∈ posRoots r := simpleRoot_mem_posRoots hr2 i
  set w := (((torusWeylNu r K hr2 ⟨n, hn⟩)⁻¹ : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
    with hw
  have hpos : w (simpleRoot r i) ∈ posRoots r →
      ∃ c₁ ∈ borel r K, ∃ c₂ ∈ borel r K,
        b₁ * weylElt r K i * b₂ * n * b₃ = c₁ * (weylElt r K i * n) * c₂ := by
    intro hwα
    have hx := inv_mul_rootElt_mul_mem hr2 hn (posRoots_subset_roots hα) s
    refine ⟨c₁, hc₁, _, mul_mem (unipotent_le_borel (rootSubgroup_le_unipotent hwα hx)) hc₂, ?_⟩
    rw [he]
    group
  refine ⟨hpos, ?_⟩
  by_cases hwα : w (simpleRoot r i) ∈ posRoots r
  · exact Or.inl (hpos hwα)
  by_cases hs : s = 0
  · refine Or.inl ⟨c₁, hc₁, c₂, hc₂, ?_⟩
    rw [he, hs, rootElt_zero, mul_one, mul_assoc c₁]
  right
  have hroot : w (simpleRoot r i) ∈ roots r :=
    apply_mem_roots (torusWeylNu r K hr2 ⟨n, hn⟩)⁻¹.2 (posRoots_subset_roots hα)
  have hneg : -(w (simpleRoot r i)) ∈ posRoots r :=
    ((mem_posRoots_or_neg_mem_posRoots hroot).1).resolve_left hwα
  obtain ⟨hH, -, hfac, hnr⟩ := orthogonal_geometry_split_root_rank_one_factorization (K := K)
    (posRoots_subset_roots hα)
  have hni : weylElt r K i = rootN r K (simpleRoot r i) 1 := hnr i
  have hx := inv_mul_rootElt_mul_mem hr2 hn (neg_mem_roots (posRoots_subset_roots hα)) s⁻¹
  rw [map_neg] at hx
  have hb : c₁ * rootElt r K (simpleRoot r i) (-s⁻¹) * rootH r K (simpleRoot r i) (-s⁻¹) ∈
      borel r K :=
    mul_mem (mul_mem hc₁ (unipotent_le_borel (rootSubgroup_le_unipotent hα
      (rootElt_mem_rootSubgroup _ _)))) (torus_le_borel (hH _ (neg_ne_zero.2 (inv_ne_zero hs))))
  refine ⟨_, hb, _, mul_mem (unipotent_le_borel (rootSubgroup_le_unipotent hneg hx)) hc₂, ?_⟩
  rw [he, mul_assoc c₁ (weylElt r K i), hni, hfac s hs]
  group

end Exchange

theorem orthogonal_geometry_split_Bruhat_exchange {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r)
    {n : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hn : n ∈ torusWeyl r K) (i : Fin r) :
    (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) * {weylElt r K i} *
        (borel r K : Set _) * {n} * (borel r K : Set _) ⊆
      (borel r K : Set _) * {weylElt r K i * n} * (borel r K : Set _) ∪
        (borel r K : Set _) * {n} * (borel r K : Set _) ∧
    ((((torusWeylNu r K (by omega) ⟨n, hn⟩)⁻¹ : weylGroup r) : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ))
        (simpleRoot r i) ∈ posRoots r →
      (borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) * {weylElt r K i} *
          (borel r K : Set _) * {n} * (borel r K : Set _) =
        (borel r K : Set _) * {weylElt r K i * n} * (borel r K : Set _)) := by
  refine ⟨fun g hg => ?_, fun hw => Set.Subset.antisymm (fun g hg => ?_) fun g hg => ?_⟩
  · obtain ⟨b₁, h1, b₂, h2, b₃, h3, rfl⟩ := mem_mul_singleton_mul_singleton_mul.1 hg
    rcases (borel_weylElt_mul_mem hr hn i h1 h2 h3).2 with ⟨c₁, hc₁, c₂, hc₂, he⟩ |
      ⟨c₁, hc₁, c₂, hc₂, he⟩
    · exact Or.inl (mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩)
    · exact Or.inr (mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩)
  · obtain ⟨b₁, h1, b₂, h2, b₃, h3, rfl⟩ := mem_mul_singleton_mul_singleton_mul.1 hg
    obtain ⟨c₁, hc₁, c₂, hc₂, he⟩ := (borel_weylElt_mul_mem hr hn i h1 h2 h3).1 hw
    exact mem_mul_singleton_mul.2 ⟨c₁, hc₁, c₂, hc₂, he⟩
  · obtain ⟨b₁, h1, b₂, h2, rfl⟩ := mem_mul_singleton_mul.1 hg
    exact mem_mul_singleton_mul_singleton_mul.2 ⟨b₁, h1, 1, one_mem _, b₂, h2, by group⟩

theorem orthogonal_geometry_split_Borel_Weyl_generation {K : Type*} [Field K] {r : ℕ}
    (hr : 3 ≤ r) :
    orthElementaryGroup (quadPlus r K) =
      Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K))) ∪
        Set.range (weylElt r K)) := by
  have hr2 : 2 ≤ r := by omega
  set H := Subgroup.closure ((borel r K : Set ((Fin r ⊕ Fin r → K) ≃ₗ[K] _)) ∪
    Set.range (weylElt r K)) with hH
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · have hB : borel r K ≤ H := fun b hb => Subgroup.subset_closure (Or.inl hb)
    have hN : torusWeyl r K ≤ H := by
      rw [torusWeyl, Subgroup.closure_le]
      rintro _ (ht | ⟨i, rfl⟩)
      · exact hB (torus_le_borel ht)
      · exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
    rw [(orthogonal_geometry_split_root_generation (K := K) hr).1, rootSupr]
    refine iSup₂_le fun α hα => ?_
    set α₀ := simpleRoot r ⟨0, by omega⟩ with hα₀
    have hα₀p : α₀ ∈ posRoots r := simpleRoot_mem_posRoots hr2 _
    obtain ⟨w, hw, hwα⟩ := exists_weyl_apply_eq hr (posRoots_subset_roots hα₀p) hα
    obtain ⟨n, hn⟩ := torusWeylNu_surjective (K := K) hr2 hr ⟨w, hw⟩
    have hmap := map_conj_rootSubgroup_torusWeyl hr2 n (posRoots_subset_roots hα₀p)
    rw [hn] at hmap
    change _ = rootSubgroup r K (w α₀) at hmap
    rw [← hwα, ← hmap]
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem (hN n.2) (hB (unipotent_le_borel (rootSubgroup_le_unipotent hα₀p hx))))
      (inv_mem (hN n.2))
  · rintro _ (hb | ⟨i, rfl⟩)
    · exact borel_le hb
    · exact weylElt_mem i

theorem orthogonal_geometry_split_Bruhat_coverage {K : Type*} [Field K] {r : ℕ} (hr : 3 ≤ r)
    (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) :
    g ∈ orthElementaryGroup (quadPlus r K) ↔
      ∃ b₁ ∈ borel r K, ∃ n ∈ torusWeyl r K, ∃ b₂ ∈ borel r K, g = b₁ * n * b₂ := by
  have hr2 : 2 ≤ r := by omega
  refine ⟨fun hg => ?_, ?_⟩
  · rw [orthogonal_geometry_split_Borel_Weyl_generation hr] at hg
    have hni : ∀ (i : Fin r) (y : (Fin r ⊕ Fin r → K) ≃ₗ[K] _),
        (∃ b₁ ∈ borel r K, ∃ n ∈ torusWeyl r K, ∃ b₂ ∈ borel r K, y = b₁ * n * b₂) →
        ∃ b₁ ∈ borel r K, ∃ n ∈ torusWeyl r K, ∃ b₂ ∈ borel r K,
          weylElt r K i * y = b₁ * n * b₂ := by
      rintro i _ ⟨b₁, h1, n, hn, b₂, h2, rfl⟩
      rcases (borel_weylElt_mul_mem hr hn i (one_mem _) h1 h2).2 with
        ⟨c₁, hc₁, c₂, hc₂, he⟩ | ⟨c₁, hc₁, c₂, hc₂, he⟩
      · exact ⟨c₁, hc₁, _, mul_mem (weylElt_mem_torusWeyl i) hn, c₂, hc₂, by
          rw [← he]
          group⟩
      · exact ⟨c₁, hc₁, n, hn, c₂, hc₂, by
          rw [← he]
          group⟩
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by group⟩
    | mul_left x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ := ih
        exact ⟨x * b₁, mul_mem hx h1, n, hn, b₂, h2, by group⟩
      · exact hni i y ih
    | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ := ih
        exact ⟨x⁻¹ * b₁, mul_mem (inv_mem hx) h1, n, hn, b₂, h2, by group⟩
      ·
        obtain ⟨-, hsq, -, hn⟩ := orthogonal_geometry_split_root_rank_one_factorization (K := K)
          (posRoots_subset_roots (simpleRoot_mem_posRoots hr2 i))
        rw [← hn i] at hsq
        obtain ⟨b₁, h1, n, hn', b₂, h2, rfl⟩ := ih
        obtain ⟨c₁, hc₁, m, hm, c₂, hc₂, he⟩ := hni i ((weylElt r K i ^ 2)⁻¹ * b₁ * n * b₂)
          ⟨_, mul_mem (inv_mem (torus_le_borel hsq)) h1, n, hn', b₂, h2, rfl⟩
        refine ⟨c₁, hc₁, m, hm, c₂, hc₂, ?_⟩
        rw [← he]
        group
  · rintro ⟨b₁, h1, n, hn, b₂, h2, rfl⟩
    exact mul_mem (mul_mem (borel_le h1) (torusWeyl_le hn)) (borel_le h2)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
