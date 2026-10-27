module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem isSubnormal_subgroupOf_of_three_step {A : Type*} [Group A] {H L M C : Subgroup A}
    (hHL : H ≤ L) (hLM : L ≤ M) (hH : ∀ h ∈ H, ∀ l ∈ L, l * h * l⁻¹ ∈ H)
    (hL : ∀ l ∈ L, ∀ m ∈ M, m * l * m⁻¹ ∈ L) (hM : ∀ m ∈ M, ∀ c ∈ C, c * m * c⁻¹ ∈ M) :
    (H.subgroupOf C).IsSubnormal := by
  have hMn : (M.subgroupOf C).Normal := by
    constructor
    intro m hm c
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact hM _ hm _ c.2
  have hLsub : (L.subgroupOf C).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (M.subgroupOf C) ?_ hMn.isSubnormal ?_
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact hLM hx
    · constructor
      intro l hl m
      have hl' : ((l : ↥C) : A) ∈ L :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hl)
      have hm' : ((m : ↥C) : A) ∈ M := Subgroup.mem_subgroupOf.mp m.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hL _ hl' _ hm'
  refine Subgroup.IsSubnormal.step _ (L.subgroupOf C) ?_ hLsub ?_
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hHL hx
  · constructor
    intro h hh g
    have hh' : ((h : ↥C) : A) ∈ H := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh)
    have hg : ((g : ↥C) : A) ∈ L := Subgroup.mem_subgroupOf.mp g.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hH _ hh' _ hg

theorem isI4PlusIn_map_of_chain {A B : Type} [Group A] [Group B] (ρ : A →* B)
    (hρ : Function.Surjective ρ) (hcent : ∀ m ∈ ρ.ker, ∀ g : A, g * m = m * g)
    {z : A} (hzz : orderOf z = 2) {K M : Subgroup A} (hzK : z ∈ K) (hKM : K ≤ M)
    (hMC : M ≤ centralizer ({z} : Set A))
    (hKM' : ∀ h ∈ K, ∀ l ∈ M, l * h * l⁻¹ ∈ K)
    (hMC' : ∀ l ∈ M, ∀ c ∈ centralizer ({z} : Set A), c * l * c⁻¹ ∈ M)
    (hK : IsSL23Mod K) (hdis : Disjoint K ρ.ker) :
    IsI4PlusIn (⊤ : Subgroup B) (ρ z) := by
  have hKker : K ⊓ ρ.ker = ⊥ := disjoint_iff.mp hdis
  have hzz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzz
    exact absurd hzz (by decide)
  have hρz_ne : ρ z ≠ 1 := by
    intro h
    have hzker : z ∈ ρ.ker := MonoidHom.mem_ker.mpr h
    have hzb : z ∈ (⊥ : Subgroup A) := by
      rw [← hKker]
      exact ⟨hzK, hzker⟩
    exact hzz1 (Subgroup.mem_bot.mp hzb)
  have hzsq : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzz] at this
  have hρz2 : (ρ z) ^ 2 = 1 := by
    rw [← map_pow, hzsq, map_one]
  have key : ∀ g : A, ρ g * ρ z = ρ z * ρ g →
      ∀ c ∈ centralizer ({z} : Set A), g * c * g⁻¹ ∈ centralizer ({z} : Set A) := by
    intro g hgz c hc
    set n : A := z⁻¹ * (g * z * g⁻¹) with hn
    have hρn : ρ n = 1 := by
      rw [hn]
      simp only [map_mul, map_inv]
      rw [hgz]
      group
    have hnmem : n ∈ ρ.ker := MonoidHom.mem_ker.mpr hρn
    have hnc : ∀ a : A, a * n = n * a := fun a => hcent n hnmem a
    have hzconj : g * z * g⁻¹ = z * n := by rw [hn]; group
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have hcomm : (g * c * g⁻¹) * (z * n) = (z * n) * (g * c * g⁻¹) := by
      rw [← hzconj]
      calc (g * c * g⁻¹) * (g * z * g⁻¹) = g * (c * z) * g⁻¹ := by group
        _ = g * (z * c) * g⁻¹ := by rw [hc]
        _ = (g * z * g⁻¹) * (g * c * g⁻¹) := by group
    have h1 : (g * c * g⁻¹) * (z * n) = n * ((g * c * g⁻¹) * z) := by
      calc (g * c * g⁻¹) * (z * n) = (g * c * g⁻¹) * (n * z) := by rw [hnc z]
        _ = ((g * c * g⁻¹) * n) * z := by group
        _ = (n * (g * c * g⁻¹)) * z := by rw [hnc (g * c * g⁻¹)]
        _ = n * ((g * c * g⁻¹) * z) := by group
    have h2 : (z * n) * (g * c * g⁻¹) = n * (z * (g * c * g⁻¹)) := by
      calc (z * n) * (g * c * g⁻¹) = z * (n * (g * c * g⁻¹)) := by group
        _ = z * ((g * c * g⁻¹) * n) := by rw [(hnc (g * c * g⁻¹)).symm]
        _ = (z * (g * c * g⁻¹)) * n := by group
        _ = n * (z * (g * c * g⁻¹)) := hnc (z * (g * c * g⁻¹))
    have hn_eq : n * ((g * c * g⁻¹) * z) = n * (z * (g * c * g⁻¹)) := by
      rw [← h1, hcomm, h2]
    exact mul_left_cancel hn_eq
  have hsub : ((K.map ρ).subgroupOf (⊤ ⊓ centralizer ({ρ z} : Set B))).IsSubnormal := by
    refine isSubnormal_subgroupOf_of_three_step (C := ⊤ ⊓ centralizer ({ρ z} : Set B))
      (Subgroup.map_mono hKM) (Subgroup.map_mono hMC) ?_ ?_ ?_
    · intro h hh l hl
      obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      exact Subgroup.mem_map.mpr ⟨l₀ * h₀ * l₀⁻¹, hKM' h₀ hh₀ l₀ hl₀, by simp⟩
    · intro l hl m hm
      obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.mp hl
      obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
      exact Subgroup.mem_map.mpr ⟨m₀ * l₀ * m₀⁻¹, hMC' l₀ hl₀ m₀ hm₀, by simp⟩
    · intro m hm c hc
      obtain ⟨m₀, hm₀, rfl⟩ := Subgroup.mem_map.mp hm
      have hcC : c ∈ centralizer ({ρ z} : Set B) := (Subgroup.mem_inf.mp hc).2
      obtain ⟨g, hg⟩ := hρ c
      have hcomm : ρ g * ρ z = ρ z * ρ g := by
        rw [hg]
        exact Subgroup.mem_centralizer_singleton_iff.mp hcC
      refine Subgroup.mem_map.mpr ⟨g * m₀ * g⁻¹, key g hcomm m₀ hm₀, ?_⟩
      rw [← hg]
      simp
  have hker : (ρ.domRestrict K).ker = ⊥ := by
    rw [MonoidHom.ker_domRestrict]
    exact Subgroup.subgroupOf_eq_bot.mpr hdis.symm
  have hinj : Function.Injective (ρ.domRestrict K) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have hsl : IsSL23Mod ↥(K.map ρ) :=
    isSL23Mod_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans
        (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range (f := ρ) (K := K)))) hK
  refine ⟨orderOf_eq_prime hρz2 hρz_ne, K.map ρ, ?_, ?_, hsub, hsl⟩
  · exact Subgroup.mem_map.mpr ⟨z, hzK, rfl⟩
  · refine le_inf le_top ?_
    rintro x ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hMC (hKM hk))]

end CFSG.OddStandard.SmallF3.Omega
