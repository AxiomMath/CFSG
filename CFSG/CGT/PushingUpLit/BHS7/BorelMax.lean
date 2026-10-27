module

public import CFSG.CGT.PushingUpLit.BHS.SL2Facts
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.CGT.PushingUpLit.BHS
open scoped LinearAlgebra.Projectivization

variable {Γ : Type} [Group Γ] [Finite Γ] {F : Type} [Field F] [Finite F] [CharP F 2]
  {E S : Subgroup Γ}

omit [Finite Γ] [CharP F 2] in
theorem mem_normalizer_iff_smul_eq (π : ↥E →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hπ : Function.Surjective π) (hSE : S ≤ E) (hker : π.ker ≤ S.subgroupOf E)
    {ℓ : ℙ F (Fin 2 → F)} (hℓ : (S.subgroupOf E).map π = rootGrp ℓ) (x : ↥E) :
    (x : Γ) ∈ Subgroup.normalizer (S : Set Γ) ↔ π x • ℓ = ℓ := by
  have hiff : ∀ y : ↥E, (y : Γ) ∈ S ↔ π y ∈ rootGrp ℓ := by
    intro y
    constructor
    · intro hy
      rw [← hℓ]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hy)
    · intro hy
      rw [← hℓ] at hy
      obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
      have h1 : π (s⁻¹ * y) = 1 := by rw [map_mul, map_inv, hsy, inv_mul_cancel]
      have h2 : s⁻¹ * y ∈ S.subgroupOf E := hker h1
      have h3 : y = s * (s⁻¹ * y) := by group
      rw [h3]
      exact S.mul_mem (Subgroup.mem_subgroupOf.mp hs) (Subgroup.mem_subgroupOf.mp h2)
  have hconj : ∀ u : ↥E, π (x * u * x⁻¹) = π x * π u * (π x)⁻¹ := fun u => by
    simp [map_mul, map_inv]
  rw [← mem_normalizer_rootGrp_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx t
    obtain ⟨u, rfl⟩ := hπ t
    rw [← hconj u, ← hiff, ← hiff]
    exact hx (u : Γ)
  · intro hx h
    constructor
    · intro hh
      have hhE : h ∈ E := hSE hh
      have h1 := (hx (π ⟨h, hhE⟩)).mp ((hiff ⟨h, hhE⟩).mp hh)
      rw [← hconj, ← hiff] at h1
      exact h1
    · intro hh
      have hxS : (x : Γ) * h * (x : Γ)⁻¹ ∈ E := hSE hh
      have hhE : h ∈ E := by
        have := E.mul_mem (E.mul_mem (E.inv_mem x.2) hxS) x.2
        simpa [mul_assoc] using this
      have h1 : π ⟨(x : Γ) * h * (x : Γ)⁻¹, hxS⟩ ∈ rootGrp ℓ := (hiff _).mp hh
      have h2 : (⟨(x : Γ) * h * (x : Γ)⁻¹, hxS⟩ : ↥E) = x * ⟨h, hhE⟩ * x⁻¹ := rfl
      rw [h2, hconj] at h1
      exact (hiff ⟨h, hhE⟩).mpr ((hx (π ⟨h, hhE⟩)).mpr h1)

theorem normalizer_inf_maximal_of_sl2 (hS : IsSylowTwoOf S E)
    (π : ↥E →* Matrix.SpecialLinearGroup (Fin 2) F) (hπ : Function.Surjective π)
    (hker : π.ker ≤ S.subgroupOf E) {K : Subgroup Γ} (hKE : K ≤ E)
    (hK : Subgroup.normalizer (S : Set Γ) ⊓ E ≤ K) :
    K = Subgroup.normalizer (S : Set Γ) ⊓ E ∨ K = E := by
  obtain ⟨ℓ, hℓ⟩ := exists_rootGrp_eq_map_of_isSylowTwoOf hS π hπ
  have hSE : S ≤ E := hS.1
  have hSK : S ≤ K := fun s hs =>
    hK ⟨Subgroup.le_normalizer hs, hSE hs⟩
  by_cases hall : ∀ k : ↥E, (k : Γ) ∈ K → π k • ℓ = ℓ
  · left
    refine le_antisymm (fun k hk => ?_) hK
    exact ⟨(mem_normalizer_iff_smul_eq π hπ hSE hker hℓ ⟨k, hKE hk⟩).mpr (hall ⟨k, hKE hk⟩ hk),
      hKE hk⟩
  · right
    push Not at hall
    obtain ⟨k, hkK, hkℓ⟩ := hall
    have hX : rootGrp ℓ ≤ (K.subgroupOf E).map π := by
      rw [← hℓ]
      exact Subgroup.map_mono (fun s hs => Subgroup.mem_subgroupOf.mpr
        (hSK (Subgroup.mem_subgroupOf.mp hs)))
    have htop := eq_top_of_rootGrp_le hX ⟨π k, Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr hkK), hkℓ⟩
    refine le_antisymm hKE fun e he => ?_
    have hmem : π ⟨e, he⟩ ∈ (K.subgroupOf E).map π := htop ▸ Subgroup.mem_top _
    obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.mp hmem
    have h1 : π (k'⁻¹ * ⟨e, he⟩) = 1 := by rw [map_mul, map_inv, hk'e, inv_mul_cancel]
    have h2 : k'⁻¹ * ⟨e, he⟩ ∈ S.subgroupOf E := hker h1
    have h4 : e = (k' : Γ) * ((k'⁻¹ * ⟨e, he⟩ : ↥E) : Γ) := by simp
    rw [h4]
    exact K.mul_mem (Subgroup.mem_subgroupOf.mp hk')
      (hSK (Subgroup.mem_subgroupOf.mp h2))

end CFSG.CGT.PushingUpLit.BHS7
