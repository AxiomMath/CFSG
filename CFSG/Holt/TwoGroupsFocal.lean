module

public import CFSG.Holt.Centralizer

public section

namespace CFSG.Holt

open Subgroup CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

section Focal

theorem focalSubgroup_le_of_conj {P U : Subgroup G}
    (hfoc : ∀ x ∈ P, ∀ g : G, g * x * g⁻¹ ∈ P → x⁻¹ * (g * x * g⁻¹) ∈ U) :
    P.focalSubgroup ≤ U := by
  rw [Subgroup.focalSubgroup_def, Subgroup.closure_le]
  rintro _ ⟨hgP, x, hxP, u, rfl⟩
  have h1 : u * x⁻¹ * u⁻¹ ∈ P := by
    have e : u * x⁻¹ * u⁻¹ = x⁻¹ * ⁅x, u⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (inv_mem hxP) hgP
  have h2 := hfoc x⁻¹ (inv_mem hxP) u h1
  rw [inv_inv] at h2
  rw [SetLike.mem_coe, commutatorElement_def]
  simpa only [mul_assoc] using h2

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_normal_inf_eq_of_focal (P : Sylow p G) {U : Subgroup G} (hUP : U ≤ P)
    (hfoc : ∀ x ∈ (P : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) →
      x⁻¹ * (g * x * g⁻¹) ∈ U) :
    ∃ (N : Subgroup G) (_ : N.Normal), IsPGroup p (G ⧸ N) ∧ N.index = U.relIndex P ∧
      N ⊓ P = U := by
  classical
  have hF := focalSubgroup_le_of_conj hfoc
  set ψ := (P : Subgroup G).transferFocal with hψ
  have hψs : Function.Surjective ψ := Subgroup.transferFocal_surjective P
  have hUn : (U.map ψ).Normal := inferInstance
  set N := (U.map ψ).comap ψ with hN
  have hNn : N.Normal := hUn.comap ψ
  have hinf : N ⊓ P = U := by
    refine le_antisymm (fun x hx => ?_) (le_inf (Subgroup.le_comap_map ψ U) hUP)
    have hx1 : ψ x ∈ U.map ψ := (Subgroup.mem_inf.mp hx).1
    have hxP : x ∈ (P : Subgroup G) := (Subgroup.mem_inf.mp hx).2
    obtain ⟨u, huU, hu⟩ := Subgroup.mem_map.mp hx1
    have hk : u⁻¹ * x ∈ ψ.ker ⊓ P := Subgroup.mem_inf.mpr
      ⟨by rw [MonoidHom.mem_ker, map_mul, map_inv, hu, inv_mul_cancel],
        mul_mem (inv_mem (hUP huU)) hxP⟩
    rw [Subgroup.ker_transferFocal_inf_eq_focalSubgroup] at hk
    simpa using mul_mem huU (hF hk)
  have hsup : (P : Subgroup G) ⊔ N = ⊤ := by
    refine eq_top_iff.mpr fun g _ => ?_
    obtain ⟨y, hy⟩ := Subgroup.focalSubgroupOf.pow_index_surjective P (ψ g)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hx : ψ x = ψ g := by
      rw [hψ, Subgroup.transferFocal_eq_pow]
      exact hy
    have hk : (x : G)⁻¹ * g ∈ N := by
      change ψ ((x : G)⁻¹ * g) ∈ U.map ψ
      rw [map_mul, map_inv, hx, inv_mul_cancel]
      exact one_mem _
    simpa using Subgroup.mul_mem_sup x.2 hk
  have hidx : N.index = U.relIndex P := by
    rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right,
      ← Subgroup.inf_relIndex_right, hinf]
  refine ⟨N, hNn, ?_, hidx, hinf⟩
  have hQ : IsPGroup p (P ⧸ (P : Subgroup G).focalSubgroupOf) := P.2.to_quotient _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have hdvd : N.index ∣ p ^ n := by
    rw [hN, Subgroup.index_comap_of_surjective _ hψs, ← hn]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact IsPGroup.of_card (n := j) (by rw [← Subgroup.index, hj])

end Focal

section Relative

theorem exists_le_of_subgroupOf {p : ℕ} {H S U : Subgroup G} (hSH : S ≤ H) (hUS : U ≤ S)
    {N' : Subgroup H} (hN' : N'.Normal) (hp : IsPGroup p (H ⧸ N'))
    (hidx : N'.index = (U.subgroupOf H).relIndex (S.subgroupOf H))
    (hinf : N' ⊓ S.subgroupOf H = U.subgroupOf H) :
    ∃ N : Subgroup G, N ≤ H ∧ ∃ (_ : (N.subgroupOf H).Normal),
      IsPGroup p (H ⧸ N.subgroupOf H) ∧ N.relIndex H = U.relIndex S ∧ N ⊓ S = U := by
  have hsub : (N'.map H.subtype).subgroupOf H = N' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N'
  refine ⟨N'.map H.subtype, Subgroup.map_subtype_le N', ?_⟩
  rw [Subgroup.relIndex, hsub, hidx, Subgroup.relIndex_subgroupOf hSH]
  refine ⟨hN', hp, rfl, le_antisymm (fun x hx => ?_) fun x hx => ?_⟩
  · obtain ⟨⟨y, hyN, rfl⟩, hyS⟩ := Subgroup.mem_inf.mp hx
    have hy : y ∈ N' ⊓ S.subgroupOf H := Subgroup.mem_inf.mpr ⟨hyN, hyS⟩
    rw [hinf] at hy
    exact hy
  · have hy : (⟨x, hSH (hUS hx)⟩ : H) ∈ N' ⊓ S.subgroupOf H := by
      rw [hinf]
      exact hx
    exact Subgroup.mem_inf.mpr ⟨⟨_, (Subgroup.mem_inf.mp hy).1, rfl⟩, hUS hx⟩

variable [Finite G]

theorem exists_normal_inf_eq_of_focal' {p : ℕ} [Fact p.Prime] {H S U : Subgroup G}
    (hS : fusionIsSylowIn p S H) (hUS : U ≤ S)
    (hfoc : ∀ x ∈ S, ∀ g ∈ H, g * x * g⁻¹ ∈ S → x⁻¹ * (g * x * g⁻¹) ∈ U) :
    ∃ N : Subgroup G, N ≤ H ∧ ∃ (_ : (N.subgroupOf H).Normal),
      IsPGroup p (H ⧸ N.subgroupOf H) ∧ N.relIndex H = U.relIndex S ∧ N ⊓ S = U := by
  obtain ⟨T, hT⟩ := exists_sylow_eq_subgroupOf_of_fusionIsSylowIn hS
  obtain ⟨N', hN', hp, hidx, hinf⟩ := exists_normal_inf_eq_of_focal T (U := U.subgroupOf H)
    (by rw [hT]; exact fun x hx => hUS hx) (by
      intro x hx g hg
      rw [hT, Subgroup.mem_subgroupOf] at hx hg
      rw [Subgroup.mem_subgroupOf]
      push_cast at hg ⊢
      exact hfoc x hx g g.2 hg)
  rw [hT] at hidx hinf
  exact exists_le_of_subgroupOf hS.1 hUS hN' hp hidx hinf

end Relative

end CFSG.Holt
