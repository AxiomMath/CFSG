module

public import CFSG.Goldschmidt75.Closure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_conj_le_sylow (T T' : Sylow p G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    ∃ x : G, conjSub x S ≤ T' ∧ fusionStronglyClosed ((conjSub x S : Subgroup G) : Set G) T' ∧
      ∀ u ∈ (T' : Subgroup G), ∀ g : G, g⁻¹ * u * g ∈ S → u ∈ conjSub x S := by
  obtain ⟨y, hy⟩ := exists_conjSub_eq T' T
  have hcl : fusionStronglyClosed ((conjSub y S : Subgroup G) : Set G) T' := by
    intro a ha g hg
    rw [SetLike.mem_coe, mem_conjSub] at ha
    have hg' : (y * g * y⁻¹)⁻¹ * (y * a * y⁻¹) * (y * g * y⁻¹) ∈ (T : Subgroup G) := by
      rw [← hy] at hg
      have := mem_conjSub.1 hg
      simpa [mul_assoc] using this
    have h1 := hS _ ha _ hg'
    rw [SetLike.mem_coe, mem_conjSub]
    simpa [mul_assoc] using h1
  refine ⟨y, hy ▸ conjSub_mono hST, hcl, fun u hu g hgu => ?_⟩
  have h1 : ((g * y)⁻¹)⁻¹ * (y⁻¹ * (g⁻¹ * u * g) * y) * (g * y)⁻¹ ∈ (T' : Subgroup G) := by
    simpa [mul_assoc] using hu
  have h2 := hcl _ (conj_mem_conjSub hgu) _ h1
  simpa [mul_assoc] using h2

omit [Finite G] [Fact p.Prime] in
theorem stronglyClosed_trace (T' : Sylow p G) {S' H : Subgroup G}
    (hS' : fusionStronglyClosed (S' : Set G) T') (TH : Sylow p H)
    (hTH : (TH : Subgroup H).map H.subtype ≤ T') :
    fusionStronglyClosed (((S' ⊓ H).subgroupOf H : Subgroup H) : Set H) TH := by
  intro a ha h hh
  have h1 : ((h⁻¹ * a * h : H) : G) ∈ (T' : Subgroup G) := hTH ⟨_, hh, rfl⟩
  have h2 : (h : G)⁻¹ * a * h ∈ S' := hS' _ ha.1 _ (by simpa using h1)
  exact ⟨by simpa using h2, (h⁻¹ * a * h).2⟩

omit [Finite G] [Fact p.Prime] in
theorem inf_subgroupOf_eq_sylow (T' : Sylow p G) {H : Subgroup G} (TH : Sylow p H)
    (hTH : (TH : Subgroup H).map H.subtype ≤ T') :
    ((T' : Subgroup G) ⊓ H).subgroupOf H = TH := by
  have hle : (TH : Subgroup H) ≤ ((T' : Subgroup G) ⊓ H).subgroupOf H :=
    fun x hx => ⟨hTH ⟨x, hx, rfl⟩, x.2⟩
  have hp : IsPGroup p (((T' : Subgroup G) ⊓ H).subgroupOf H) :=
    (T'.isPGroup'.to_inf_left).comap_subtype
  exact TH.is_maximal' hp hle

omit [Finite G] [Fact p.Prime] in
theorem trace_le_sylow (T' : Sylow p G) {S' H : Subgroup G} (hS'T : S' ≤ T') (TH : Sylow p H)
    (hTH : (TH : Subgroup H).map H.subtype ≤ T') :
    (S' ⊓ H).subgroupOf H ≤ TH := by
  rw [← inf_subgroupOf_eq_sylow T' TH hTH]
  exact fun x hx => ⟨hS'T hx.1, hx.2⟩

end CFSG.Goldschmidt75
