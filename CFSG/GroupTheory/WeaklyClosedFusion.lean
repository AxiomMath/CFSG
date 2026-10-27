module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
private theorem exists_isSylowOf_ge_aux {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup p P) :
    ∃ R : Subgroup G, IsSylowOf p R K ∧ P ≤ R := by
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hPK hx⟩, hQ hx, rfl⟩⟩

theorem exists_mem_conj_mem_of_weaklyClosed_of_isSylowOf_centralizer
    {H E Y : Subgroup G} {x : G}
    (hY : IsSylowOf p Y (centralizer ({x} : Set G))) (hYH : Y ≤ H)
    (hEH : E ≤ H) (hEp : IsPGroup p E) (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hweak : ∀ T : Subgroup G, IsSylowOf p T H → E ≤ T → ∀ m : G,
      (∀ a ∈ E, m⁻¹ * a * m ∈ T) → ∀ y : G, m * y * m⁻¹ ∈ E → y ∈ E)
    {g : G} (hg : g * x * g⁻¹ ∈ E) :
    ∃ c ∈ H, c * x * c⁻¹ ∈ E := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  let E' : Subgroup G := E.comap (MulAut.conj g).toMonoidHom
  have hE'mem : ∀ w, w ∈ E' ↔ g * w * g⁻¹ ∈ E := fun w => Iff.rfl
  have hE'p : IsPGroup p E' := hEp.comap_of_injective _ (MulAut.conj g).injective
  have hE'C : E' ≤ C := by
    intro w hw
    rw [hC, mem_centralizer_singleton_iff]
    have h1 := hEab _ ((hE'mem w).mp hw) _ hg
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h1]
      _ = x * w := by group
  obtain ⟨S, hS⟩ := (hE'p.comap_subtype (K := C)).exists_le_sylow
  have hY₁ : IsSylowOf p ((S : Subgroup C).map C.subtype) C := ⟨S, rfl⟩
  have hE'Y₁ : E' ≤ (S : Subgroup C).map C.subtype := fun w hw =>
    ⟨⟨w, hE'C hw⟩, hS (show (⟨w, hE'C hw⟩ : C) ∈ E'.subgroupOf C from hw), rfl⟩
  obtain ⟨k, hkC, hk⟩ := hY.exists_mem_conj hY₁
  have hconj : ∀ w ∈ E', k⁻¹ * w * k ∈ Y := fun w hw => (hk w).mp (hE'Y₁ hw)
  have hkx : k * x * k⁻¹ = x := by
    have h1 : k * x = x * k := mem_centralizer_singleton_iff.mp hkC
    calc k * x * k⁻¹ = (x * k) * k⁻¹ := by rw [h1]
      _ = x := by group
  have hmY : ∀ a ∈ E, (g * k)⁻¹ * a * (g * k) ∈ Y := by
    intro a ha
    have hw : g⁻¹ * a * g ∈ E' := by
      rw [hE'mem]
      have h1 : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
      rw [h1]
      exact ha
    have h2 : (g * k)⁻¹ * a * (g * k) = k⁻¹ * (g⁻¹ * a * g) * k := by group
    rw [h2]
    exact hconj _ hw
  have hmx : (g * k) * x * (g * k)⁻¹ ∈ E := by
    have h1 : (g * k) * x * (g * k)⁻¹ = g * x * g⁻¹ := by
      calc (g * k) * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hkx]
    rw [h1]
    exact hg
  obtain ⟨T₀, hT₀, hET₀⟩ := exists_isSylowOf_ge_aux hEH hEp
  obtain ⟨T', hT', hYT'⟩ := exists_isSylowOf_ge_aux hYH hY.isPGroup
  obtain ⟨h, hhH, hh⟩ := hT₀.exists_mem_conj hT'
  have hcl : h⁻¹ * x * h ∈ E := by
    refine hweak T₀ hT₀ hET₀ ((g * k) * h) (fun a ha => ?_) (h⁻¹ * x * h) ?_
    · have h1 : ((g * k) * h)⁻¹ * a * ((g * k) * h) = h⁻¹ * ((g * k)⁻¹ * a * (g * k)) * h := by
        group
      rw [h1]
      exact (hh _).mp (hYT' (hmY a ha))
    · have h1 : ((g * k) * h) * (h⁻¹ * x * h) * ((g * k) * h)⁻¹ = (g * k) * x * (g * k)⁻¹ := by
        group
      rw [h1]
      exact hmx
  exact ⟨h⁻¹, inv_mem hhH, by rw [inv_inv]; exact hcl⟩

end CFSG.GroupTheory
