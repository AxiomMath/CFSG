module

public import CFSG.Foundations.Basic

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

section Aux

variable {G : Type*} [Group G]

private theorem mem_conjugate_iff_aux {A : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    simpa [this] using ha
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private theorem conjugate_conjugate_aux (A : Subgroup G) (g h : G) :
    CFSG.conjugate (CFSG.conjugate A g) h = CFSG.conjugate A (g * h) := by
  ext x
  simp only [mem_conjugate_iff_aux]
  have : g * (h * x * h⁻¹) * g⁻¹ = (g * h) * x * (g * h)⁻¹ := by group
  rw [this]

private theorem conjugate_eq_iff_mem_normalizer_aux {A : Subgroup G} {g : G} :
    CFSG.conjugate A g = A ↔ g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff, SetLike.ext_iff]
  simp only [mem_conjugate_iff_aux, SetLike.mem_coe]
  exact forall_congr' fun x => Iff.comm

private theorem exists_conj_le_sylow_aux [Finite G] {p : ℕ} [Fact p.Prime] (T : Sylow p G)
    {N Q₁ Q₂ : Subgroup G} (hQ₁N : Q₁ ≤ N) (hQ₂N : Q₂ ≤ N) (hQ₁ : IsPGroup p Q₁)
    (hQ₂ : IsPGroup p Q₂) :
    ∃ c ∈ N, ∃ y : G, CFSG.conjugate Q₁ y ≤ T ∧ CFSG.conjugate Q₂ (c * y) ≤ T := by
  have hp1 : IsPGroup p (Q₁.subgroupOf N) :=
    hQ₁.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₁N).symm
  have hp2 : IsPGroup p (Q₂.subgroupOf N) :=
    hQ₂.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₂N).symm
  obtain ⟨P₁, hP₁⟩ := hp1.exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := hp2.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N P₁ P₂
  have hP₁G : IsPGroup p ((P₁ : Subgroup N).map N.subtype) := P₁.isPGroup'.map _
  obtain ⟨T', hT'⟩ := hP₁G.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G T T'
  have key : ∀ z : G, z ∈ (T' : Subgroup G) → y⁻¹ * z * y ∈ (T : Subgroup G) := by
    intro z hz
    subst hy
    have : z ∈ ((y • T : Sylow p G) : Subgroup G) := hz
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
    simpa [MulAut.conj_apply] using this
  refine ⟨c, c.2, y, ?_, ?_⟩
  · intro x hx
    rw [mem_conjugate_iff_aux] at hx
    have h1 : (⟨y * x * y⁻¹, hQ₁N hx⟩ : N) ∈ (P₁ : Subgroup N) :=
      hP₁ (Subgroup.mem_subgroupOf.2 hx)
    have h2 : y * x * y⁻¹ ∈ (T' : Subgroup G) := hT' ⟨_, h1, rfl⟩
    have h3 := key _ h2
    have h4 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [h4] at h3
  · intro x hx
    rw [mem_conjugate_iff_aux] at hx
    have h0 : (⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ : N) ∈ (P₂ : Subgroup N) :=
      hP₂ (Subgroup.mem_subgroupOf.2 hx)
    have h1 : (c : N)⁻¹ * ⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ * c ∈ (P₁ : Subgroup N) := by
      subst hc
      have : (⟨(c * y) * x * (c * y)⁻¹, hQ₂N hx⟩ : N) ∈ ((c • P₁ : Sylow p N) : Subgroup N) := h0
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at this
      simpa [MulAut.conj_apply] using this
    have h2 : y * x * y⁻¹ ∈ (T' : Subgroup G) := by
      refine hT' ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h3 := key _ h2
    have h4 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rwa [h4] at h3

end Aux

open CFSG in
theorem burnside_fusion {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (A : Subgroup G) (hAP : A ≤ (P : Subgroup G))
    (hab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hweak : ∀ g : G, CFSG.conjugate A g ≤ (P : Subgroup G) → CFSG.conjugate A g = A)
    {a g : G} (ha : a ∈ A) (hg : g * a * g⁻¹ ∈ A) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n * a * n⁻¹ = g * a * g⁻¹ := by
  have hAC : A ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hab x hx _ hg
  have hBC : CFSG.conjugate A g⁻¹ ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := fun x hx => by
    rw [mem_conjugate_iff_aux] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hab _ hx a ha
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
      _ = g * a * g⁻¹ * x := by group
  have hAp : IsPGroup p A := P.isPGroup'.to_le hAP
  have hBp : IsPGroup p (CFSG.conjugate A g⁻¹) := hAp.map _
  obtain ⟨c, hcC, y, hy1, hy2⟩ := exists_conj_le_sylow_aux P hAC hBC hAp hBp
  have hyN : y ∈ Subgroup.normalizer (A : Set G) :=
    conjugate_eq_iff_mem_normalizer_aux.1 (hweak y hy1)
  rw [conjugate_conjugate_aux] at hy2
  have hxN : g⁻¹ * (c * y) ∈ Subgroup.normalizer (A : Set G) :=
    conjugate_eq_iff_mem_normalizer_aux.1 (hweak _ hy2)
  have hgc : g⁻¹ * c ∈ Subgroup.normalizer (A : Set G) := by
    have := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hyN)
    simpa [mul_assoc] using this
  refine ⟨(g⁻¹ * c)⁻¹, Subgroup.inv_mem _ hgc, ?_⟩
  have hcom : c * (g * a * g⁻¹) = g * a * g⁻¹ * c :=
    Subgroup.mem_centralizer_singleton_iff.1 hcC
  calc (g⁻¹ * c)⁻¹ * a * (g⁻¹ * c)⁻¹⁻¹ = c⁻¹ * (g * a * g⁻¹ * c) := by group
    _ = g * a * g⁻¹ := by rw [← hcom, inv_mul_cancel_left]

end CFSG.GF2Type.Aschbacher1976Full.HS
