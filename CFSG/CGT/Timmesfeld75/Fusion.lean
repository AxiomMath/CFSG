module

public import CFSG.CGT.Timmesfeld75.WCBasic

public section

namespace CFSG.CGT.Timmesfeld75

section SylowConjugates

variable {H : Type*} [Group H]

theorem mem_sylow_smul_iff_inv_mul_mul_mem {p : ℕ} (P : Sylow p H) (b x : H) :
    x ∈ (b • P : Sylow p H) ↔ b⁻¹ * x * b ∈ P :=
  Subgroup.mem_pointwise_smul_iff_inv_smul_mem

end SylowConjugates

section KeyClaim

variable {G : Type*} [Group G]

private theorem eq_conjSubgroup_of_le_conjSubgroup [Finite G] {T : Subgroup G} {g : G}
    (h : T ≤ conjSubgroup g T) : T = conjSubgroup g T :=
  Subgroup.eq_of_le_of_card_ge h
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).le

theorem closure_inter_eq_of_le_pGroup [Finite G] (S : Sylow 2 G) (D : Set G)
    (hD : ∀ d ∈ D, ∀ g : G, g * d * g⁻¹ ∈ D) {U : Subgroup G} (hU : IsPGroup 2 U)
    (hSU : Subgroup.closure ((S : Set G) ∩ D) ≤ U) :
    Subgroup.closure ((U : Set G) ∩ D) = Subgroup.closure ((S : Set G) ∩ D) := by
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G S P
  have hle : Subgroup.closure ((U : Set G) ∩ D) ≤
      conjSubgroup b (Subgroup.closure ((S : Set G) ∩ D)) := by
    rw [Subgroup.closure_le]
    rintro u ⟨huU, huD⟩
    refine mem_conjSubgroup.2 (Subgroup.subset_closure ⟨?_, ?_⟩)
    · exact (mem_sylow_smul_iff_inv_mul_mul_mem S b u).1 (hUP huU)
    · simpa using hD u huD b⁻¹
  have hge : Subgroup.closure ((S : Set G) ∩ D) ≤ Subgroup.closure ((U : Set G) ∩ D) :=
    Subgroup.closure_mono fun s hs => ⟨hSU (Subgroup.subset_closure hs), hs.2⟩
  have heq := eq_conjSubgroup_of_le_conjSubgroup (hge.trans hle)
  exact le_antisymm (heq ▸ hle) hge

end KeyClaim

section Fusion

variable {G : Type*} [Group G]

theorem exists_pGroup_containing_conjSubgroup [Finite G] {C A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : IsPGroup 2 B) (hAC : A ≤ C) (hBC : B ≤ C) :
    ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≤ C ∧ A ≤ U ∧ ∃ c ∈ C, conjSubgroup c B ≤ U := by
  obtain ⟨Q₁, hQ₁⟩ := (hA.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (hB.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  refine ⟨(Q₁ : Subgroup C).map C.subtype, Q₁.isPGroup'.map _, Subgroup.map_subtype_le _, ?_,
    c, c.2, ?_⟩
  · intro a ha
    exact ⟨⟨a, hAC ha⟩, hQ₁ ha, rfl⟩
  · intro z hz
    have hzB : (c : G)⁻¹ * z * c ∈ B := mem_conjSubgroup.1 hz
    have hzC : z ∈ C := by
      have : z = c * ((c : G)⁻¹ * z * c) * (c : G)⁻¹ := by group
      rw [this]
      exact C.mul_mem (C.mul_mem c.2 (hBC hzB)) (C.inv_mem c.2)
    have hmem : (⟨z, hzC⟩ : C) ∈ (c • Q₂ : Sylow 2 C) :=
      (mem_sylow_smul_iff_inv_mul_mul_mem Q₂ c ⟨z, hzC⟩).2 (hQ₂ hzB)
    rw [hc] at hmem
    exact ⟨⟨z, hzC⟩, hmem, rfl⟩

theorem normalizer_controls_fusion_of_weaklyClosedIn_pGroup [Finite G] {R : Subgroup G}
    (hR : IsPGroup 2 R) (hweak : ∀ U : Subgroup G, IsPGroup 2 U → R ≤ U → WeaklyClosedIn R U)
    {x y g : G} (hx : ∀ s ∈ R, x * s = s * x) (hy : ∀ s ∈ R, y * s = s * y)
    (hxy : g⁻¹ * x * g = y) :
    ∃ h ∈ Subgroup.normalizer (R : Set G), h⁻¹ * x * h = y := by
  have hRC : R ≤ Subgroup.centralizer ({y} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hy s hs
  have hR'C : conjSubgroup g⁻¹ R ≤ Subgroup.centralizer ({y} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz, ← hxy]
    have h1 := hx _ (mem_conjSubgroup.1 ht)
    simp only [inv_inv] at h1
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h1]
      _ = t * (g⁻¹ * x * g) := by group
  obtain ⟨U, hU2, -, hRU, c, hcC, hcU⟩ := exists_pGroup_containing_conjSubgroup hR
    (hR.map (MulAut.conj g⁻¹).toMonoidHom) hRC hR'C
  have hnorm : conjSubgroup (c * g⁻¹) R = R :=
    (hweak U hU2 hRU).2 (c * g⁻¹) (by rwa [← conjSubgroup_conjSubgroup])
  refine ⟨g * c⁻¹, ?_, ?_⟩
  · have h1 : c * g⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.2 hnorm
    have h2 := (Subgroup.inv_mem_iff _).2 h1
    simpa [mul_inv_rev] using h2
  · have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.1 hcC y (Set.mem_singleton y)
    calc (g * c⁻¹)⁻¹ * x * (g * c⁻¹) = c * (g⁻¹ * x * g) * c⁻¹ := by group
      _ = c * y * c⁻¹ := by rw [hxy]
      _ = y := by rw [← hcy]; group

end Fusion

end CFSG.CGT.Timmesfeld75
