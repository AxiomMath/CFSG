module

public import CFSG.ClassicalInvolution.Asc77.AscL62Quat

public section

namespace CFSG.ClassicalInvolution.Asc77.T3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62

variable {G : Type} [Group G]

theorem exists_base_of_isWreathed {P : Subgroup G} (hP : IsWreathed P) :
    ∃ B : Subgroup G, B ≤ P ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ∉ B → y ∉ B → x⁻¹ * y ∈ B) ∧ (∀ w ∈ P, w * w ∈ B) := by
  obtain ⟨a, c, b, -, -, hac, -, hb2, hbab, hbcb, hcl⟩ := hP
  subst hcl
  set B : Subgroup G := Subgroup.closure ({a, c} : Set G) with hB
  have haB : a ∈ B := Subgroup.subset_closure (by simp)
  have hcB : c ∈ B := Subgroup.subset_closure (by simp)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hBP : B ≤ Subgroup.closure ({a, c, b} : Set G) :=
    Subgroup.closure_mono (by
      intro x hx
      rcases hx with rfl | rfl
      · simp
      · simp)
  have hbP : b ∈ Subgroup.closure ({a, c, b} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    have h1 : ∀ y ∈ ({a, c} : Set G), B ≤ Subgroup.centralizer ({y} : Set G) := by
      intro y hy
      rw [hB, Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact hac
      · exact hac.symm
      · rfl
    have h2 : B ≤ Subgroup.centralizer (B : Set G) := by
      rw [hB, Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (h1 y hy hx)
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (h2 hy) x hx
  have hbB : ∀ x ∈ B, b * x * b⁻¹ ∈ B := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · rw [hbab]; exact hcB
      · rw [hbcb]; exact haB
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) by group]
      exact B.mul_mem hx hy
    | inv x _ hx =>
      rw [show b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ by group]
      exact B.inv_mem hx
  have key : ∀ x ∈ Subgroup.closure ({a, c, b} : Set G), x ∈ B ∨ ∃ y ∈ B, x = y * b := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact Or.inl haB
      · exact Or.inl hcB
      · exact Or.inr ⟨1, B.one_mem, by simp⟩
    | one => exact Or.inl B.one_mem
    | mul x y _ _ hx hy =>
      rcases hx with hx | ⟨x', hx', rfl⟩ <;> rcases hy with hy | ⟨y', hy', rfl⟩
      · exact Or.inl (B.mul_mem hx hy)
      · exact Or.inr ⟨x * y', B.mul_mem hx hy', by group⟩
      · refine Or.inr ⟨x' * (b * y * b⁻¹), B.mul_mem hx' (hbB y hy), ?_⟩
        group
      · refine Or.inl ?_
        have : x' * b * (y' * b) = x' * (b * y' * b⁻¹) * (b * b) := by group
        rw [this, hb2, mul_one]
        exact B.mul_mem hx' (hbB y' hy')
    | inv x _ hx =>
      rcases hx with hx | ⟨x', hx', rfl⟩
      · exact Or.inl (B.inv_mem hx)
      · refine Or.inr ⟨b * x'⁻¹ * b⁻¹, hbB _ (B.inv_mem hx'), ?_⟩
        calc (x' * b)⁻¹ = b⁻¹ * x'⁻¹ := by group
          _ = b * x'⁻¹ := by rw [hbinv]
          _ = b * x'⁻¹ * b⁻¹ * b := by group
  refine ⟨B, hBP, hcomm, ?_, ?_⟩
  · intro x hx y hy hxB hyB
    obtain ⟨x', hx', rfl⟩ := (key x hx).resolve_left hxB
    obtain ⟨y', hy', rfl⟩ := (key y hy).resolve_left hyB
    have : (x' * b)⁻¹ * (y' * b) = b * (x'⁻¹ * y') * b⁻¹ := by
      calc (x' * b)⁻¹ * (y' * b) = b⁻¹ * (x'⁻¹ * y') * b := by group
        _ = b * (x'⁻¹ * y') * b⁻¹ := by rw [hbinv]
    rw [this]
    exact hbB _ (B.mul_mem (B.inv_mem hx') hy')
  · intro w hw
    rcases key w hw with hwB | ⟨x', hx', rfl⟩
    · exact B.mul_mem hwB hwB
    · have : x' * b * (x' * b) = x' * (b * x' * b⁻¹) * (b * b) := by group
      rw [this, hb2, mul_one]
      exact B.mul_mem hx' (hbB x' hx')

theorem isCyclic_of_abelian_of_isQuatSub [Finite G] {R A : Subgroup G} (hR : IsQuatSub R) {z : G}
    (hz : IsUniqueInvolution R z) (hAR : A ≤ R) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    IsCyclic ↥A := by
  obtain ⟨C, hCR, hC, hcard, -⟩ := hR.exists_cyclic_max
  by_cases hAC : A ≤ C
  · have : IsCyclic ↥(A.subgroupOf C) := inferInstance
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hAC)).mp this
  · obtain ⟨a, haA, haC⟩ := Set.not_subset.mp hAC
    have haR : a ∈ R := hAR haA
    have hsq : a * a = z := sq_eq_of_not_mem hR hz hCR hC hcard haR haC
    have hCA : ∀ y ∈ A, y ∈ C → y ∈ Subgroup.zpowers a := by
      intro y hy hyC
      have h1 : a * y * a⁻¹ = y⁻¹ := conj_eq_inv_of_not_mem hR hz hCR hC hcard haR haC hyC
      have h2 : a * y * a⁻¹ = y := by rw [hcomm a haA y hy]; group
      have hyy : y * y = 1 := by
        have h3 : y⁻¹ = y := h1.symm.trans h2
        calc y * y = y⁻¹ * y := by rw [h3]
          _ = 1 := inv_mul_cancel y
      rcases hz.unique y (hCR hyC) hyy with rfl | rfl
      · exact Subgroup.one_mem _
      · rw [← hsq]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    have hAeq : A = Subgroup.zpowers a := by
      refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.mpr haA)
      by_cases hxC : x ∈ C
      · exact hCA x hx hxC
      · have h3 : a⁻¹ * x ∈ C := inv_mul_mem_of_index_two hCR hcard haR (hAR hx) haC hxC
        have h4 : a⁻¹ * x ∈ Subgroup.zpowers a :=
          hCA _ (A.mul_mem (A.inv_mem haA) hx) h3
        have : x = a * (a⁻¹ * x) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) h4
    rw [hAeq]
    infer_instance

theorem exists_mul_of_mem_sup {R V : Subgroup G} (hV : V ≤ Subgroup.normalizer (R : Set G))
    {g : G} (hg : g ∈ R ⊔ V) : ∃ r ∈ R, ∃ v ∈ V, r * v = g := by
  have := Subgroup.coe_mul_of_right_le_normalizer_left R V hV
  have hg' : g ∈ ((R ⊔ V : Subgroup G) : Set G) := hg
  rw [this] at hg'
  exact hg'

theorem exists_cyclic_index_two_le_centralizer [Finite G] {R V : Subgroup G} (hR : IsQuatSub R)
    {z : G} (hz : IsUniqueInvolution R z) (hP : IsWreathed (R ⊔ V)) {w j : G}
    (hw : w ∈ R ⊔ V) (hwj : w * w = j) :
    ∃ U : Subgroup G, U ≤ R ∧ IsCyclic ↥U ∧ U.relIndex R = 2 ∧
      U ≤ Subgroup.centralizer ({j} : Set G) := by
  obtain ⟨B, hBP, hBcomm, hBout, hBsq⟩ := exists_base_of_isWreathed hP
  have hjB : j ∈ B := by rw [← hwj]; exact hBsq w hw
  have hRP : R ≤ R ⊔ V := le_sup_left
  have hAcomm : ∀ x ∈ R ⊓ B, ∀ y ∈ R ⊓ B, x * y = y * x := fun x hx y hy => hBcomm x hx.2 y hy.2
  refine ⟨R ⊓ B, inf_le_left, isCyclic_of_abelian_of_isQuatSub hR hz inf_le_left hAcomm, ?_, ?_⟩
  · obtain ⟨x₀, hx₀R, hx₀B⟩ : ∃ x₀ ∈ R, x₀ ∉ B := by
      by_contra hcon
      push Not at hcon
      obtain ⟨x, hx, y, hy, hxy⟩ := hR.exists_not_commute
      exact hxy (hBcomm x (hcon x hx) y (hcon y hy))
    have hidx : ((R ⊓ B).subgroupOf R).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨x₀, hx₀R⟩, fun b => ?_⟩
      obtain ⟨y, hyR⟩ := b
      have hmem : ∀ (t : G) (htR : t ∈ R),
          ((⟨t, htR⟩ : ↥R) ∈ (R ⊓ B).subgroupOf R ↔ t ∈ B) := by
        intro t htR
        rw [Subgroup.mem_subgroupOf]
        exact ⟨fun h => h.2, fun h => ⟨htR, h⟩⟩
      by_cases hyB : y ∈ B
      · refine Or.inr ⟨?_, ?_⟩
        · exact (hmem y hyR).mpr hyB
        · intro h
          have h1 : y * x₀ ∈ B := (hmem (y * x₀) (R.mul_mem hyR hx₀R)).mp h
          exact hx₀B (by simpa using B.mul_mem (B.inv_mem hyB) h1)
      · refine Or.inl ⟨?_, ?_⟩
        · have hy'B : y⁻¹ ∉ B := fun h => hyB (by simpa using B.inv_mem h)
          have := hBout y⁻¹ (hRP (R.inv_mem hyR)) x₀ (hRP hx₀R) hy'B hx₀B
          exact (hmem (y * x₀) (R.mul_mem hyR hx₀R)).mpr (by simpa using this)
        · intro h
          exact hyB ((hmem y hyR).mp h)
    exact hidx
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hBcomm j hjB x hx.2).symm

end CFSG.ClassicalInvolution.Asc77.T3
