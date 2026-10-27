module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.QuaternionStructure
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F] {n m : ℕ}

theorem commute_planeGroup_of_orth (hn : 2 ≤ n) {P Q : Submodule F (Fin n ⊕ Fin n → F)}
    (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, form x y = 0) :
    ∀ a ∈ planeGroup P, ∀ b ∈ planeGroup Q, a * b = b * a := by
  obtain ⟨u₁, w₁, h₁, rfl⟩ := hP
  obtain ⟨u₂, w₂, h₂, rfl⟩ := hQ
  have hs : ∀ x ∈ (Submodule.span F {u₁, w₁} : Submodule F (Fin n ⊕ Fin n → F)), ∀ y ∈
      (Submodule.span F {u₂, w₂} : Submodule F (Fin n ⊕ Fin n → F)), form x y = 0 := horth
  have o₁ : form u₁ u₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₂ : form u₁ w₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₃ : form w₁ u₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  have o₄ : form w₁ w₂ = 0 := hs _ (Submodule.subset_span (by simp)) _
    (Submodule.subset_span (by simp))
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ := exists_sp_apply_eq_two_at (k := (⟨0, by omega⟩ : Fin n))
    (l := (⟨1, by omega⟩ : Fin n)) (by simp [Fin.ext_iff]) u₁ w₁ u₂ w₂ h₁ h₂ o₁ o₂ o₃ o₄
  have e1 : planeGroup (Submodule.span F {u₁, w₁}) =
      (longBlock F n ⟨0, by omega⟩).range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg1, ← hg2, planeGroup_span_conj]
    exact congrArg _ (planeGroup_stdPlane _)
  have e2 : planeGroup (Submodule.span F {u₂, w₂}) =
      (longBlock F n ⟨1, by omega⟩).range.map (MulAut.conj g).toMonoidHom := by
    rw [← hg3, ← hg4, planeGroup_span_conj]
    exact congrArg _ (planeGroup_stdPlane _)
  intro a ha b hb
  rw [e1] at ha
  rw [e2] at hb
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨B, rfl⟩, rfl⟩ := hb
  have hc := commute_longBlock_longBlock (K := F) (n := n) (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]) A B
  simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
  have := hc.eq
  calc g * longBlock F n ⟨0, by omega⟩ A * g⁻¹ * (g * longBlock F n ⟨1, by omega⟩ B * g⁻¹)
      = g * (longBlock F n ⟨0, by omega⟩ A * longBlock F n ⟨1, by omega⟩ B) * g⁻¹ := by group
    _ = g * (longBlock F n ⟨1, by omega⟩ B * longBlock F n ⟨0, by omega⟩ A) * g⁻¹ := by rw [this]
    _ = g * longBlock F n ⟨1, by omega⟩ B * g⁻¹ * (g * longBlock F n ⟨0, by omega⟩ A * g⁻¹) := by
      group

theorem orth_of_commute_map [Finite F] (h2 : (2 : F) ≠ 0)
    (hex : ∃ a : Fˣ, (a : F) ≠ ((a⁻¹ : Fˣ) : F)) {X : Type*} [Group X]
    (ψ : StatedSp n F →* X) (hψ : ψ.ker ≤ Subgroup.center (StatedSp n F))
    {P Q : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q)
    (hne : (planeGroup P).map ψ ≠ (planeGroup Q).map ψ)
    (hc : ∀ x ∈ (planeGroup P).map ψ, ∀ y ∈ (planeGroup Q).map ψ, x * y = y * x) :
    ∀ u ∈ P, ∀ v ∈ Q, form u v = 0 := by
  refine forall_form_eq_zero_of_commutator_mem_center h2 hex hP hQ (fun h => hne (by rw [h])) ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  apply hψ
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul]
  exact hc _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

theorem mulAut_sl2_neg_one (h2 : (2 : F) ≠ 0) (α : MulAut SL(2, F)) : α (-1) = -1 := by
  have hc : α (-1) ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : (-1 : SL(2, F)) ∈ Subgroup.center SL(2, F) :=
      mem_center_specialLinearGroup_two_iff.mpr (Or.inr rfl)
    have := Subgroup.mem_center_iff.mp h1 (α.symm y)
    calc y * α (-1) = α (α.symm y * -1) := by rw [map_mul, MulEquiv.apply_symm_apply]
      _ = α (-1 * α.symm y) := by rw [this]
      _ = α (-1) * y := by rw [map_mul, MulEquiv.apply_symm_apply]
  rcases mem_center_specialLinearGroup_two_iff.mp hc with h | h
  · exfalso
    have h' : α (-1) = α 1 := by rw [h, map_one]
    have := α.injective h'
    have hord := orderOf_neg_one_specialLinearGroup_two h2
    rw [this, orderOf_one] at hord
    omega
  · exact h

theorem map_neg_one_eq_of_range_eq [Finite F] (hm : 2 ≤ m) (h2 : (2 : F) ≠ 0) {X : Type*}
    [Group X] (ψ : StatedSp m F →* X) (hψ : ψ.ker ≤ Subgroup.center (StatedSp m F)) (k : Fin m)
    (β : SL(2, F) →* X) (hβ : Function.Injective β)
    (hr : β.range = (longBlock F m k).range.map ψ) : β (-1) = ψ (longInv F m k) := by
  have hinj : Function.Injective (ψ.comp (longBlock F m k)) := by
    have := injective_comp_conj_longBlock hm ψ hψ 1 k
    have e : (MulAut.conj (1 : StatedSp m F)).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rwa [e, MonoidHom.comp_id] at this
  have hrange : (ψ.comp (longBlock F m k)).range = β.range := by
    rw [hr, MonoidHom.range_comp]
  obtain ⟨α, hα⟩ := exists_mulAut_comp_eq hinj hβ hrange
  have := DFunLike.congr_fun hα (-1)
  rw [← this]
  simp [mulAut_sl2_neg_one h2 α, longInv]

theorem mem_sup_stdPlane_of_orth {a b : Fin n} (hab : a ≠ b) {u : Fin n ⊕ Fin n → F}
    (h : ∀ c, c ≠ a → c ≠ b → ∀ v ∈ stdPlane F n c, form u v = 0) :
    u ∈ stdPlane F n a ⊔ stdPlane F n b := by
  rw [mem_sup_stdPlane_iff hab]
  intro t ht
  have key : ∀ c, c ≠ a → c ≠ b → ∀ s ∈ coords c, u s = 0 := by
    intro c hca hcb s hs
    have hu : u ∈ orthSet (stdPlane F n c : Set (Fin n ⊕ Fin n → F)) := h c hca hcb
    rw [orthSet_stdPlane] at hu
    exact hu s hs
  have ht' : t ∉ coords a ∧ t ∉ coords b := by
    simp only [Set.mem_union, not_or] at ht
    exact ht
  rcases t with c | c
  · refine key c ?_ ?_ _ (inl_mem_coords c)
    · rintro rfl
      exact ht'.1 (inl_mem_coords _)
    · rintro rfl
      exact ht'.2 (inl_mem_coords _)
  · refine key c ?_ ?_ _ (inr_mem_coords c)
    · rintro rfl
      exact ht'.1 (inr_mem_coords _)
    · rintro rfl
      exact ht'.2 (inr_mem_coords _)

theorem orth_stdPlane_of_mem_sup {a b c : Fin n} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    {u : Fin n ⊕ Fin n → F} (hu : u ∈ stdPlane F n a ⊔ stdPlane F n b) :
    ∀ v ∈ stdPlane F n c, form u v = 0 := by
  have hu' := (mem_sup_stdPlane_iff hab).mp hu
  have : u ∈ orthSet (stdPlane F n c : Set (Fin n ⊕ Fin n → F)) := by
    rw [orthSet_stdPlane]
    intro t ht
    refine hu' t ?_
    simp only [Set.mem_union, not_or]
    constructor
    · intro h
      rcases mem_coords.mp ht with rfl | rfl <;> rcases mem_coords.mp h with h' | h' <;>
        simp_all
    · intro h
      rcases mem_coords.mp ht with rfl | rfl <;> rcases mem_coords.mp h with h' | h' <;>
        simp_all
  exact this

theorem false_of_pairPlane_orth {a b : Fin n} (hab : a ≠ b)
    {H : Submodule F (Fin n ⊕ Fin n → F)} (hH : IsHyperbolicPlane H)
    (hle : H ≤ stdPlane F n a ⊔ stdPlane F n b)
    (h₁ : ∀ x ∈ H, ∀ y ∈ stdPlane F n a, form x y = 0)
    (h₂ : ∀ x ∈ H, ∀ y ∈ stdPlane F n b, form x y = 0) : False := by
  obtain ⟨u, w, huw, rfl⟩ := hH
  have hu : u ∈ (Submodule.span F {u, w} : Submodule F _) := Submodule.subset_span (by simp)
  have hu' := (mem_sup_stdPlane_iff hab).mp (hle hu)
  have hu1 : u ∈ orthSet (stdPlane F n a : Set (Fin n ⊕ Fin n → F)) := h₁ u hu
  have hu2 : u ∈ orthSet (stdPlane F n b : Set (Fin n ⊕ Fin n → F)) := h₂ u hu
  rw [orthSet_stdPlane] at hu1 hu2
  have hu0 : u = 0 := by
    funext t
    by_cases ht : t ∈ coords a ∪ coords b
    · rcases ht with ht | ht
      · exact hu1 t ht
      · exact hu2 t ht
    · exact hu' t ht
  rw [hu0] at huw
  simp [form] at huw

end CFSG.ClassicalInvolution.RouteD
