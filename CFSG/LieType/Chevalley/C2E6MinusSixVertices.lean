module

public import CFSG.LieType.Chevalley.C2E6MinusSixPoints
public import Mathlib.Tactic.ENatToNat

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ptVertex (i : Fin 27) : QVertex :=
  ⟨ptSub i, isTotallySingular_ptSub i, Or.inl (finrank_ptSub i)⟩

@[expose] def lnVertex (j : Fin 45) : QVertex :=
  ⟨lnSub j, isTotallySingular_lnSub j, Or.inr (finrank_lnSub j)⟩

@[expose] def vertexOf : Fin 27 ⊕ Fin 45 → QVertex
  | .inl i => ptVertex i
  | .inr j => lnVertex j

@[expose] def CType : Fin 27 ⊕ Fin 45 → ℕ
  | .inl _ => 1
  | .inr _ => 2

theorem type_vertexOf (a : Fin 27 ⊕ Fin 45) : (vertexOf a).type = CType a := by
  rcases a with i | j
  · exact finrank_ptSub i
  · exact finrank_lnSub j

theorem vertexOf_injective : Function.Injective vertexOf := by
  intro a b h
  have ht := type_vertexOf a
  rw [h, type_vertexOf] at ht
  rcases a with i | j <;> rcases b with i' | j'
  · exact congrArg Sum.inl (ptSub_injective (congrArg Subtype.val h))
  · exact absurd ht (by simp [CType])
  · exact absurd ht (by simp [CType])
  · exact congrArg Sum.inr (lnSub_injective (congrArg Subtype.val h))

theorem vertexOf_surjective : Function.Surjective vertexOf := by
  rintro ⟨U, hU, h1 | h2⟩
  · obtain ⟨i, rfl⟩ := exists_ptSub_eq hU h1
    exact ⟨.inl i, rfl⟩
  · obtain ⟨j, rfl⟩ := exists_lnSub_eq hU h2
    exact ⟨.inr j, rfl⟩

theorem vertexOf_bijective : Function.Bijective vertexOf :=
  ⟨vertexOf_injective, vertexOf_surjective⟩

@[expose] def CInc : Fin 27 ⊕ Fin 45 → Fin 27 ⊕ Fin 45 → Prop
  | .inl i, .inl i' => i = i'
  | .inl i, .inr j => PtOn i j
  | .inr j, .inl i => PtOn i j
  | .inr j, .inr j' => j = j'

instance : DecidableRel CInc
  | .inl _, .inl _ => inferInstanceAs (Decidable (_ = _))
  | .inl _, .inr _ => inferInstanceAs (Decidable (PtOn _ _))
  | .inr _, .inl _ => inferInstanceAs (Decidable (PtOn _ _))
  | .inr _, .inr _ => inferInstanceAs (Decidable (_ = _))

theorem eq_of_le_of_finrank {U U' : Submodule (ZMod 2) X} (h : U ≤ U')
    (hf : finrank (ZMod 2) U = finrank (ZMod 2) U') : U = U' :=
  Submodule.eq_of_le_of_finrank_eq h hf

theorem incident_vertexOf_iff (a b : Fin 27 ⊕ Fin 45) :
    (vertexOf a).Incident (vertexOf b) ↔ CInc a b := by
  have hle : ∀ j i, ¬ lnSub j ≤ ptSub i := fun j i h => by
    have := Submodule.finrank_mono h
    rw [finrank_lnSub, finrank_ptSub] at this
    omega
  rcases a with i | j <;> rcases b with i' | j' <;>
    simp only [QVertex.Incident, vertexOf, ptVertex, lnVertex, CInc]
  · constructor
    · rintro (h | h)
      · exact ptSub_injective (eq_of_le_of_finrank h (by rw [finrank_ptSub, finrank_ptSub]))
      · exact (ptSub_injective (eq_of_le_of_finrank h
          (by rw [finrank_ptSub, finrank_ptSub]))).symm
    · rintro rfl
      exact Or.inl le_rfl
  · rw [ptSub_le_lnSub_iff, or_iff_left (hle j' i)]
  · rw [ptSub_le_lnSub_iff, or_iff_right (hle j i')]
  · constructor
    · rintro (h | h)
      · exact lnSub_injective (eq_of_le_of_finrank h (by rw [finrank_lnSub, finrank_lnSub]))
      · exact (lnSub_injective (eq_of_le_of_finrank h
          (by rw [finrank_lnSub, finrank_lnSub]))).symm
    · rintro rfl
      exact Or.inl le_rfl

@[expose] def QVertex.Near (x y : QVertex) : Prop :=
  ∃ z : QVertex, x.Incident z ∧ z.Incident y

@[expose] def CNear : Fin 27 ⊕ Fin 45 → Fin 27 ⊕ Fin 45 → Prop
  | .inl i, .inl i' => polarQ (ptVec i) (ptVec i') = 0
  | .inl i, .inr j => PtOn i j
  | .inr j, .inl i => PtOn i j
  | .inr j, .inr j' => PtOn (lnA j) j' ∨ PtOn (lnB j) j' ∨ PtOn (lnC j) j'

instance : DecidableRel CNear
  | .inl _, .inl _ => inferInstanceAs (Decidable (_ = _))
  | .inl _, .inr _ => inferInstanceAs (Decidable (PtOn _ _))
  | .inr _, .inl _ => inferInstanceAs (Decidable (PtOn _ _))
  | .inr _, .inr _ => inferInstanceAs (Decidable (_ ∨ _))

theorem polarQ_ptVec_eq_zero_iff : ∀ i i' : Fin 27,
    polarQ (ptVec i) (ptVec i') = 0 ↔ i = i' ∨ ∃ j, PtOn i j ∧ PtOn i' j := by
  decide

theorem cNear_iff (a b : Fin 27 ⊕ Fin 45) : CNear a b ↔ ∃ c, CInc a c ∧ CInc c b := by
  rcases a with i | j <;> rcases b with i' | j'
  · simp only [CNear, polarQ_ptVec_eq_zero_iff]
    constructor
    · rintro (rfl | ⟨j, hj, hj'⟩)
      · exact ⟨.inl i, rfl, rfl⟩
      · exact ⟨.inr j, hj, hj'⟩
    · rintro ⟨c | l, h1, h2⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inr ⟨l, h1, h2⟩
  · simp only [CNear]
    constructor
    · intro h
      exact ⟨.inr j', h, rfl⟩
    · rintro ⟨c | l, h1, h2⟩
      · exact (show i = c from h1) ▸ h2
      · exact (show l = j' from h2) ▸ h1
  · simp only [CNear]
    constructor
    · intro h
      exact ⟨.inl i', h, rfl⟩
    · rintro ⟨c | l, h1, h2⟩
      · exact (show c = i' from h2) ▸ h1
      · exact (show j = l from h1) ▸ h2
  · simp only [CNear]
    constructor
    · rintro (h | h | h)
      · exact ⟨.inl (lnA j), Or.inl rfl, h⟩
      · exact ⟨.inl (lnB j), Or.inr (Or.inl rfl), h⟩
      · exact ⟨.inl (lnC j), Or.inr (Or.inr rfl), h⟩
    · rintro ⟨c | l, h1, h2⟩
      · rcases (h1 : PtOn c j) with rfl | rfl | rfl
        · exact Or.inl h2
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr h2)
      · have hjl : j = l := h1
        have hlj : l = j' := h2
        subst hjl hlj
        exact Or.inl (Or.inl rfl)

theorem near_vertexOf_iff (a b : Fin 27 ⊕ Fin 45) :
    (vertexOf a).Near (vertexOf b) ↔ CNear a b := by
  rw [cNear_iff]
  constructor
  · rintro ⟨z, h1, h2⟩
    obtain ⟨c, rfl⟩ := vertexOf_surjective z
    exact ⟨c, (incident_vertexOf_iff a c).mp h1, (incident_vertexOf_iff c b).mp h2⟩
  · rintro ⟨c, h1, h2⟩
    exact ⟨vertexOf c, (incident_vertexOf_iff a c).mpr h1, (incident_vertexOf_iff c b).mpr h2⟩

theorem perm_apply_inv {α : Type*} (σ : Equiv.Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  Equiv.apply_symm_apply σ x

@[expose] def typeAut : Subgroup (Equiv.Perm QVertex) where
  carrier := {σ | (∀ x, (σ x).type = x.type) ∧ ∀ x y, (σ x).Incident (σ y) ↔ x.Incident y}
  mul_mem' {σ τ} hσ hτ :=
    ⟨fun x => (hσ.1 (τ x)).trans (hτ.1 x), fun x y => (hσ.2 (τ x) (τ y)).trans (hτ.2 x y)⟩
  one_mem' := ⟨fun _ => rfl, fun _ _ => Iff.rfl⟩
  inv_mem' {σ} hσ := by
    refine ⟨fun x => ?_, fun x y => ?_⟩
    · have := hσ.1 (σ⁻¹ x)
      rw [perm_apply_inv] at this
      exact this.symm
    · have := hσ.2 (σ⁻¹ x) (σ⁻¹ y)
      rw [perm_apply_inv, perm_apply_inv] at this
      exact this.symm

theorem mem_typeAut {σ : Equiv.Perm QVertex} :
    σ ∈ typeAut ↔ (∀ x, (σ x).type = x.type) ∧ ∀ x y, (σ x).Incident (σ y) ↔ x.Incident y :=
  Iff.rfl

theorem near_map {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut) (x y : QVertex) :
    (σ x).Near (σ y) ↔ x.Near y := by
  constructor
  · rintro ⟨z, h1, h2⟩
    refine ⟨σ⁻¹ z, ?_, ?_⟩
    · rw [← hσ.2, perm_apply_inv]
      exact h1
    · rw [← hσ.2, perm_apply_inv]
      exact h2
  · rintro ⟨z, h1, h2⟩
    exact ⟨σ z, (hσ.2 x z).mpr h1, (hσ.2 z y).mpr h2⟩

theorem fix_of_unique {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut) {F : List QVertex}
    (hF : ∀ f ∈ F, σ f = f) {x : QVertex}
    (hx : ∀ y : QVertex, y.type = x.type → (∀ f ∈ F, y.Incident f ↔ x.Incident f) →
      (∀ f ∈ F, y.Near f ↔ x.Near f) → y = x) : σ x = x := by
  refine hx (σ x) (hσ.1 x) (fun f hf => ?_) (fun f hf => ?_)
  · conv_lhs => rw [← hF f hf]
    exact hσ.2 x f
  · conv_lhs => rw [← hF f hf]
    exact near_map hσ x f

theorem fix_vertexOf_of_unique {σ : Equiv.Perm QVertex} (hσ : σ ∈ typeAut)
    {F : List (Fin 27 ⊕ Fin 45)} (hF : ∀ f ∈ F, σ (vertexOf f) = vertexOf f)
    {a : Fin 27 ⊕ Fin 45}
    (ha : ∀ b, CType b = CType a → (∀ f ∈ F, CInc b f ↔ CInc a f) →
      (∀ f ∈ F, CNear b f ↔ CNear a f) → b = a) : σ (vertexOf a) = vertexOf a := by
  refine fix_of_unique hσ (F := F.map vertexOf) (fun f hf => ?_) fun y hy hinc hnear => ?_
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
    exact hF a ha
  obtain ⟨b, rfl⟩ := vertexOf_surjective y
  rw [type_vertexOf, type_vertexOf] at hy
  rw [ha b hy (fun f hf => ?_) (fun f hf => ?_)]
  · rw [← incident_vertexOf_iff, ← incident_vertexOf_iff]
    exact hinc _ (List.mem_map_of_mem hf)
  · rw [← near_vertexOf_iff, ← near_vertexOf_iff]
    exact hnear _ (List.mem_map_of_mem hf)

theorem eq_one_of_forall_fix {σ : Equiv.Perm QVertex}
    (h : ∀ a, σ (vertexOf a) = vertexOf a) : σ = 1 := by
  ext x : 1
  obtain ⟨a, rfl⟩ := vertexOf_surjective x
  exact h a

end CFSG.LieType.Chevalley.C2E6Overlap
