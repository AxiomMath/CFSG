module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A4
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Klein

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3

variable {G : Type} [Group G]

theorem klein_elems [Finite G] {V : Subgroup G} (hV : Nat.card V = 4) {z y : G} (hz : z ∈ V) (hy : y ∈ V)
    (hz1 : z ≠ 1) (hy' : y ∉ Subgroup.zpowers z) :
    ∀ u ∈ V, u = 1 ∨ u = z ∨ u = y ∨ u = y * z := by
  intro u hu
  by_contra hcon
  push Not at hcon
  obtain ⟨hu1, huz, huy, huyz⟩ := hcon
  have hy1 : y ≠ 1 := fun h => hy' (h ▸ one_mem _)
  have hyz1 : y * z ≠ 1 := by
    intro h
    apply hy'
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this]
    exact inv_mem (Subgroup.mem_zpowers z)
  have hzy : z ≠ y := fun h => hy' (h ▸ Subgroup.mem_zpowers z)
  have hzyz : z ≠ y * z := fun h => hy1 (by
    have : z = 1 * z := by rw [one_mul]
    exact mul_right_cancel (this.symm.trans h).symm)
  have hyyz : y ≠ y * z := fun h => hz1 (by
    have : y * 1 = y * z := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm)
  have hlist : ([1, z, y, y * z, u] : List G).Nodup := by
    simp [List.nodup_cons, hz1.symm, hy1.symm, hyz1.symm, hu1.symm, hzy, hzyz, huz.symm, hyyz,
      huy.symm, huyz.symm]
  have hlen := list_length_le_four hV _ hlist (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz
    · exact hy
    · exact V.mul_mem hy hz
    · exact hu)
  simp at hlen

@[expose] def klabel (y₁ z₁ y₂ z₂ : G) : Fin 5 → G := ![y₁, y₁ * z₁, y₂, y₂ * z₂, 1]

structure KPair (U₁ U₂ : Subgroup G) (z₁ y₁ z₂ y₂ : G) : Prop where
  card₁ : Nat.card U₁ = 4
  card₂ : Nat.card U₂ = 4
  sq₁ : ∀ a ∈ U₁, a ^ 2 = 1
  sq₂ : ∀ a ∈ U₂, a ^ 2 = 1
  comm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a
  inf : U₁ ⊓ U₂ = ⊥
  hz₁ : z₁ ∈ U₁
  hz₂ : z₂ ∈ U₂
  hy₁ : y₁ ∈ U₁
  hy₂ : y₂ ∈ U₂
  z₁_ne : z₁ ≠ 1
  z₂_ne : z₂ ≠ 1
  y₁_nmem : y₁ ∉ Subgroup.zpowers z₁
  y₂_nmem : y₂ ∉ Subgroup.zpowers z₂

namespace KPair

variable {U₁ U₂ : Subgroup G} {z₁ y₁ z₂ y₂ : G} (K : KPair U₁ U₂ z₁ y₁ z₂ y₂)
include K

theorem elems₁ [Finite G] : ∀ u ∈ U₁, u = 1 ∨ u = z₁ ∨ u = y₁ ∨ u = y₁ * z₁ :=
  klein_elems K.card₁ K.hz₁ K.hy₁ K.z₁_ne K.y₁_nmem

theorem elems₂ [Finite G] : ∀ u ∈ U₂, u = 1 ∨ u = z₂ ∨ u = y₂ ∨ u = y₂ * z₂ :=
  klein_elems K.card₂ K.hz₂ K.hy₂ K.z₂_ne K.y₂_nmem

theorem cross {u v : G} (hu : u ∈ U₁) (hv : v ∈ U₂) (h : u = v) : u = 1 := by
  have : u ∈ U₁ ⊓ U₂ := ⟨hu, h ▸ hv⟩
  rw [K.inf, Subgroup.mem_bot] at this
  exact this

theorem y₁_ne_one : y₁ ≠ 1 := fun h => K.y₁_nmem (h ▸ one_mem _)

theorem y₂_ne_one : y₂ ≠ 1 := fun h => K.y₂_nmem (h ▸ one_mem _)

theorem y₁z₁_ne_one : y₁ * z₁ ≠ 1 := by
  intro h
  apply K.y₁_nmem
  have : y₁ = z₁⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this]
  exact inv_mem (Subgroup.mem_zpowers z₁)

theorem y₂z₂_ne_one : y₂ * z₂ ≠ 1 := by
  intro h
  apply K.y₂_nmem
  have : y₂ = z₂⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [this]
  exact inv_mem (Subgroup.mem_zpowers z₂)

theorem y₁z₁_mem : y₁ * z₁ ∈ U₁ := U₁.mul_mem K.hy₁ K.hz₁

theorem y₂z₂_mem : y₂ * z₂ ∈ U₂ := U₂.mul_mem K.hy₂ K.hz₂

theorem y₁_sq : y₁ * y₁ = 1 := by simpa [pow_two] using K.sq₁ y₁ K.hy₁

theorem y₂_sq : y₂ * y₂ = 1 := by simpa [pow_two] using K.sq₂ y₂ K.hy₂

theorem comm₁ : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := C5.comm_of_sq_eq_one K.sq₁

theorem comm₂ : ∀ a ∈ U₂, ∀ b ∈ U₂, a * b = b * a := C5.comm_of_sq_eq_one K.sq₂

theorem lab_mem (i : Fin 5) : klabel y₁ z₁ y₂ z₂ i ∈ U₁ ⊔ U₂ := by
  fin_cases i
  · exact Subgroup.mem_sup_left K.hy₁
  · exact Subgroup.mem_sup_left K.y₁z₁_mem
  · exact Subgroup.mem_sup_right K.hy₂
  · exact Subgroup.mem_sup_right K.y₂z₂_mem
  · exact one_mem _

theorem lab_inj : Function.Injective (klabel y₁ z₁ y₂ z₂) := by
  have h01 : y₁ ≠ y₁ * z₁ := fun h => K.z₁_ne (by
    have : y₁ * 1 = y₁ * z₁ := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm)
  have h23 : y₂ ≠ y₂ * z₂ := fun h => K.z₂_ne (by
    have : y₂ * 1 = y₂ * z₂ := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm)
  have h02 : y₁ ≠ y₂ := fun h => K.y₁_ne_one (K.cross K.hy₁ K.hy₂ h)
  have h03 : y₁ ≠ y₂ * z₂ := fun h => K.y₁_ne_one (K.cross K.hy₁ K.y₂z₂_mem h)
  have h12 : y₁ * z₁ ≠ y₂ := fun h => K.y₁z₁_ne_one (K.cross K.y₁z₁_mem K.hy₂ h)
  have h13 : y₁ * z₁ ≠ y₂ * z₂ := fun h => K.y₁z₁_ne_one (K.cross K.y₁z₁_mem K.y₂z₂_mem h)
  have h04 : y₁ ≠ 1 := K.y₁_ne_one
  have h14 : y₁ * z₁ ≠ 1 := K.y₁z₁_ne_one
  have h24 : y₂ ≠ 1 := K.y₂_ne_one
  have h34 : y₂ * z₂ ≠ 1 := K.y₂z₂_ne_one
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [klabel, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hij ⊢ <;>
    first
    | rfl
    | exact absurd hij ‹_›
    | exact absurd hij.symm ‹_›

theorem lab_gen [Finite G] : U₁ ⊔ U₂ ≤ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) := by
  have h0 : y₁ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have h1 : y₁ * z₁ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have h2 : y₂ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) :=
    Subgroup.subset_closure ⟨2, rfl⟩
  have h3 : y₂ * z₂ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) :=
    Subgroup.subset_closure ⟨3, rfl⟩
  have hz1 : z₁ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) := by
    have := mul_mem h0 h1
    have e : y₁ * (y₁ * z₁) = z₁ := by rw [← mul_assoc, K.y₁_sq, one_mul]
    rwa [e] at this
  have hz2 : z₂ ∈ Subgroup.closure (Set.range (klabel y₁ z₁ y₂ z₂)) := by
    have := mul_mem h2 h3
    have e : y₂ * (y₂ * z₂) = z₂ := by rw [← mul_assoc, K.y₂_sq, one_mul]
    rwa [e] at this
  refine sup_le (fun u hu => ?_) (fun u hu => ?_)
  · rcases K.elems₁ u hu with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz1
    · exact h0
    · exact h1
  · rcases K.elems₂ u hu with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hz2
    · exact h2
    · exact h3

theorem elemAbelian₁ : IsElemAbelian 2 U₁ :=
  C5.isElemAbelian_two_iff.2 ⟨K.comm₁, K.sq₁⟩

theorem elemAbelian₂ : IsElemAbelian 2 U₂ :=
  C5.isElemAbelian_two_iff.2 ⟨K.comm₂, K.sq₂⟩

theorem elemAbelian_sup [Finite G] : IsElemAbelian 2 (U₁ ⊔ U₂) :=
  B2F.isElemAbelian_sup_of_commute K.elemAbelian₁ K.elemAbelian₂ K.comm

theorem card_sup [Finite G] : Nat.card ↥(U₁ ⊔ U₂) = 16 := by
  have := C5.card_sup_mul_card_inf_of_le_normalizer (C5.le_normalizer_of_commute K.comm)
  rw [K.inf, Subgroup.card_bot, mul_one, K.card₁, K.card₂] at this
  omega

end KPair

end CFSG.QuasithinUnique.AppD
