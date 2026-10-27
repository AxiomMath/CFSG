module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cLemma

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section ConjE

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def conjE (j : Y) (E : Subgroup Y) : Subgroup Y := E.map (MulAut.conj j).toMonoidHom

theorem mem_conjE {j x : Y} {E : Subgroup Y} : x ∈ conjE j E ↔ j⁻¹ * x * j ∈ E := by
  unfold conjE
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    have : j⁻¹ * ((MulAut.conj j).toMonoidHom e) * j = e := by
      show j⁻¹ * (j * e * j⁻¹) * j = e
      group
    rw [this]
    exact he
  · intro h
    refine ⟨_, h, ?_⟩
    show j * (j⁻¹ * x * j) * j⁻¹ = x
    group

theorem conj_mem_conjE {j e : Y} {E : Subgroup Y} (he : e ∈ E) : j * e * j⁻¹ ∈ conjE j E := by
  rw [mem_conjE]
  have : j⁻¹ * (j * e * j⁻¹) * j = e := by group
  rw [this]
  exact he

theorem card_conjE (j : Y) (E : Subgroup Y) : Nat.card (conjE j E) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj j).injective

theorem mul_mem_iff_of_card {A B : Subgroup Y} (hA : Nat.card A = 32) (hAB : Nat.card ↥(B ⊓ A) = 16)
    {x y : Y} (hx : x ∈ A) (hy : y ∈ A) : x * y ∈ B ↔ (x ∈ B ↔ y ∈ B) := by
  have h1 : B.relIndex A * Nat.card ↥(B ⊓ A) = Nat.card A := Subgroup.relIndex_mul_card B A
  have h2 : B.relIndex A = 2 := by
    rw [hA, hAB] at h1
    omega
  have h3 : (B.subgroupOf A).index = 2 := h2
  have := Subgroup.mul_mem_iff_of_index_two h3 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  simpa [Subgroup.mem_subgroupOf] using this

structure TwinStr (c t j a d : Y) (X E K₃ K₄ : Subgroup Y) (ρ : Y → AEQ 6) (α : Finset (Fin 6))
    (h : α.card = 4) (b : Bool) : Prop where
  t_mem : t ∈ E
  rho_t : ρ t = zBar α h
  K₃X : ∀ k ∈ K₃, k ∈ X
  K₄X : ∀ k ∈ K₄, k ∈ X
  K₃_lab : (∀ k ∈ K₃, ρ k ∈ memBar α h b) ∧ ∀ x ∈ memBar α h b, ∃ k ∈ K₃, ρ k = x
  K₄_lab : (∀ k ∈ K₄, ρ k ∈ memBar α h (!b)) ∧ ∀ x ∈ memBar α h (!b), ∃ k ∈ K₄, ρ k = x
  j_c : j * c * j⁻¹ = c * t
  j_t : j * t = t * j
  j_K₃ : ∀ k ∈ K₃, j * k = k * j
  j_K₄ : ∀ k ∈ K₄, j * k = k * j
  a_C : a ∈ Subgroup.centralizer ({c} : Set Y)
  a_sq : a * a = t
  a_t : a * t = t * a
  a_K₃ : ∀ k ∈ K₃, a * k = k * a
  a_K₄ : ∀ k ∈ K₄, a * k = k * a
  d_C : d ∈ Subgroup.centralizer ({c} : Set Y)
  d_sq : d * d = 1
  d_a : d * a * d⁻¹ = a * t
  d_t : d * t = t * d
  d_K₃ : ∀ k ∈ K₃, d * k = k * d
  d_K₄ : ∀ k ∈ K₄, d * k = k * d
  j_d : j⁻¹ * d * j = d
  j_a : j⁻¹ * a * j = a * t

namespace TwinStr

variable {c t j a d : Y} {X E K₃ K₄ : Subgroup Y} {ρ : Y → AEQ 6} {α : Finset (Fin 6)} {h : α.card = 4}
  {b : Bool} (S : EStr c X E ρ) (T : TwinStr c t j a d X E K₃ K₄ ρ α h b)

include S T

theorem tt : t * t = 1 := S.E_sq t T.t_mem

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (tt S T)

theorem jinv_t : j⁻¹ * t * j = t := by
  calc j⁻¹ * t * j = j⁻¹ * (t * j) := by group
    _ = j⁻¹ * (j * t) := by rw [T.j_t]
    _ = t := by group

theorem jinv_ct : j⁻¹ * (c * t) * j = c := by
  rw [← T.j_c]
  group

theorem jinv_c : j⁻¹ * c * j = c * t := by
  have h3 : j⁻¹ * t⁻¹ * j = t := by
    rw [show j⁻¹ * t⁻¹ * j = (j⁻¹ * t * j)⁻¹ by group, jinv_t S T, t_inv S T]
  calc j⁻¹ * c * j = (j⁻¹ * (c * t) * j) * (j⁻¹ * t⁻¹ * j) := by group
    _ = c * t := by rw [jinv_ct S T, h3]

theorem j_ct : j * (c * t) * j⁻¹ = c := by
  have hjt : j * t * j⁻¹ = t := by rw [T.j_t]; group
  calc j * (c * t) * j⁻¹ = (j * c * j⁻¹) * (j * t * j⁻¹) := by group
    _ = (c * t) * t := by rw [T.j_c, hjt]
    _ = c := by rw [mul_assoc, tt S T, mul_one]

theorem Ej_abel {x y : Y} (hx : x ∈ conjE j E) (hy : y ∈ conjE j E) : x * y = y * x := by
  have h1 := mem_conjE.1 hx
  have h2 := mem_conjE.1 hy
  have h3 := S.E_comm h1 h2
  have h4 : j⁻¹ * (x * y) * j = j⁻¹ * (y * x) * j := by
    calc j⁻¹ * (x * y) * j = (j⁻¹ * x * j) * (j⁻¹ * y * j) := by group
      _ = (j⁻¹ * y * j) * (j⁻¹ * x * j) := h3
      _ = j⁻¹ * (y * x) * j := by group
  exact mul_left_cancel (mul_right_cancel h4)

theorem c_mem_Ej : c ∈ conjE j E := by
  rw [mem_conjE, jinv_c S T]
  exact E.mul_mem S.c_mem_E T.t_mem

theorem Ej_C {x : Y} (hx : x ∈ conjE j E) : x ∈ Subgroup.centralizer ({c} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have he := mem_conjE.1 hx
  have hct : c * t ∈ E := E.mul_mem S.c_mem_E T.t_mem
  have hcomm := S.E_comm he hct
  calc x * c = x * (j * (c * t) * j⁻¹) := by rw [j_ct S T]
    _ = j * ((j⁻¹ * x * j) * (c * t)) * j⁻¹ := by group
    _ = j * ((c * t) * (j⁻¹ * x * j)) * j⁻¹ := by rw [hcomm]
    _ = (j * (c * t) * j⁻¹) * x := by group
    _ = c * x := by rw [j_ct S T]

theorem Ej_conj_E {x e : Y} (hx : x ∈ conjE j E) (he : e ∈ E) : x * e * x⁻¹ ∈ E :=
  S.E_conj x (Ej_C S T hx) e he

theorem jinv_E_C {e : Y} (he : e ∈ E) : j⁻¹ * e * j ∈ Subgroup.centralizer ({c} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hct : c * t ∈ E := E.mul_mem S.c_mem_E T.t_mem
  have hcomm := S.E_comm he hct
  calc j⁻¹ * e * j * c = j⁻¹ * e * j * (j⁻¹ * (c * t) * j) := by rw [jinv_ct S T]
    _ = j⁻¹ * (e * (c * t)) * j := by group
    _ = j⁻¹ * ((c * t) * e) * j := by rw [hcomm]
    _ = (j⁻¹ * (c * t) * j) * (j⁻¹ * e * j) := by group
    _ = c * (j⁻¹ * e * j) := by rw [jinv_ct S T]

theorem E_conj_Ej {e x : Y} (he : e ∈ E) (hx : x ∈ conjE j E) : e * x * e⁻¹ ∈ conjE j E := by
  rw [mem_conjE]
  have hxe := mem_conjE.1 hx
  have := S.E_conj _ (jinv_E_C S T he) _ hxe
  have e1 : j⁻¹ * (e * x * e⁻¹) * j = (j⁻¹ * e * j) * (j⁻¹ * x * j) * (j⁻¹ * e * j)⁻¹ := by group
  rw [e1]
  exact this

theorem K_conj_E {k e : Y} (hk : k ∈ X) (he : e ∈ E) : k * e * k⁻¹ ∈ E := S.E_conj k (S.XC hk) e he

theorem K_conj_Ej {k x : Y} (hk : k ∈ X) (hjk : j * k = k * j) (hx : x ∈ conjE j E) :
    k * x * k⁻¹ ∈ conjE j E := by
  rw [mem_conjE]
  have hc : Commute j k := hjk
  have h1 : j⁻¹ * k = k * j⁻¹ := hc.inv_left.eq
  have h2 : k⁻¹ * j = j * k⁻¹ := hc.symm.inv_left.eq
  have e1 : j⁻¹ * (k * x * k⁻¹) * j = k * (j⁻¹ * x * j) * k⁻¹ := by
    calc j⁻¹ * (k * x * k⁻¹) * j = (j⁻¹ * k) * x * (k⁻¹ * j) := by group
      _ = (k * j⁻¹) * x * (j * k⁻¹) := by rw [h1, h2]
      _ = k * (j⁻¹ * x * j) * k⁻¹ := by group
  rw [e1]
  exact S.E_conj k (S.XC hk) _ (mem_conjE.1 hx)

end TwinStr

end ConjE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
