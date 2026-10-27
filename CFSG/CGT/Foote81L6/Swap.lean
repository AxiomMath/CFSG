module

public import CFSG.CGT.Foote81L6.TStruct.TAction

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

private theorem conj_mem_B₁_of_mem_B₀B₁' {w x : G} (hw : w ∈ D.B₀ ⊔ D.B₁) (hx : x ∈ D.B₁) :
    w * x * w⁻¹ ∈ D.B₁ := by
  obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
  have h1 : w₀ * (w₁ * x * w₁⁻¹) = (w₁ * x * w₁⁻¹) * w₀ :=
    D.B₀_comm_B₁ w₀ hw₀ _ (mul_mem (mul_mem hw₁ hx) (inv_mem hw₁))
  have e : w₀ * w₁ * x * (w₀ * w₁)⁻¹ = w₁ * x * w₁⁻¹ := by
    calc w₀ * w₁ * x * (w₀ * w₁)⁻¹ = (w₀ * (w₁ * x * w₁⁻¹)) * w₀⁻¹ := by group
      _ = w₁ * x * w₁⁻¹ := by rw [h1]; group
  rw [e]
  exact mul_mem (mul_mem hw₁ hx) (inv_mem hw₁)

theorem conj_mem_B₀_of_not_mem {c x : G} (hc : c ∈ D.B) (hc' : c ∉ D.B₀ ⊔ D.B₁) (hx : x ∈ D.B₁) :
    c * x * c⁻¹ ∈ D.B₀ := by
  have hcs : c * D.s ∈ D.B₀ ⊔ D.B₁ := (D.mem_B_iff.1 hc).resolve_left hc'
  have e : (c * D.s) * (D.s * x * D.s⁻¹) * (c * D.s)⁻¹ = c * x * c⁻¹ := by
    calc (c * D.s) * (D.s * x * D.s⁻¹) * (c * D.s)⁻¹
        = c * (D.s * D.s) * x * (D.s * D.s)⁻¹ * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [D.s_mul_s, inv_one, mul_one, mul_one]
  rw [← e]
  exact D.conj_mem_B₀_of_mem_B₀B₁ hcs (D.conj_s_mem_B₀ hx)

theorem conj_mem_B₁_of_not_mem {c x : G} (hc : c ∈ D.B) (hc' : c ∉ D.B₀ ⊔ D.B₁) (hx : x ∈ D.B₀) :
    c * x * c⁻¹ ∈ D.B₁ := by
  have hcs : c * D.s ∈ D.B₀ ⊔ D.B₁ := (D.mem_B_iff.1 hc).resolve_left hc'
  have e : (c * D.s) * (D.s * x * D.s⁻¹) * (c * D.s)⁻¹ = c * x * c⁻¹ := by
    calc (c * D.s) * (D.s * x * D.s⁻¹) * (c * D.s)⁻¹
        = c * (D.s * D.s) * x * (D.s * D.s)⁻¹ * c⁻¹ := by group
      _ = c * x * c⁻¹ := by rw [D.s_mul_s, inv_one, mul_one, mul_one]
  rw [← e]
  exact D.conj_mem_B₁_of_mem_B₀B₁' hcs (D.conj_s_mem_B₁ hx)

theorem exists_comm_t_not_mem_B₀B₁ :
    ∃ c ∈ D.B, c ∉ D.B₀ ⊔ D.B₁ ∧ c * D.t = D.t * c := by
  by_contra hcon
  push Not at hcon
  haveI := D.finite_B₀
  set C : Subgroup G := (D.B₀ ⊔ D.B₁) ⊓ centralizer ({D.t} : Set G)
  have hle : D.B ⊓ centralizer ({D.t} : Set G) ≤ C := by
    intro c hc
    obtain ⟨hcB, hct⟩ := mem_inf.1 hc
    refine mem_inf.2 ⟨?_, hct⟩
    by_contra hc'
    exact hcon c hcB hc' (mem_centralizer_singleton_iff.1 hct)
  have hmemC : ∀ y : ↥D.B₀, (y : G) * (D.t * y * D.t⁻¹) ∈ C := by
    intro y
    refine mem_inf.2 ⟨mul_mem (mem_sup_left y.2) (D.B₀t_le_B₀B₁ (D.conj_t_mem_B₀t y.2)),
      mem_centralizer_singleton_iff.2 ?_⟩
    have hc : (y : G) * (D.t * y * D.t⁻¹) = (D.t * y * D.t⁻¹) * y :=
      D.B₀_comm_B₀t y.2 (D.conj_t_mem_B₀t y.2)
    have htt : D.t * (D.t * (y : G) * D.t⁻¹) * D.t⁻¹ = y := by
      calc D.t * (D.t * (y : G) * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * y * (D.t * D.t)⁻¹ := by group
        _ = y := by rw [D.t_mul_t, one_mul, inv_one, mul_one]
    calc (y : G) * (D.t * y * D.t⁻¹) * D.t = (D.t * y * D.t⁻¹) * y * D.t := by rw [hc]
      _ = (D.t * y * D.t⁻¹) * (D.t * (D.t * y * D.t⁻¹) * D.t⁻¹) * D.t := by rw [htt]
      _ = D.t * (y * (D.t * y * D.t⁻¹)) := by group
  let f : ↥D.B₀ → ↥C := fun y => ⟨(y : G) * (D.t * y * D.t⁻¹), hmemC y⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨hxB, hxt⟩ := mem_inf.1 hx
    rw [← D.B₀_sup_B₀t] at hxB
    obtain ⟨y, hy, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun u hu v hv => D.B₀_comm_B₀t hu hv)).1 hxB
    have hct := mem_centralizer_singleton_iff.1 hxt
    have hty : D.t * y * D.t⁻¹ ∈ D.B₀t := D.conj_t_mem_B₀t hy
    have htz : D.t * z * D.t⁻¹ ∈ D.B₀ := (D.mem_B₀t_iff).1 hz
    have hconj : (D.t * z * D.t⁻¹) * (D.t * y * D.t⁻¹) = y * z := by
      have h1 : D.t * (y * z) * D.t⁻¹ = y * z := by rw [← hct, mul_inv_cancel_right]
      calc (D.t * z * D.t⁻¹) * (D.t * y * D.t⁻¹)
          = (D.t * y * D.t⁻¹) * (D.t * z * D.t⁻¹) := D.B₀_comm_B₀t htz hty
        _ = D.t * (y * z) * D.t⁻¹ := by group
        _ = y * z := h1
    obtain ⟨-, hzy⟩ := TStruct.eq_and_eq_of_mul_eq_mul D.B₀_inf_B₀t htz hy hty hz hconj
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    show y * (D.t * y * D.t⁻¹) = y * z
    rw [hzy]
  have hcard : Nat.card ↥C ≤ 2 ^ n := by
    rw [← D.card_B₀]
    exact Nat.card_le_card_of_surjective f hf
  haveI : Finite ↥C := Finite.of_surjective f hf
  have hle' := Subgroup.card_le_of_le hle
  rw [D.card_CBt] at hle'
  have hlt : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

@[expose] noncomputable def swap : FooteCore G T m n where
  A := D.A
  B := D.B
  B₀ := D.B₁
  B₁ := D.B₀
  t := D.t
  s := D.s
  a := D.a
  b₀ := D.b₁
  b₁ := D.b₀
  T_eq := D.T_eq
  A_inf_B := D.A_inf_B
  A_comm_B := D.A_comm_B
  conj_t_A := D.conj_t_A
  conj_t_B := D.conj_t_B
  t_sq := D.t_sq
  two_le_m := D.two_le_m
  A_iso := D.A_iso
  At_iso := D.At_iso
  B_eq := by rw [D.B_eq, sup_comm D.B₀ D.B₁]
  B₀_inf_B₁ := by rw [inf_comm]; exact D.B₀_inf_B₁
  B₀_comm_B₁ := fun x hx y hy => (D.B₀_comm_B₁ y hy x hx).symm
  m_lt_n := D.m_lt_n
  B₀_iso := D.B₁_iso
  B₁_iso := D.B₀_iso
  s_sq := D.s_sq
  conj_s_B₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact D.conj_s_mem_B₀ hy
    · intro hx
      refine ⟨D.s * x * D.s⁻¹, D.conj_s_mem_B₁ hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc D.s * (D.s * x * D.s⁻¹) * D.s⁻¹ = (D.s * D.s) * x * (D.s * D.s)⁻¹ := by group
        _ = x := by rw [D.s_mul_s, one_mul, inv_one, mul_one]
  Bt_conj := D.Bt_conj
  CBt_iso := D.CBt_iso
  a_mem := D.a_mem
  a_order := D.a_order
  a_comm := D.a_comm
  b₀_mem := D.b₁_mem
  b₀_order := D.b₁_order
  b₀_comm := D.b₁_comm
  b₁_mem := D.b₀_mem
  b₁_order := D.b₀_order
  b₁_comm := D.b₀_comm

@[simp] theorem swap_A : D.swap.A = D.A := rfl
@[simp] theorem swap_B : D.swap.B = D.B := rfl
@[simp] theorem swap_B₀ : D.swap.B₀ = D.B₁ := rfl
@[simp] theorem swap_B₁ : D.swap.B₁ = D.B₀ := rfl
@[simp] theorem swap_t : D.swap.t = D.t := rfl
@[simp] theorem swap_s : D.swap.s = D.s := rfl
@[simp] theorem swap_a : D.swap.a = D.a := rfl
@[simp] theorem swap_b₀ : D.swap.b₀ = D.b₁ := rfl
@[simp] theorem swap_b₁ : D.swap.b₁ = D.b₀ := rfl

theorem swap_b : D.swap.b = D.b := by
  show D.b₁ * D.b₀ = D.b₀ * D.b₁
  exact (D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem).symm

theorem swap_T₁ : D.swap.T₁ = D.T₁ := by
  show D.A ⊔ (D.B₁ ⊔ D.B₀) = D.A ⊔ (D.B₀ ⊔ D.B₁)
  rw [sup_comm D.B₁ D.B₀]

theorem swap_Astar : D.swap.Astar = D.Astar := by
  rw [FooteCore.Astar, FooteCore.Astar, D.swap_b]
  rfl

end FooteCore

namespace FooteData

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteData G T m n)

private theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm

private theorem isConj_of_isConj_conj {x y : G} (g : G) (h : IsConj x (g * y * g⁻¹)) :
    IsConj x y :=
  h.trans (isConj_iff.2 ⟨g, rfl⟩).symm

theorem fusion_v_of_mem {t' r : G} (ht' : t' ∈ T) (ht'0 : t' ∉ D.T₀) (ht'2 : t' * t' = 1)
    (hr : r ∈ D.B₀ ∨ r ∈ D.B₁) (hr2 : orderOf r = 2) :
    ¬ IsConj D.a (r * (t' * r * t'⁻¹)) := by
  intro hc
  obtain ⟨h, hhT₀, hht⟩ := D.exists_conj_t ht' ht'0 ht'2
  obtain ⟨α, hα, β, hβ, rfl⟩ := D.mem_T₀_iff.1 hhT₀
  have hrB : r ∈ D.B := hr.elim (fun h => D.B₀_le_B h) (fun h => D.B₁_le_B h)
  have hαr : α * r = r * α := D.A_comm_B α hα r hrB
  set r' := β⁻¹ * r * β⁻¹⁻¹ with hr'_def
  have hr'eq : (α * β)⁻¹ * r * (α * β) = r' := by
    calc (α * β)⁻¹ * r * (α * β) = β⁻¹ * (α⁻¹ * (r * α)) * β := by group
      _ = β⁻¹ * (α⁻¹ * (α * r)) * β := by rw [hαr]
      _ = r' := by rw [hr'_def]; group
  have hkey : r * (t' * r * t'⁻¹) = (α * β) * (r' * (D.t * r' * D.t⁻¹)) * (α * β)⁻¹ := by
    rw [← hht, ← hr'eq]
    group
  have hc' : IsConj D.a (r' * (D.t * r' * D.t⁻¹)) := by
    rw [hkey] at hc
    exact isConj_of_isConj_conj _ hc
  have hr'2 : orderOf r' = 2 := by rw [hr'_def, orderOf_conj', hr2]
  have hr' : r' ∈ D.B₀ ∨ r' ∈ D.B₁ := by
    by_cases hb : β⁻¹ ∈ D.B₀ ⊔ D.B₁
    · rcases hr with hr | hr
      · exact Or.inl (D.conj_mem_B₀_of_mem_B₀B₁ hb hr)
      · exact Or.inr (D.conj_mem_B₁_of_mem_B₀B₁' hb hr)
    · rcases hr with hr | hr
      · exact Or.inr (D.conj_mem_B₁_of_not_mem (inv_mem hβ) hb hr)
      · exact Or.inl (D.conj_mem_B₀_of_not_mem (inv_mem hβ) hb hr)
  rcases hr' with hr' | hr'
  · exact D.fusion_v r' hr' hr'2 hc'
  · obtain ⟨c, hcB, hcn, hct⟩ := D.exists_comm_t_not_mem_B₀B₁
    have hcr : c * r' * c⁻¹ ∈ D.B₀ := D.conj_mem_B₀_of_not_mem hcB hcn hr'
    apply D.fusion_v _ hcr (by rw [orderOf_conj', hr'2])
    refine hc'.trans (isConj_iff.2 ⟨c, ?_⟩)
    have hct' : c * D.t * c⁻¹ = D.t := by rw [hct, mul_inv_cancel_right]
    calc c * (r' * (D.t * r' * D.t⁻¹)) * c⁻¹
        = (c * r' * c⁻¹) * ((c * D.t * c⁻¹) * (c * r' * c⁻¹) * (c * D.t * c⁻¹)⁻¹) := by group
      _ = (c * r' * c⁻¹) * (D.t * (c * r' * c⁻¹) * D.t⁻¹) := by rw [hct']

private theorem exists_conj_s {r : G} (hr : r ∈ D.B₁) :
    D.s * r * D.s⁻¹ ∈ D.B₀ ∧ D.s * (D.s * r * D.s⁻¹) * D.s⁻¹ = r := by
  refine ⟨D.conj_s_mem_B₀ hr, ?_⟩
  calc D.s * (D.s * r * D.s⁻¹) * D.s⁻¹ = (D.s * D.s) * r * (D.s * D.s)⁻¹ := by group
    _ = r := by rw [D.s_mul_s, one_mul, inv_one, mul_one]

@[expose] noncomputable def swap : FooteData G T m n :=
  { D.toFooteCore.swap with
    fusion_i := by
      intro x hx hx2 hxa r hr hr2 hc
      obtain ⟨hr₀, hrr⟩ := D.exists_conj_s hr
      have hxs : D.s * x * D.s⁻¹ = x := by
        rw [(D.A_comm_B x hx D.s D.s_mem_B).symm, mul_inv_cancel_right]
      apply D.fusion_i x hx hx2 hxa _ hr₀ (by rw [orderOf_conj']; exact hr2)
      apply isConj_of_isConj_conj D.s
      have e : D.s * (x * (D.s * r * D.s⁻¹)) * D.s⁻¹ =
          (D.s * x * D.s⁻¹) * (D.s * (D.s * r * D.s⁻¹) * D.s⁻¹) := by group
      rw [e, hxs, hrr]
      exact hc
    fusion_ii := by
      intro r hr hr2 hc
      obtain ⟨hr₀, hrr⟩ := D.exists_conj_s hr
      apply D.fusion_ii _ hr₀ (by rw [orderOf_conj']; exact hr2)
      apply isConj_of_isConj_conj D.s
      have e : D.s * ((D.s * r * D.s⁻¹) * D.b₁) * D.s⁻¹ =
          (D.s * (D.s * r * D.s⁻¹) * D.s⁻¹) * (D.s * D.b₁ * D.s⁻¹) := by group
      rw [e, hrr, D.conj_s_b₁]
      exact hc
    fusion_iii := by
      intro x hx hx2 hxa y hy hy2 hya r hr hr2 hc
      obtain ⟨hr₀, hrr⟩ := D.exists_conj_s hr
      have hxs : D.s * x * D.s⁻¹ = x := by
        rw [(D.A_comm_B x hx D.s D.s_mem_B).symm, mul_inv_cancel_right]
      apply D.fusion_iii x hx hx2 hxa y hy hy2 hya _ hr₀ (by rw [orderOf_conj']; exact hr2)
      have e : x * r = D.s * (x * (D.s * r * D.s⁻¹)) * D.s⁻¹ := by
        have e' : D.s * (x * (D.s * r * D.s⁻¹)) * D.s⁻¹ =
            (D.s * x * D.s⁻¹) * (D.s * (D.s * r * D.s⁻¹) * D.s⁻¹) := by group
        rw [e', hxs, hrr]
      rw [e] at hc
      exact (isConj_iff.2 ⟨D.s, rfl⟩).trans hc
    fusion_iv := by
      intro x hx hx2 hxa r hr hr2 hc
      obtain ⟨hr₀, hrr⟩ := D.exists_conj_s hr
      have hxs : D.s * x * D.s⁻¹ = x := by
        rw [(D.A_comm_B x hx D.s D.s_mem_B).symm, mul_inv_cancel_right]
      apply D.fusion_iv x hx hx2 hxa _ hr₀ (by rw [orderOf_conj']; exact hr2)
      have e1 : x * r * D.b₀ = D.s * (x * (D.s * r * D.s⁻¹) * D.b₁) * D.s⁻¹ := by
        have e' : D.s * (x * (D.s * r * D.s⁻¹) * D.b₁) * D.s⁻¹ =
            (D.s * x * D.s⁻¹) * (D.s * (D.s * r * D.s⁻¹) * D.s⁻¹) * (D.s * D.b₁ * D.s⁻¹) := by
          group
        rw [e', hxs, hrr, D.conj_s_b₁]
      have e2 : x * D.b₁ = D.s * (x * D.b₀) * D.s⁻¹ := by
        have e' : D.s * (x * D.b₀) * D.s⁻¹ = (D.s * x * D.s⁻¹) * (D.s * D.b₀ * D.s⁻¹) := by group
        rw [e', hxs, D.conj_s_b₀]
      change IsConj (x * r * D.b₀) (x * D.b₁) at hc
      rw [e1, e2] at hc
      exact (isConj_iff.2 ⟨D.s, rfl⟩).trans (hc.trans (isConj_iff.2 ⟨D.s, rfl⟩).symm)
    fusion_v := by
      intro r hr hr2
      exact D.fusion_v_of_mem D.t_mem_T D.t_not_mem_T₀ D.t_mul_t (Or.inr hr) hr2 }

theorem swap_toFooteCore : D.swap.toFooteCore = D.toFooteCore.swap := rfl

end FooteData

end CFSG.CGT.Foote81L6
