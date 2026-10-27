module

public import CFSG.CGT.Foote81L6.TStruct.Dihedral2

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem A_le_T₀ : D.A ≤ D.T₀ := le_sup_left

theorem B_le_T₀ : D.B ≤ D.T₀ := le_sup_right

theorem A_le_T₁ : D.A ≤ D.T₁ := le_sup_left

theorem B₀B₁_le_T₁ : D.B₀ ⊔ D.B₁ ≤ D.T₁ := le_sup_right

theorem B₀_le_T₁ : D.B₀ ≤ D.T₁ := le_sup_left.trans D.B₀B₁_le_T₁

theorem B₁_le_T₁ : D.B₁ ≤ D.T₁ := le_sup_right.trans D.B₀B₁_le_T₁

theorem T₁_le_T₀ : D.T₁ ≤ D.T₀ := sup_le_sup_left D.B₀B₁_le_B _

theorem T₁_le_T : D.T₁ ≤ T := D.T₁_le_T₀.trans D.T₀_le_T

theorem A_comm_B₀B₁ : ∀ x ∈ D.A, ∀ y ∈ D.B₀ ⊔ D.B₁, x * y = y * x :=
  fun x hx y hy => D.A_comm_B x hx y (D.B₀B₁_le_B hy)

theorem A_inf_B₀B₁ : D.A ⊓ (D.B₀ ⊔ D.B₁) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_left _ D.B₀B₁_le_B).trans D.A_inf_B.le)

theorem mem_T₁_iff {g : G} : g ∈ D.T₁ ↔ ∃ x ∈ D.A, ∃ w ∈ D.B₀ ⊔ D.B₁, g = x * w :=
  mem_sup_iff_of_le_normalizer (le_normalizer_of_comm D.A_comm_B₀B₁)

theorem eq_of_mul_eq_mul_T₀ {x x' y y' : G} (hx : x ∈ D.A) (hx' : x' ∈ D.A) (hy : y ∈ D.B)
    (hy' : y' ∈ D.B) (h : x * y = x' * y') : x = x' ∧ y = y' :=
  eq_and_eq_of_mul_eq_mul D.A_inf_B hx hx' hy hy' h

theorem eq_of_mul_eq_mul_B₀B₁ {x x' y y' : G} (hx : x ∈ D.B₀) (hx' : x' ∈ D.B₀) (hy : y ∈ D.B₁)
    (hy' : y' ∈ D.B₁) (h : x * y = x' * y') : x = x' ∧ y = y' :=
  eq_and_eq_of_mul_eq_mul D.B₀_inf_B₁ hx hx' hy hy' h

theorem mul_eq_one_T₀ {x y : G} (hx : x ∈ D.A) (hy : y ∈ D.B) (h : x * y = 1) :
    x = 1 ∧ y = 1 :=
  D.eq_of_mul_eq_mul_T₀ hx (one_mem _) hy (one_mem _) (h.trans (mul_one 1).symm)

theorem mul_eq_one_B₀B₁ {x y : G} (hx : x ∈ D.B₀) (hy : y ∈ D.B₁) (h : x * y = 1) :
    x = 1 ∧ y = 1 :=
  D.eq_of_mul_eq_mul_B₀B₁ hx (one_mem _) hy (one_mem _) (h.trans (mul_one 1).symm)

theorem mem_T₁_or_mul_s_mem_T₁ {g : G} (hg : g ∈ D.T₀) : g ∈ D.T₁ ∨ g * D.s ∈ D.T₁ := by
  obtain ⟨x, hx, y, hy, rfl⟩ := D.mem_T₀_iff.1 hg
  rcases D.mem_B_iff.1 hy with h | h
  · exact Or.inl (mul_mem (D.A_le_T₁ hx) (D.B₀B₁_le_T₁ h))
  · right
    rw [mul_assoc]
    exact mul_mem (D.A_le_T₁ hx) (D.B₀B₁_le_T₁ h)

theorem T₀_le_T₁_sup_s : D.T₀ ≤ D.T₁ ⊔ zpowers D.s := by
  intro g hg
  rcases D.mem_T₁_or_mul_s_mem_T₁ hg with h | h
  · exact mem_sup_left h
  · have e : g = g * D.s * D.s := by rw [mul_assoc, D.s_mul_s, mul_one]
    rw [e]
    exact mul_mem (mem_sup_left h) (mem_sup_right (mem_zpowers _))

theorem s_not_mem_T₁ : D.s ∉ D.T₁ := by
  intro hs
  obtain ⟨x, hx, w, hw, hxw⟩ := D.mem_T₁_iff.1 hs
  have h := D.eq_of_mul_eq_mul_T₀ (one_mem _) hx D.s_mem_B (D.B₀B₁_le_B hw)
    ((one_mul _).trans hxw)
  exact D.s_not_mem_B₀B₁ (h.2 ▸ hw)

theorem exists_conj_t_of_mem_A {x : G} (hx : x ∈ D.A) (hxt : x * D.t * (x * D.t) = 1) :
    ∃ α ∈ D.A, α * (x * D.t) * α⁻¹ = D.t := by
  obtain ⟨e⟩ := D.At_iso
  obtain ⟨eA⟩ := D.A_iso
  have hAAt : D.A ≤ D.A ⊔ zpowers D.t := le_sup_left
  have htAt : D.t ∈ D.A ⊔ zpowers D.t := mem_sup_right (mem_zpowers _)
  have hxtAt : x * D.t ∈ D.A ⊔ zpowers D.t := mul_mem (hAAt hx) htAt
  set H' : Subgroup (DihedralGroup (2 ^ m)) := (D.A.subgroupOf (D.A ⊔ zpowers D.t)).map
    e.toMonoidHom with hH'
  have hmemH' : ∀ g : ↥(D.A ⊔ zpowers D.t), e g ∈ H' ↔ (g : G) ∈ D.A := by
    intro g
    rw [hH', mem_map_equiv, MulEquiv.symm_apply_apply, mem_subgroupOf]
  have hcardH' : Nat.card H' = 2 ^ m := by
    rw [hH', card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAAt).toEquiv, D.card_A]
  have hindex : H'.index = 2 := by
    have h := card_mul_index H'
    rw [hcardH', DihedralGroup.nat_card] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ m) (h.trans (mul_comm _ _))
  have hr : r 1 ∉ H' := by
    intro hr1
    have hcz : Nat.card (zpowers (r 1 : DihedralGroup (2 ^ m))) = 2 ^ m := by
      rw [Nat.card_zpowers, orderOf_r_one]
    have heq : zpowers (r 1 : DihedralGroup (2 ^ m)) = H' :=
      eq_of_le_of_card_ge (zpowers_le.2 hr1) (by rw [hcz, hcardH'])
    have hcyc : IsCyclic H' := by rw [← heq]; infer_instance
    have eH : H' ≃* DihedralGroup (2 ^ (m - 1)) :=
      ((equivMapOfInjective _ e.toMonoidHom e.injective).symm.trans
        (subgroupOfEquivOfLe hAAt)).trans eA
    have h2 : 2 ≤ 2 ^ (m - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by have := D.two_le_m; omega)
    exact DihedralGroup.not_isCyclic (by omega) (eH.isCyclic.1 hcyc)
  have hu : e ⟨x * D.t, hxtAt⟩ ∉ H' := by
    rw [hmemH']
    intro h
    apply D.t_not_mem_A
    have e1 : D.t = x⁻¹ * (x * D.t) := by group
    rw [e1]
    exact mul_mem (inv_mem hx) h
  have hw : e ⟨D.t, htAt⟩ ∉ H' := by
    rw [hmemH']
    exact D.t_not_mem_A
  have hu2 : e ⟨x * D.t, hxtAt⟩ * e ⟨x * D.t, hxtAt⟩ = 1 := by
    rw [← map_mul, ← e.map_one]
    exact congrArg e (Subtype.ext hxt)
  have hw2 : e ⟨D.t, htAt⟩ * e ⟨D.t, htAt⟩ = 1 := by
    rw [← map_mul, ← e.map_one]
    exact congrArg e (Subtype.ext D.t_mul_t)
  obtain ⟨h, hh, hconj⟩ :=
    conj_of_not_mem_of_index_two D.two_le_m hindex hr hu hw hu2 hw2
  obtain ⟨g, rfl⟩ := e.surjective h
  rw [hmemH'] at hh
  refine ⟨g, hh, ?_⟩
  have h1 : e (g * ⟨x * D.t, hxtAt⟩ * g⁻¹) = e ⟨D.t, htAt⟩ := by
    rw [map_mul, map_mul, map_inv]
    exact hconj
  exact congrArg Subtype.val (e.injective h1)

theorem exists_conj_t {g : G} (hg : g ∈ T) (hg0 : g ∉ D.T₀) (hg2 : g * g = 1) :
    ∃ h ∈ D.T₀, h * D.t * h⁻¹ = g := by
  have hgt : g * D.t ∈ D.T₀ := (D.mem_T_iff.1 hg).resolve_left hg0
  obtain ⟨x, hx, y, hy, hxy⟩ := D.mem_T₀_iff.1 hgt
  have hg' : g = x * y * D.t := by
    calc g = g * D.t * D.t := by rw [mul_assoc, D.t_mul_t, mul_one]
      _ = x * y * D.t := by rw [hxy]
  have hx' : D.t * x * D.t⁻¹ ∈ D.A := D.conj_t_A x hx
  have hy' : D.t * y * D.t⁻¹ ∈ D.B := D.conj_t_B y hy
  have hc : y * (D.t * x * D.t⁻¹) = (D.t * x * D.t⁻¹) * y := (D.A_comm_B _ hx' y hy).symm
  have hgg : (x * (D.t * x * D.t⁻¹)) * (y * (D.t * y * D.t⁻¹)) = 1 := by
    calc (x * (D.t * x * D.t⁻¹)) * (y * (D.t * y * D.t⁻¹))
        = x * ((D.t * x * D.t⁻¹) * y) * (D.t * y * D.t⁻¹) := by group
      _ = x * (y * (D.t * x * D.t⁻¹)) * (D.t * y * D.t⁻¹) := by rw [hc]
      _ = x * y * (D.t * (x * y) * D.t⁻¹) := by group
      _ = x * y * (D.t * (x * y) * D.t⁻¹) * (D.t * D.t) := by rw [D.t_mul_t, mul_one]
      _ = g * g := by rw [hg']; group
      _ = 1 := hg2
  obtain ⟨hxx, hyy⟩ := D.mul_eq_one_T₀ (mul_mem hx hx') (mul_mem hy hy') hgg
  have hxt : x * D.t * (x * D.t) = 1 := by
    calc x * D.t * (x * D.t) = x * (D.t * x * D.t⁻¹) * (D.t * D.t) := by group
      _ = 1 := by rw [hxx, D.t_mul_t, one_mul]
  have hyt : (y * D.t) ^ 2 = 1 := by
    rw [pow_two]
    calc y * D.t * (y * D.t) = y * (D.t * y * D.t⁻¹) * (D.t * D.t) := by group
      _ = 1 := by rw [hyy, D.t_mul_t, one_mul]
  obtain ⟨β, hβ, hβc⟩ := D.Bt_conj y hy hyt
  obtain ⟨α, hα, hαc⟩ := D.exists_conj_t_of_mem_A hx hxt
  refine ⟨β⁻¹ * α⁻¹, mul_mem (inv_mem (D.B_le_T₀ hβ)) (inv_mem (D.A_le_T₀ hα)), ?_⟩
  have h1 : α⁻¹ * D.t * α = x * D.t := by
    calc α⁻¹ * D.t * α = α⁻¹ * (α * (x * D.t) * α⁻¹) * α := by rw [hαc]
      _ = x * D.t := by group
  have h2 : β⁻¹ * D.t * β = y * D.t := by
    calc β⁻¹ * D.t * β = β⁻¹ * (β * (y * D.t) * β⁻¹) * β := by rw [hβc]
      _ = y * D.t := by group
  have hxβ : β⁻¹ * x = x * β⁻¹ := (D.A_comm_B x hx _ (inv_mem hβ)).symm
  calc β⁻¹ * α⁻¹ * D.t * (β⁻¹ * α⁻¹)⁻¹ = β⁻¹ * (α⁻¹ * D.t * α) * β := by group
    _ = β⁻¹ * (x * D.t) * β := by rw [h1]
    _ = (β⁻¹ * x) * D.t * β := by group
    _ = x * (β⁻¹ * D.t * β) := by rw [hxβ]; group
    _ = x * (y * D.t) := by rw [h2]
    _ = g := by rw [hg']; group

theorem mem_CBt_or_of_comm_t {x : G} (hx : x ∈ D.T₀) (hxt : x * D.t = D.t * x) :
    x ∈ D.B ⊓ centralizer {D.t} ∨ x * D.a ∈ D.B ⊓ centralizer {D.t} := by
  obtain ⟨y, hy, w, hw, rfl⟩ := D.mem_T₀_iff.1 hx
  have hy' := D.conj_t_A y hy
  have hw' := D.conj_t_B w hw
  have hconj : (D.t * y * D.t⁻¹) * (D.t * w * D.t⁻¹) = y * w := by
    calc (D.t * y * D.t⁻¹) * (D.t * w * D.t⁻¹) = D.t * (y * w) * D.t⁻¹ := by group
      _ = y * w := by rw [← hxt, mul_inv_cancel_right]
  obtain ⟨hyy, hww⟩ := D.eq_of_mul_eq_mul_T₀ hy' hy hw' hw hconj
  have hyt : y * D.t = D.t * y := by
    calc y * D.t = (D.t * y * D.t⁻¹) * D.t := by rw [hyy]
      _ = D.t * y := by group
  have hwt : w * D.t = D.t * w := by
    calc w * D.t = (D.t * w * D.t⁻¹) * D.t := by rw [hww]
      _ = D.t * w := by group
  have hwC : w ∈ D.B ⊓ centralizer {D.t} := ⟨hw, mem_centralizer_singleton_iff.2 hwt⟩
  rcases D.eq_one_or_a_of_comm_t hy hyt with rfl | rfl
  · left
    rwa [one_mul]
  · right
    have e : D.a * w * D.a = w := by
      rw [D.A_comm_B D.a D.a_mem w hw, mul_assoc, D.a_mul_a, mul_one]
    rwa [e]

theorem exists_conj_mul_s {g : G} (hg : g ∈ D.T₀) (hg1 : g ∉ D.T₁) (hg2 : g * g = 1) :
    ∃ a₁ ∈ D.A, a₁ * a₁ = 1 ∧ ∃ u ∈ D.B₀, u * (a₁ * D.s) * u⁻¹ = g := by
  obtain ⟨x, hx, y, hy, rfl⟩ := D.mem_T₀_iff.1 hg
  have hyB : y ∉ D.B₀ ⊔ D.B₁ := fun h => hg1 (mul_mem (D.A_le_T₁ hx) (D.B₀B₁_le_T₁ h))
  have hys : y * D.s ∈ D.B₀ ⊔ D.B₁ := (D.mem_B_iff.1 hy).resolve_left hyB
  obtain ⟨w₀, hw₀, w₁, hw₁, hw⟩ := D.mem_B₀B₁_iff.1 hys
  have hxy : (x * x) * (y * y) = 1 := by
    have hc : y * x = x * y := (D.A_comm_B x hx y hy).symm
    calc (x * x) * (y * y) = x * (x * y) * y := by group
      _ = x * (y * x) * y := by rw [hc]
      _ = x * y * (x * y) := by group
      _ = 1 := hg2
  obtain ⟨hxx, hyy⟩ := D.mul_eq_one_T₀ (mul_mem hx hx) (mul_mem hy hy) hxy
  have hy' : y = w₀ * w₁ * D.s := by
    calc y = y * D.s * D.s := by rw [mul_assoc, D.s_mul_s, mul_one]
      _ = w₀ * w₁ * D.s := by rw [hw]
  have hv₀ : D.s * w₁ * D.s⁻¹ ∈ D.B₀ := D.conj_s_mem_B₀ hw₁
  have hv₁ : D.s * w₀ * D.s⁻¹ ∈ D.B₁ := D.conj_s_mem_B₁ hw₀
  have hc' : (D.s * w₁ * D.s⁻¹) * (w₁ * (D.s * w₀ * D.s⁻¹)) =
      (w₁ * (D.s * w₀ * D.s⁻¹)) * (D.s * w₁ * D.s⁻¹) :=
    D.B₀_comm_B₁ _ hv₀ _ (mul_mem hw₁ hv₁)
  have hprod : (w₀ * (D.s * w₁ * D.s⁻¹)) * (w₁ * (D.s * w₀ * D.s⁻¹)) = 1 := by
    calc (w₀ * (D.s * w₁ * D.s⁻¹)) * (w₁ * (D.s * w₀ * D.s⁻¹))
        = w₀ * ((D.s * w₁ * D.s⁻¹) * (w₁ * (D.s * w₀ * D.s⁻¹))) := by group
      _ = w₀ * ((w₁ * (D.s * w₀ * D.s⁻¹)) * (D.s * w₁ * D.s⁻¹)) := by rw [hc']
      _ = w₀ * w₁ * (D.s * (w₀ * w₁) * D.s⁻¹) := by group
      _ = y * y := by rw [hy', D.s_inv]; group
      _ = 1 := hyy
  obtain ⟨-, h1⟩ := D.mul_eq_one_B₀B₁ (mul_mem hw₀ hv₀) (mul_mem hw₁ hv₁) hprod
  have hw₁' : w₁ = D.s * w₀⁻¹ * D.s⁻¹ := by
    calc w₁ = (D.s * w₀ * D.s⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = D.s * w₀⁻¹ * D.s⁻¹ := by group
  have hxw : w₀ * x = x * w₀ := (D.A_comm_B x hx w₀ (D.B₀_le_B hw₀)).symm
  refine ⟨x, hx, hxx, w₀, hw₀, ?_⟩
  calc w₀ * (x * D.s) * w₀⁻¹ = (w₀ * x) * D.s * w₀⁻¹ := by group
    _ = x * (w₀ * D.s * w₀⁻¹) := by rw [hxw]; group
    _ = x * (w₀ * w₁ * D.s) := by rw [hw₁']; group
    _ = x * y := by rw [hy']

@[expose] def sDiag : D.B₀ →* G :=
  MonoidHom.mk' (fun u => (u : G) * (D.s * u * D.s⁻¹)) (by
    intro u v
    have hc : (v : G) * (D.s * u * D.s⁻¹) = (D.s * u * D.s⁻¹) * v :=
      D.B₀_comm_B₁ v v.2 _ (D.conj_s_mem_B₁ u.2)
    show ((u : G) * v) * (D.s * ((u : G) * v) * D.s⁻¹) =
      ((u : G) * (D.s * u * D.s⁻¹)) * ((v : G) * (D.s * v * D.s⁻¹))
    calc ((u : G) * v) * (D.s * ((u : G) * v) * D.s⁻¹)
        = u * (v * (D.s * u * D.s⁻¹)) * (D.s * v * D.s⁻¹) := by group
      _ = u * ((D.s * u * D.s⁻¹) * v) * (D.s * v * D.s⁻¹) := by rw [hc]
      _ = ((u : G) * (D.s * u * D.s⁻¹)) * ((v : G) * (D.s * v * D.s⁻¹)) := by group)

theorem sDiag_apply (u : D.B₀) : D.sDiag u = u * (D.s * u * D.s⁻¹) := rfl

theorem sDiag_injective : Function.Injective D.sDiag := by
  rw [injective_iff_map_eq_one]
  intro u hu
  rw [sDiag_apply] at hu
  exact Subtype.ext (D.mul_eq_one_B₀B₁ u.2 (D.conj_s_mem_B₁ u.2) hu).1

theorem sDiag_comm_s (u : D.B₀) : D.sDiag u * D.s = D.s * D.sDiag u := by
  rw [sDiag_apply]
  have hc : (u : G) * (D.s * u * D.s⁻¹) = (D.s * u * D.s⁻¹) * u :=
    D.B₀_comm_B₁ u u.2 _ (D.conj_s_mem_B₁ u.2)
  calc (u : G) * (D.s * u * D.s⁻¹) * D.s = (D.s * u * D.s⁻¹) * u * D.s := by rw [hc]
    _ = D.s * (u * (D.s * u * D.s⁻¹)) := by rw [D.s_inv]; group

theorem sDiag_range : D.sDiag.range = (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s} := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 (D.sDiag_comm_s u)⟩
    rw [sDiag_apply]
    exact mul_mem (mem_sup_left u.2) (mem_sup_right (D.conj_s_mem_B₁ u.2))
  · intro w hw'
    obtain ⟨hw, hws⟩ := mem_inf.1 hw'
    rw [mem_centralizer_singleton_iff] at hws
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
    have hv₀ := D.conj_s_mem_B₀ hw₁
    have hv₁ := D.conj_s_mem_B₁ hw₀
    have hconj : (D.s * w₁ * D.s⁻¹) * (D.s * w₀ * D.s⁻¹) = w₀ * w₁ := by
      have hc : (D.s * w₁ * D.s⁻¹) * (D.s * w₀ * D.s⁻¹) =
          (D.s * w₀ * D.s⁻¹) * (D.s * w₁ * D.s⁻¹) := D.B₀_comm_B₁ _ hv₀ _ hv₁
      rw [hc]
      calc (D.s * w₀ * D.s⁻¹) * (D.s * w₁ * D.s⁻¹) = D.s * (w₀ * w₁) * D.s⁻¹ := by group
        _ = w₀ * w₁ := by rw [← hws, mul_inv_cancel_right]
    obtain ⟨-, h1⟩ := D.eq_of_mul_eq_mul_B₀B₁ hv₀ hw₀ hv₁ hw₁ hconj
    refine ⟨⟨w₀, hw₀⟩, ?_⟩
    rw [sDiag_apply]
    show w₀ * (D.s * w₀ * D.s⁻¹) = w₀ * w₁
    rw [h1]

theorem mem_A_sup_of_comm {x a₁ : G} (hx : x ∈ D.T₁) (ha₁ : a₁ ∈ D.A)
    (hc : x * (a₁ * D.s) = a₁ * D.s * x) :
    x ∈ D.A ⊔ ((D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s}) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx
  have hwB := D.B₀B₁_le_B hw
  have h1 : w * a₁ = a₁ * w := (D.A_comm_B a₁ ha₁ w hwB).symm
  have h2 : D.s * y = y * D.s := (D.A_comm_B y hy D.s D.s_mem_B).symm
  have h : (y * a₁) * (w * D.s) = (a₁ * y) * (D.s * w) := by
    calc (y * a₁) * (w * D.s) = y * (a₁ * w) * D.s := by group
      _ = y * (w * a₁) * D.s := by rw [h1]
      _ = y * w * (a₁ * D.s) := by group
      _ = a₁ * D.s * (y * w) := hc
      _ = a₁ * (D.s * y) * w := by group
      _ = a₁ * (y * D.s) * w := by rw [h2]
      _ = (a₁ * y) * (D.s * w) := by group
  obtain ⟨-, hws⟩ := D.eq_of_mul_eq_mul_T₀ (mul_mem hy ha₁) (mul_mem ha₁ hy)
    (mul_mem hwB D.s_mem_B) (mul_mem D.s_mem_B hwB) h
  exact mul_mem (mem_sup_left hy) (mem_sup_right ⟨hw, mem_centralizer_singleton_iff.2 hws⟩)

end FooteCore

end CFSG.CGT.Foote81L6
