module

public import CFSG.CGT.PushingUpLit.T2KR.Fus613N0

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P613

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G] {L M : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_closure_pair {r u : G} (hr2 : r * r = 1) (hu2 : u * u = 1) (hru : r * u = u * r)
    {y : G} (hy : y ∈ Subgroup.closure ({r, u} : Set G)) :
    y = 1 ∨ y = r ∨ y = u ∨ y = r * u := by
  have e1 : u * r = r * u := hru.symm
  have e2 : r * u * r = u := by
    calc r * u * r = r * (u * r) := by group
      _ = r * (r * u) := by rw [e1]
      _ = (r * r) * u := by group
      _ = u := by rw [hr2, one_mul]
  have e3 : r * u * u = r := by
    calc r * u * u = r * (u * u) := by group
      _ = r := by rw [hu2, mul_one]
  have e4 : r * (r * u) = u := by
    calc r * (r * u) = (r * r) * u := by group
      _ = u := by rw [hr2, one_mul]
  have e5 : u * (r * u) = r := by
    calc u * (r * u) = (u * r) * u := by group
      _ = (r * u) * u := by rw [e1]
      _ = r := e3
  have e6 : r * u * (r * u) = 1 := by
    calc r * u * (r * u) = (r * u * r) * u := by group
      _ = u * u := by rw [e2]
      _ = 1 := hu2
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul y y' _ _ hy hy' =>
    rcases hy with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
      simp [hr2, hu2, e1, e2, e3, e4, e5, e6]
  | inv y _ hy =>
    rcases hy with rfl | rfl | rfl | rfl
    · simp
    · right; left; exact inv_eq_of_mul_eq_one_right hr2
    · right; right; left; exact inv_eq_of_mul_eq_one_right hu2
    · right; right; right; exact inv_eq_of_mul_eq_one_right e6

section Delta

variable {H : MData G L M n} {T' : Subgroup G} {x r b : G} {e₁ e₂ : Fin 2 → Fq n} {ω : Fq n}
  (c : Cfg H T' x r b) (bs : Basis H r b e₁ e₂ ω)

include c bs in
theorem Cfg.not_comm_x {u : G} (huL : u ∈ L) (hu2 : u * u = 1) (hru : r * u = u * r)
    (hutv : IsTv H e₁ e₂ u ω) : x * u ≠ u * x := by
  intro hxu
  have hω := bs.ω_eq
  have h2 : (2 : Fq n) = 0 := two_eq_zero
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  have hrutv : IsTv H e₁ e₂ (r * u) (1 + ω) := hrtv.mul hutv c.r_L (H.le huL)
  have hω0 : ω ≠ 0 := root_ne_zero hω
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω
    have : (1 : Fq n) = 0 := by linear_combination hω - h2
    exact one_ne_zero this
  have h1ω : 1 + ω ≠ 0 := by
    intro h
    apply hω1
    linear_combination h - h2
  have hrne : r ≠ 1 := by
    intro h
    rw [h] at hrtv
    exact one_ne_zero (IsTv.unique bs.e₁_ne hrtv (IsTv.one e₁ e₂))
  have hune : u ≠ 1 := by
    intro h
    rw [h] at hutv
    exact hω0 (IsTv.unique bs.e₁_ne hutv (IsTv.one e₁ e₂))
  have hrue : r ≠ u := by
    intro h
    rw [h] at hrtv
    exact hω1 (IsTv.unique bs.e₁_ne hrtv hutv).symm
  set X := Subgroup.closure ({r, u} : Set G) with hX
  have hmem : ∀ {y : G}, y ∈ X → y = 1 ∨ y = r ∨ y = u ∨ y = r * u :=
    fun hy => mem_closure_pair c.r_sq hu2 hru hy
  have hrX : r ∈ X := Subgroup.subset_closure (by simp)
  have huX : u ∈ X := Subgroup.subset_closure (by simp)
  have hXLQ : X ≤ L ⊔ QM L M := by
    rw [hX, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact (le_sup_left : L ≤ L ⊔ QM L M) c.r_L
    · exact (le_sup_left : L ≤ L ⊔ QM L M) huL
  have hrusq : r * u * (r * u) = 1 := by
    calc r * u * (r * u) = r * (u * r) * u := by group
      _ = r * (r * u) * u := by rw [← hru]
      _ = (r * r) * (u * u) := by group
      _ = 1 := by rw [c.r_sq, hu2, one_mul]
  have hX2 : ∀ y ∈ X, y * y = 1 := by
    intro y hy
    rcases hmem hy with rfl | rfl | rfl | rfl
    · simp
    · exact c.r_sq
    · exact hu2
    · exact hrusq
  have hXQ : X ⊓ QM L M = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyX, hyQ⟩
    rcases hmem hyX with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hyQ c.r_Q
    · exfalso
      have hV := c.QL ⟨hyQ, huL⟩
      have hs : IsTv H e₁ e₂ y 0 :=
        ⟨MData.act_blockU H hV e₁, by rw [MData.act_blockU H hV e₂, zero_smul, add_zero]⟩
      exact hω0 (IsTv.unique bs.e₁_ne hutv hs)
    · exfalso
      have hV := c.QL ⟨hyQ, L.mul_mem c.r_L huL⟩
      have hs : IsTv H e₁ e₂ (r * u) 0 :=
        ⟨MData.act_blockU H hV e₁, by rw [MData.act_blockU H hV e₂, zero_smul, add_zero]⟩
      exact h1ω (IsTv.unique bs.e₁_ne hrutv hs)
  have hcard : 3 ≤ Nat.card X := by
    let f : Fin 3 → X := ![⟨1, X.one_mem⟩, ⟨r, hrX⟩, ⟨u, huX⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
      · exact hrne.symm hij
      · exact hune.symm hij
      · exact hrne hij
      · exact hrue hij
      · exact hune hij
      · exact hrue.symm hij
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hrel : 3 ≤ (X ⊓ QM L M).relIndex X := by
    rw [hXQ, Subgroup.relIndex_bot_left]
    exact hcard
  have hcent := (H.centralizer_QM_eq_of_three_le X hXLQ hX2 hrel).1
  have hxC : x ∈ QM L M ⊓ Subgroup.centralizer (X : Set G) := by
    refine ⟨c.x_Q, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rcases hmem hy with rfl | rfl | rfl | rfl
    · simp
    · exact c.xr.symm
    · exact hxu.symm
    · calc r * u * x = r * (u * x) := by group
        _ = r * (x * u) := by rw [← hxu]
        _ = (r * x) * u := by group
        _ = (x * r) * u := by rw [← c.xr]
        _ = x * (r * u) := by group
  rw [hcent] at hxC
  exact c.x_V hxC.1

include c bs in
theorem Cfg.u_conj_x {u : G} (huL : u ∈ L) (hu2 : u * u = 1) (hru : r * u = u * r)
    (hutv : IsTv H e₁ e₂ u ω) (hbu : b * u * b⁻¹ = r * u) :
    u * x * u⁻¹ = x * H.vec e₁ := by
  have hrM : r ∈ M := H.le c.r_L
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right c.b_sq
  have hrtv : IsTv H e₁ e₂ r 1 := ⟨bs.r1, by rw [one_smul]; exact bs.r2⟩
  have hu_LQ : u ∈ L ⊔ QM L M := (le_sup_left : L ≤ L ⊔ QM L M) huL
  set δ := x⁻¹ * (u * x * u⁻¹) with hδ
  have hδV : δ ∈ blockU L := H.commutator_mem_V hu_LQ c.x_Q
  have hδ' : u * x * u⁻¹ = x * δ := by rw [hδ]; group
  have hrx : r * x * r⁻¹ = x := by
    calc r * x * r⁻¹ = x * r * r⁻¹ := by rw [← c.xr]
      _ = x := by group
  have hbx : b * x * b⁻¹ = x := by
    calc b * x * b⁻¹ = x * b * b⁻¹ := by rw [← c.xb]
      _ = x := by group
  have hru' : r * u * r⁻¹ = u := by
    calc r * u * r⁻¹ = u * r * r⁻¹ := by rw [hru]
      _ = u := by group
  have e2 : r * (u * x * u⁻¹) * r⁻¹ = u * x * u⁻¹ := by
    calc r * (u * x * u⁻¹) * r⁻¹ = (r * u * r⁻¹) * (r * x * r⁻¹) * (r * u * r⁻¹)⁻¹ := by group
      _ = u * x * u⁻¹ := by rw [hru', hrx]
  have e3 : b * (u * x * u⁻¹) * b⁻¹ = u * x * u⁻¹ := by
    calc b * (u * x * u⁻¹) * b⁻¹ = (b * u * b⁻¹) * (b * x * b⁻¹) * (b * u * b⁻¹)⁻¹ := by group
      _ = (r * u) * x * (r * u)⁻¹ := by rw [hbu, hbx]
      _ = r * (u * x * u⁻¹) * r⁻¹ := by group
      _ = u * x * u⁻¹ := e2
  have hr_δ : r * δ * r⁻¹ = δ := by
    have e1 : r * x⁻¹ * r⁻¹ = x⁻¹ := by
      calc r * x⁻¹ * r⁻¹ = (r * x * r⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hrx]
    calc r * δ * r⁻¹ = (r * x⁻¹ * r⁻¹) * (r * (u * x * u⁻¹) * r⁻¹) := by rw [hδ]; group
      _ = δ := by rw [e1, e2]
  have hb_δ : b * δ * b⁻¹ = δ := by
    have e1 : b * x⁻¹ * b⁻¹ = x⁻¹ := by
      calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hbx]
    calc b * δ * b⁻¹ = (b * x⁻¹ * b⁻¹) * (b * (u * x * u⁻¹) * b⁻¹) := by rw [hδ]; group
      _ = δ := by rw [e1, e3]
  obtain ⟨α, β, hw⟩ := bs.span (H.D.ψe δ)
  have hδvec : δ = H.vec (α • e₁ + β • e₂) := by rw [← hw, H.vec_ψe hδV]
  have hrw : H.act r (α • e₁ + β • e₂) = α • e₁ + β • e₂ := by
    have h1 := H.conj_vec hrM (α • e₁ + β • e₂)
    rw [hδvec] at hr_δ
    exact H.vec_injective (h1.symm.trans hr_δ)
  have hβ0 : β = 0 := by
    rw [hrtv.act_coord c.r_L] at hrw
    have : β • e₁ = 0 := by linear_combination (norm := module) hrw
    exact (smul_eq_zero.1 this).resolve_right bs.e₁_ne
  have hδvec' : δ = H.vec (α • e₁) := by rw [hδvec, hβ0, zero_smul, add_zero]
  have hα2 : α ^ 2 = α := by
    have h1 := H.conj_vec c.b_M (α • e₁)
    rw [hδvec'] at hb_δ
    have := H.vec_injective (h1.symm.trans hb_δ)
    rw [bs.b_semi, bs.b1] at this
    have h4 : (α ^ 2 - α) • e₁ = 0 := by
      rw [sub_smul, this, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right bs.e₁_ne)
  have hα0 : α ≠ 0 := by
    intro h
    apply c.not_comm_x bs huL hu2 hru hutv
    have hδ1 : δ = 1 := by rw [hδvec', h, zero_smul, H.vec_zero]
    have h1 : u * x * u⁻¹ = x := by rw [hδ', hδ1, mul_one]
    calc x * u = (u * x * u⁻¹) * u := by rw [h1]
      _ = u * x := by group
  have hα1 : α = 1 := by
    have : α * (α - 1) = 0 := by linear_combination hα2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hα0
    · exact sub_eq_zero.1 h
  rw [hδ', hδvec', hα1, one_smul]

end Delta

end CFSG.CGT.PushingUpLit.T2KR.P613
