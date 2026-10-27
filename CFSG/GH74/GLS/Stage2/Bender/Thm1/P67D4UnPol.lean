module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnTits

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

namespace RankTwoSystem

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

structure IsOpposition (τ : X ≃* X) : Prop where
  mem_torus : ∀ h ∈ D.B ⊓ D.N, τ h ∈ D.B ⊓ D.N
  mem_root : ∀ k : ℤ, IsRoot 3 k → ∀ x ∈ D.root k, τ x ∈ D.root (-k)
  lift₁ : ∃ m : D.N, (m : D.Weyl) = D.w₁ ∧ (m : X)⁻¹ * τ (m : X) ∈ D.B ⊓ D.N
  lift₂ : ∃ m : D.N, (m : D.Weyl) = D.w₂ ∧ (m : X)⁻¹ * τ (m : X) ∈ D.B ⊓ D.N

section Aux

private theorem mem_P₁_iff_dc {x : X} : x ∈ D.P₁ ↔ x ∈ D.B ∨ x ∈ dc D.B D.N D.w₁ :=
  mem_parabolic_single_iff D.isTits (D.rank2.gen_mem true)

private theorem mem_P₂_iff_dc {x : X} : x ∈ D.P₂ ↔ x ∈ D.B ∨ x ∈ dc D.B D.N D.w₂ :=
  mem_parabolic_single_iff D.isTits (D.rank2.gen_mem false)

private theorem braid_w : D.w₁ * D.w₂ * D.w₁ = D.w₂ * D.w₁ * D.w₂ := by
  have h := D.rank2.dih.altWord_eq
  simpa only [altWord, one_mul] using h

private theorem w₀_eq_mul : D.w₀ = D.w₁ * D.w₂ * D.w₁ := by
  simp only [w₀, altWord, one_mul]

private theorem w₀_mul_self_eq_one : D.w₀ * D.w₀ = 1 := by
  have ha := D.w₁_mul_self
  have hb := D.w₂_mul_self
  rw [w₀_eq_mul]
  calc D.w₁ * D.w₂ * D.w₁ * (D.w₁ * D.w₂ * D.w₁)
      = D.w₁ * (D.w₂ * (D.w₁ * D.w₁) * D.w₂) * D.w₁ := by simp only [mul_assoc]
    _ = 1 := by rw [ha, mul_one, hb, mul_one, ha]

private theorem w₀_inv_eq : D.w₀⁻¹ = D.w₀ := inv_eq_of_mul_eq_one_right D.w₀_mul_self_eq_one

private theorem w₀_mul_w₁_mul_w₀ : D.w₀ * D.w₁ * D.w₀ = D.w₂ := by
  have ha := D.w₁_mul_self
  have hb := D.w₂_mul_self
  have hbr := D.braid_w
  calc D.w₀ * D.w₁ * D.w₀ = D.w₁ * D.w₂ * D.w₁ * D.w₁ * (D.w₁ * D.w₂ * D.w₁) := by
        rw [w₀_eq_mul]
    _ = D.w₁ * D.w₂ * (D.w₁ * D.w₁) * D.w₁ * D.w₂ * D.w₁ := by simp only [mul_assoc]
    _ = D.w₁ * D.w₂ * D.w₁ * D.w₂ * D.w₁ := by rw [ha, mul_one]
    _ = D.w₂ * D.w₁ * D.w₂ * D.w₂ * D.w₁ := by rw [hbr]
    _ = D.w₂ := by
        rw [mul_assoc (D.w₂ * D.w₁) D.w₂ D.w₂, hb, mul_one, mul_assoc, ha, mul_one]

private theorem w₀_mul_w₂_mul_w₀ : D.w₀ * D.w₂ * D.w₀ = D.w₁ := by
  have ha := D.w₁_mul_self
  have hb := D.w₂_mul_self
  have hbr := D.braid_w
  have h0 : D.w₀ = D.w₂ * D.w₁ * D.w₂ := by rw [w₀_eq_mul, hbr]
  calc D.w₀ * D.w₂ * D.w₀ = D.w₂ * D.w₁ * D.w₂ * D.w₂ * (D.w₂ * D.w₁ * D.w₂) := by
        rw [← h0]
    _ = D.w₂ * D.w₁ * (D.w₂ * D.w₂) * D.w₂ * D.w₁ * D.w₂ := by simp only [mul_assoc]
    _ = D.w₂ * D.w₁ * D.w₂ * D.w₁ * D.w₂ := by rw [hb, mul_one]
    _ = D.w₁ * D.w₂ * D.w₁ * D.w₁ * D.w₂ := by rw [← hbr]
    _ = D.w₁ := by
        rw [mul_assoc (D.w₁ * D.w₂) D.w₁ D.w₁, ha, mul_one, mul_assoc, hb, mul_one]

private theorem w₂_mul_w₁_mul_w₂ : D.w₂ * D.w₁ * D.w₂ = D.w₀ := by
  rw [w₀_eq_mul, D.braid_w]

private def oppConj (τ : X ≃* X) (w : X) : X ≃* X := τ.trans (MulAut.conj w⁻¹)

private theorem oppConj_apply (τ : X ≃* X) (w x : X) : oppConj τ w x = w⁻¹ * τ x * w := by
  simp [oppConj]

variable {D}

private theorem mk_inv_w₀ {w : D.N} (hw : (w : D.Weyl) = D.w₀) :
    ((w⁻¹ : D.N) : D.Weyl) = D.w₀ := by
  rw [QuotientGroup.mk_inv, hw, D.w₀_inv_eq]

private theorem oppConj_root {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {k q : ℤ} (hk : IsRoot 3 k) (hq : Rt 3 q = -k) {x : X}
    (hx : x ∈ D.root k) : oppConj τ (w : X) x ∈ D.root (Rt 3 (tauA 3 3 q)) := by
  have h1 : τ x ∈ D.root (Rt 3 q) := by
    rw [hq]
    exact hτ.mem_root k hk x hx
  have h2 := actsPos_altWord₁ (D := D) 3 (w⁻¹) (mk_inv_w₀ hw) q _ h1
  rw [oppConj_apply]
  simpa using h2

private theorem oppConj_root₁ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 1) :
    oppConj τ (w : X) x ∈ D.root 3 := by
  have h := oppConj_root hτ hw (k := 1) (q := 3) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 3) = 3 by decide] at h

private theorem oppConj_root₂ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 2) :
    oppConj τ (w : X) x ∈ D.root 2 := by
  have h := oppConj_root hτ hw (k := 2) (q := 4) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 4) = 2 by decide] at h

private theorem oppConj_root₃ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.root 3) :
    oppConj τ (w : X) x ∈ D.root 1 := by
  have h := oppConj_root hτ hw (k := 3) (q := 5) ⟨by norm_num, by norm_num⟩ (by decide) hx
  rwa [show Rt 3 (tauA 3 3 5) = 1 by decide] at h

private theorem intList_one_three : intList 1 ((3 : ℕ) : ℤ) = [1, 2, 3] := by decide

private theorem oppConj_mem_U {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {u : X} (hu : u ∈ D.U) : oppConj τ (w : X) u ∈ D.U := by
  have hu' : u ∈ chainProd D.root (intList 1 ((3 : ℕ) : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hu
  rw [intList_one_three, chainProd_cons, chainProd_cons, chainProd_singleton] at hu'
  obtain ⟨x₁, hx₁, y, hy, rfl⟩ := Set.mem_mul.1 hu'
  obtain ⟨x₂, hx₂, x₃, hx₃, rfl⟩ := Set.mem_mul.1 hy
  have hmem : oppConj τ (w : X) x₁ * (oppConj τ (w : X) x₂ * oppConj τ (w : X) x₃) ∈
      chainProd D.root [3, 2, 1] := by
    rw [chainProd_cons, chainProd_cons, chainProd_singleton]
    exact Set.mem_mul.2 ⟨_, oppConj_root₁ hτ hw hx₁, _,
      Set.mem_mul.2 ⟨_, oppConj_root₂ hτ hw hx₂, _, oppConj_root₃ hτ hw hx₃, rfl⟩, rfl⟩
  have hrev := chainProd_intList_reverse D (a := 1) (b := 3) (by norm_num) (by norm_num)
  have hl : intList 1 3 = [1, 2, 3] := by decide
  rw [hl] at hrev
  have hmem' : oppConj τ (w : X) x₁ * (oppConj τ (w : X) x₂ * oppConj τ (w : X) x₃) ∈
      chainProd D.root [1, 2, 3] := by
    rw [hrev]
    exact hmem
  have hU : (D.U : Set X) = chainProd D.root [1, 2, 3] := by
    rw [D.roots.carrier_eq, intList_one_three]
  rw [← SetLike.mem_coe, hU, map_mul, map_mul]
  exact hmem'

private theorem oppConj_mem_torus {τ : X ≃* X} (hτ : D.IsOpposition τ) (w : D.N) {h : X}
    (hh : h ∈ D.B ⊓ D.N) : oppConj τ (w : X) h ∈ D.B ⊓ D.N := by
  have := D.conj_cartan_mem (w⁻¹) (hτ.mem_torus h hh)
  rw [oppConj_apply]
  simpa using this

private theorem oppConj_mem_B {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {b : X} (hb : b ∈ D.B) : oppConj τ (w : X) b ∈ D.B := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, u, hu, rfl⟩ := Set.mem_mul.1 hb'
  rw [map_mul]
  exact D.B.mul_mem (oppConj_mem_torus hτ w hh).1 (D.U_le_B (oppConj_mem_U hτ hw hu))

private theorem oppConj_mem_dc {τ : X ≃* X} (w : D.N) {m : D.N}
    (hm : (m : X)⁻¹ * τ (m : X) ∈ D.B ⊓ D.N) (hw : (w : D.Weyl) = D.w₀) :
    oppConj τ (w : X) (m : X) ∈ dc D.B D.N (D.w₀ * (m : D.Weyl) * D.w₀) := by
  have hn : (((w⁻¹ * m * w : D.N)) : D.Weyl) = D.w₀ * (m : D.Weyl) * D.w₀ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, mk_inv_w₀ hw, hw]
  have h1 := coe_mem_dc (B := D.B) (N := D.N) (w⁻¹ * m * w)
  rw [hn] at h1
  have h2 := D.conj_cartan_mem (w⁻¹) hm
  have h3 := mul_mem_dc h1 D.B.one_mem h2.1
  have e : (1 : X) * ((w⁻¹ * m * w : D.N) : X) *
      (((w⁻¹ : D.N) : X) * ((m : X)⁻¹ * τ (m : X)) * ((w⁻¹ : D.N) : X)⁻¹) =
      oppConj τ (w : X) (m : X) := by
    rw [oppConj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rwa [e] at h3

private theorem H_conj_mem_U {h : X} (hh : h ∈ D.B ⊓ D.N) {u : X} (hu : u ∈ D.U) :
    h * u * h⁻¹ ∈ D.U := by
  have hu' : u ∈ chainProd D.root (intList 1 ((3 : ℕ) : ℤ)) := by
    rw [← D.roots.carrier_eq]
    exact hu
  refine chainProd_conj_mem D.root D.U h _ (fun k hk y hy => ?_) u hu'
  obtain ⟨hk1, hk2⟩ := mem_intList_iff.1 hk
  exact D.root_le_U hk1 hk2 (D.roots.invariant k ⟨by omega, by omega⟩ h hh y hy)

private theorem B_conj_mem_U {b : X} (hb : b ∈ D.B) {u : X} (hu : u ∈ D.U) :
    b * u * b⁻¹ ∈ D.U := by
  have hb' : b ∈ ((D.B ⊓ D.N : Subgroup X) : Set X) * (D.U : Set X) := D.isSplit.2 ▸ hb
  obtain ⟨h, hh, v, hv, rfl⟩ := Set.mem_mul.1 hb'
  have e : h * v * u * (h * v)⁻¹ = h * (v * u * v⁻¹) * h⁻¹ := by group
  rw [e]
  exact H_conj_mem_U hh (D.U.mul_mem (D.U.mul_mem hv hu) (D.U.inv_mem hv))

private theorem oppConj_mem_P₂ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.P₁) : oppConj τ (w : X) x ∈ D.P₂ := by
  rcases (D.mem_P₁_iff_dc).1 hx with hB | hd
  · exact (D.mem_P₂_iff_dc).2 (Or.inl (oppConj_mem_B hτ hw hB))
  · obtain ⟨m, hm, hmτ⟩ := hτ.lift₁
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm).1 hd
    have h1 := oppConj_mem_dc w hmτ hw
    rw [hm, D.w₀_mul_w₁_mul_w₀] at h1
    refine (D.mem_P₂_iff_dc).2 (Or.inr ?_)
    rw [map_mul, map_mul]
    exact mul_mem_dc h1 (oppConj_mem_B hτ hw hb) (oppConj_mem_B hτ hw hb')

private theorem oppConj_mem_P₁ {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {x : X} (hx : x ∈ D.P₂) : oppConj τ (w : X) x ∈ D.P₁ := by
  rcases (D.mem_P₂_iff_dc).1 hx with hB | hd
  · exact (D.mem_P₁_iff_dc).2 (Or.inl (oppConj_mem_B hτ hw hB))
  · obtain ⟨m, hm, hmτ⟩ := hτ.lift₂
    obtain ⟨b, hb, b', hb', rfl⟩ := (mem_dc_of_lift hm).1 hd
    have h1 := oppConj_mem_dc w hmτ hw
    rw [hm, D.w₀_mul_w₂_mul_w₀] at h1
    refine (D.mem_P₁_iff_dc).2 (Or.inr ?_)
    rw [map_mul, map_mul]
    exact mul_mem_dc h1 (oppConj_mem_B hτ hw hb) (oppConj_mem_B hτ hw hb')

private theorem isPolarity_of_mk_eq {τ : X ≃* X} (hτ : D.IsOpposition τ) {w : D.N}
    (hw : (w : D.Weyl) = D.w₀) {g : X} (hg : g * (w : X) ∈ D.B) :
    D.IsPolarity (τ.trans (MulAut.conj g)) := by
  have key : ∀ x, (τ.trans (MulAut.conj g)) x =
      (g * (w : X)) * oppConj τ (w : X) x * (g * (w : X))⁻¹ := by
    intro x
    rw [oppConj_apply]
    simp only [MulEquiv.trans_apply, MulAut.conj_apply]
    group
  have hP₁ : D.B ≤ D.P₁ := fun b hb => (D.mem_P₁_iff_dc).2 (Or.inl hb)
  have hP₂ : D.B ≤ D.P₂ := fun b hb => (D.mem_P₂_iff_dc).2 (Or.inl hb)
  refine ⟨fun b hb => ?_, fun u hu => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [key]
    exact D.B.mul_mem (D.B.mul_mem hg (oppConj_mem_B hτ hw hb)) (D.B.inv_mem hg)
  · rw [key]
    exact B_conj_mem_U hg (oppConj_mem_U hτ hw hu)
  · rw [key]
    exact D.P₂.mul_mem (D.P₂.mul_mem (hP₂ hg) (oppConj_mem_P₂ hτ hw hx))
      (D.P₂.inv_mem (hP₂ hg))
  · rw [key]
    exact D.P₁.mul_mem (D.P₁.mul_mem (hP₁ hg) (oppConj_mem_P₁ hτ hw hx))
      (D.P₁.inv_mem (hP₁ hg))

end Aux

variable {D}

theorem IsOpposition.isPolarity {τ : X ≃* X} (hτ : D.IsOpposition τ) {g : X}
    (hg : g * ((D.lift D.w₀ : D.N) : X) ∈ D.B) : D.IsPolarity (τ.trans (MulAut.conj g)) :=
  isPolarity_of_mk_eq hτ (D.lift_mk D.w₀) hg

theorem exists_adapted_mid {m₀ : D.N} (hm₀ : (m₀ : D.Weyl) = D.w₀) {a h : X}
    (ha : a ∈ D.root 2) (hh : h ∈ D.B ⊓ D.N) :
    (a * h * (m₀ : X)) * ((D.lift D.w₀ : D.N) : X) ∈ D.B := by
  have h1 : ((m₀ * D.lift D.w₀ : D.N) : D.Weyl) = 1 := by
    rw [QuotientGroup.mk_mul, hm₀, D.lift_mk D.w₀]
    exact D.w₀_mul_self_eq_one
  have h2 : ((m₀ * D.lift D.w₀ : D.N) : X) ∈ D.B := mk_eq_one_iff.1 h1
  have h3 : a * h * (m₀ : X) * ((D.lift D.w₀ : D.N) : X) =
      a * h * ((m₀ * D.lift D.w₀ : D.N) : X) := by
    simp only [Subgroup.coe_mul, mul_assoc]
  rw [h3]
  exact D.B.mul_mem (D.B.mul_mem (D.U_le_B (D.root_le_U (by norm_num) (by norm_num) ha)) hh.1) h2

end RankTwoSystem

end CFSG.GH74.BNPair
