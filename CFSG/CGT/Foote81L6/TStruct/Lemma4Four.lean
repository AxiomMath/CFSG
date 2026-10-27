module

public import CFSG.CGT.Foote81L6.TStruct.Classes

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct DihedralGroup

private theorem exists_conj_le_sylow_of_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (T : Sylow p G) {H P : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hPH : P ≤ H)
    (hP : IsPGroup p P) : ∃ k ∈ H, P.map (MulAut.conj k).toMonoidHom ≤ T := by
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H S (T.subtype hTH)
  refine ⟨x, x.2, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzS : (⟨z, hPH hz⟩ : H) ∈ (S : Subgroup H) :=
    hS (show (⟨z, hPH hz⟩ : H) ∈ P.comap H.subtype from hz)
  have hmem : MulAut.conj x • (⟨z, hPH hz⟩ : H) ∈ ((x • S : Sylow p H) : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
    exact smul_mem_pointwise_smul _ _ _ hzS
  rw [hx, Sylow.coe_subtype, mem_subgroupOf, MulAut.smul_def, MulAut.conj_apply] at hmem
  simpa using hmem

private theorem comm_r_sr {N : ℕ} (j : ZMod N) :
    (r j * sr 0 * (r j)⁻¹ * (sr 0)⁻¹ : DihedralGroup N) = r (j + j) := by
  simp only [r_mul_sr, inv_r, sr_mul_r, inv_sr, sr_mul_sr]
  congr 1
  ring

namespace FooteCore

section Local

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem eq_b_of_isConj_b_of_lemma3 (hL3 : ∀ x ∈ D.Zab, ∀ y ∈ D.Zab, IsConj x y → x = y ∨
      (x = D.b₀ ∧ y = D.b₁) ∨ (x = D.b₁ ∧ y = D.b₀) ∨ (x = D.a * D.b₀ ∧ y = D.a * D.b₁) ∨
      (x = D.a * D.b₁ ∧ y = D.a * D.b₀)) :
    ∀ y ∈ D.Zab, IsConj D.b y → y = D.b := by
  intro y hy h
  have hb₀ : D.b₀ ∈ D.Zab := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb₁ : D.b₁ ∈ D.Zab :=
    subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hB : ∀ {x : G}, x ∈ D.B → D.a = x → False := fun hx h =>
    D.a_ne_one (mem_bot.1 (D.A_inf_B ▸ mem_inf.2 ⟨D.a_mem, by rw [h]; exact hx⟩))
  rcases hL3 _ (mul_mem hb₀ hb₁) _ hy h with h1 | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact h1.symm
  · exact absurd (mul_eq_left.1 h1) D.b₁_ne_one
  · exact absurd (mul_eq_right.1 h1) D.b₀_ne_one
  · exact (hB D.b₁_mem_B (mul_left_cancel
      (h1.trans (D.A_comm_B D.a D.a_mem D.b₀ D.b₀_mem_B))).symm).elim
  · exact (hB D.b₀_mem_B (mul_right_cancel h1.symm)).elim

theorem mul_self_of_mem_A_two (hm : m = 2) {x : G} (hx : x ∈ D.A) : x * x = 1 :=
  (show IsFourIn D.A D.A from D.repU_eq_A hm ▸ D.isFourIn_repU).2.1 x hx

theorem comm_T₀_of_mem_A (hm : m = 2) {α x : G} (hα : α ∈ D.A) (hx : x ∈ D.T₀) :
    x * α = α * x :=
  comm_of_mem_sup (fun y hy => comm_of_mul_self (fun z hz => D.mul_self_of_mem_A_two hm hz) hy hα)
    (fun y hy => (D.A_comm_B α hα y hy).symm) hx

theorem comm_mem_B₀B₁_of_mem_B {β β' : G} (hβ : β ∈ D.B) (hβ' : β' ∈ D.B) :
    β * β' * β⁻¹ * β'⁻¹ ∈ D.B₀ ⊔ D.B₁ := by
  haveI : Finite D.B := Nat.finite_of_card_ne_zero (by rw [D.card_B]; positivity)
  have hcard : Nat.card D.B = 2 * Nat.card ↥(D.B₀ ⊔ D.B₁) := by
    rw [D.card_B, D.card_B₀B₁, pow_succ, mul_comm]
  have hT : β ∈ T := D.B_le_T hβ
  by_cases h : β' ∈ D.B₀ ⊔ D.B₁
  · exact mul_mem (D.conj_mem_B₀B₁ hT h) (inv_mem h)
  · have h1 : β * β' * β⁻¹ ∉ D.B₀ ⊔ D.B₁ := fun h1 => h (by
      have := D.conj_mem_B₀B₁ (inv_mem hT) h1
      rwa [show β⁻¹ * (β * β' * β⁻¹) * β⁻¹⁻¹ = β' by group] at this)
    exact mul_inv_mem_of_card_eq_two_mul D.B₀B₁_le_B hcard
      (mul_mem (mul_mem hβ hβ') (inv_mem hβ)) hβ' h1 h

theorem comm_mem_B₀B₁ (hm : m = 2) {p q : G} (hp : p ∈ D.T₀) (hq : q ∈ D.T₀) :
    p * q * p⁻¹ * q⁻¹ ∈ D.B₀ ⊔ D.B₁ := by
  obtain ⟨α, hα, β, hβ, rfl⟩ := D.mem_T₀_iff.1 hp
  obtain ⟨α', hα', β', hβ', rfl⟩ := D.mem_T₀_iff.1 hq
  have hβT : β ∈ D.T₀ := D.B_le_T₀ hβ
  have hX : β * (α' * β') * β⁻¹ ∈ D.T₀ := mul_mem (mul_mem hβT hq) (inv_mem hβT)
  have hY : β * β' * β⁻¹ * β'⁻¹ ∈ D.T₀ :=
    mul_mem (mul_mem (mul_mem hβT (D.B_le_T₀ hβ')) (inv_mem hβT)) (inv_mem (D.B_le_T₀ hβ'))
  have c1 := D.comm_T₀_of_mem_A hm hα hX
  have c2 := D.comm_T₀_of_mem_A hm hα' hY
  have c3 : β * α' = α' * β := (D.A_comm_B α' hα' β hβ).symm
  have e : α * β * (α' * β') * (α * β)⁻¹ * (α' * β')⁻¹ = β * β' * β⁻¹ * β'⁻¹ := by
    calc α * β * (α' * β') * (α * β)⁻¹ * (α' * β')⁻¹
        = α * (β * (α' * β') * β⁻¹) * α⁻¹ * (α' * β')⁻¹ := by group
      _ = β * (α' * β') * β⁻¹ * (α' * β')⁻¹ := by rw [← c1, mul_inv_cancel_right]
      _ = β * α' * β' * β⁻¹ * β'⁻¹ * α'⁻¹ := by group
      _ = α' * (β * β' * β⁻¹ * β'⁻¹) * α'⁻¹ := by rw [c3]; group
      _ = β * β' * β⁻¹ * β'⁻¹ := by rw [← c2, mul_inv_cancel_right]
  rw [e]
  exact D.comm_mem_B₀B₁_of_mem_B hβ hβ'

theorem Astar_le_A_sup : D.Astar ≤ D.A ⊔ zpowers D.b := by
  rw [Astar, closure_le]
  rintro _ ⟨x, hx, -, -, rfl⟩
  exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers _))

theorem exists_comm_eq_b₀ : ∃ X R : D.B₀, X * R * X⁻¹ * R⁻¹ = ⟨D.b₀, D.b₀_mem⟩ ∧ R * R = 1 ∧
    X * R * (X * R) = 1 ∧ R ≠ 1 ∧ X * R ≠ 1 ∧ R ≠ ⟨D.b₀, D.b₀_mem⟩ ∧
    X * R ≠ ⟨D.b₀, D.b₀_mem⟩ := by
  set e₀ := D.B₀_iso.some
  have hk : 2 ≤ n - 1 := D.two_le_n_sub_one
  have hb : e₀ ⟨D.b₀, D.b₀_mem⟩ = zc (n - 1) := by
    have h := symm_zc_eq e₀ hk D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy
    rw [show (⟨D.b₀, D.b₀_mem⟩ : D.B₀) = e₀.symm (zc (n - 1)) from Subtype.ext h.symm,
      MulEquiv.apply_symm_apply]
  have hz : zc (n - 1) = r ((2 ^ (n - 1 - 1) : ℕ) : ZMod (2 ^ (n - 1))) := zc_eq_r (by omega)
  have hne : ∀ i i' : ZMod (2 ^ (n - 1)), (sr i : DihedralGroup (2 ^ (n - 1))) ≠ r i' := by
    intro i i' h
    cases h
  refine ⟨e₀.symm (r ((2 ^ (n - 1 - 2) : ℕ) : ZMod (2 ^ (n - 1)))), e₀.symm (sr 0), ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · apply e₀.injective
    rw [hb, hz, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, comm_r_sr, quarter_add_quarter hk]
  · rw [← map_mul, sr_mul_sr, sub_self, ← one_def, map_one]
  · rw [← map_mul, ← map_mul, r_mul_sr, sr_mul_sr, sub_self, ← one_def, map_one]
  · intro h
    have := congrArg e₀ h
    rw [MulEquiv.apply_symm_apply, map_one, one_def] at this
    exact hne _ _ this
  · intro h
    have := congrArg e₀ h
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, map_one, one_def,
      r_mul_sr] at this
    exact hne _ _ this
  · intro h
    have := congrArg e₀ h
    rw [MulEquiv.apply_symm_apply, hb, hz] at this
    exact hne _ _ this
  · intro h
    have := congrArg e₀ h
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hb, hz, r_mul_sr] at this
    exact hne _ _ this

theorem sDiag_b₀ : D.sDiag ⟨D.b₀, D.b₀_mem⟩ = D.b := by
  show D.b₀ * (D.s * D.b₀ * D.s⁻¹) = D.b₀ * D.b₁
  rw [D.conj_s_b₀]

theorem elem32_of_mem_CB₀B₁s (hm : m = 2) {w : G} (hw : w ∈ (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s})
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwb : w ≠ D.b) :
    D.A ⊔ ((zpowers w ⊔ zpowers D.b) ⊔ zpowers D.s) ≤ T ∧
      (∀ x ∈ D.A ⊔ ((zpowers w ⊔ zpowers D.b) ⊔ zpowers D.s), x * x = 1) ∧
      Nat.card ↥(D.A ⊔ ((zpowers w ⊔ zpowers D.b) ⊔ zpowers D.s)) = 2 ^ 5 ∧
      ∀ a₁ ∈ D.A, D.A ⊔ ((zpowers w ⊔ zpowers D.b) ⊔ zpowers D.s) ≤ centralizer {a₁ * D.s} := by
  set C := zpowers w ⊔ zpowers D.b with hC
  have hbC : D.b ∈ (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s} :=
    mem_inf.2 ⟨D.b_mem_B₀B₁, mem_centralizer_singleton_iff.2 (D.b_comm_B D.s_mem_B).symm⟩
  have hCC : C ≤ (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s} := sup_le (zpowers_le.2 hw) (zpowers_le.2 hbC)
  have hwbc : w * D.b = D.b * w := D.b_comm_B (D.B₀B₁_le_B (mem_inf.1 hw).1)
  have hC2 : ∀ x ∈ C, x * x = 1 := fun x hx =>
    mul_self_of_mem_zpowers_sup_zpowers hw2 D.b_mul_b hwbc hx
  have hC4 : Nat.card C = 4 := card_zpowers_sup_zpowers hw2 D.b_mul_b hw1 D.b_ne_one hwb hwbc
  have hA2 : ∀ x ∈ D.A, x * x = 1 := fun x hx => D.mul_self_of_mem_A_two hm hx
  have hA4 : Nat.card D.A = 4 := by rw [D.card_A, hm]; norm_num
  have hs2 : ∀ x ∈ zpowers D.s, x * x = 1 := by
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hx with rfl | rfl
    · exact mul_one 1
    · exact D.s_mul_s
  have hCs : ∀ x ∈ C, ∀ y ∈ zpowers D.s, x * y = y * x := by
    intro x hx y hy
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hy with rfl | rfl
    · rw [mul_one, one_mul]
    · exact mem_centralizer_singleton_iff.1 (mem_inf.1 (hCC hx)).2
  have hiCs : C ⊓ zpowers D.s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxC, hxs⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hxs with rfl | rfl
    · exact one_mem _
    · exact absurd (mem_inf.1 (hCC hxC)).1 D.s_not_mem_B₀B₁
  have hCsB : C ⊔ zpowers D.s ≤ D.B :=
    sup_le ((hCC.trans inf_le_left).trans D.B₀B₁_le_B) (zpowers_le.2 D.s_mem_B)
  have hcA : ∀ x ∈ D.A, ∀ y ∈ C ⊔ zpowers D.s, x * y = y * x :=
    fun x hx y hy => D.A_comm_B x hx y (hCsB hy)
  have hiA : D.A ⊓ (C ⊔ zpowers D.s) = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ hCsB).trans D.A_inf_B.le)
  refine ⟨sup_le D.A_le_T (hCsB.trans D.B_le_T),
    fun x hx => mul_self_of_mem_sup hA2 (fun y hy => mul_self_of_mem_sup hC2 hs2 hCs hy) hcA hx,
    ?_, fun a₁ ha₁ => sup_le (fun x hx => ?_) (fun x hx => ?_)⟩
  · have h : Nat.card ↥(D.A ⊔ (C ⊔ zpowers D.s)) = 4 * (4 * 2) := by
      rw [card_sup_of_le_normalizer (le_normalizer_of_comm hcA) hiA,
        card_sup_of_le_normalizer (le_normalizer_of_comm hCs) hiCs, hA4, hC4, Nat.card_zpowers,
        D.orderOf_s]
    exact h.trans (by norm_num)
  · rw [mem_centralizer_singleton_iff]
    have h1 : x * a₁ = a₁ * x := comm_of_mul_self hA2 hx ha₁
    have h2 : x * D.s = D.s * x := D.A_comm_B x hx D.s D.s_mem_B
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  · rw [mem_centralizer_singleton_iff]
    have h1 : x * a₁ = a₁ * x := (D.A_comm_B a₁ ha₁ x (hCsB hx)).symm
    have h2 : x * D.s = D.s * x :=
      comm_of_mem_sup (fun y hy => mem_centralizer_singleton_iff.1 (mem_inf.1 (hCC hy)).2)
        (fun y hy => by
          rcases eq_one_or_eq_of_mem_zpowers D.s_mul_s hy with rfl | rfl
          · rw [one_mul, mul_one]
          · rfl) hx
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

end Local

section Sylow

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {m n : ℕ}
  (D : FooteCore G (T : Subgroup G) m n)

theorem exists_conj_a_of_mem_T₀ (hm : m = 2) (hab : ¬ IsConj D.a (D.a * D.b)) {g : G}
    (hg0 : g * D.a * g⁻¹ ∈ D.T₀) (hg1 : g * D.a * g⁻¹ ∉ D.T₁) :
    ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ D.A ∧ y * D.a * y⁻¹ ∉ D.Astar := by
  have hu2 : g * D.a * g⁻¹ * (g * D.a * g⁻¹) = 1 := by
    rw [show g * D.a * g⁻¹ * (g * D.a * g⁻¹) = g * (D.a * D.a) * g⁻¹ by group, D.a_mul_a,
      mul_one, mul_inv_cancel]
  obtain ⟨a₁, ha₁, -, w, -, hwu⟩ := D.exists_conj_mul_s hg0 hg1 hu2
  obtain ⟨v, hv⟩ : ∃ v, v = a₁ * D.s := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = w⁻¹ * g := ⟨_, rfl⟩
  have ha_eq : D.a = g₁⁻¹ * v * g₁ := by
    rw [hv, hg₁]
    calc D.a = (w⁻¹ * g)⁻¹ * (w⁻¹ * (g * D.a * g⁻¹) * w) * (w⁻¹ * g) := by group
      _ = (w⁻¹ * g)⁻¹ * (a₁ * D.s) * (w⁻¹ * g) := by rw [← hwu]; group
  obtain ⟨X, R, hXR, hR2, hXR2, hR1, hXR1, hRb, hXRb⟩ := D.exists_comm_eq_b₀
  have hmemC : ∀ u : D.B₀, D.sDiag u ∈ (D.B₀ ⊔ D.B₁) ⊓ centralizer {D.s} := fun u =>
    D.sDiag_range ▸ ⟨u, rfl⟩
  have hcd : D.sDiag X * D.sDiag R * (D.sDiag X)⁻¹ * (D.sDiag R)⁻¹ = D.b := by
    rw [← D.sDiag_b₀, ← hXR, map_mul, map_mul, map_mul, map_inv, map_inv]
  obtain ⟨hE₁T, hE₁2, hE₁5, hE₁c⟩ := D.elem32_of_mem_CB₀B₁s hm (hmemC R)
    (by rw [← map_mul, hR2, map_one])
    (fun h => hR1 (D.sDiag_injective (h.trans (map_one D.sDiag).symm)))
    (fun h => hRb (D.sDiag_injective (h.trans D.sDiag_b₀.symm)))
  obtain ⟨hE₂T, hE₂2, hE₂5, hE₂c⟩ := D.elem32_of_mem_CB₀B₁s hm (hmemC (X * R))
    (by rw [← map_mul, hXR2, map_one])
    (fun h => hXR1 (D.sDiag_injective (h.trans (map_one D.sDiag).symm)))
    (fun h => hXRb (D.sDiag_injective (h.trans D.sDiag_b₀.symm)))
  set E₁ := D.A ⊔ ((zpowers (D.sDiag R) ⊔ zpowers D.b) ⊔ zpowers D.s) with hE₁
  set E₂ := D.A ⊔ ((zpowers (D.sDiag (X * R)) ⊔ zpowers D.b) ⊔ zpowers D.s) with hE₂
  have hTC : (T : Subgroup G) ≤ centralizer {D.a} := fun x hx =>
    mem_centralizer_singleton_iff.2 (D.a_comm_T hx)
  have hHC : (E₁ ⊔ E₂).map (MulAut.conj g₁⁻¹).toMonoidHom ≤ centralizer {D.a} := by
    rintro _ ⟨z, hz, rfl⟩
    have hzv : z * v = v * z := by
      have := (sup_le (hE₁c a₁ ha₁) (hE₂c a₁ ha₁)) hz
      rw [mem_centralizer_singleton_iff] at this
      rw [hv]
      exact this
    show g₁⁻¹ * z * g₁⁻¹⁻¹ ∈ centralizer {D.a}
    rw [mem_centralizer_singleton_iff, ha_eq, inv_inv]
    calc g₁⁻¹ * z * g₁ * (g₁⁻¹ * v * g₁) = g₁⁻¹ * (z * v) * g₁ := by group
      _ = g₁⁻¹ * (v * z) * g₁ := by rw [hzv]
      _ = g₁⁻¹ * v * g₁ * (g₁⁻¹ * z * g₁) := by group
  have hHp : IsPGroup 2 ↥((E₁ ⊔ E₂).map (MulAut.conj g₁⁻¹).toMonoidHom) :=
    (T.isPGroup'.to_le (sup_le hE₁T hE₂T)).map _
  obtain ⟨k, hk, hkT⟩ := exists_conj_le_sylow_of_le T hTC hHC hHp
  set κ := k * g₁⁻¹ with hκ
  have hψ : ∀ E : Subgroup G, E ≤ E₁ ⊔ E₂ → E.map (MulAut.conj κ).toMonoidHom ≤ T := by
    intro E hE
    rw [hκ, ← map_conj_map_conj]
    exact (map_mono (map_mono hE)).trans hkT
  have hψv : κ * v * κ⁻¹ = D.a := by
    have hka : k * D.a = D.a * k := mem_centralizer_singleton_iff.1 hk
    calc κ * v * κ⁻¹ = k * (g₁⁻¹ * v * g₁) * k⁻¹ := by rw [hκ]; group
      _ = D.a := by rw [← ha_eq, hka, mul_inv_cancel_right]
  have hT₀ : ∀ E : Subgroup G, E ≤ E₁ ⊔ E₂ → (∀ x ∈ E, x * x = 1) → Nat.card E = 2 ^ 5 →
      ∀ x ∈ E, κ * x * κ⁻¹ ∈ D.T₀ := by
    intro E hE hE2 hE5 x hx
    refine D.le_T₀_of_mul_self (hψ E hE) (mul_self_map_conj hE2 κ) ?_ (conj_mem_map_conj hx)
    rw [card_map_conj, hE5]
    norm_num
  have hd : κ * D.sDiag R * κ⁻¹ ∈ D.T₀ :=
    hT₀ E₁ le_sup_left hE₁2 hE₁5 _ (mem_sup_right (mem_sup_left (mem_sup_left (mem_zpowers _))))
  have hcd' : κ * D.sDiag (X * R) * κ⁻¹ ∈ D.T₀ :=
    hT₀ E₂ le_sup_right hE₂2 hE₂5 _ (mem_sup_right (mem_sup_left (mem_sup_left (mem_zpowers _))))
  have hc : κ * D.sDiag X * κ⁻¹ ∈ D.T₀ := by
    have e : κ * D.sDiag X * κ⁻¹ = κ * D.sDiag (X * R) * κ⁻¹ * (κ * D.sDiag R * κ⁻¹)⁻¹ := by
      rw [map_mul]; group
    rw [e]
    exact mul_mem hcd' (inv_mem hd)
  have hβ : κ * D.b * κ⁻¹ ∈ D.B₀ ⊔ D.B₁ := by
    have e : κ * D.b * κ⁻¹ = κ * D.sDiag X * κ⁻¹ * (κ * D.sDiag R * κ⁻¹) *
        (κ * D.sDiag X * κ⁻¹)⁻¹ * (κ * D.sDiag R * κ⁻¹)⁻¹ := by
      rw [← hcd]; group
    rw [e]
    exact D.comm_mem_B₀B₁ hm hc hd
  have hβ1 : κ * D.b * κ⁻¹ ≠ 1 := fun h => D.b_ne_one (by
    rw [show D.b = κ⁻¹ * (κ * D.b * κ⁻¹) * κ by group, h]; group)
  have hbv : D.b₀ * v * D.b₀⁻¹ = v * D.b := by
    have h1 : D.b₀ * a₁ = a₁ * D.b₀ := (D.A_comm_B a₁ ha₁ D.b₀ D.b₀_mem_B).symm
    have h2 : D.s⁻¹ * D.b₀ * D.s = D.b₁ := by
      rw [D.s_inv, ← D.conj_s_b₀, D.s_inv]
    have h3 : D.b₁ * D.b₀ = D.b₀ * D.b₁ := (D.B₀_comm_B₁ D.b₀ D.b₀_mem D.b₁ D.b₁_mem).symm
    have h4 : D.b₀⁻¹ = D.b₀ := inv_eq_of_mul_eq_one_right D.b₀_mul_b₀
    rw [hv]
    calc D.b₀ * (a₁ * D.s) * D.b₀⁻¹ = a₁ * (D.b₀ * D.s * D.b₀) := by rw [← mul_assoc, h1, h4]; group
      _ = a₁ * D.s * ((D.s⁻¹ * D.b₀ * D.s) * D.b₀) := by group
      _ = a₁ * D.s * (D.b₀ * D.b₁) := by rw [h2, h3]
  have hya : κ * D.b₀ * κ⁻¹ * D.a * (κ * D.b₀ * κ⁻¹)⁻¹ = D.a * (κ * D.b * κ⁻¹) := by
    rw [← hψv]
    calc κ * D.b₀ * κ⁻¹ * (κ * v * κ⁻¹) * (κ * D.b₀ * κ⁻¹)⁻¹
        = κ * (D.b₀ * v * D.b₀⁻¹) * κ⁻¹ := by group
      _ = κ * (v * D.b) * κ⁻¹ := by rw [hbv]
      _ = κ * v * κ⁻¹ * (κ * D.b * κ⁻¹) := by group
  refine ⟨κ * D.b₀ * κ⁻¹, ?_, ?_, ?_⟩
  · rw [hya]
    exact mul_mem (D.A_le_T₁ D.a_mem) (D.B₀B₁_le_T₁ hβ)
  · rw [hya]
    intro h
    have hA : κ * D.b * κ⁻¹ ∈ D.A := by
      have := mul_mem (inv_mem D.a_mem) h
      rwa [inv_mul_cancel_left] at this
    exact hβ1 (mem_bot.1 (D.A_inf_B₀B₁ ▸ mem_inf.2 ⟨hA, hβ⟩))
  · rw [hya]
    intro h
    have h' : κ * D.b * κ⁻¹ ∈ D.A ⊔ zpowers D.b := by
      have := mul_mem (inv_mem (mem_sup_left D.a_mem : D.a ∈ D.A ⊔ zpowers D.b)) (D.Astar_le_A_sup h)
      rwa [inv_mul_cancel_left] at this
    have hcomm : ∀ x ∈ D.A, ∀ y ∈ zpowers D.b, x * y = y * x := fun x hx y hy =>
      D.A_comm_B x hx y (zpowers_le.2 D.b_mem_B hy)
    obtain ⟨α, hα, β, hβb, hαβ⟩ :=
      (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm hcomm)).1 h'
    have hβB : β ∈ D.B₀ ⊔ D.B₁ := zpowers_le.2 D.b_mem_B₀B₁ hβb
    have hα1 : α = 1 := by
      have hαB : α ∈ D.B₀ ⊔ D.B₁ := by
        rw [show α = κ * D.b * κ⁻¹ * β⁻¹ by rw [hαβ]; group]
        exact mul_mem hβ (inv_mem hβB)
      exact mem_bot.1 (D.A_inf_B₀B₁ ▸ mem_inf.2 ⟨hα, hαB⟩)
    rw [hα1, one_mul] at hαβ
    rcases eq_one_or_eq_of_mem_zpowers D.b_mul_b hβb with h1 | h1
    · exact hβ1 (hαβ.trans h1)
    · apply hab
      refine isConj_iff.2 ⟨κ * D.b₀ * κ⁻¹, ?_⟩
      rw [hya, hαβ, h1]

theorem lemma4_one_four (hm : m = 2) (hab : ¬ IsConj D.a (D.a * D.b))
    (hT₀ : ∀ g : G, g * D.a * g⁻¹ ∈ (T : Subgroup G) → g * D.a * g⁻¹ ∉ D.T₀ →
      IsConj D.a (D.a * D.b))
    {g : G} (hgT : g * D.a * g⁻¹ ∈ (T : Subgroup G)) (hg1 : g * D.a * g⁻¹ ∉ D.T₁) :
    ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ D.A ∧ y * D.a * y⁻¹ ∉ D.Astar := by
  by_cases h0 : g * D.a * g⁻¹ ∈ D.T₀
  · exact D.exists_conj_a_of_mem_T₀ hm hab h0 hg1
  · exact absurd (hT₀ g hgT h0) hab

end Sylow

end FooteCore

end CFSG.CGT.Foote81L6
