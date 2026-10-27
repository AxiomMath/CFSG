module

public import CFSG.GH74.GLS.Stage4.T2P71Defs

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest
  CFSG.GH74.GLS.Stage4.Rest.T6 CFSG.GH74.GLS.Stage4.Rest.T9 CFSG.GH74.BNPair
  CFSG.GH74.GLS.Stage4.Rest.DodecA

namespace CFSG.GH74.GLS.Stage4.Rest.P71NonabAux

variable {G : Type} [Group G] [Finite G] {N4 : T2N4 G} {u : G}

abbrev Vtx := Bool × Bool × ZMod 3

def Vtx.sh (v : Vtx) : Vtx := (v.1, v.2.1, v.2.2 + 1)
def Vtx.w₁ (v : Vtx) : Vtx := (v.1, if v.1 then v.2.1 else !v.2.1, -v.2.2)
def Vtx.w₂ (v : Vtx) : Vtx := (v.1, if v.1 then !v.2.1 else v.2.1, -v.2.2)

def bs (N4 : T2N4 G) (t s : Bool) : Subgroup G :=
  if t then (if s then N4.X₂' else N4.X₂) else (if s then N4.X₁' else N4.X₁)

theorem bs_H {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {x : G} (hx : x ∈ N4.H)
    {y : G} (hy : y ∈ bs N4 t s) : x * y * x⁻¹ ∈ bs N4 t s := by
  have hloc := h.sec5.loc
  cases t <;> cases s <;> simp only [bs, Bool.false_eq_true, ite_false, ite_true] at hy ⊢
  · exact hloc.H_norm_X₁ x hx y hy
  · exact hloc.H_norm_X₁' x hx y hy
  · exact hloc.H_norm_X₂ x hx y hy
  · exact hloc.H_norm_X₂' x hx y hy

theorem bs_le_K₁ {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (s : Bool) : bs N4 false s ≤ N4.K₁ := by
  cases s
  · simp only [bs, Bool.false_eq_true, ite_false]; exact X₁_le_K₁ h
  · simp only [bs, Bool.false_eq_true, ite_false, ite_true]
    rw [h.sec5.loc.K₁_eq]; exact le_sup_right

theorem bs_le_K₂ {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (s : Bool) : bs N4 true s ≤ N4.K₂ := by
  cases s
  · simp only [bs, ite_true, Bool.false_eq_true, ite_false]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_left
  · simp only [bs, ite_true]
    rw [h.sec5.loc.K₂_eq]; exact le_sup_right

theorem bs_le_K {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) : bs N4 t s ≤ N4.K₁ ⊔ N4.K₂ := by
  cases t
  · exact (bs_le_K₁ h s).trans le_sup_left
  · exact (bs_le_K₂ h s).trans le_sup_right

theorem bs_nontriv {u : G} (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) : ∃ x ∈ bs N4 t s, x ≠ 1 := by
  have hloc := h.sec5.loc
  have hq₁ := hloc.q₁_ge
  have hq₂ := hloc.q₂_ge
  by_contra hcon
  push Not at hcon
  have hbot : bs N4 t s = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hcon x hx)
  have hc : Nat.card ↥(bs N4 t s) = 1 := by rw [hbot]; exact Subgroup.card_bot
  cases t <;> cases s <;> simp only [bs, Bool.false_eq_true, ite_false, ite_true] at hc
  · rw [hloc.card_X₁] at hc; omega
  · rw [hloc.card_X₁'] at hc; omega
  · rw [hloc.card_X₂] at hc; omega
  · rw [hloc.card_X₂'] at hc; omega

def rg (N4 : T2N4 G) (v : Vtx) : Subgroup G := conjBy (N4.a ^ v.2.2.val) (bs N4 v.1 v.2.1)

def Cm (A B : Subgroup G) : Prop := ∀ x ∈ A, ∀ y ∈ B, x * y = y * x

omit [Finite G] in
theorem Cm.conjBy {A B : Subgroup G} (g : G) (h : Cm A B) :
    Cm (BNPair.conjBy g A) (BNPair.conjBy g B) := by
  intro x hx y hy
  rw [mem_conjBy_iff] at hx hy
  have h1 := h _ hx _ hy
  have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have e2 : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
  rw [e1, e2] at h1
  exact mul_left_cancel (mul_right_cancel h1)

omit [Finite G] in
theorem zmod3_val_add_one (k : ZMod 3) : (k + 1).val = (k.val + 1) % 3 := by
  fin_cases k <;> decide

omit [Finite G] in
theorem zmod3_val_neg (k : ZMod 3) : (-k).val = (2 * k.val) % 3 := by
  fin_cases k <;> decide

theorem rg_sh (h : T6Ctx N4.toT2N3 u N4.p) (v : Vtx) : conjBy N4.a (rg N4 v) = rg N4 v.sh := by
  unfold rg
  have hB : HInv N4.H (bs N4 v.1 v.2.1) := fun x hx y hy => bs_H h v.1 v.2.1 hx hy
  have e1 : conjBy N4.a (conjBy (N4.a ^ v.2.2.val) (bs N4 v.1 v.2.1)) =
      conjBy (N4.a ^ (v.2.2.val + 1)) (bs N4 v.1 v.2.1) := by
    have := conjBy_pow_add N4.a 1 v.2.2.val (bs N4 v.1 v.2.1)
    rw [pow_one] at this
    exact this
  rw [e1, conjBy_pow_mod hB h.sec5.weyl.a_normH h.sec5.weyl.a_cube]
  show _ = conjBy (N4.a ^ (v.2.2 + 1).val) (bs N4 v.1 v.2.1)
  rw [zmod3_val_add_one]

theorem hinv_base (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) : HInv N4.H (bs N4 t s) :=
  fun _ hx _ hy => bs_H h t s hx hy

theorem base_w₁ (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) :
    conjBy N4.w₁⁻¹ (bs N4 t s) = bs N4 t (if t then s else !s) := by
  have hloc := h.sec5.loc
  have hsq : N4.w₁ * N4.w₁ ∈ N4.H := by rw [hloc.w₁_sq]; exact hloc.z_mem_H
  cases t
  · cases s
    · simp only [bs, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]
      rw [conjBy_inv_eq hloc.H_norm_X₁ hloc.w₁_normH hsq]
      exact conjBy_eq_of_swap hsq hloc.H_norm_X₁' hloc.w₁_swap hloc.w₁_swap'
    · simp only [bs, Bool.false_eq_true, ite_false, Bool.not_true, ite_true]
      rw [conjBy_inv_eq hloc.H_norm_X₁' hloc.w₁_normH hsq]
      exact conjBy_eq_of_swap hsq hloc.H_norm_X₁ hloc.w₁_swap' hloc.w₁_swap
  · simp only [ite_true]
    refine conjBy_eq_self_of_comm fun x hx => ?_
    exact hloc.K_comm _ (N4.K₁.inv_mem hloc.w₁_mem) x (bs_le_K₂ h s hx)

theorem base_w₂ (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) :
    conjBy N4.w₂⁻¹ (bs N4 t s) = bs N4 t (if t then !s else s) := by
  have hloc := h.sec5.loc
  have hsq : N4.w₂ * N4.w₂ ∈ N4.H := by rw [hloc.w₂_sq]; exact hloc.z_mem_H
  cases t
  · simp only [Bool.false_eq_true, ite_false]
    refine conjBy_eq_self_of_comm fun x hx => ?_
    exact (hloc.K_comm x (bs_le_K₁ h s hx) _ (N4.K₂.inv_mem hloc.w₂_mem)).symm
  · cases s
    · simp only [bs, ite_true, Bool.false_eq_true, ite_false, Bool.not_false]
      rw [conjBy_inv_eq hloc.H_norm_X₂ hloc.w₂_normH hsq]
      exact conjBy_eq_of_swap hsq hloc.H_norm_X₂' hloc.w₂_swap hloc.w₂_swap'
    · simp only [bs, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [conjBy_inv_eq hloc.H_norm_X₂' hloc.w₂_normH hsq]
      exact conjBy_eq_of_swap hsq hloc.H_norm_X₂ hloc.w₂_swap' hloc.w₂_swap

theorem rg_w₁ (h : T6Ctx N4.toT2N3 u N4.p) (v : Vtx) : conjBy N4.w₁⁻¹ (rg N4 v) = rg N4 v.w₁ := by
  unfold rg
  have hB := hinv_base h v.1 v.2.1
  rw [conjBy_w_conjBy_a_pow hB h.sec5.loc.w₁_normH h.sec5.weyl.a_normH h.sec5.weyl.a_cube
    h.sec5.weyl.w₁_a, base_w₁ h]
  rw [conjBy_pow_mod (hinv_base h v.1 _) h.sec5.weyl.a_normH h.sec5.weyl.a_cube]
  show _ = conjBy (N4.a ^ (-v.2.2).val) (bs N4 v.1 (if v.1 then v.2.1 else !v.2.1))
  rw [zmod3_val_neg]

theorem rg_w₂ (h : T6Ctx N4.toT2N3 u N4.p) (v : Vtx) : conjBy N4.w₂⁻¹ (rg N4 v) = rg N4 v.w₂ := by
  unfold rg
  have hB := hinv_base h v.1 v.2.1
  rw [conjBy_w_conjBy_a_pow hB h.sec5.loc.w₂_normH h.sec5.weyl.a_normH h.sec5.weyl.a_cube
    h.sec5.weyl.w₂_a, base_w₂ h]
  rw [conjBy_pow_mod (hinv_base h v.1 _) h.sec5.weyl.a_normH h.sec5.weyl.a_cube]
  show _ = conjBy (N4.a ^ (-v.2.2).val) (bs N4 v.1 (if v.1 then !v.2.1 else v.2.1))
  rw [zmod3_val_neg]

omit [Finite G] in
theorem rg_zero (N4 : T2N4 G) (t s : Bool) : rg N4 (t, s, 0) = bs N4 t s := by
  unfold rg
  simp only [ZMod.val_zero, pow_zero]
  exact t9_conjBy_one _

theorem base_pow_p (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {y : G} (hy : y ∈ bs N4 t s) :
    y ^ N4.p = 1 := by
  have hloc := h.sec5.loc
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hq₁ := hloc.q₁_ge
  have hq₂ := hloc.q₂_ge
  have hm0 : m ≠ 0 := by rintro rfl; simp [hm] at hq₁
  have hn0 : n ≠ 0 := by rintro rfl; simp [hn] at hq₂
  have h1 : N4.q₁.minFac = N4.p := by rw [hm]; exact h.prime.pow_minFac hm0
  have h2 : N4.q₂.minFac = N4.p := by rw [hn]; exact h.prime.pow_minFac hn0
  cases t <;> cases s <;> simp only [bs, Bool.false_eq_true, ite_false, ite_true] at hy
  · have := hloc.X₁_exp y hy; rwa [h1] at this
  · have := hloc.X₁'_exp y hy; rwa [h1] at this
  · have := hloc.X₂_exp y hy; rwa [h2] at this
  · have := hloc.X₂'_exp y hy; rwa [h2] at this

theorem base_inv_u (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {y : G} (hy : y ∈ bs N4 t s) :
    u * y * u⁻¹ = y⁻¹ := by
  have hloc := h.sec5.loc
  cases t <;> cases s <;> simp only [bs, Bool.false_eq_true, ite_false, ite_true] at hy
  · exact hloc.u_inv_X₁ y hy
  · exact hloc.u_inv_X₁' y hy
  · exact hloc.u_inv_X₂ y hy
  · exact hloc.u_inv_X₂' y hy

theorem base_z_cent (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {y : G} (hy : y ∈ bs N4 t s) :
    N4.z * y * N4.z⁻¹ = y := by
  have h1 : y * N4.z = N4.z * y := h.zK y (bs_le_K h t s hy)
  calc N4.z * y * N4.z⁻¹ = (y * N4.z) * N4.z⁻¹ := by rw [h1]
    _ = y := by group

theorem zu_inv_base (h : T6Ctx N4.toT2N3 u N4.p) (t s : Bool) {y : G} (hy : y ∈ bs N4 t s) :
    (N4.z * u) * y * (N4.z * u)⁻¹ = y⁻¹ := by
  calc (N4.z * u) * y * (N4.z * u)⁻¹ = N4.z * (u * y * u⁻¹) * N4.z⁻¹ := by group
    _ = N4.z * y⁻¹ * N4.z⁻¹ := by rw [base_inv_u h t s hy]
    _ = (N4.z * y * N4.z⁻¹)⁻¹ := by group
    _ = y⁻¹ := by rw [base_z_cent h t s hy]

theorem rg_z_inv (h : T6Ctx N4.toT2N3 u N4.p) {v : Vtx} (hk : v.2.2 ≠ 0) {x : G} (hx : x ∈ rg N4 v) :
    N4.z * x * N4.z⁻¹ = x⁻¹ := by
  obtain ⟨t, s, c⟩ := v
  obtain ⟨ha1, ha2⟩ := a_conj_facts h
  obtain ⟨-, e2, -⟩ := t9_a_facts h
  unfold rg at hx
  fin_cases c
  · exact absurd rfl hk
  ·
    have hy : N4.a ^ 1 * x * (N4.a ^ 1)⁻¹ ∈ bs N4 t s := (mem_conjBy_iff).1 hx
    rw [pow_one] at hy
    have hzu := zu_inv_base h t s hy
    have hzu' : (N4.a * N4.z * N4.a⁻¹) * (N4.a * x * N4.a⁻¹) * (N4.a * N4.z * N4.a⁻¹)⁻¹ =
        (N4.a * x * N4.a⁻¹)⁻¹ := by rw [ha2]; exact hzu
    have e : N4.z * x * N4.z⁻¹ = N4.a⁻¹ * ((N4.a * N4.z * N4.a⁻¹) * (N4.a * x * N4.a⁻¹) *
        (N4.a * N4.z * N4.a⁻¹)⁻¹) * N4.a := by group
    rw [e, hzu']
    group
  ·
    have hy : N4.a ^ 2 * x * (N4.a ^ 2)⁻¹ ∈ bs N4 t s := (mem_conjBy_iff).1 hx
    have hu := base_inv_u h t s hy
    have hu' : (N4.a ^ 2 * N4.z * (N4.a ^ 2)⁻¹) * (N4.a ^ 2 * x * (N4.a ^ 2)⁻¹) *
        (N4.a ^ 2 * N4.z * (N4.a ^ 2)⁻¹)⁻¹ = (N4.a ^ 2 * x * (N4.a ^ 2)⁻¹)⁻¹ := by rw [e2]; exact hu
    have e : N4.z * x * N4.z⁻¹ = (N4.a ^ 2)⁻¹ * ((N4.a ^ 2 * N4.z * (N4.a ^ 2)⁻¹) *
        (N4.a ^ 2 * x * (N4.a ^ 2)⁻¹) * (N4.a ^ 2 * N4.z * (N4.a ^ 2)⁻¹)⁻¹) * N4.a ^ 2 := by group
    rw [e, hu']
    group

theorem witness (h : T6Ctx N4.toT2N3 u N4.p) {v : Vtx} (hk : v.2.2 ≠ 0)
    (h1 : Cm (rg N4 v) (rg N4 (true, false, 0))) (h2 : Cm (rg N4 v) (rg N4 (true, true, 0))) :
    False := by
  have hloc := h.sec5.loc
  obtain ⟨y, hy, hy1⟩ := bs_nontriv h v.1 v.2.1
  have hx : (N4.a ^ v.2.2.val)⁻¹ * y * N4.a ^ v.2.2.val ∈ rg N4 v := by
    unfold rg
    rw [mem_conjBy_iff]
    have e : N4.a ^ v.2.2.val * ((N4.a ^ v.2.2.val)⁻¹ * y * N4.a ^ v.2.2.val) *
        (N4.a ^ v.2.2.val)⁻¹ = y := by group
    rw [e]; exact hy
  set x := (N4.a ^ v.2.2.val)⁻¹ * y * N4.a ^ v.2.2.val with hxdef
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hy1
    have : y = N4.a ^ v.2.2.val * x * (N4.a ^ v.2.2.val)⁻¹ := by rw [hxdef]; group
    rw [this, hx1]; group
  have hxz : x * N4.z = N4.z * x := by
    have hK : N4.X₂ ⊔ N4.X₂' ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        have := h1 x hx a (by rw [rg_zero]; exact ha)
        exact this
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        have := h2 x hx a (by rw [rg_zero]; exact ha)
        exact this
    have hz : N4.z ∈ N4.X₂ ⊔ N4.X₂' := by rw [← hloc.K₂_eq]; exact hloc.z_mem_K₂
    exact Subgroup.mem_centralizer_iff.1 (hK hz) x (Set.mem_singleton x)
  have hzx : N4.z * x * N4.z⁻¹ = x := by
    calc N4.z * x * N4.z⁻¹ = (x * N4.z) * N4.z⁻¹ := by rw [hxz]
      _ = x := by group
  have hinv := rg_z_inv h hk hx
  rw [hzx] at hinv
  have hsq : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← hinv]
      _ = 1 := mul_inv_cancel x
  have hp : x ^ N4.p = 1 := by
    have e := conj_pow (a := (N4.a ^ v.2.2.val)⁻¹) (b := y) (i := N4.p)
    rw [inv_inv] at e
    rw [hxdef, e, base_pow_p h v.1 v.2.1 hy]
    group
  have hdvd1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  have hdvd2 : orderOf x ∣ N4.p := orderOf_dvd_of_pow_eq_one hp
  have hcop : Nat.Coprime 2 N4.p := (Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.p_ne_two)
  have h1' : orderOf x ∣ 1 := by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hdvd1 hdvd2
  exact hx1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1'))

def fiveV (α β γ δ : Bool) : List Vtx :=
  [(true, false, 0), (false, α, 1), (true, β, 1), (false, γ, 2), (true, δ, 2)]

def E0L (α β γ δ : Bool) : List (Vtx × Vtx) :=
  (fiveV α β γ δ).flatMap fun v => (fiveV α β γ δ).map fun w => (v, w)

def stepL (E : List (Vtx × Vtx)) : List (Vtx × Vtx) :=
  E ++ E.map (fun e => (e.1.sh, e.2.sh)) ++ E.map (fun e => (e.1.w₁, e.2.w₁)) ++
    E.map (fun e => (e.1.w₂, e.2.w₂))

def allV : List Vtx :=
  [false, true].flatMap fun t => [false, true].flatMap fun s => [0, 1, 2].map fun k => (t, s, (k : ZMod 3))

theorem comb : ∀ α β γ δ : Bool, ∃ v ∈ allV, v.2.2 ≠ 0 ∧
    (v, ((true, false, 0) : Vtx)) ∈ stepL (E0L α β γ δ) ∧
      (v, ((true, true, 0) : Vtx)) ∈ stepL (E0L α β γ δ) := by
  decide

def Sound (N4 : T2N4 G) (E : List (Vtx × Vtx)) : Prop := ∀ e ∈ E, Cm (rg N4 e.1) (rg N4 e.2)

theorem sound_step (h : T6Ctx N4.toT2N3 u N4.p) {E : List (Vtx × Vtx)} (hE : Sound N4 E) :
    Sound N4 (stepL E) := by
  intro e he
  simp only [stepL, List.mem_append, List.mem_map] at he
  rcases he with ((he | ⟨e', he', rfl⟩) | ⟨e', he', rfl⟩) | ⟨e', he', rfl⟩
  · exact hE e he
  · have := (hE e' he').conjBy N4.a
    rwa [rg_sh h, rg_sh h] at this
  · have := (hE e' he').conjBy N4.w₁⁻¹
    rwa [rg_w₁ h, rg_w₁ h] at this
  · have := (hE e' he').conjBy N4.w₂⁻¹
    rwa [rg_w₂ h, rg_w₂ h] at this

omit [Finite G] in
theorem sound_E0 {α β γ δ : Bool} (R : Subgroup G)
    (hle : ∀ v ∈ fiveV α β γ δ, rg N4 v ≤ R) (hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) :
    Sound N4 (E0L α β γ δ) := by
  intro e he
  simp only [E0L, List.mem_flatMap, List.mem_map] at he
  obtain ⟨v, hv, w, hw, rfl⟩ := he
  exact fun x hx y hy => hab x (hle _ hv hx) y (hle _ hw hy)

theorem false_of_sound (h : T6Ctx N4.toT2N3 u N4.p) {α β γ δ : Bool} (R : Subgroup G)
    (hle : ∀ v ∈ fiveV α β γ δ, rg N4 v ≤ R) (hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) : False := by
  obtain ⟨v, -, hv0, h1, h2⟩ := comb α β γ δ
  have hS := sound_step h (sound_E0 (N4 := N4) R hle hab)
  exact witness h hv0 (by simpa [rg_zero] using hS _ h1) (by simpa [rg_zero] using hS _ h2)

omit [Finite G] in
theorem rg_one (N4 : T2N4 G) (t s : Bool) : rg N4 (t, s, 1) = conjBy N4.a (bs N4 t s) := by
  unfold rg
  have : (1 : ZMod 3).val = 1 := rfl
  simp only [this, pow_one]

omit [Finite G] in
theorem rg_two (N4 : T2N4 G) (t s : Bool) : rg N4 (t, s, 2) = conjBy (N4.a ^ 2) (bs N4 t s) := by
  unfold rg
  have : (2 : ZMod 3).val = 2 := rfl
  simp only [this]

omit [Finite G] in
theorem base_false (N4 : T2N4 G) (s : Bool) : bs N4 false s = N4.toCh6.A s := by
  cases s <;> rfl

omit [Finite G] in
theorem base_true (N4 : T2N4 G) (s : Bool) : bs N4 true s = N4.toCh6.B s := by
  cases s <;> rfl

theorem shape_le (h : T6Ctx N4.toT2N3 u N4.p) (hS6 : S6Shape N4.toCh6) :
    ∃ α β γ δ : Bool, ∀ v ∈ fiveV α β γ δ, rg N4 v ≤ R₂ N4.toT2N3 N4.p := by
  obtain ⟨α, β, γ, δ, -, -, hu, hzu⟩ := (t9_shape_core h hS6).shape
  refine ⟨α, β, γ, δ, ?_⟩
  have hu0 : N4.a⁻¹ * N4.toT2N3.z * N4.a = u := h.sec5.u_eq
  have hRA : conjBy N4.a (N4.toCh6.A α ⊔ N4.toCh6.B β) ≤ R₂ N4.toT2N3 N4.p := by
    have h1 : Subgroup.centralizer {N4.toCh6.u} ⊓ N4.P = conjBy N4.a (N4.toCh6.A α ⊔ N4.toCh6.B β) := hu
    rw [← h1]
    show Subgroup.centralizer {N4.a⁻¹ * N4.toT2N3.z * N4.a} ⊓ N4.P ≤ _
    rw [hu0, t9_cent_u h hS6]
    exact inf_le_left
  have hRB : conjBy (N4.a ^ 2) (N4.toCh6.A γ ⊔ N4.toCh6.B δ) ≤ R₂ N4.toT2N3 N4.p := by
    have h1 : Subgroup.centralizer {N4.toCh6.z * N4.toCh6.u} ⊓ N4.P =
        conjBy (N4.a ^ 2) (N4.toCh6.A γ ⊔ N4.toCh6.B δ) := hzu
    rw [← h1]
    show Subgroup.centralizer {N4.toT2N3.z * (N4.a⁻¹ * N4.toT2N3.z * N4.a)} ⊓ N4.P ≤ _
    rw [hu0, t9_cent_zu h hS6]
    exact inf_le_left
  intro v hv
  simp only [fiveV, List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · rw [rg_zero]; exact X₂_le_R₂ h
  · rw [rg_one]
    refine le_trans (t9_conjBy_mono _ ?_) hRA
    rw [base_false]; exact le_sup_left
  · rw [rg_one]
    refine le_trans (t9_conjBy_mono _ ?_) hRA
    rw [base_true]; exact le_sup_right
  · rw [rg_two]
    refine le_trans (t9_conjBy_mono _ ?_) hRB
    rw [base_false]; exact le_sup_left
  · rw [rg_two]
    refine le_trans (t9_conjBy_mono _ ?_) hRB
    rw [base_true]; exact le_sup_right

theorem s6Shape_of {N : T2N3 G} {u : G} (h : T6Ctx N u 3)
    (hord : Nat.card ↥(R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3) :
    S6Shape (T2N4.toCh6 ⟨N, 3, ⊥, R₂ N 3 ⊔ N.X₁⟩) := by
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hloc := h.sec5.loc
  have hX₁K := X₁_le_K₁ h
  have hnormX₁R : N.X₁ ≤ Subgroup.normalizer (R₂ N 3 : Set G) := fun g hg =>
    Subgroup.mem_normalizer_fintype (fun n hn => R₂_norm N 3 (K₁_le_M₂ h (hX₁K hg)) hn)
  have hdisj : Disjoint (R₂ N 3) N.X₁ := by
    rw [disjoint_iff, eq_bot_iff, ← R₂_inf_K₁ h]
    exact inf_le_inf_left _ hX₁K
  have hPcard : Nat.card ↥(R₂ N 3 ⊔ N.X₁) = N.q₁ ^ 3 * N.q₂ ^ 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormX₁R hdisj,
      hord, hloc.card_X₁]
    ring
  exact
    { R₂_card := hord
      R₂_comm := (R₂_inv_comm h).2
      K₁_normR₂ := fun x hx r hr => R₂_norm N 3 (K₁_le_M₂ h hx) hr
      P_eq := rfl
      P_pGroup := IsPGroup.of_card (n := 3 * m + 3 * n) (by
        show Nat.card ↥(R₂ N 3 ⊔ N.X₁) = 3 ^ (3 * m + 3 * n)
        rw [hPcard, hm, hn, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf) }

theorem p71_abelian_false {N : T2N3 G} {u : G} (h : T6Ctx N u 3)
    (hord : Nat.card ↥(R₂ N 3) = N.q₁ ^ 2 * N.q₂ ^ 3)
    (hab : ∀ x ∈ R₂ N 3, ∀ y ∈ R₂ N 3, x * y = y * x) : False := by
  let N4 : T2N4 G := ⟨N, 3, ⊥, R₂ N 3 ⊔ N.X₁⟩
  have hS6 : S6Shape N4.toCh6 := s6Shape_of h hord
  have h4 : T6Ctx N4.toT2N3 u N4.p := h
  obtain ⟨α, β, γ, δ, hle⟩ := shape_le h4 hS6
  exact false_of_sound h4 (R₂ N4.toT2N3 N4.p) hle hab

end CFSG.GH74.GLS.Stage4.Rest.P71NonabAux

namespace CFSG.GH74.GLS.Stage4.Rest

theorem p71Nonab_proved : P71Nonab := by
  intro G _ _ Gs _ n N u hE _ hcard
  by_contra hcon
  have hab : ∀ x ∈ T6.R₂ N 3, ∀ y ∈ T6.R₂ N 3, x * y = y * x := by
    intro x hx y hy
    by_contra hne
    exact hcon ⟨x, hx, y, hy, hne⟩
  exact P71NonabAux.p71_abelian_false hE.ctx hcard hab

end CFSG.GH74.GLS.Stage4.Rest
