module

public import CFSG.GH74.BNPair.Dihedral
public import CFSG.GH74.Tits83.Section3D

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

variable {G : Type u} [Group G]

namespace TitsSystem

variable (T : TitsSystem G 8)

@[expose] def Ctriv : Subgroup G :=
  (⨅ k : ℤ, Subgroup.centralizer (T.U (2 * k + 1) : Set G)) ⊓
    ⨅ k : ℤ, Subgroup.centralizer (T.Uprime (2 * k) : Set G)

theorem conj_mem_Ctriv {g : G} {ε c : ℤ} (hε : ε = 1 ∨ ε = -1) (hc : Even c)
    (hg : T.Moves g (fun j => ε * j + c)) {x : G} (hx : x ∈ T.Ctriv) :
    g * x * g⁻¹ ∈ T.Ctriv := by
  obtain ⟨c', rfl⟩ := hc
  change x ∈ (⨅ k : ℤ, Subgroup.centralizer (T.U (2 * k + 1) : Set G)) ⊓
    ⨅ k : ℤ, Subgroup.centralizer (T.Uprime (2 * k) : Set G) at hx
  have key : ∀ {j : ℤ} {y : G}, Odd j → y ∈ T.U j → y * x = x * y := by
    intro j y hj hy
    obtain ⟨k, rfl⟩ := hj
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_iInf.mp hx.1 k) y hy
  have key' : ∀ {j : ℤ} {y : G}, Even j → y ∈ T.Uprime j → y * x = x * y := by
    intro j y hj hy
    obtain ⟨k, rfl⟩ := hj
    have hmem := Subgroup.mem_iInf.mp hx.2 k
    rw [show (2 : ℤ) * k = k + k by ring] at hmem
    exact Subgroup.mem_centralizer_iff.mp hmem y hy
  constructor
  · refine Subgroup.mem_iInf.mpr fun k => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rcases hε with rfl | rfl
    · have hg1 : T.Moves g (· + (c' + c')) := by simpa [one_mul] using hg
      have hy' : g⁻¹ * y * g ∈ T.U ((2 * k + 1) - (c' + c')) := by
        have h := TitsSystem.Moves.conj_mem T (TitsSystem.Moves.inv_shift T hg1) (j := 2 * k + 1) hy
        simpa using h
      have hcomm := key ⟨k - c', by ring⟩ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * y := by group
    · have hg1 : T.Moves g ((c' + c') - ·) := by
        simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hg
      have hy' : g⁻¹ * y * g ∈ T.U ((c' + c') - (2 * k + 1)) := by
        have h := TitsSystem.Moves.conj_mem T (TitsSystem.Moves.inv_refl T hg1) (j := 2 * k + 1) hy
        simpa using h
      have hcomm := key ⟨c' - k - 1, by ring⟩ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * y := by group
  · refine Subgroup.mem_iInf.mpr fun k => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rcases hε with rfl | rfl
    · have hg1 : T.Moves g (· + (c' + c')) := by simpa [one_mul] using hg
      have hmv : T.Moves g⁻¹ (fun j => 1 * j + (-c' + -c')) := by
        have h := TitsSystem.Moves.inv_shift T hg1
        convert h using 2
        ring
      have hy' : g⁻¹ * y * g ∈ T.Uprime (2 * k - (c' + c')) := by
        have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmv (j := 2 * k) hy
        simpa [show 2 * k + (-c' + -c') = 2 * k - (c' + c') by ring] using h
      have hcomm := key' ⟨k - c', by ring⟩ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * y := by group
    · have hg1 : T.Moves g ((c' + c') - ·) := by
        simpa [sub_eq_add_neg, neg_one_mul, add_comm] using hg
      have hmv : T.Moves g⁻¹ (fun j => -1 * j + (c' + c')) := by
        have h := TitsSystem.Moves.inv_refl T hg1
        convert h using 2
        ring
      have hy' : g⁻¹ * y * g ∈ T.Uprime ((c' + c') - 2 * k) := by
        have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inr rfl) hmv (j := 2 * k) hy
        simpa [show -(2 * k) + (c' + c') = (c' + c') - 2 * k by ring] using h
      have hcomm := key' ⟨c' - k, by ring⟩ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = (g * x * g⁻¹) * y := by group

theorem Ctriv_comm_odd {g x : G} (hg : g ∈ T.Ctriv) {j : ℤ} (hj : Odd j) (hx : x ∈ T.U j) :
    g * x = x * g := by
  change g ∈ (⨅ k : ℤ, Subgroup.centralizer (T.U (2 * k + 1) : Set G)) ⊓
    ⨅ k : ℤ, Subgroup.centralizer (T.Uprime (2 * k) : Set G) at hg
  obtain ⟨k, rfl⟩ := hj
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_iInf.mp hg.1 k) x hx).symm

theorem Ctriv_comm_Uprime {g x : G} (hg : g ∈ T.Ctriv) {j : ℤ} (hj : Even j)
    (hx : x ∈ T.Uprime j) : g * x = x * g := by
  change g ∈ (⨅ k : ℤ, Subgroup.centralizer (T.U (2 * k + 1) : Set G)) ⊓
    ⨅ k : ℤ, Subgroup.centralizer (T.Uprime (2 * k) : Set G) at hg
  obtain ⟨k, rfl⟩ := hj
  have hmem := Subgroup.mem_iInf.mp hg.2 k
  rw [show (2 : ℤ) * k = k + k by ring] at hmem
  exact (Subgroup.mem_centralizer_iff.mp hmem x hx).symm

theorem Moves.congr {g : G} {π π' : ℤ → ℤ} (hg : T.Moves g π)
    (h : ∀ j, ∃ k, π' j = π j + 16 * k) : T.Moves g π' := by
  intro j
  obtain ⟨k, hk⟩ := h j
  rw [hg j, hk]
  convert (U_add_two_mul T (π j) k).symm using 1
  ring

theorem mu_one_comm (hT : T.Normalized) {u x : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hx : x ∈ T.U 5) : T.mu 1 u * x = x * T.mu 1 u := by
  have hux : u * x = x * u := T.lemma34_iii hT hu hx
  have h := (T.lemma212_ii (by norm_num : 3 ≤ (8 : ℕ)) (i := 1) (j := 5)
    (by norm_num) hu hu1 hx hux).2
  exact h.symm

theorem mu_one_comm' (hT : T.Normalized) {u x : G} (hu : u ∈ T.U 1) (hu1 : u ≠ 1)
    (hx : x ∈ T.U (-3)) : T.mu 1 u * x = x * T.mu 1 u := by
  have hux : u * x = x * u :=
    (T.comm_odd_add_four hT (j := -3) (by decide) hx hu).symm
  have h := (T.lemma212_ii' (by norm_num : 3 ≤ (8 : ℕ)) (i := 1) (j := -3)
    (by norm_num) hu hu1 hx hux).2
  exact h.symm

end TitsSystem

structure OctFrame (T : TitsSystem G 8) where
  hT : T.Normalized
  e1 : G
  e8 : G
  e1_mem : e1 ∈ T.U 1
  e1_ne : e1 ≠ 1
  e8_mem : e8 ∈ T.Uprime 8
  e8_ne : e8 ≠ 1

theorem exists_octFrame {T : TitsSystem G 8} (hT : T.Normalized) : Nonempty (OctFrame T) := by
  obtain ⟨e1, he1, he1'⟩ := Subgroup.exists_mem_ne_one_of_ne_bot (T.ne_bot 1)
  obtain ⟨e8, he8, he8'⟩ := T.exists_Uprime hT (j := 8) ⟨4, by norm_num⟩
  exact ⟨⟨hT, e1, e8, he1, he1', he8, he8'⟩⟩

namespace OctFrame
variable {T : TitsSystem G 8} (F : OctFrame T)

@[expose] noncomputable def a : G := T.mu 1 F.e1
@[expose] noncomputable def b : G := T.mu 8 F.e8
noncomputable def rho : G := F.a * F.b

theorem a_mul_self : F.a * F.a = 1 := by
  exact T.lemma35_ii F.hT (j := 1) (by decide) F.e1_mem F.e1_ne

theorem b_mul_self : F.b * F.b = 1 := by
  exact T.mu_mul_self_Uprime F.hT (j := 8) ⟨4, by norm_num⟩ F.e8_mem F.e8_ne

theorem moves_a : T.Moves F.a (fun j => 10 - j) := by
  simpa [OctFrame.a] using T.moves_mu (i := 1) F.e1_mem F.e1_ne

theorem moves_b : T.Moves F.b (fun j => 24 - j) := by
  simpa [OctFrame.b] using
    T.moves_mu (i := 8) (T.Uprime_le 8 F.e8_mem) F.e8_ne

theorem moves_rho : T.Moves F.rho (fun j => j + 2) := by
  have h := TitsSystem.Moves.mul T F.moves_a F.moves_b
  have hm : T.Moves (F.a * F.b) (fun j : ℤ => j - 14) := by
    convert h using 2
    simp only [Function.comp_apply]
    ring
  have hfinal := TitsSystem.Moves.congr T (π := fun j : ℤ => j - 14)
    (π' := fun j : ℤ => j + 2) hm (fun j => ⟨1, by ring⟩)
  simpa [OctFrame.rho] using hfinal

theorem b_eq : F.b = F.rho⁻¹ * F.a := by
  have ha : F.a⁻¹ = F.a := inv_eq_of_mul_eq_one_right F.a_mul_self
  have hb : F.b⁻¹ = F.b := inv_eq_of_mul_eq_one_right F.b_mul_self
  rw [OctFrame.rho, mul_inv_rev, ha, hb, mul_assoc, F.a_mul_self, mul_one]

theorem rho_pow_eight : F.rho ^ 8 = 1 := by
  have hba : F.b * F.a = F.rho⁻¹ := by
    calc F.b * F.a = (F.rho⁻¹ * F.a) * F.a := by rw [F.b_eq]
      _ = F.rho⁻¹ * (F.a * F.a) := by group
      _ = F.rho⁻¹ := by rw [F.a_mul_self, mul_one]
  have hbraid := T.braid (by norm_num : 3 ≤ (8 : ℕ)) F.e1_mem F.e1_ne
    (T.Uprime_le 8 F.e8_mem) F.e8_ne
  have h1 := altWord_two_mul (T.mu 1 F.e1) (T.mu ((8 : ℕ) : ℤ) F.e8) 4
  have h2 := altWord_two_mul (T.mu ((8 : ℕ) : ℤ) F.e8) (T.mu 1 F.e1) 4
  rw [show (2 * 4 : ℕ) = 8 by norm_num] at h1 h2
  rw [h1, h2] at hbraid
  have h4 : (F.rho⁻¹) ^ 4 = F.rho ^ 4 := by
    rw [← hba]
    simpa [OctFrame.a, OctFrame.b, OctFrame.rho] using hbraid
  rw [inv_pow] at h4
  calc F.rho ^ 8 = F.rho ^ 4 * F.rho ^ 4 := by
        rw [show (8 : ℕ) = 4 + 4 by norm_num, pow_add]
    _ = F.rho ^ 4 * (F.rho ^ 4)⁻¹ := by rw [h4]
    _ = 1 := mul_inv_cancel _

theorem moves_rho_zpow (k : ℤ) : T.Moves (F.rho ^ k) (fun j => j + 2 * k) := by
  induction k using Int.induction_on with
  | zero =>
    intro j
    have hconj1 : MulAut.conj (1 : G) = 1 := by
      ext x
      simp [MulAut.conj_apply]
    have hmap' : (MulEquiv.toMonoidHom (1 : MulAut G)) = MonoidHom.id G := rfl
    rw [show F.rho ^ (0 : ℤ) = 1 by simp, hconj1, hmap']
    simpa using Subgroup.map_id (T.U j)
  | succ i ih =>
    have h := TitsSystem.Moves.mul T ih F.moves_rho
    have hpow : F.rho ^ ((i : ℤ) + 1) = F.rho ^ (i : ℤ) * F.rho := zpow_add_one F.rho _
    have hfun : (fun j : ℤ => j + 2 * ((i : ℤ) + 1)) =
        (fun j : ℤ => j + 2 * (i : ℤ)) ∘ (fun j : ℤ => j + 2) := by
      funext j
      simp only [Function.comp_apply]
      ring
    rw [show ((i : ℕ) + 1 : ℤ) = (i : ℤ) + 1 by push_cast; ring, hpow, hfun]
    exact h
  | pred i ih =>
    have h := TitsSystem.Moves.mul T ih (TitsSystem.Moves.inv_shift T F.moves_rho)
    have hpow : F.rho ^ (-(i : ℤ) - 1) = F.rho ^ (-(i : ℤ)) * F.rho⁻¹ :=
      zpow_sub_one F.rho _
    have hfun : (fun j : ℤ => j + 2 * (-(i : ℤ) - 1)) =
        (fun j : ℤ => j + 2 * (-(i : ℤ))) ∘ (fun j : ℤ => j - 2) := by
      funext j
      simp only [Function.comp_apply]
      ring
    rw [hpow, hfun]
    exact h

theorem moves_rho_zpow_a (k : ℤ) : T.Moves (F.rho ^ k * F.a) (fun j => 10 + 2 * k - j) := by
  have h := TitsSystem.Moves.mul T (F.moves_rho_zpow k) F.moves_a
  have hfun : (fun j : ℤ => 10 + 2 * k - j) =
      (fun j : ℤ => j + 2 * k) ∘ (fun j : ℤ => 10 - j) := by
    funext j
    simp only [Function.comp_apply]
    ring
  rw [hfun]
  exact h

theorem a_mul_rho_zpow (k : ℤ) : F.a * F.rho ^ k = F.rho ^ (-k) * F.a := by
  have ha_conj : ∀ n : ℤ, F.a * F.rho ^ n * F.a⁻¹ = F.rho ^ (-n) := by
    intro n
    have h := conj_zpow (a := F.a) (b := F.rho) (i := n)
    have hba : F.b * F.a = F.rho⁻¹ := by
      calc F.b * F.a = (F.rho⁻¹ * F.a) * F.a := by rw [F.b_eq]
        _ = F.rho⁻¹ * (F.a * F.a) := by group
        _ = F.rho⁻¹ := by rw [F.a_mul_self, mul_one]
    have ha : F.a * F.rho * F.a⁻¹ = F.rho⁻¹ := by
      rw [OctFrame.rho]
      calc F.a * (F.a * F.b) * F.a⁻¹ = (F.a * F.a) * F.b * F.a⁻¹ := by group
        _ = F.b * F.a⁻¹ := by rw [F.a_mul_self]; group
        _ = F.b * F.a := by
              rw [show F.a⁻¹ = F.a from inv_eq_of_mul_eq_one_right F.a_mul_self]
        _ = F.rho⁻¹ := hba
    rw [ha, inv_zpow] at h
    rw [← h, zpow_neg]
  calc F.a * F.rho ^ k = (F.a * F.rho ^ k * F.a⁻¹) * F.a := by group
    _ = F.rho ^ (-k) * F.a := by rw [ha_conj k]

theorem b_mul_rho_zpow (k : ℤ) : F.b * F.rho ^ k = F.rho ^ (-k) * F.b := by
  have hb_conj : ∀ n : ℤ, F.b * F.rho ^ n * F.b⁻¹ = F.rho ^ (-n) := by
    intro n
    have h := conj_zpow (a := F.b) (b := F.rho) (i := n)
    have hb : F.b * F.rho * F.b⁻¹ = F.rho⁻¹ := by
      have hba : F.b * F.a = F.rho⁻¹ := by
        calc F.b * F.a = (F.rho⁻¹ * F.a) * F.a := by rw [F.b_eq]
          _ = F.rho⁻¹ * (F.a * F.a) := by group
          _ = F.rho⁻¹ := by rw [F.a_mul_self, mul_one]
      calc F.b * F.rho * F.b⁻¹ = F.b * (F.a * F.b) * F.b⁻¹ := by rw [OctFrame.rho]
        _ = F.b * F.a := by group
        _ = F.rho⁻¹ := hba
    rw [hb, inv_zpow] at h
    rw [← h, zpow_neg]
  calc F.b * F.rho ^ k = (F.b * F.rho ^ k * F.b⁻¹) * F.b := by group
    _ = F.rho ^ (-k) * F.b := by rw [hb_conj k]

theorem a_comm {x : G} (hx : x ∈ T.U 5) : F.a * x = x * F.a :=
  T.mu_one_comm F.hT F.e1_mem F.e1_ne hx

theorem b_comm {x : G} (hx : x ∈ T.U 4) : F.b * x = x * F.b := by
  have hex : F.e8 * x = x * F.e8 :=
    T.Uprime_comm (j := 8) (k := 4) (by norm_num) (by norm_num) F.e8_mem hx
  have h := (T.lemma212_ii' (by norm_num : 3 ≤ (8 : ℕ)) (i := 8) (j := 4)
    (by norm_num) (T.Uprime_le 8 F.e8_mem) F.e8_ne hx hex).2
  exact h.symm

theorem refl_comm {x : G} (hx : x ∈ T.U 1) :
    F.rho ^ (-4 : ℤ) * F.a * x = x * (F.rho ^ (-4 : ℤ) * F.a) := by
  have ha : F.rho ^ (-4 : ℤ) * F.a = F.rho ^ (-2 : ℤ) * F.a * F.rho ^ (2 : ℤ) := by
    have h := F.a_mul_rho_zpow 2
    calc F.rho ^ (-4 : ℤ) * F.a = F.rho ^ (-2 : ℤ) * (F.rho ^ (-2 : ℤ) * F.a) := by
          rw [← mul_assoc, ← zpow_add]
          norm_num
      _ = F.rho ^ (-2 : ℤ) * (F.a * F.rho ^ (2 : ℤ)) := by rw [h]
      _ = F.rho ^ (-2 : ℤ) * F.a * F.rho ^ (2 : ℤ) := by group
  have hx5 : F.rho ^ (2 : ℤ) * x * (F.rho ^ (2 : ℤ))⁻¹ ∈ T.U 5 := by
    have h := TitsSystem.Moves.conj_mem T (F.moves_rho_zpow 2) (j := 1) hx
    simpa using h
  have hcomm := F.a_comm hx5
  rw [ha, show F.rho ^ (-2 : ℤ) = (F.rho ^ (2 : ℤ))⁻¹ by rw [zpow_neg]]
  calc ((F.rho ^ (2 : ℤ))⁻¹ * F.a * F.rho ^ (2 : ℤ)) * x
      = (F.rho ^ (2 : ℤ))⁻¹ * F.a *
          (F.rho ^ (2 : ℤ) * x * (F.rho ^ (2 : ℤ))⁻¹) * F.rho ^ (2 : ℤ) := by group
    _ = (F.rho ^ (2 : ℤ))⁻¹ * (F.a *
          (F.rho ^ (2 : ℤ) * x * (F.rho ^ (2 : ℤ))⁻¹)) * F.rho ^ (2 : ℤ) := by group
    _ = (F.rho ^ (2 : ℤ))⁻¹ *
          ((F.rho ^ (2 : ℤ) * x * (F.rho ^ (2 : ℤ))⁻¹) * F.a) * F.rho ^ (2 : ℤ) := by
          rw [hcomm]
    _ = x * ((F.rho ^ (2 : ℤ))⁻¹ * F.a * F.rho ^ (2 : ℤ)) := by group

noncomputable def e6 : G := F.rho⁻¹ * F.e8 * F.rho
noncomputable def xo (j : ℤ) (x : G) : G :=
  F.rho ^ ((j - 1) / 2) * x * (F.rho ^ ((j - 1) / 2))⁻¹
noncomputable def xp (j : ℤ) (x : G) : G :=
  F.rho ^ ((j - 4) / 2) * ⁅x, F.e6⁆ * (F.rho ^ ((j - 4) / 2))⁻¹

theorem e6_mem : F.e6 ∈ T.Uprime 6 := by
  have hmv : T.Moves (F.rho⁻¹) (fun j => 1 * j + (-2 : ℤ)) := by
    simpa [sub_eq_add_neg] using TitsSystem.Moves.inv_shift T F.moves_rho
  have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmv (j := 8) F.e8_mem
  simpa [OctFrame.e6, show (1 * 8 + (-2) : ℤ) = 6 by norm_num] using h

theorem e6_ne : F.e6 ≠ 1 := by
  intro h
  apply F.e8_ne
  have h2 : F.rho * F.e6 * F.rho⁻¹ = 1 := by
    have := congrArg (fun y => F.rho * y * F.rho⁻¹) h
    simpa using this
  rw [OctFrame.e6] at h2
  have h3 : F.rho * (F.rho⁻¹ * F.e8 * F.rho) * F.rho⁻¹ = F.e8 := by group
  rwa [h3] at h2

theorem xo_mem {j : ℤ} (hj : Odd j) {x : G} (hx : x ∈ T.U 1) : F.xo j x ∈ T.U j := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (2 * m + 1 - 1) / 2 = m := by
    rw [show 2 * m + 1 - 1 = 2 * m by ring]
    exact Int.mul_ediv_cancel_left m (by norm_num)
  have h := TitsSystem.Moves.conj_mem T (F.moves_rho_zpow m) (j := 1) hx
  simpa [OctFrame.xo, hdiv, show (1 : ℤ) + 2 * m = 2 * m + 1 by ring] using h

theorem xp_mem {j : ℤ} (hj : Even j) {x : G} (hx : x ∈ T.U 1) :
    F.xp j x ∈ T.Uprime j := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (m + m - 4) / 2 = m - 2 := by
    rw [show m + m - 4 = 2 * (m - 2) by ring]
    exact Int.mul_ediv_cancel_left (m - 2) (by norm_num)
  have hy : ⁅x, F.e6⁆ ∈ T.Uprime 4 := T.lemma33_i F.hT hx F.e6_mem
  have hmv : T.Moves (F.rho ^ (m - 2)) (fun j => 1 * j + 2 * (m - 2)) := by
    simpa using F.moves_rho_zpow (m - 2)
  have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmv (j := 4) hy
  simpa [OctFrame.xp, hdiv, show (4 + 2 * (m - 2) : ℤ) = m + m by ring] using h

theorem xo_one (x : G) : F.xo 1 x = x := by
  simp [OctFrame.xo]

theorem xp_four (x : G) : F.xp 4 x = ⁅x, F.e6⁆ := by
  simp [OctFrame.xp]

theorem xo_one_eq (j : ℤ) : F.xo j 1 = 1 := by
  simp [OctFrame.xo]

theorem xp_one_eq (j : ℤ) : F.xp j 1 = 1 := by
  simp [OctFrame.xp]

theorem rho_zpow_conj_xo (k j : ℤ) (x : G) :
    F.rho ^ k * F.xo j x * (F.rho ^ k)⁻¹ = F.xo (j + 2 * k) x := by
  have hdiv : (j + 2 * k - 1) / 2 = (j - 1) / 2 + k := by
    rw [show j + 2 * k - 1 = (j - 1) + k * 2 by ring]
    exact Int.add_mul_ediv_right (j - 1) k (by norm_num : (2 : ℤ) ≠ 0)
  simp only [OctFrame.xo, hdiv]
  rw [show F.rho ^ ((j - 1) / 2 + k) = F.rho ^ k * F.rho ^ ((j - 1) / 2) by
    rw [← zpow_add]
    congr 1
    ring]
  rw [mul_inv_rev]
  group

theorem rho_zpow_conj_xp (k j : ℤ) (x : G) :
    F.rho ^ k * F.xp j x * (F.rho ^ k)⁻¹ = F.xp (j + 2 * k) x := by
  have hdiv : (j + 2 * k - 4) / 2 = (j - 4) / 2 + k := by
    rw [show j + 2 * k - 4 = (j - 4) + k * 2 by ring]
    exact Int.add_mul_ediv_right (j - 4) k (by norm_num : (2 : ℤ) ≠ 0)
  simp only [OctFrame.xp, hdiv]
  rw [show F.rho ^ ((j - 4) / 2 + k) = F.rho ^ k * F.rho ^ ((j - 4) / 2) by
    rw [← zpow_add]
    congr 1
    ring]
  rw [mul_inv_rev]
  group

theorem xo_add_sixteen (j : ℤ) (x : G) : F.xo (j + 16) x = F.xo j x := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := (F.rho_zpow_conj_xo 8 j x).symm
  rw [h8] at h
  simpa using h

theorem xp_add_sixteen (j : ℤ) (x : G) : F.xp (j + 16) x = F.xp j x := by
  have h8 : F.rho ^ (8 : ℤ) = 1 := by
    rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact F.rho_pow_eight
  have h := (F.rho_zpow_conj_xp 8 j x).symm
  rw [h8] at h
  simpa using h

theorem xo_mul (j : ℤ) (x y : G) : F.xo j (x * y) = F.xo j x * F.xo j y := by
  simp only [OctFrame.xo]
  group

theorem xp_mul {x y : G} (hx : x ∈ T.U 1) (hy : y ∈ T.U 1) (j : ℤ) :
    F.xp j (x * y) = F.xp j x * F.xp j y := by
  have hcomm : ⁅x * y, F.e6⁆ = ⁅x, F.e6⁆ * ⁅y, F.e6⁆ :=
    T.lemma33_i_mul F.hT hx hy F.e6_mem
  simp only [OctFrame.xp]
  rw [hcomm]
  group

theorem a_conj_xo {j : ℤ} (hj : Odd j) {x : G} (hx : x ∈ T.U 1) :
    F.a * F.xo j x * F.a⁻¹ = F.xo (10 - j) x := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (2 * m + 1 - 1) / 2 = m := by
    rw [show 2 * m + 1 - 1 = 2 * m by ring]
    exact Int.mul_ediv_cancel_left m (by norm_num)
  have hdiv' : (10 - (2 * m + 1) - 1) / 2 = 4 - m := by
    rw [show 10 - (2 * m + 1) - 1 = 2 * (4 - m) by ring]
    exact Int.mul_ediv_cancel_left (4 - m) (by norm_num)
  have hrefl : F.a * x * F.a⁻¹ = F.rho ^ (4 : ℤ) * x * (F.rho ^ (4 : ℤ))⁻¹ := by
    have h := F.refl_comm hx
    have hc : (F.rho ^ (-4 : ℤ) * F.a) * x * (F.rho ^ (-4 : ℤ) * F.a)⁻¹ = x := by
      rw [h]
      group
    have haeq : F.a = F.rho ^ (4 : ℤ) * (F.rho ^ (-4 : ℤ) * F.a) := by
      rw [← mul_assoc, ← zpow_add]
      norm_num
    calc F.a * x * F.a⁻¹
        = (F.rho ^ (4 : ℤ) * (F.rho ^ (-4 : ℤ) * F.a)) * x *
            (F.rho ^ (4 : ℤ) * (F.rho ^ (-4 : ℤ) * F.a))⁻¹ := by
          conv_lhs => rw [haeq]
      _ = F.rho ^ (4 : ℤ) *
            ((F.rho ^ (-4 : ℤ) * F.a) * x * (F.rho ^ (-4 : ℤ) * F.a)⁻¹) *
            (F.rho ^ (4 : ℤ))⁻¹ := by group
      _ = F.rho ^ (4 : ℤ) * x * (F.rho ^ (4 : ℤ))⁻¹ := by rw [hc]
  have ha_conj : ∀ n : ℤ, F.a * F.rho ^ n * F.a⁻¹ = F.rho ^ (-n) := by
    intro n
    have h := conj_zpow (a := F.a) (b := F.rho) (i := n)
    have ha : F.a * F.rho * F.a⁻¹ = F.rho⁻¹ := by
      have h1 : F.a * F.rho = F.rho⁻¹ * F.a := by simpa using F.a_mul_rho_zpow 1
      calc F.a * F.rho * F.a⁻¹ = (F.rho⁻¹ * F.a) * F.a⁻¹ := by rw [h1]
        _ = F.rho⁻¹ := by group
    rw [ha, inv_zpow] at h
    rw [← h, zpow_neg]
  have ha_m' : F.a * (F.rho ^ m)⁻¹ * F.a⁻¹ = F.rho ^ m := by
    rw [show (F.rho ^ m)⁻¹ = F.rho ^ (-m) by rw [zpow_neg]]
    simpa using ha_conj (-m)
  calc F.a * F.xo (2 * m + 1) x * F.a⁻¹
      = F.a * (F.rho ^ m * x * (F.rho ^ m)⁻¹) * F.a⁻¹ := by
          simp only [OctFrame.xo, hdiv]
    _ = (F.a * F.rho ^ m) * x * (F.rho ^ m)⁻¹ * F.a⁻¹ := by group
    _ = (F.rho ^ (-m) * F.a) * x * (F.rho ^ m)⁻¹ * F.a⁻¹ := by
          rw [F.a_mul_rho_zpow m]
    _ = F.rho ^ (-m) * (F.a * x * F.a⁻¹) *
          (F.a * (F.rho ^ m)⁻¹ * F.a⁻¹) := by group
    _ = F.rho ^ (-m) * (F.rho ^ (4 : ℤ) * x * (F.rho ^ (4 : ℤ))⁻¹) *
          F.rho ^ m := by rw [hrefl, ha_m']
    _ = F.rho ^ (4 - m) * x * (F.rho ^ (4 - m))⁻¹ := by
          rw [show F.rho ^ (-m) *
              (F.rho ^ (4 : ℤ) * x * (F.rho ^ (4 : ℤ))⁻¹) * F.rho ^ m =
              (F.rho ^ (-m) * F.rho ^ (4 : ℤ)) * x *
                (F.rho ^ (-4 : ℤ) * F.rho ^ m) by
            rw [show (F.rho ^ (4 : ℤ))⁻¹ = F.rho ^ (-4 : ℤ) by rw [zpow_neg]]
            group]
          rw [← zpow_add, ← zpow_add]
          rw [show -m + 4 = 4 - m by ring,
            show -4 + m = -(4 - m) by ring, zpow_neg]
    _ = F.xo (10 - (2 * m + 1)) x := by
          simp only [OctFrame.xo, hdiv']

theorem a_conj_xp {j : ℤ} (hj : Even j) {x : G} (hx : x ∈ T.U 1) :
    F.a * F.xp j x * F.a⁻¹ = F.xp (10 - j) x := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (m + m - 4) / 2 = m - 2 := by
    rw [show m + m - 4 = 2 * (m - 2) by ring]
    exact Int.mul_ediv_cancel_left (m - 2) (by norm_num)
  have hdiv' : (10 - (m + m) - 4) / 2 = 3 - m := by
    rw [show 10 - (m + m) - 4 = 2 * (3 - m) by ring]
    exact Int.mul_ediv_cancel_left (3 - m) (by norm_num)
  have hx4mem : F.xp 4 x ∈ T.Uprime 4 := F.xp_mem (by decide : Even (4 : ℤ)) hx
  have hx4U : F.xp 4 x ∈ T.U 4 := T.Uprime_le 4 hx4mem
  have hb4 : F.b * F.xp 4 x * F.b⁻¹ = F.xp 4 x := by
    rw [F.b_comm hx4U]
    group
  have ha4 : F.a * F.xp 4 x * F.a⁻¹ = F.rho * F.xp 4 x * F.rho⁻¹ := by
    have haeq : F.a = F.rho * F.b := by
      rw [F.b_eq]
      group
    calc F.a * F.xp 4 x * F.a⁻¹
        = (F.rho * F.b) * F.xp 4 x * (F.rho * F.b)⁻¹ := by
          conv_lhs => rw [haeq]
      _ = F.rho * (F.b * F.xp 4 x * F.b⁻¹) * F.rho⁻¹ := by group
      _ = F.rho * F.xp 4 x * F.rho⁻¹ := by rw [hb4]
  have ha_conj : ∀ n : ℤ, F.a * F.rho ^ n * F.a⁻¹ = F.rho ^ (-n) := by
    intro n
    have h := conj_zpow (a := F.a) (b := F.rho) (i := n)
    have ha : F.a * F.rho * F.a⁻¹ = F.rho⁻¹ := by
      have h1 : F.a * F.rho = F.rho⁻¹ * F.a := by simpa using F.a_mul_rho_zpow 1
      calc F.a * F.rho * F.a⁻¹ = (F.rho⁻¹ * F.a) * F.a⁻¹ := by rw [h1]
        _ = F.rho⁻¹ := by group
    rw [ha, inv_zpow] at h
    rw [← h, zpow_neg]
  have ha_m' : F.a * (F.rho ^ (m - 2))⁻¹ * F.a⁻¹ = F.rho ^ (m - 2) := by
    rw [show (F.rho ^ (m - 2))⁻¹ = F.rho ^ (-(m - 2)) by rw [zpow_neg]]
    simpa using ha_conj (-(m - 2))
  calc F.a * F.xp (m + m) x * F.a⁻¹
      = F.a * (F.rho ^ (m - 2) * F.xp 4 x * (F.rho ^ (m - 2))⁻¹) * F.a⁻¹ := by
          rw [F.xp_four, OctFrame.xp, hdiv]
    _ = (F.a * F.rho ^ (m - 2)) * F.xp 4 x * (F.rho ^ (m - 2))⁻¹ * F.a⁻¹ := by group
    _ = (F.rho ^ (-(m - 2)) * F.a) * F.xp 4 x * (F.rho ^ (m - 2))⁻¹ * F.a⁻¹ := by
          rw [F.a_mul_rho_zpow (m - 2)]
    _ = F.rho ^ (-(m - 2)) * (F.a * F.xp 4 x * F.a⁻¹) *
          (F.a * (F.rho ^ (m - 2))⁻¹ * F.a⁻¹) := by group
    _ = F.rho ^ (-(m - 2)) * (F.rho * F.xp 4 x * F.rho⁻¹) *
          F.rho ^ (m - 2) := by rw [ha4, ha_m']
    _ = F.rho ^ (1 - (m - 2)) * F.xp 4 x * (F.rho ^ (1 - (m - 2)))⁻¹ := by
          rw [show F.rho ^ (-(m - 2)) * (F.rho * F.xp 4 x * F.rho⁻¹) *
              F.rho ^ (m - 2) =
              (F.rho ^ (-(m - 2)) * F.rho ^ (1 : ℤ)) * F.xp 4 x *
                (F.rho ^ (-1 : ℤ) * F.rho ^ (m - 2)) by
            rw [show F.rho ^ (1 : ℤ) = F.rho by norm_num,
              show F.rho ^ (-1 : ℤ) = F.rho⁻¹ by rw [zpow_neg, zpow_one]]
            group]
          rw [← zpow_add, ← zpow_add]
          rw [show -(m - 2) + 1 = 1 - (m - 2) by ring,
            show -1 + (m - 2) = -(1 - (m - 2)) by ring, zpow_neg]
    _ = F.xp (10 - (m + m)) x := by
          rw [F.xp_four, OctFrame.xp, hdiv']
          rw [show (1 - (m - 2) : ℤ) = 3 - m by ring]

theorem b_conj_xo {j : ℤ} (hj : Odd j) {x : G} (hx : x ∈ T.U 1) :
    F.b * F.xo j x * F.b⁻¹ = F.xo (24 - j) x := by
  have h8 : F.b * F.xo j x * F.b⁻¹ = F.xo (8 - j) x := by
    have ha := F.a_conj_xo hj hx
    calc F.b * F.xo j x * F.b⁻¹
        = (F.rho⁻¹ * F.a) * F.xo j x * (F.rho⁻¹ * F.a)⁻¹ := by
          conv_lhs => rw [F.b_eq]
      _ = F.rho⁻¹ * (F.a * F.xo j x * F.a⁻¹) * (F.rho⁻¹)⁻¹ := by group
      _ = F.rho⁻¹ * F.xo (10 - j) x * (F.rho⁻¹)⁻¹ := by rw [ha]
      _ = F.xo (8 - j) x := by
            have h := F.rho_zpow_conj_xo (-1) (10 - j) x
            rw [show (10 - j + 2 * (-1) : ℤ) = 8 - j by ring] at h
            simpa using h
  calc F.b * F.xo j x * F.b⁻¹ = F.xo (8 - j) x := h8
    _ = F.xo (24 - j) x := by
          rw [show 24 - j = (8 - j) + 16 by ring, F.xo_add_sixteen]

theorem rho_zpow_a_conj_xo (k : ℤ) {j : ℤ} (hj : Odd j) {x : G} (hx : x ∈ T.U 1) :
    F.rho ^ k * F.a * F.xo j x * (F.rho ^ k * F.a)⁻¹ = F.xo (10 + 2 * k - j) x := by
  have ha := F.a_conj_xo hj hx
  have h := F.rho_zpow_conj_xo k (10 - j) x
  calc F.rho ^ k * F.a * F.xo j x * (F.rho ^ k * F.a)⁻¹
      = F.rho ^ k * (F.a * F.xo j x * F.a⁻¹) * (F.rho ^ k)⁻¹ := by group
    _ = F.rho ^ k * F.xo (10 - j) x * (F.rho ^ k)⁻¹ := by rw [ha]
    _ = F.xo (10 - j + 2 * k) x := h
    _ = F.xo (10 + 2 * k - j) x := by
          rw [show 10 - j + 2 * k = 10 + 2 * k - j by ring]

theorem rho_zpow_a_conj_xp (k : ℤ) {j : ℤ} (hj : Even j) {x : G} (hx : x ∈ T.U 1) :
    F.rho ^ k * F.a * F.xp j x * (F.rho ^ k * F.a)⁻¹ = F.xp (10 + 2 * k - j) x := by
  have ha := F.a_conj_xp hj hx
  have h := F.rho_zpow_conj_xp k (10 - j) x
  calc F.rho ^ k * F.a * F.xp j x * (F.rho ^ k * F.a)⁻¹
      = F.rho ^ k * (F.a * F.xp j x * F.a⁻¹) * (F.rho ^ k)⁻¹ := by group
    _ = F.rho ^ k * F.xp (10 - j) x * (F.rho ^ k)⁻¹ := by rw [ha]
    _ = F.xp (10 - j + 2 * k) x := h
    _ = F.xp (10 + 2 * k - j) x := by
          rw [show 10 - j + 2 * k = 10 + 2 * k - j by ring]

theorem comm_e1_e6 : ⁅F.e1, F.e6⁆ = F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ) := by
  have h1 : ⁅F.e1, F.e6⁆ = F.a * F.e6 * F.a⁻¹ := by
    simpa [OctFrame.a] using T.lemma33_i_eq F.hT F.e1_mem F.e1_ne F.e6_mem
  have hρa : F.a * F.rho⁻¹ = F.rho * F.a := by
    simpa using F.a_mul_rho_zpow (-1)
  have hρa' : F.rho * F.a⁻¹ = F.a⁻¹ * F.rho⁻¹ := by
    have ha : F.a * F.rho * F.a⁻¹ = F.rho⁻¹ := by
      have h1' : F.a * F.rho = F.rho⁻¹ * F.a := by simpa using F.a_mul_rho_zpow 1
      calc F.a * F.rho * F.a⁻¹ = (F.rho⁻¹ * F.a) * F.a⁻¹ := by rw [h1']
        _ = F.rho⁻¹ := by group
    calc F.rho * F.a⁻¹ = F.a⁻¹ * (F.a * F.rho * F.a⁻¹) := by group
      _ = F.a⁻¹ * F.rho⁻¹ := by rw [ha]
  have hae8 : F.a * F.e8 * F.a⁻¹ = F.rho * (F.b * F.e8 * F.b⁻¹) * F.rho⁻¹ := by
    have haeq : F.a = F.rho * F.b := by
      rw [F.b_eq]
      group
    calc F.a * F.e8 * F.a⁻¹
        = (F.rho * F.b) * F.e8 * (F.rho * F.b)⁻¹ := by conv_lhs => rw [haeq]
      _ = F.rho * (F.b * F.e8 * F.b⁻¹) * F.rho⁻¹ := by group
  have hρ4b : F.rho ^ (4 : ℤ) * F.b = F.rho ^ (2 : ℤ) * F.b * (F.rho ^ (2 : ℤ))⁻¹ := by
    have hb2 : F.b * (F.rho ^ (2 : ℤ))⁻¹ = F.rho ^ (2 : ℤ) * F.b := by
      simpa using F.b_mul_rho_zpow (-2)
    calc F.rho ^ (4 : ℤ) * F.b = F.rho ^ (2 : ℤ) * (F.rho ^ (2 : ℤ) * F.b) := by
          rw [show F.rho ^ (4 : ℤ) = F.rho ^ (2 : ℤ) * F.rho ^ (2 : ℤ) by
            rw [← zpow_add]; norm_num]
          group
      _ = F.rho ^ (2 : ℤ) * (F.b * (F.rho ^ (2 : ℤ))⁻¹) := by rw [← hb2]
      _ = F.rho ^ (2 : ℤ) * F.b * (F.rho ^ (2 : ℤ))⁻¹ := by group
  have hx4 : F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ) ∈ T.U 4 := by
    have h := TitsSystem.Moves.conj_mem T (F.moves_rho_zpow (-2)) (j := 8) (T.Uprime_le 8 F.e8_mem)
    simpa [show (8 : ℤ) + 2 * (-2) = 4 by norm_num,
      show (F.rho ^ (-2 : ℤ))⁻¹ = F.rho ^ (2 : ℤ) by rw [zpow_neg, inv_inv]] using h
  have hb4 : F.b * (F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ)) * F.b⁻¹ =
      F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ) := by
    rw [F.b_comm hx4]
    group
  have hcform : (F.rho ^ (4 : ℤ) * F.b) * F.e8 * (F.rho ^ (4 : ℤ) * F.b)⁻¹ =
      F.rho ^ (2 : ℤ) *
        (F.b * (F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ)) * F.b⁻¹) *
        F.rho ^ (-2 : ℤ) := by
    rw [hρ4b]
    rw [show (F.rho ^ (2 : ℤ) * F.b * (F.rho ^ (2 : ℤ))⁻¹)⁻¹ =
        F.rho ^ (2 : ℤ) * F.b⁻¹ * (F.rho ^ (2 : ℤ))⁻¹ by group]
    rw [show (F.rho ^ (2 : ℤ))⁻¹ = F.rho ^ (-2 : ℤ) by rw [zpow_neg]]
    group
  have hc : (F.rho ^ (4 : ℤ) * F.b) * F.e8 * (F.rho ^ (4 : ℤ) * F.b)⁻¹ = F.e8 := by
    rw [hcform, hb4]
    calc F.rho ^ (2 : ℤ) * (F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ)) *
          F.rho ^ (-2 : ℤ)
        = (F.rho ^ (2 : ℤ) * F.rho ^ (-2 : ℤ)) * F.e8 *
            (F.rho ^ (2 : ℤ) * F.rho ^ (-2 : ℤ)) := by group
      _ = F.e8 := by
            rw [show F.rho ^ (2 : ℤ) * F.rho ^ (-2 : ℤ) = 1 by
              rw [← zpow_add]; norm_num]
            group
  have hb_e8 : F.b * F.e8 * F.b⁻¹ = F.rho ^ (-4 : ℤ) * F.e8 * F.rho ^ (4 : ℤ) := by
    have hconj : F.rho ^ (4 : ℤ) * (F.b * F.e8 * F.b⁻¹) * (F.rho ^ (4 : ℤ))⁻¹ = F.e8 := by
      calc F.rho ^ (4 : ℤ) * (F.b * F.e8 * F.b⁻¹) * (F.rho ^ (4 : ℤ))⁻¹
          = (F.rho ^ (4 : ℤ) * F.b) * F.e8 * (F.rho ^ (4 : ℤ) * F.b)⁻¹ := by group
        _ = F.e8 := hc
    calc F.b * F.e8 * F.b⁻¹
        = (F.rho ^ (4 : ℤ))⁻¹ *
            (F.rho ^ (4 : ℤ) * (F.b * F.e8 * F.b⁻¹) * (F.rho ^ (4 : ℤ))⁻¹) *
            F.rho ^ (4 : ℤ) := by group
      _ = (F.rho ^ (4 : ℤ))⁻¹ * F.e8 * F.rho ^ (4 : ℤ) := by rw [hconj]
      _ = F.rho ^ (-4 : ℤ) * F.e8 * F.rho ^ (4 : ℤ) := by
          rw [show (F.rho ^ (4 : ℤ))⁻¹ = F.rho ^ (-4 : ℤ) by rw [zpow_neg]]
  have hmain : ⁅F.e1, F.e6⁆ = F.rho ^ (2 : ℤ) * (F.b * F.e8 * F.b⁻¹) *
      (F.rho ^ (2 : ℤ))⁻¹ := by
    calc ⁅F.e1, F.e6⁆ = F.a * F.e6 * F.a⁻¹ := h1
      _ = F.a * (F.rho⁻¹ * F.e8 * F.rho) * F.a⁻¹ := by rw [OctFrame.e6]
      _ = (F.a * F.rho⁻¹) * F.e8 * (F.rho * F.a⁻¹) := by group
      _ = (F.rho * F.a) * F.e8 * (F.a⁻¹ * F.rho⁻¹) := by rw [hρa, hρa']
      _ = F.rho * (F.a * F.e8 * F.a⁻¹) * F.rho⁻¹ := by group
      _ = F.rho * (F.rho * (F.b * F.e8 * F.b⁻¹) * F.rho⁻¹) * F.rho⁻¹ := by rw [hae8]
      _ = F.rho ^ (2 : ℤ) * (F.b * F.e8 * F.b⁻¹) * (F.rho ^ (2 : ℤ))⁻¹ := by
            rw [show F.rho ^ (2 : ℤ) = F.rho * F.rho by
              rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, zpow_add, zpow_one]]
            group
  rw [hmain, hb_e8, show (F.rho ^ (2 : ℤ))⁻¹ = F.rho ^ (-2 : ℤ) by rw [zpow_neg]]
  calc F.rho ^ (2 : ℤ) * (F.rho ^ (-4 : ℤ) * F.e8 * F.rho ^ (4 : ℤ)) *
        F.rho ^ (-2 : ℤ)
      = (F.rho ^ (2 : ℤ) * F.rho ^ (-4 : ℤ)) * F.e8 *
          (F.rho ^ (4 : ℤ) * F.rho ^ (-2 : ℤ)) := by group
    _ = F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ) := by
          rw [← zpow_add, ← zpow_add]
          norm_num

theorem xp_six_e1 : F.xp 6 F.e1 = F.e6 := by
  have h2 : F.rho ^ (2 : ℤ) = F.rho * F.rho := by
    rw [show (2 : ℤ) = (1 : ℤ) + (1 : ℤ) by norm_num, zpow_add, zpow_one]
  have hm2 : F.rho ^ (-2 : ℤ) = (F.rho * F.rho)⁻¹ := by
    rw [zpow_neg, h2]
  rw [show F.xp 6 F.e1 = F.rho * ⁅F.e1, F.e6⁆ * F.rho⁻¹ by simp [OctFrame.xp]]
  rw [F.comm_e1_e6, OctFrame.e6, h2, hm2]
  group

theorem rho_eq : F.rho = T.mu 5 (F.xo 5 F.e1) * T.mu 4 (F.xp 4 F.e1) := by
  have h5 : T.mu 5 (F.xo 5 F.e1) = F.rho ^ (4 : ℤ) * F.a := by
    have hmv : T.Moves (F.rho ^ (2 : ℤ)) (fun j => 1 * j + 4) := by
      simpa using F.moves_rho_zpow 2
    have hm := (T.mu_conj (by norm_num : 3 ≤ (8 : ℕ)) (g := F.rho ^ (2 : ℤ))
      (ε := 1) (c := 4) (Or.inl rfl) hmv (i := 1) (u := F.e1) F.e1_mem F.e1_ne).1
    have hxo : F.xo 5 F.e1 = F.rho ^ (2 : ℤ) * F.e1 * (F.rho ^ (2 : ℤ))⁻¹ := by
      simp [OctFrame.xo]
    rw [hxo, show (5 : ℤ) = 1 * 1 + 4 by norm_num, hm]
    rw [show (F.rho ^ (2 : ℤ))⁻¹ = F.rho ^ (-2 : ℤ) by rw [zpow_neg], mul_assoc]
    change F.rho ^ (2 : ℤ) * (F.a * F.rho ^ (-2 : ℤ)) = F.rho ^ (4 : ℤ) * F.a
    rw [F.a_mul_rho_zpow (-2)]
    rw [show F.rho ^ (4 : ℤ) = F.rho ^ (2 : ℤ) * F.rho ^ (2 : ℤ) by
      rw [← zpow_add]; norm_num]
    group
  have h4 : T.mu 4 (F.xp 4 F.e1) = F.rho ^ (-4 : ℤ) * F.b := by
    have hmv : T.Moves (F.rho ^ (-2 : ℤ)) (fun j => 1 * j + (-4)) := by
      simpa using F.moves_rho_zpow (-2)
    have hm := (T.mu_conj (by norm_num : 3 ≤ (8 : ℕ)) (g := F.rho ^ (-2 : ℤ))
      (ε := 1) (c := -4) (Or.inl rfl) hmv (i := 8) (u := F.e8)
      (T.Uprime_le 8 F.e8_mem) F.e8_ne).1
    have hxpe : F.xp 4 F.e1 = F.rho ^ (-2 : ℤ) * F.e8 * F.rho ^ (2 : ℤ) := by
      simpa [OctFrame.xp] using F.comm_e1_e6
    have hinv : F.rho ^ (2 : ℤ) = (F.rho ^ (-2 : ℤ))⁻¹ := by
      rw [zpow_neg, inv_inv]
    rw [hxpe, show (4 : ℤ) = 1 * 8 + (-4) by norm_num, hinv, hm]
    rw [show (-(1 * 8 + -4) : ℤ) = -4 by norm_num,
      show (F.rho ^ (-2 : ℤ))⁻¹ = F.rho ^ (2 : ℤ) by rw [zpow_neg, inv_inv], mul_assoc]
    change F.rho ^ (-2 : ℤ) * (F.b * F.rho ^ (2 : ℤ)) = F.rho ^ (-4 : ℤ) * F.b
    rw [F.b_mul_rho_zpow 2]
    rw [show F.rho ^ (-4 : ℤ) = F.rho ^ (-2 : ℤ) * F.rho ^ (-2 : ℤ) by
      rw [← zpow_add]; norm_num]
    group
  rw [h5, h4]
  symm
  calc (F.rho ^ (4 : ℤ) * F.a) * (F.rho ^ (-4 : ℤ) * F.b)
      = F.rho ^ (4 : ℤ) * (F.a * F.rho ^ (-4 : ℤ)) * F.b := by group
    _ = F.rho ^ (4 : ℤ) * (F.rho ^ (4 : ℤ) * F.a) * F.b := by
          rw [F.a_mul_rho_zpow (-4)]
          rw [show (- -4 : ℤ) = 4 by norm_num]
    _ = F.rho ^ (8 : ℤ) * F.a * F.b := by
          rw [show F.rho ^ (8 : ℤ) = F.rho ^ (4 : ℤ) * F.rho ^ (4 : ℤ) by
            rw [← zpow_add]; norm_num]
          group
    _ = F.rho := by
          have h8 : F.rho ^ (8 : ℤ) = 1 := by
            rw [show (8 : ℤ) = ((8 : ℕ) : ℤ) by norm_num, zpow_natCast]
            exact F.rho_pow_eight
          rw [h8, one_mul]
          rfl

theorem xo_bijOn {j : ℤ} (hj : Odd j) : Set.BijOn (F.xo j) (T.U 1 : Set G) (T.U j : Set G) := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (2 * m + 1 - 1) / 2 = m := by
    rw [show 2 * m + 1 - 1 = 2 * m by ring]
    exact Int.mul_ediv_cancel_left m (by norm_num)
  refine ⟨fun x hx => F.xo_mem ⟨m, rfl⟩ hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact (MulAut.conj (F.rho ^ m)).injective (by simpa [OctFrame.xo, hdiv] using hxy)
  · intro y hy
    refine ⟨F.rho ^ (-m) * y * F.rho ^ m, ?_, ?_⟩
    · have h := TitsSystem.Moves.conj_mem T (F.moves_rho_zpow (-m)) (j := 2 * m + 1) hy
      simpa [show (2 * m + 1) + 2 * (-m) = 1 by ring,
        show (F.rho ^ (-m : ℤ))⁻¹ = F.rho ^ m by rw [zpow_neg, inv_inv]] using h
    · calc F.xo (2 * m + 1) (F.rho ^ (-m) * y * F.rho ^ m)
          = F.rho ^ m * (F.rho ^ (-m) * y * F.rho ^ m) * (F.rho ^ m)⁻¹ := by
              simp only [OctFrame.xo, hdiv]
        _ = y := by
              rw [show F.rho ^ (-m : ℤ) = (F.rho ^ m)⁻¹ by rw [zpow_neg]]
              group

theorem xp_bijOn {j : ℤ} (hj : Even j) :
    Set.BijOn (F.xp j) (T.U 1 : Set G) (T.Uprime j : Set G) := by
  obtain ⟨m, hm⟩ := hj
  rw [hm]
  have hdiv : (m + m - 4) / 2 = m - 2 := by
    rw [show m + m - 4 = 2 * (m - 2) by ring]
    exact Int.mul_ediv_cancel_left (m - 2) (by norm_num)
  refine ⟨fun x hx => F.xp_mem ⟨m, rfl⟩ hx, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxy' : F.rho ^ ((m + m - 4) / 2) * ⁅x, F.e6⁆ *
          (F.rho ^ ((m + m - 4) / 2))⁻¹ =
        F.rho ^ ((m + m - 4) / 2) * ⁅y, F.e6⁆ *
          (F.rho ^ ((m + m - 4) / 2))⁻¹ := by
      simpa [OctFrame.xp] using hxy
    have hc : ⁅x, F.e6⁆ = ⁅y, F.e6⁆ :=
      (MulAut.conj (F.rho ^ ((m + m - 4) / 2))).injective hxy'
    exact T.lemma33_i_inj F.hT F.e6_mem F.e6_ne hx hy hc
  · intro y hy
    let k := m - 2
    have hk : (m + m - 4) / 2 = k := by
      simpa [k] using hdiv
    have hy4 : F.rho ^ (-k) * y * F.rho ^ k ∈ T.Uprime 4 := by
      have hmv : T.Moves (F.rho ^ (-k)) (fun j => 1 * j + 2 * (-k)) := by
        simpa using F.moves_rho_zpow (-k)
      have h := TitsSystem.Moves.conj_mem_Uprime T (Or.inl rfl) hmv (j := m + m) hy
      convert h using 2
      · dsimp [k]
        ring
      · rw [show (F.rho ^ (-k))⁻¹ = F.rho ^ k by rw [zpow_neg, inv_inv]]
    have hnorm : (T.shift (-2)).Normalized := F.hT.shift ⟨-1, by ring⟩
    have he6 : F.e6 ∈ (T.shift (-2)).Uprime 8 := by
      rw [TitsSystem.Uprime_shift]
      simpa using F.e6_mem
    have hy4' : F.rho ^ (-k) * y * F.rho ^ k ∈ (T.shift (-2)).Uprime 6 := by
      rw [TitsSystem.Uprime_shift]
      simpa using hy4
    obtain ⟨u, hu, hcomm⟩ := (T.shift (-2)).lemma39_surj hnorm he6 F.e6_ne hy4'
    have hu1 : u ∈ T.U 1 := by
      have h := hu
      rw [shift_U] at h
      simpa using h
    refine ⟨u, hu1, ?_⟩
    have hxp : F.xp (m + m) u = F.rho ^ k * ⁅u, F.e6⁆ * (F.rho ^ k)⁻¹ := by
      simp only [OctFrame.xp, hk]
    rw [hxp, hcomm]
    rw [show F.rho ^ k * (F.rho ^ (-k) * y * F.rho ^ k) * (F.rho ^ k)⁻¹ = y by
      rw [show F.rho ^ (-k) = (F.rho ^ k)⁻¹ by rw [zpow_neg]]
      group]

end OctFrame

end CFSG.GH74.Tits83
