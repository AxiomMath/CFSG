module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

@[expose] def a10gX : Finset (Fin 10) := {0, 1, 2, 3, 4}

@[expose] def a10gY : Finset (Fin 10) := a10gXᶜ

theorem a10g_mem_gX {x : Fin 10} : x ∈ a10gX ↔ x.val < 5 := by
  revert x; decide

theorem a10g_mem_gY {x : Fin 10} : x ∈ a10gY ↔ 5 ≤ x.val := by
  revert x; decide

theorem a10g_card_gX : a10gX.card = 5 := by decide

theorem a10g_card_gY : a10gY.card = 5 := by decide

theorem a10g_compl_gX : a10gXᶜ = a10gY := rfl

theorem a10g_compl_gY : a10gYᶜ = a10gX := compl_compl _

theorem a10g_zero_mem_gX : (0 : Fin 10) ∈ a10gX := by decide

theorem a10g_five_mem_gY : (5 : Fin 10) ∈ a10gY := by decide

theorem a10g_mem_smul {g : A10} {B : Finset (Fin 10)} {y : Fin 10} :
    y ∈ g • B ↔ (g : Perm (Fin 10))⁻¹ y ∈ B := by
  rw [← Finset.inv_smul_mem_iff]
  rfl

theorem a10g_smul_compl (g : A10) (B : Finset (Fin 10)) : g • Bᶜ = (g • B)ᶜ := by
  rw [Finset.compl_eq_univ_sdiff, Finset.compl_eq_univ_sdiff, Finset.smul_finset_sdiff,
    Finset.smul_finset_univ]

@[expose] def a10gHat : Subgroup A10 where
  carrier := {g | g • a10gX = a10gX ∨ g • a10gX = a10gY}
  one_mem' := Or.inl (one_smul _ _)
  mul_mem' := by
    rintro g h (hg | hg) (hh | hh)
    · left; rw [mul_smul, hh, hg]
    · right; rw [mul_smul, hh, ← a10g_compl_gX, a10g_smul_compl, hg]
    · right; rw [mul_smul, hh, hg]
    · left; rw [mul_smul, hh, ← a10g_compl_gX, a10g_smul_compl, hg, a10g_compl_gY]
  inv_mem' := by
    rintro g (hg | hg)
    · left; rw [inv_smul_eq_iff]; exact hg.symm
    · right
      rw [inv_smul_eq_iff, ← a10g_compl_gX, a10g_smul_compl, hg, a10g_compl_gY]

theorem a10g_mem_hat {g : A10} : g ∈ a10gHat ↔ g • a10gX = a10gX ∨ g • a10gX = a10gY := Iff.rfl

@[expose] def a10gGamma : Subgroup A10 :=
  Subgroup.closure {g : A10 | ∃ B : Subgroup A10, B ≤ S₀ ∧ B ≠ ⊥ ∧ g ∈ normalizer (B : Set A10)}

theorem a10g_a₁_smul : (a₁ : A10) • a10gX = a10gX := by decide

theorem a10g_a₂_smul : (a₂ : A10) • a10gX = a10gX := by decide

theorem a10g_S₀_smul {s : A10} (hs : s ∈ S₀) : s • a10gX = a10gX := by
  obtain ⟨i, j, rfl⟩ := mem_S₀.1 hs
  have h1 : a₁ ∈ MulAction.stabilizer A10 a10gX := a10g_a₁_smul
  have h2 : a₂ ∈ MulAction.stabilizer A10 a10gX := a10g_a₂_smul
  exact MulAction.mem_stabilizer_iff.1
    (Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 i) (Subgroup.pow_mem _ h2 j))

theorem a10g_pres_iff {c : A10} (hc : c • a10gX = a10gX) (p : Fin 10) : c • p ∈ a10gX ↔ p ∈ a10gX := by
  have := Finset.smul_mem_smul_finset_iff (s := a10gX) c (b := p)
  rwa [hc] at this

theorem a10g_conn_X : ∀ i j : Fin 5, i ≠ 0 → ∀ x y : Fin 10, x.val < 5 → y.val < 5 →
    ∃ m : Fin 5, (((a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ)) ^ (m : ℕ) : A10) : Perm (Fin 10)) x = y := by
  decide +kernel

theorem a10g_conn_Y : ∀ i j : Fin 5, j ≠ 0 → ∀ x y : Fin 10, 5 ≤ x.val → 5 ≤ y.val →
    ∃ m : Fin 5, (((a₁ ^ (i : ℕ) * a₂ ^ (j : ℕ)) ^ (m : ℕ) : A10) : Perm (Fin 10)) x = y := by
  decide +kernel

theorem a10g_conn {b : A10} (hb : b ∈ S₀) (hb1 : b ≠ 1) :
    (∀ x ∈ a10gX, ∀ y ∈ a10gX, ∃ m : ℕ, (b ^ m) • x = y) ∨
      (∀ x ∈ a10gY, ∀ y ∈ a10gY, ∃ m : ℕ, (b ^ m) • x = y) := by
  obtain ⟨i, j, rfl⟩ := mem_S₀.1 hb
  have hi : a₁ ^ i = a₁ ^ (i % 5) := pow_eq_pow_mod i a₁_pow
  have hj : a₂ ^ j = a₂ ^ (j % 5) := pow_eq_pow_mod j a₂_pow
  by_cases h0 : i % 5 = 0
  · right
    have hj0 : j % 5 ≠ 0 := by
      intro hj0
      apply hb1
      rw [hi, hj, h0, hj0]
      simp
    intro x hx y hy
    obtain ⟨m, hm⟩ := a10g_conn_Y ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ (by simpa [Fin.ext_iff] using hj0) x y
      (a10g_mem_gY.1 hx) (a10g_mem_gY.1 hy)
    refine ⟨m, ?_⟩
    rw [hi, hj]
    exact hm
  · left
    intro x hx y hy
    obtain ⟨m, hm⟩ := a10g_conn_X ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ (by simpa [Fin.ext_iff] using h0) x y
      (a10g_mem_gX.1 hx) (a10g_mem_gX.1 hy)
    refine ⟨m, ?_⟩
    rw [hi, hj]
    exact hm

theorem a10g_hat_of_side {g : A10} {Z : Finset (Fin 10)} (hZ : Z = a10gX ∨ Z = a10gY) (x₀ : Fin 10)
    (h : ∀ x ∈ Z, (g • x ∈ a10gX ↔ g • x₀ ∈ a10gX)) (hx₀ : x₀ ∈ Z) : g ∈ a10gHat := by
  have hZc : Z.card = 5 := by
    rcases hZ with rfl | rfl
    exacts [a10g_card_gX, a10g_card_gY]
  have hgZ : g • Z = a10gX ∨ g • Z = a10gY := by
    by_cases hx : g • x₀ ∈ a10gX
    · left
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨x, hxZ, rfl⟩ := Finset.mem_smul_finset.1 hz
        exact (h x hxZ).2 hx
      · rw [Finset.card_smul_finset, hZc, a10g_card_gX]
    · right
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨x, hxZ, rfl⟩ := Finset.mem_smul_finset.1 hz
        rw [← a10g_compl_gX, Finset.mem_compl]
        intro hmem
        exact hx ((h x hxZ).1 hmem)
      · rw [Finset.card_smul_finset, hZc, a10g_card_gY]
  rcases hZ with rfl | rfl
  · exact hgZ
  · rcases hgZ with h1 | h1
    · right
      rw [← a10g_compl_gY, a10g_smul_compl, h1, a10g_compl_gX]
    · left
      rw [← a10g_compl_gY, a10g_smul_compl, h1, a10g_compl_gY]

theorem a10g_hat_of_conn {g b : A10} (hpow : ∀ m : ℕ, (g * b * g⁻¹) ^ m ∈ S₀)
    {Z : Finset (Fin 10)} (hZ : Z = a10gX ∨ Z = a10gY) (x₀ : Fin 10) (hx₀ : x₀ ∈ Z)
    (hconn : ∀ x ∈ Z, ∃ m : ℕ, (b ^ m) • x₀ = x) : g ∈ a10gHat := by
  refine a10g_hat_of_side hZ x₀ (fun x hx => ?_) hx₀
  obtain ⟨m, hm⟩ := hconn x hx
  have h1 : g • x = ((g * b * g⁻¹) ^ m) • (g • x₀) := by
    rw [← mul_smul, conj_pow, ← hm, ← mul_smul, mul_assoc, mul_assoc, inv_mul_cancel,
      mul_one, mul_smul]
  rw [h1]
  exact a10g_pres_iff (a10g_S₀_smul (hpow m)) _

theorem a10g_gamma_le_hat : a10gGamma ≤ a10gHat := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨B, hBS, hB1, hg⟩
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hcB : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hg b).1 hbB
  have hpow : ∀ m : ℕ, (g * b * g⁻¹) ^ m ∈ S₀ := fun m => hBS (B.pow_mem hcB m)
  rcases a10g_conn (hBS hbB) hb1' with hX | hY
  · exact a10g_hat_of_conn hpow (Or.inl rfl) 0 a10g_zero_mem_gX
      (fun x hx => hX 0 a10g_zero_mem_gX x hx)
  · exact a10g_hat_of_conn hpow (Or.inr rfl) 5 a10g_five_mem_gY
      (fun x hx => hY 5 a10g_five_mem_gY x hx)

theorem a10g_decomp (g : Perm (Fin 10)) (h : ∀ p, g p ∈ a10gX ↔ p ∈ a10gX) :
    ∃ α β : Perm (Fin 10), g = α * β ∧ (∀ y ∈ a10gY, α y = y) ∧ (∀ x ∈ a10gX, β x = x) := by
  classical
  let α : Perm (Fin 10) := Equiv.Perm.ofSubtype (g.subtypePerm (p := fun z => z ∈ a10gX) h)
  have hα1 : ∀ x ∈ a10gX, α x = g x := by
    intro x hx
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    rfl
  have hα2 : ∀ y, y ∉ a10gX → α y = y := fun y hy => Equiv.Perm.ofSubtype_apply_of_not_mem _ hy
  refine ⟨α, α⁻¹ * g, by simp, fun y hy => hα2 y ?_, fun x hx => ?_⟩
  · rw [← a10g_compl_gX] at hy
    exact Finset.mem_compl.1 hy
  · rw [Perm.mul_apply, ← hα1 x hx]
    simp

theorem a10g_a₂_fix : ∀ x ∈ a10gX, ((a₂ : A10) : Perm (Fin 10)) x = x := by decide

theorem a10g_a₁_fix : ∀ y ∈ a10gY, ((a₁ : A10) : Perm (Fin 10)) y = y := by decide

theorem a10g_S₀_ne_bot : S₀ ≠ ⊥ := by
  intro h
  apply a₁_ne
  have : a₁ ∈ S₀ := a₁_mem
  rw [h] at this
  exact (Subgroup.mem_bot).1 this

theorem a10g_mem_gamma_of_normalizes {B : Subgroup A10} (hB : B ≤ S₀) (hB1 : B ≠ ⊥) {g : A10}
    (hg : g ∈ normalizer (B : Set A10)) : g ∈ a10gGamma :=
  Subgroup.subset_closure ⟨B, hB, hB1, hg⟩

theorem a10g_gamma_mem_of_fixY {α : A10} (hα : ∀ y ∈ a10gY, (α : Perm (Fin 10)) y = y) :
    α ∈ a10gGamma := by
  have hdisj : Equiv.Perm.Disjoint (α : Perm (Fin 10)) (a₂ : Perm (Fin 10)) := by
    intro x
    by_cases hx : x ∈ a10gX
    · exact Or.inr (a10g_a₂_fix x hx)
    · exact Or.inl (hα x (by rw [← a10g_compl_gX]; exact Finset.mem_compl.2 hx))
  have hcomm : Commute α a₂ := Subtype.ext hdisj.commute.eq
  have hN : α ∈ normalizer ((zpowers a₂ : Subgroup A10) : Set A10) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hcomm.symm.zpow_left k).eq
  exact a10g_mem_gamma_of_normalizes (zpowers_le.2 a₂_mem)
    (fun h => a₂_ne (Subgroup.zpowers_eq_bot.1 h)) hN

theorem a10g_gamma_mem_of_fixX {β : A10} (hβ : ∀ x ∈ a10gX, (β : Perm (Fin 10)) x = x) :
    β ∈ a10gGamma := by
  have hdisj : Equiv.Perm.Disjoint (β : Perm (Fin 10)) (a₁ : Perm (Fin 10)) := by
    intro x
    by_cases hx : x ∈ a10gX
    · exact Or.inl (hβ x hx)
    · exact Or.inr (a10g_a₁_fix x (by rw [← a10g_compl_gX]; exact Finset.mem_compl.2 hx))
  have hcomm : Commute β a₁ := Subtype.ext hdisj.commute.eq
  have hN : β ∈ normalizer ((zpowers a₁ : Subgroup A10) : Set A10) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hcomm.symm.zpow_left k).eq
  exact a10g_mem_gamma_of_normalizes (zpowers_le.2 a₁_mem)
    (fun h => a₁_ne (Subgroup.zpowers_eq_bot.1 h)) hN

theorem a10g_ν₀_mem_gamma : (ν₀ : A10) ∈ a10gGamma :=
  a10g_mem_gamma_of_normalizes le_rfl a10g_S₀_ne_bot ν₀_mem

theorem a10g_ν₂_mem_gamma : (ν₂ : A10) ∈ a10gGamma :=
  a10g_mem_gamma_of_normalizes le_rfl a10g_S₀_ne_bot (mem_normalizer_of_mem_list (by simp))

theorem a10g_g₁_sign : sign g₁ = -1 := by decide

theorem a10g_g₂_sign : sign g₂ = -1 := by decide

theorem a10g_g₁_fix : ∀ y ∈ a10gY, g₁ y = y := by decide

theorem a10g_g₂_fix : ∀ x ∈ a10gX, g₂ x = x := by decide

theorem a10g_ν₀_coe : ((ν₀ : A10) : Perm (Fin 10)) = g₁ * g₂ := by decide

theorem a10g_hat_stab_le_gamma {g : A10} (hg : g • a10gX = a10gX) : g ∈ a10gGamma := by
  have hpres : ∀ p, (g : Perm (Fin 10)) p ∈ a10gX ↔ p ∈ a10gX := a10g_pres_iff hg
  obtain ⟨α, β, hgαβ, hαY, hβX⟩ := a10g_decomp (g : Perm (Fin 10)) hpres
  have hsg : sign (g : Perm (Fin 10)) = 1 := mem_alternatingGroup.1 g.2
  have hsab : sign α * sign β = 1 := by rw [← map_mul, ← hgαβ]; exact hsg
  rcases Int.units_eq_one_or (sign α) with hα | hα
  · have hβ : sign β = 1 := by rw [hα, one_mul] at hsab; exact hsab
    have e : g = (⟨α, mem_alternatingGroup.2 hα⟩ : A10) * ⟨β, mem_alternatingGroup.2 hβ⟩ :=
      Subtype.ext hgαβ
    rw [e]
    exact Subgroup.mul_mem _ (a10g_gamma_mem_of_fixY hαY) (a10g_gamma_mem_of_fixX hβX)
  · have hβ : sign β = -1 := by
      rcases Int.units_eq_one_or (sign β) with h | h
      · rw [hα, h] at hsab; exact absurd hsab (by decide)
      · exact h
    obtain ⟨α₁, hα₁⟩ : ∃ a : Perm (Fin 10), a = α * g₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨β₁, hβ₁⟩ : ∃ b : Perm (Fin 10), b = g₂⁻¹ * β := ⟨_, rfl⟩
    have hsα₁ : sign α₁ = 1 := by
      rw [hα₁, map_mul, map_inv, hα, a10g_g₁_sign]; decide
    have hsβ₁ : sign β₁ = 1 := by
      rw [hβ₁, map_mul, map_inv, hβ, a10g_g₂_sign]; decide
    have hα₁Y : ∀ y ∈ a10gY, α₁ y = y := by
      intro y hy
      rw [hα₁, Perm.mul_apply]
      have : g₁⁻¹ y = y := Perm.inv_eq_iff_eq.2 (a10g_g₁_fix y hy).symm
      rw [this, hαY y hy]
    have hβ₁X : ∀ x ∈ a10gX, β₁ x = x := by
      intro x hx
      rw [hβ₁, Perm.mul_apply, hβX x hx]
      exact Perm.inv_eq_iff_eq.2 (a10g_g₂_fix x hx).symm
    have e : g = (⟨α₁, mem_alternatingGroup.2 hsα₁⟩ : A10) * ν₀ *
        ⟨β₁, mem_alternatingGroup.2 hsβ₁⟩ := by
      apply Subtype.ext
      show (g : Perm (Fin 10)) = α₁ * ((ν₀ : A10) : Perm (Fin 10)) * β₁
      rw [a10g_ν₀_coe, hgαβ, hα₁, hβ₁]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (a10g_gamma_mem_of_fixY hα₁Y) a10g_ν₀_mem_gamma)
      (a10g_gamma_mem_of_fixX hβ₁X)

theorem a10g_ν₂_smul : (ν₂ : A10) • a10gX = a10gY := by decide

theorem a10g_hat_le_gamma : a10gHat ≤ a10gGamma := by
  intro g hg
  rcases a10g_mem_hat.1 hg with h | h
  · exact a10g_hat_stab_le_gamma h
  · have h1 : (ν₂ : A10)⁻¹ • a10gX = a10gY := by
      rw [inv_smul_eq_iff, ← a10g_compl_gX, a10g_smul_compl, a10g_ν₂_smul, a10g_compl_gY]
    have h' : (g * (ν₂ : A10)⁻¹) • a10gX = a10gX := by
      rw [mul_smul, h1, ← a10g_compl_gX, a10g_smul_compl, h, a10g_compl_gY]
    have := Subgroup.mul_mem _ (a10g_hat_stab_le_gamma h') a10g_ν₂_mem_gamma
    simpa using this

theorem a10g_gamma_eq_hat : a10gGamma = a10gHat :=
  le_antisymm a10g_gamma_le_hat a10g_hat_le_gamma

theorem a10g_exists_perm_fiber {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (f f' : α → β)
    (h : ∀ b, (Finset.univ.filter (fun a => f a = b)).card =
      (Finset.univ.filter (fun a => f' a = b)).card) :
    ∃ σ : Perm α, ∀ a, f' (σ a) = f a := by
  have h' : ∀ b, Fintype.card {a // f a = b} = Fintype.card {a // f' a = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h b
  let e : ∀ b, {a // f a = b} ≃ {a // f' a = b} := fun b => Fintype.equivOfCardEq (h' b)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv f')), fun a => ?_⟩
  exact (e (f a) ⟨a, rfl⟩).2

theorem a10g_fiber_tt (X B : Finset (Fin 10)) :
    (Finset.univ.filter (fun a => (decide (a ∈ X), decide (a ∈ B)) = (true, true))).card =
      (X ∩ B).card := by
  congr 1; ext a; simp

theorem a10g_fiber_tf (X B : Finset (Fin 10)) :
    (Finset.univ.filter (fun a => (decide (a ∈ X), decide (a ∈ B)) = (true, false))).card =
      (X \ B).card := by
  congr 1; ext a; simp

theorem a10g_fiber_ft (X B : Finset (Fin 10)) :
    (Finset.univ.filter (fun a => (decide (a ∈ X), decide (a ∈ B)) = (false, true))).card =
      (B \ X).card := by
  congr 1; ext a; simp [and_comm]

theorem a10g_fiber_ff (X B : Finset (Fin 10)) :
    (Finset.univ.filter (fun a => (decide (a ∈ X), decide (a ∈ B)) = (false, false))).card =
      ((X ∪ B)ᶜ).card := by
  congr 1; ext a; simp

theorem a10g_fiber_eq (X X' B B' : Finset (Fin 10)) (hX : X.card = X'.card)
    (hB : B.card = B'.card) (hXB : (X ∩ B).card = (X' ∩ B').card) (b : Bool × Bool) :
    (Finset.univ.filter (fun a => (decide (a ∈ X), decide (a ∈ B)) = b)).card =
      (Finset.univ.filter (fun a => (decide (a ∈ X'), decide (a ∈ B')) = b)).card := by
  obtain ⟨u, v⟩ := b
  have h1 := Finset.card_sdiff_add_card_inter X B
  have h2 := Finset.card_sdiff_add_card_inter X' B'
  have h3 := Finset.card_sdiff_add_card_inter B X
  have h4 := Finset.card_sdiff_add_card_inter B' X'
  have h5 := Finset.card_union_add_card_inter X B
  have h6 := Finset.card_union_add_card_inter X' B'
  rw [Finset.inter_comm B X] at h3
  rw [Finset.inter_comm B' X'] at h4
  cases u <;> cases v
  · rw [a10g_fiber_ff, a10g_fiber_ff, Finset.card_compl, Finset.card_compl, Fintype.card_fin]
    omega
  · rw [a10g_fiber_ft, a10g_fiber_ft]
    omega
  · rw [a10g_fiber_tf, a10g_fiber_tf]
    omega
  · rw [a10g_fiber_tt, a10g_fiber_tt]
    exact hXB

theorem a10g_exists_perm_pair (X X' B B' : Finset (Fin 10)) (hX : X.card = X'.card)
    (hB : B.card = B'.card) (hXB : (X ∩ B).card = (X' ∩ B').card) :
    ∃ σ : Perm (Fin 10), (∀ x, σ x ∈ X' ↔ x ∈ X) ∧ (∀ x, σ x ∈ B' ↔ x ∈ B) := by
  obtain ⟨σ, hσ⟩ := a10g_exists_perm_fiber (fun a => (decide (a ∈ X), decide (a ∈ B)))
    (fun a => (decide (a ∈ X'), decide (a ∈ B'))) (a10g_fiber_eq X X' B B' hX hB hXB)
  refine ⟨σ, fun x => ?_, fun x => ?_⟩
  · have := congrArg Prod.fst (hσ x)
    simpa using this
  · have := congrArg Prod.snd (hσ x)
    simpa using this

theorem a10g_swap_pres {P : Fin 10 → Prop} {x y : Fin 10} (h : P x ↔ P y) (z : Fin 10) :
    P (swap x y z) ↔ P z := by
  by_cases hzx : z = x
  · subst hzx
    rw [swap_apply_left]
    exact h.symm
  · by_cases hzy : z = y
    · subst hzy
      rw [swap_apply_right]
      exact h
    · rw [swap_apply_of_ne_of_ne hzx hzy]

theorem a10g_exists_a10_pair (X X' B B' : Finset (Fin 10)) (hX3 : 3 ≤ X.card)
    (hX : X.card = X'.card) (hB : B.card = B'.card) (hXB : (X ∩ B).card = (X' ∩ B').card) :
    ∃ σ : A10, σ • X = X' ∧ σ • B = B' := by
  obtain ⟨σ, hσX, hσB⟩ := a10g_exists_perm_pair X X' B B' hX hB hXB
  have key : ∃ σ' : Perm (Fin 10), sign σ' = 1 ∧ (∀ x, σ' x ∈ X' ↔ x ∈ X) ∧
      (∀ x, σ' x ∈ B' ↔ x ∈ B) := by
    rcases Int.units_eq_one_or (sign σ) with h | h
    · exact ⟨σ, h, hσX, hσB⟩
    · obtain ⟨x, hx, y, hy, hxy, hxyB⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := X) (t := (Finset.univ : Finset Bool)) (f := fun a => decide (a ∈ B))
        (by simp; omega) (fun a _ => Finset.mem_coe.2 (Finset.mem_univ _))
      have hxyB' : x ∈ B ↔ y ∈ B := decide_eq_decide.1 hxyB
      refine ⟨σ * swap x y, ?_, fun z => ?_, fun z => ?_⟩
      · rw [map_mul, h, sign_swap hxy]; decide
      · rw [Perm.mul_apply, hσX, a10g_swap_pres (P := fun w => w ∈ X) (iff_of_true hx hy) z]
      · rw [Perm.mul_apply, hσB, a10g_swap_pres (P := fun w => w ∈ B) hxyB' z]
  obtain ⟨σ', hs, hσ'X, hσ'B⟩ := key
  refine ⟨⟨σ', mem_alternatingGroup.2 hs⟩, ?_, ?_⟩
  · ext y
    rw [a10g_mem_smul]
    have := hσ'X (σ'⁻¹ y)
    have h0 : σ' (σ'⁻¹ y) = y := by simp
    rw [h0] at this
    exact this.symm
  · ext y
    rw [a10g_mem_smul]
    have := hσ'B (σ'⁻¹ y)
    have h0 : σ' (σ'⁻¹ y) = y := by simp
    rw [h0] at this
    exact this.symm

theorem a10g_orbit_eq : MulAction.orbit A10 a10gX = {B : Finset (Fin 10) | B.card = 5} := by
  ext B
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    show (g • a10gX).card = 5
    rw [Finset.card_smul_finset, a10g_card_gX]
  · intro hB
    have hB5 : B.card = 5 := hB
    obtain ⟨σ, -, hσ⟩ := a10g_exists_a10_pair Finset.univ Finset.univ a10gX B (by simp) rfl
      (by rw [a10g_card_gX, hB5]) (by simp [a10g_card_gX, hB5])
    exact ⟨σ, hσ⟩

theorem a10g_ncard_orbit : (MulAction.orbit A10 a10gX).ncard = 252 := by
  rw [a10g_orbit_eq]
  have : {B : Finset (Fin 10) | B.card = 5} =
      ↑(Finset.powersetCard 5 (Finset.univ : Finset (Fin 10))) := by
    ext B; simp [Finset.mem_powersetCard]
  rw [this, Set.ncard_coe_finset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

theorem a10g_index_stab : (MulAction.stabilizer A10 a10gX).index = 252 := by
  rw [MulAction.index_stabilizer, a10g_ncard_orbit]

theorem a10g_stab_le_hat : MulAction.stabilizer A10 a10gX ≤ a10gHat :=
  fun _ hg => Or.inl (MulAction.mem_stabilizer_iff.1 hg)

theorem a10g_orbit_ncard_mul_index {H : Subgroup A10} (hH : a10gHat ≤ H) :
    (MulAction.orbit H a10gX).ncard * H.index = 252 := by
  have hSt : MulAction.stabilizer A10 a10gX ≤ H := a10g_stab_le_hat.trans hH
  have h := Subgroup.relIndex_mul_index hSt
  rw [a10g_index_stab] at h
  rw [← h, Subgroup.relIndex, MulAction.stabilizer_subgroupOf, MulAction.index_stabilizer]

theorem a10g_saturate {H : Subgroup A10} (hH : a10gHat ≤ H) {B B' : Finset (Fin 10)}
    (hB : B ∈ MulAction.orbit H a10gX) (hB' : B'.card = 5) (hκ : (B' ∩ a10gX).card = (B ∩ a10gX).card) :
    B' ∈ MulAction.orbit H a10gX := by
  obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hB
  have h5 : ((h : A10) • a10gX).card = 5 := by rw [Finset.card_smul_finset, a10g_card_gX]
  obtain ⟨σ, hσX, hσB⟩ := a10g_exists_a10_pair a10gX a10gX ((h : A10) • a10gX) B'
    (by rw [a10g_card_gX]; norm_num) rfl (by rw [h5, hB'])
    (by rw [Finset.inter_comm a10gX, Finset.inter_comm a10gX]; exact hκ.symm)
  have hσH : σ ∈ H := hH (Or.inl hσX)
  refine MulAction.mem_orbit_iff.2 ⟨⟨σ, hσH⟩ * h, ?_⟩
  show (σ * (h : A10)) • a10gX = B'
  rw [mul_smul]
  exact hσB

@[expose] def a10gLvl (T : Finset ℕ) : Finset (Finset (Fin 10)) :=
  (Finset.powersetCard 5 (Finset.univ : Finset (Fin 10))).filter (fun B => (B ∩ a10gX).card ∈ T)

theorem a10g_lvl_arith : ∀ T ∈ (Finset.range 6).powerset, 0 ∈ T → 5 ∈ T →
    (a10gLvl T).card ∣ 252 → (∀ k ∈ T, k = 0 ∨ k = 5) ∨ (a10gLvl T).card = 252 := by
  decide +kernel

theorem a10g_hat_max {H : Subgroup A10} (hH : a10gHat ≤ H) : H = a10gHat ∨ H = ⊤ := by
  classical
  have hmul := a10g_orbit_ncard_mul_index hH
  have hcardO : ∀ {B : Finset (Fin 10)}, B ∈ MulAction.orbit H a10gX → B.card = 5 := by
    intro B hB
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hB
    show ((h : A10) • a10gX).card = 5
    rw [Finset.card_smul_finset, a10g_card_gX]
  let T : Finset ℕ :=
    (Finset.range 6).filter (fun k => ∃ B ∈ MulAction.orbit H a10gX, (B ∩ a10gX).card = k)
  have hTmem : ∀ {B : Finset (Fin 10)}, B ∈ MulAction.orbit H a10gX → (B ∩ a10gX).card ∈ T := by
    intro B hB
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, B, hB, rfl⟩
    have : (B ∩ a10gX).card ≤ a10gX.card := Finset.card_le_card Finset.inter_subset_right
    rw [a10g_card_gX] at this
    omega
  have hOT : MulAction.orbit H a10gX = ↑(a10gLvl T) := by
    ext B
    rw [Finset.mem_coe, a10gLvl, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · intro hB
      exact ⟨⟨Finset.subset_univ _, hcardO hB⟩, hTmem hB⟩
    · rintro ⟨⟨-, hc⟩, hk⟩
      obtain ⟨-, B₀, hB₀, hκ⟩ := Finset.mem_filter.1 hk
      exact a10g_saturate hH hB₀ hc hκ.symm
  have hYO : a10gY ∈ MulAction.orbit H a10gX := by
    refine MulAction.mem_orbit_iff.2 ⟨⟨ν₂, hH (a10g_mem_hat.2 (Or.inr a10g_ν₂_smul))⟩, ?_⟩
    exact a10g_ν₂_smul
  have hXO : a10gX ∈ MulAction.orbit H a10gX := MulAction.mem_orbit_self a10gX
  have hT0 : 0 ∈ T := by
    have := hTmem hYO
    have e : (a10gY ∩ a10gX).card = 0 := by decide
    rwa [e] at this
  have hT5 : 5 ∈ T := by
    have := hTmem hXO
    have e : (a10gX ∩ a10gX).card = 5 := by decide
    rwa [e] at this
  have hncard : (MulAction.orbit H a10gX).ncard = (a10gLvl T).card := by
    rw [hOT, Set.ncard_coe_finset]
  have hdvd : (a10gLvl T).card ∣ 252 := ⟨H.index, by rw [← hncard]; exact hmul.symm⟩
  rcases a10g_lvl_arith T (Finset.mem_powerset.2 (Finset.filter_subset _ _)) hT0 hT5 hdvd with
    hall | hc
  · left
    refine le_antisymm (fun h hh => ?_) hH
    have hmem : h • a10gX ∈ MulAction.orbit H a10gX := MulAction.mem_orbit_iff.2 ⟨⟨h, hh⟩, rfl⟩
    have hcard : (h • a10gX).card = 5 := hcardO hmem
    rcases hall _ (hTmem hmem) with h0 | h5
    · right
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        rw [← a10g_compl_gX, Finset.mem_compl]
        intro hzX
        have : 0 < ((h • a10gX) ∩ a10gX).card := Finset.card_pos.2 ⟨z, Finset.mem_inter.2 ⟨hz, hzX⟩⟩
        omega
      · rw [a10g_card_gY, hcard]
    · left
      have heq : (h • a10gX) ∩ a10gX = a10gX :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [h5, a10g_card_gX])
      have hsub : a10gX ⊆ h • a10gX := fun z hz => (Finset.mem_inter.1 (heq ▸ hz)).1
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, a10g_card_gX])).symm
  · right
    rw [hncard, hc] at hmul
    exact Subgroup.index_eq_one.1 (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm
