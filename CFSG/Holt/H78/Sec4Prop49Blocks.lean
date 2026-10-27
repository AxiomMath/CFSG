module

public import CFSG.Holt.H78.Sec4Prop49
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise commutatorElement

section Dihedral

variable {X : Type*} [Group X]

theorem exists_conj_commute_of_odd {x z : X} (hx : x * x = 1) (hz : z * z = 1) (k : ℕ)
    (hρ : ((x * z) ^ 2) ^ (2 * k + 1) = 1) :
    ∃ r g : X, r * x = x * r ∧ g * z * g⁻¹ = r ∧ z⁻¹ * r = ((x * z) ^ 2) ^ k := by
  set ρ := x * z with hρdef
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hconj : x * ρ * x⁻¹ = ρ⁻¹ := by
    rw [hρdef, mul_inv_rev, hxinv, hzinv, ← mul_assoc, hx, one_mul]
  have hconjn : ∀ n : ℕ, x * ρ ^ n * x⁻¹ = (ρ ^ n)⁻¹ := fun n => by
    rw [← conj_pow, hconj, inv_pow]
  have hρ2 : (ρ ^ (2 * k + 1)) * (ρ ^ (2 * k + 1)) = 1 := by
    rw [← pow_add, show 2 * k + 1 + (2 * k + 1) = 2 * (2 * k + 1) by ring, pow_mul, hρ]
  have hz' : z = x * ρ := by rw [hρdef, ← mul_assoc, hx, one_mul]
  refine ⟨x * ρ ^ (2 * k + 1), (ρ ^ k)⁻¹, ?_, ?_, ?_⟩
  · have h1 : x * ρ ^ (2 * k + 1) * x = (ρ ^ (2 * k + 1))⁻¹ := by
      rw [← hconjn, hxinv]
    rw [h1, ← mul_assoc, hx, one_mul]
    exact inv_eq_of_mul_eq_one_right hρ2
  · have h2 : (ρ ^ k)⁻¹ * x = x * ρ ^ k := by
      rw [← hconjn k, hxinv, mul_assoc, mul_assoc, hx, mul_one]
    rw [hz', inv_inv, ← mul_assoc, h2, mul_assoc, mul_assoc, ← pow_succ', ← pow_add,
      show k + (k + 1) = 2 * k + 1 by ring]
  · rw [hz', mul_inv_rev, hxinv, mul_assoc, ← mul_assoc x, hx, one_mul, ← pow_mul,
      show 2 * k + 1 = 1 + 2 * k by ring, pow_add, pow_one, inv_mul_cancel_left, pow_mul]

end Dihedral

section PermHelpers

variable {X : Type*} [DecidableEq X]

theorem swap_mul_comm_of_fixed {V : Equiv.Perm X} {a b : X} (ha : V a = a) (hb : V b = b) :
    Equiv.swap a b * V = V * Equiv.swap a b := by
  rw [Equiv.mul_swap_eq_swap_mul, ha, hb]

omit [DecidableEq X] in
theorem conj_mul_comm {V W c : Equiv.Perm X} (hW : W * V = V * W) (hc : c * V = V * c) :
    c * W * c⁻¹ * V = V * (c * W * c⁻¹) :=
  (((show Commute c V from hc).mul_left (show Commute W V from hW)).mul_left
    (show Commute c V from hc).inv_left).eq

omit [DecidableEq X] in
theorem zpow_apply_eq_zpow_emod_three {τ : Equiv.Perm X} {a b c : X} (hab : τ a = b)
    (hbc : τ b = c) (hca : τ c = a) (n : ℤ) : (τ ^ n) a = (τ ^ (n % 3)) a := by
  have h3 : (τ ^ (3 : ℤ)) a = a := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, pow_succ, pow_succ, pow_one,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hab, hbc, hca]
  conv_lhs => rw [← Int.emod_add_mul_ediv n 3, zpow_add, zpow_mul, Equiv.Perm.mul_apply,
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h3]

omit [DecidableEq X] in
theorem zpow_apply_three_iff {τ : Equiv.Perm X} {a b c : X} (hab : τ a = b) (hbc : τ b = c)
    (hca : τ c = a) (hab' : a ≠ b) (hac : a ≠ c) (hbc' : b ≠ c) (n : ℤ) :
    ((τ ^ n) a = a ↔ n % 3 = 0) ∧ ((τ ^ n) a = b ↔ n % 3 = 1) := by
  rw [zpow_apply_eq_zpow_emod_three hab hbc hca n]
  have h1 : (τ ^ (1 : ℤ)) a = b := by rw [zpow_one, hab]
  have h2 : (τ ^ (2 : ℤ)) a = c := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq, Equiv.Perm.mul_apply, hab, hbc]
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h <;> rw [h]
  · simp [hab']
  · rw [h1]
    simp [hab'.symm]
  · rw [h2]
    simp [hac.symm, hbc'.symm]

theorem cycle3_of_swap {W : Equiv.Perm X} {γ p : X}
    (hWW : ∀ ψ, W (W ψ) = ψ) (hγW : ∀ ψ, W ψ = ψ ↔ ψ = γ) (hpγ : p ≠ γ) :
    let s := Equiv.swap γ p
    (W * (s * W * s⁻¹)) γ = p ∧ (W * (s * W * s⁻¹)) p = W p ∧ (W * (s * W * s⁻¹)) (W p) = γ ∧
      γ ≠ p ∧ γ ≠ W p ∧ p ≠ W p := by
  intro s
  have hWγ : W γ = γ := (hγW γ).mpr rfl
  have hqγ : W p ≠ γ := fun h => hpγ (by rw [← hWW p, h, hWγ])
  have hqp : W p ≠ p := fun h => hpγ ((hγW p).mp h)
  have hsq : s (W p) = W p := Equiv.swap_apply_of_ne_of_ne hqγ hqp
  have hsi : s⁻¹ = s := Equiv.swap_inv _ _
  simp only [Equiv.Perm.mul_apply, hsi]
  refine ⟨?_, ?_, ?_, hpγ.symm, hqγ.symm, hqp.symm⟩
  · rw [show s γ = p from Equiv.swap_apply_left _ _, hsq, hWW]
  · rw [show s p = γ from Equiv.swap_apply_right _ _, hWγ,
      show s γ = p from Equiv.swap_apply_left _ _]
  · rw [hsq, hWW, show s p = γ from Equiv.swap_apply_right _ _, hWγ]

end PermHelpers

namespace P49Config

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

include C

theorem twoPointElt_mem_longInv (hS : Sec4Setting G Ω) {y : G}
    (hy : y ∈ longInvSwap G Ω α C.β) :
    twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hy)) ∈
      longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
  (hS.mem_longInv_twoPointSection_iff C.ne (C.three_le_card_holtDelta hS) _).mpr
    ⟨y, hy, fun _ => rfl⟩

theorem exists_lift (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) {y : G}
    (hy : y ∈ longInvSwap G Ω α C.β)
    (hcomm : ∀ k, D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hy)⟩ *
        D'.ρ k ⟨C.vHat, C.vHat_mem_jHull hS⟩ =
      D'.ρ k ⟨C.vHat, C.vHat_mem_jHull hS⟩ *
        D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hy)⟩) :
    ∃ c ∈ longInvSwap G Ω α C.β,
      c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
        ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
          ∀ δ' : holtDelta G Ω α C.β, (δ' : Ω) = c • (δ : Ω) →
            D'.coord δ' = fun k => D'.ρ k
              ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hy)⟩ (D'.coord δ k) := by
  have h3 := C.three_le_card_holtDelta hS
  have hzJ := C.twoPointElt_mem_longInv hS hy
  set z := twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hy))
    with hzdef
  set x := C.vHat with hxdef
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := ⟨x, C.vHat_mem_jHull hS⟩
  set zH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨z, mem_jHull_of_mem_longInv hzJ⟩
  have hxx : x * x = 1 := C.vHat_mul_vHat
  have hzz : z * z = 1 := mul_self_eq_one_of_mem_longInv hzJ
  have hsoc : ⁅x, z⁆ ∈ D'.socPre := by
    rw [show ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem (C.vHat_mem_socPre hS D')
      (D'.conj_mem_socPre zH.2 (inv_mem (C.vHat_mem_socPre hS D')))
  have hker : ⁅x, z⁆ ∈ jOrbitKernel (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    have h := (D'.mem_jOrbitKernel_iff_rho (h := ⁅xH, zH⁆)).mpr fun k => by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hcomm k).symm
    exact h
  have hO : ⁅x, z⁆ ∈ jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    rw [← D'.socPre_inf_jOrbitKernel]
    exact ⟨hsoc, hker⟩
  have hsq : (x * z) ^ 2 = ⁅x, z⁆ := by
    rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hxx, inv_eq_of_mul_eq_one_right hzz,
      sq, ← mul_assoc]
  have hodd : Odd (orderOf ((x * z) ^ 2)) := by
    rw [hsq]
    exact Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hO)
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨r, g, hrx, hgr, hzr⟩ := exists_conj_commute_of_odd hxx hzz k
    (by rw [← hk]; exact pow_orderOf_eq_one _)
  have hrJ : r ∈ longInv (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) := by
    rw [← hgr]
    exact conj_mem_longInv hzJ g
  obtain ⟨c₁, hc₁, hc₁r⟩ := (hS.mem_longInv_twoPointSection_iff C.ne h3 r).mp hrJ
  have hrB : ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      c₁ • (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := fun δ hδ => by
    rw [← hc₁r, mem_fixSet_zpowers_iff]
    have h1 : v • (δ : Ω) = δ := mem_fixSet_zpowers_iff.mp hδ
    have hxδ : x • δ = δ := Subtype.ext h1
    have h := congrArg (fun π : twoPointSection G Ω α C.β => ((π • δ : holtDelta G Ω α C.β) :
      Ω)) hrx
    simp only [mul_smul, hxδ] at h
    exact h.symm
  set Λ : Set Ω := holtDelta G Ω α C.β ∩ fixSet Ω (Subgroup.zpowers v) with hΛ
  have hc₁X := closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hc₁)
  have hc₁Δ : ∀ p ∈ holtDelta G Ω α C.β, c₁ • p ∈ holtDelta G Ω α C.β := fun p hp => by
    have h := mem_stabilizer_iff.mp (stabilizer_pair_le α C.β hc₁X)
    rw [← h]
    exact Set.smul_mem_smul_set hp
  have hc₁Λ' : ∀ p ∈ Λ, c₁ • p ∈ Λ := fun p hp =>
    ⟨hc₁Δ p hp.1, hrB ⟨p, hp.1⟩ hp.2⟩
  have hc₁Λ : c₁ ∈ stabilizer G Λ := by
    rw [mem_stabilizer_iff]
    refine Set.Subset.antisymm (Set.smul_set_subset_iff.mpr hc₁Λ') fun p hp => ?_
    refine ⟨c₁ • p, hc₁Λ' p hp, ?_⟩
    show c₁ • c₁ • p = p
    rw [smul_smul, mul_self_eq_one_of_mem_longInv hc₁.1, one_smul]
  obtain ⟨δ₀, -, hδ₀, -, -⟩ := C.exists_mem_holtDelta_ne hS
  have hVαβ : Subgroup.zpowers v ≤ stabilizer G α ⊓ stabilizer G C.β :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨mem_stabilizer_iff.mpr C.v_smul_α, mem_stabilizer_iff.mpr C.v_smul_β⟩)
  obtain ⟨c, hc, hcV, hcΛ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn (Λ := Λ) C.ne
    C.isPGroup_zpowers hVαβ ⟨(δ₀ : Ω), hδ₀, δ₀.2⟩ Set.inter_subset_right hc₁ hc₁Λ
  refine ⟨c, hc, hcV, fun δ hδ δ' hδ' => ?_⟩
  have hδ'r : δ' = r • δ := Subtype.ext (by rw [hδ', hcΛ _ ⟨δ.2, hδ⟩]; exact (hc₁r δ).symm)
  have hro : r = z * ((x * z) ^ 2) ^ k := by rw [← hzr, mul_inv_cancel_left]
  have hoO : ((x * z) ^ 2) ^ k ∈ jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    pow_mem (hsq ▸ hO) k
  have hcoord : D'.coord δ = D'.coord (((x * z) ^ 2) ^ k • δ) :=
    (D'.coord_eq_iff δ _).mpr (mem_orbit δ (⟨_, hoO⟩ :
      jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)))
  rw [hδ'r, hro, mul_smul, hcoord]
  funext j
  exact D'.coord_smul zH _ j

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem twoPointElt_commute {w : G} (hw : w ∈ longInvSwap G Ω α C.β)
    (hwv : w * v = v * w) :
    twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hw)) *
        C.vHat =
      C.vHat * twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β
        (Subgroup.subset_closure hw)) :=
  Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    show w • v • (δ : Ω) = v • w • (δ : Ω)
    rw [← mul_smul, ← mul_smul, hwv]))

theorem exists_realize (hS : Sec4Setting G Ω)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) {w : G}
    (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) (j₀ : D'.ι)
    {y : Equiv.Perm (D'.Ψc j₀)} (hyR : y ∈ (D'.ρ j₀).range)
    (hyJ : y ∈ longInv (Equiv.Perm (D'.Ψc j₀)) (D'.Ψc j₀))
    (hyv : y * D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ =
      D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ * y) :
    ∃ c ∈ longInvSwap G Ω α C.β,
      c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
        ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
          ∀ δ' : holtDelta G Ω α C.β, (δ' : Ω) = c • (δ : Ω) →
            D'.coord δ' = fun k => Function.update (fun k => D'.ρ k
              ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩) j₀ y k
                (D'.coord δ k) := by
  have h3 := C.three_le_card_holtDelta hS
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩
  set Y : ∀ k, Equiv.Perm (D'.Ψc k) := Function.update (fun k => D'.ρ k wH) j₀ y with hY
  have hwx : ∀ k, D'.ρ k wH * D'.ρ k xH = D'.ρ k xH * D'.ρ k wH := fun k => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (C.twoPointElt_commute hw hwv)
  have hYR : ∀ k, Y k ∈ (D'.ρ k).range := fun k => by
    rcases eq_or_ne k j₀ with rfl | hk
    · rw [hY, Function.update_self]
      exact hyR
    · rw [hY, Function.update_of_ne hk]
      exact ⟨wH, rfl⟩
  have hYJ : ∀ k, Y k ∈ longInv (Equiv.Perm (D'.Ψc k)) (D'.Ψc k) := fun k => by
    rcases eq_or_ne k j₀ with rfl | hk
    · rw [hY, Function.update_self]
      exact hyJ
    · rw [hY, Function.update_of_ne hk]
      exact D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) k
  have hYx : ∀ k, Y k * D'.ρ k xH = D'.ρ k xH * Y k := fun k => by
    rcases eq_or_ne k j₀ with rfl | hk
    · rw [hY, Function.update_self]
      exact hyv
    · rw [hY, Function.update_of_ne hk]
      exact hwx k
  obtain ⟨u, hu, hρu⟩ := D'.exists_mem_longInv_rho_eq Y hYR hYJ
  obtain ⟨y', hy', hy'u⟩ := (hS.mem_longInv_twoPointSection_iff C.ne h3 u).mp hu
  have hu' : (⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hy')⟩ :
      jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) = u :=
    Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (hy'u δ).symm))
  obtain ⟨c, hc, hcV, hcB⟩ := C.exists_lift hS D' hy' (fun k => by rw [hu', hρu]; exact hYx k)
  refine ⟨c, hc, hcV, fun δ hδ δ' hδ' => ?_⟩
  rw [hcB δ hδ δ' hδ', hu']
  funext k
  rw [hρu]

end Lift

section Blocks

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)
  (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))

def BlockAct (g : G) (σ : ∀ k, Equiv.Perm (D'.Ψc k)) : Prop :=
  ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
    ∀ δ' : holtDelta G Ω α C.β, (δ' : Ω) = g • (δ : Ω) → D'.coord δ' = fun k => σ k (D'.coord δ k)

abbrev stabB : Subgroup G :=
  stabilizer G ({α, C.β} : Set Ω) ⊓ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_smul_mem_B {g : G} (hg : g ∈ C.stabB) {δ : holtDelta G Ω α C.β}
    (hδ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) :
    ∃ δ'' : holtDelta G Ω α C.β, (δ'' : Ω) = g • (δ : Ω) ∧
      (δ'' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
  have hgΔ := mem_stabilizer_iff.mp (stabilizer_pair_le α C.β hg.1)
  have hmem := Set.smul_mem_smul_set (a := g) δ.2
  rw [hgΔ] at hmem
  refine ⟨⟨g • (δ : Ω), hmem⟩, rfl, ?_⟩
  rw [mem_fixSet_zpowers_iff, ← mul_smul, ← mem_centralizer_zpowers_iff.mp hg.2, mul_smul,
    mem_fixSet_zpowers_iff.mp hδ]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_stabB {c : G} (hc : c ∈ longInvSwap G Ω α C.β)
    (hcV : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) :
    c ∈ C.stabB :=
  ⟨closure_longInvSwap_le_stabilizer_pair α C.β (Subgroup.subset_closure hc), hcV⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem blockAct_one : C.BlockAct D' 1 1 := fun δ _ δ' hδ' => by
  rw [one_smul] at hδ'
  rw [Subtype.ext hδ']
  rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem BlockAct.mul {g g' : G} {σ σ' : ∀ k, Equiv.Perm (D'.Ψc k)} (hg : C.BlockAct D' g σ)
    (hg'B : g' ∈ C.stabB) (hg' : C.BlockAct D' g' σ') : C.BlockAct D' (g * g') (σ * σ') :=
  fun δ hδ δ' hδ' => by
    obtain ⟨δ'', h1, h2⟩ := C.exists_smul_mem_B hg'B hδ
    rw [hg δ'' h2 δ' (by rw [hδ', mul_smul, h1]), hg' δ hδ δ'' h1]
    rfl

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem BlockAct.inv {g : G} {σ : ∀ k, Equiv.Perm (D'.Ψc k)} (hgB : g ∈ C.stabB)
    (hg : C.BlockAct D' g σ) : C.BlockAct D' g⁻¹ σ⁻¹ := fun δ hδ δ' hδ' => by
  obtain ⟨δ'', h1, h2⟩ := C.exists_smul_mem_B (inv_mem hgB) hδ
  have he : δ' = δ'' := Subtype.ext (hδ'.trans h1.symm)
  subst he
  have h := hg δ' h2 δ (by rw [h1, smul_inv_smul])
  funext k
  show D'.coord δ' k = (σ k)⁻¹ (D'.coord δ k)
  rw [eq_comm, Equiv.Perm.inv_eq_iff_eq, ← congrFun h k]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem BlockAct.zpow {g : G} {σ : ∀ k, Equiv.Perm (D'.Ψc k)} (hgB : g ∈ C.stabB)
    (hg : C.BlockAct D' g σ) (n : ℤ) : C.BlockAct D' (g ^ n) (σ ^ n) := by
  induction n using Int.induction_on with
  | zero => simpa using C.blockAct_one D'
  | succ n ih =>
    rw [zpow_add_one, zpow_add_one]
    exact ih.mul C D' hgB hg
  | pred n ih =>
    rw [zpow_sub_one, zpow_sub_one]
    exact ih.mul C D' (inv_mem hgB) (hg.inv C D' hgB)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem BlockAct.apply_eq {g g' : G} {σ σ' : ∀ k, Equiv.Perm (D'.Ψc k)}
    (hg : C.BlockAct D' g σ) (hgB : g ∈ C.stabB) (hg' : C.BlockAct D' g' σ')
    {δ : holtDelta G Ω α C.β} (hδ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v))
    (he : g • (δ : Ω) = g' • (δ : Ω)) (k : D'.ι) :
    σ k (D'.coord δ k) = σ' k (D'.coord δ k) := by
  obtain ⟨δ'', h1, -⟩ := C.exists_smul_mem_B hgB hδ
  rw [← congrFun (hg δ hδ δ'' h1) k, ← congrFun (hg' δ hδ δ'' (h1.trans he)) k]

end Blocks

section Prop23

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)
  (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))

include C

theorem blockAct_w (hS : Sec4Setting G Ω) {w : G} (hw : w ∈ longInvSwap G Ω α C.β) :
    C.BlockAct D' w fun k =>
      D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ :=
  fun δ _ δ' hδ' => by
    rw [show δ' = twoPointElt (closure_longInvSwap_le_stabilizer_pair α C.β
      (Subgroup.subset_closure hw)) • δ from Subtype.ext hδ']
    funext k
    exact D'.coord_smul ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ δ k

theorem exists_mem_B_coord (hS : Sec4Setting G Ω)
    {γ₀ : holtDelta G Ω α C.β} (hγ₀ : (γ₀ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) (j : D'.ι)
    {ψ : D'.Ψc j} (hψ : D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ) :
    ∃ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
      D'.coord δ = Function.update (D'.coord γ₀) j ψ := by
  obtain ⟨δ, hδ⟩ := D'.coord_surjective (Function.update (D'.coord γ₀) j ψ)
  refine ⟨δ, (C.mem_fixSet_iff_rho hS D' δ).mpr fun k => ?_, hδ⟩
  rw [hδ]
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self]
    exact hψ
  · rw [Function.update_of_ne hk]
    exact (C.mem_fixSet_iff_rho hS D' γ₀).mp hγ₀ k

theorem pair_commute_B (hS : Sec4Setting G Ω) {c₁ c₂ c₃ c₄ : G}
    (h₁ : c₁ ∈ longInvSwap G Ω α C.β)
    (h₁' : c₁ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₂ : c₂ ∈ longInvSwap G Ω α C.β)
    (h₂' : c₂ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₃ : c₃ ∈ longInvSwap G Ω α C.β)
    (h₃' : c₃ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    (h₄ : c₄ ∈ longInvSwap G Ω α C.β)
    (h₄' : c₄ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G))
    {δ : holtDelta G Ω α C.β} (hδ : (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) :
    (c₁ * c₂ * (c₃ * c₄)) • (δ : Ω) = (c₃ * c₄ * (c₁ * c₂)) • (δ : Ω) := by
  rw [mul_smul (c₁ * c₂), mul_smul (c₃ * c₄)]
  exact C.pair_commute hS h₁ h₁' h₂ h₂' h₃ h₃' h₄ h₄' (δ := ⟨δ, hδ⟩)
    ((C.mem_holtDelta_iff hS ⟨δ, hδ⟩).mp δ.2).1

theorem rho_vHat_ne_one_of_isNaturalSE (hS : Sec4Setting G Ω)
    {w : G} (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) {j : D'.ι}
    (hj : IsNaturalSE (D'.M j)) : D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ≠ 1 := by
  intro h1
  obtain ⟨n, e, f, hA⟩ := IsNaturalSE.exists_isBenderAction hj
  have := hA.nontrivial
  obtain ⟨p, p', hpp'⟩ := exists_pair_ne (D'.Ψc j)
  have hcard : ∀ q, 3 ≤ (longInvAt (D'.M j) (D'.Ψc j) q).ncard := fun q => by
    rw [hA.ncard_longInvAt]
    have := hA.four_le_q
    omega
  have h0 : ∀ q, (longInvAt (D'.M j) (D'.Ψc j) q).ncard ≠ 0 := fun q => by
    have := hcard q
    omega
  obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero (h0 p)
  obtain ⟨z', hz', hzz'⟩ := Set.exists_ne_of_one_lt_ncard
    (s := longInvAt (D'.M j) (D'.Ψc j) p) (by have := hcard p; omega) z
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (h0 p')
  have hrange : (D'.ρ j).range = D'.M j :=
    D'.range_rho_of_not_isOuterFactor hj.not_isOuterFactor
  have hreal : ∀ {q : D'.Ψc j} {t : D'.M j}, t ∈ longInvAt (D'.M j) (D'.Ψc j) q →
      ∃ c ∈ longInvSwap G Ω α C.β,
        c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
          C.BlockAct D' c (Function.update (fun k => D'.ρ k
            ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩) j t) :=
    fun ht => C.exists_realize hS D' hw hwv j (by rw [hrange]; exact (_ : D'.M j).2)
      (mem_longInv_subgroup_iff.mp ht.1) (by rw [h1, mul_one, one_mul])
  obtain ⟨cz, hcz, hczV, hczB⟩ := hreal hz
  obtain ⟨cz', hcz', hcz'V, hcz'B⟩ := hreal hz'
  obtain ⟨cx, hcx, hcxV, hcxB⟩ := hreal hx
  have hB := fun {c} (hc : c ∈ longInvSwap G Ω α C.β)
    (hcV : c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =>
    C.mem_stabB hc hcV
  have hg₁ := hczB.mul C D' (hB hcz' hcz'V) hcz'B
  have hg₂ := hcxB.mul C D' (hB hcz hczV) hczB
  have hg₁₂ := hg₁.mul C D' (mul_mem (hB hcx hcxV) (hB hcz hczV)) hg₂
  have hg₂₁ := hg₂.mul C D' (mul_mem (hB hcz hczV) (hB hcz' hcz'V)) hg₁
  obtain ⟨γ₀, -, hγ₀Δ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  set Z : Equiv.Perm (D'.Ψc j) := (z : Equiv.Perm (D'.Ψc j)) with hZdef
  set Z' : Equiv.Perm (D'.Ψc j) := (z' : Equiv.Perm (D'.Ψc j)) with hZ'def
  set X : Equiv.Perm (D'.Ψc j) := (x : Equiv.Perm (D'.Ψc j)) with hXdef
  have key : ∀ ψ : D'.Ψc j, (Z * Z' * (X * Z)) ψ = (X * Z * (Z * Z')) ψ := fun ψ => by
    obtain ⟨δ, hδ, hδc⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j
      (ψ := ψ) (by rw [h1, Equiv.Perm.one_apply])
    have h := hg₁₂.apply_eq C D' (mul_mem (mul_mem (hB hcz hczV) (hB hcz' hcz'V))
      (mul_mem (hB hcx hcxV) (hB hcz hczV))) hg₂₁ hδ
      (C.pair_commute_B hS hcz hczV hcz' hcz'V hcx hcxV hcz hczV hδ) j
    simpa [hδc, Pi.mul_apply, Function.update_self] using h
  have hZZ' : Z * Z' = Z' * Z :=
    hj.commute_of_mem_mulLongInvClosure
      (hj.mem_mulLongInvClosure_of_mul_self z.2 hz.2 (mul_self_eq_one_of_mem_longInv
        (mem_longInv_subgroup_iff.mp hz.1)))
      (hj.mem_mulLongInvClosure_of_mul_self z'.2 hz'.2 (mul_self_eq_one_of_mem_longInv
        (mem_longInv_subgroup_iff.mp hz'.1)))
  have hZ : Z * Z = 1 :=
    mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_iff.mp hz.1)
  have hZ' : Z' * Z' = 1 :=
    mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_iff.mp hz'.1)
  have hkey := Equiv.ext key
  have hsx : Z * Z' * X = X * (Z * Z') := by
    calc Z * Z' * X = Z * Z' * (X * Z) * Z := by rw [mul_assoc (Z * Z'), mul_assoc X, hZ, mul_one]
      _ = X * Z * (Z * Z') * Z := by rw [hkey]
      _ = X * (Z * Z') := by
          rw [show X * Z * (Z * Z') * Z = X * (Z * (Z * Z') * Z) by group,
            show Z * (Z * Z') * Z = Z * Z' by
              rw [← mul_assoc, hZ, one_mul, hZZ']]
  refine hA.false_of_commute (s := z * z') (a := z) (b := x) ?_ hz.1.1 hx.1.1 hz.2 hx.2 hpp'
    (Subtype.ext ?_) (Subtype.ext hsx)
  · refine orderOf_eq_prime (Subtype.ext ?_) fun h => hzz' ?_
    · show Z * Z' * (Z * Z') = 1
      rw [mul_assoc, ← mul_assoc Z', ← hZZ', mul_assoc, hZ', mul_one, hZ]
    · have := eq_inv_of_mul_eq_one_right h
      rw [this, inv_eq_of_mul_eq_one_right (Subtype.ext hZ)]
  · show Z * Z' * Z = Z * (Z * Z')
    rw [mul_assoc, ← hZZ']

theorem existsUnique_fixed_of_isNaturalSE (hS : Sec4Setting G Ω)
    {w : G} (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) {j : D'.ι}
    (hj : IsNaturalSE (D'.M j)) :
    ∃! ψ : D'.Ψc j, D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ := by
  have hne := C.rho_vHat_ne_one_of_isNaturalSE D' hS hw hwv hj
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩
  have hM := D'.rho_mem_M_of_isNaturalSE hj xH
  have hsq : D'.ρ j xH * D'.ρ j xH = 1 := by
    rw [← map_mul, show xH * xH = 1 from Subtype.ext C.vHat_mul_vHat, map_one]
  have h2 : orderOf (⟨D'.ρ j xH, hM⟩ : D'.M j) = 2 :=
    orderOf_eq_prime (Subtype.ext (by rw [sq]; exact hsq)) fun h => hne (congrArg Subtype.val h)
  exact hj.existsUnique_fixed h2

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_mem_range_of_alternating {j : D'.ι} (hj : D'.M j = alternatingGroup (D'.Ψc j))
    {y : Equiv.Perm (D'.Ψc j)} (hy : y ∈ (D'.ρ j).range) (c : Equiv.Perm (D'.Ψc j)) :
    c * y * c⁻¹ ∈ (D'.ρ j).range := by
  have hAlt : alternatingGroup (D'.Ψc j) ≤ (D'.ρ j).range := hj ▸ Subgroup.map_le_range _ _
  have hcomm : c * y * c⁻¹ * y⁻¹ ∈ alternatingGroup (D'.Ψc j) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (Equiv.Perm.sign c) (Equiv.Perm.sign y)]
    group
  have := mul_mem (hAlt hcomm) hy
  rwa [inv_mul_cancel_right] at this

theorem rho_w_commute (hS : Sec4Setting G Ω) {w : G} (hw : w ∈ longInvSwap G Ω α C.β)
    (hwv : w * v = v * w) (k : D'.ι) :
    D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ *
        D'.ρ k ⟨C.vHat, C.vHat_mem_jHull hS⟩ =
      D'.ρ k ⟨C.vHat, C.vHat_mem_jHull hS⟩ *
        D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (C.twoPointElt_commute hw hwv)

theorem exists_fixed_w (hS : Sec4Setting G Ω) {w : G} (hw : w ∈ longInvSwap G Ω α C.β)
    (hwv : w * v = v * w) (k : D'.ι) :
    ∃ γ : D'.Ψc k, (∀ ψ, D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩
      ψ = ψ ↔ ψ = γ) ∧ D'.ρ k ⟨C.vHat, C.vHat_mem_jHull hS⟩ γ = γ := by
  obtain ⟨-, γ, hγ, huniq⟩ := D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) k
  have hγ' : D'.ρ k ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ γ = γ := hγ
  refine ⟨γ, fun ψ => ⟨huniq ψ, fun h => h ▸ hγ'⟩, huniq _ ?_⟩
  have h := congrArg (fun π : Equiv.Perm (D'.Ψc k) => π γ) (C.rho_w_commute D' hS hw hwv k)
  simp only [Equiv.Perm.mul_apply, hγ'] at h
  exact h

theorem card_fixed_le_three_of_alternating (hS : Sec4Setting G Ω)
    {w : G} (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) {j : D'.ι}
    (hj : D'.M j = alternatingGroup (D'.Ψc j)) :
    (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card ≤ 3 := by
  by_contra hcard
  rw [not_le] at hcard
  set V := D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ with hVdef
  set W := D'.ρ j ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ with hWdef
  obtain ⟨γ, hγW', hγV'⟩ := C.exists_fixed_w D' hS hw hwv j
  have hγW : ∀ ψ, W ψ = ψ ↔ ψ = γ := hγW'
  have hγV : V γ = γ := hγV'
  have hWJ : W ∈ longInv (Equiv.Perm (D'.Ψc j)) (D'.Ψc j) :=
    D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) j
  have hWW : ∀ ψ, W (W ψ) = ψ := fun ψ => by
    rw [← Equiv.Perm.mul_apply, mul_self_eq_one_of_mem_longInv hWJ, Equiv.Perm.one_apply]
  have hWV : W * V = V * W := C.rho_w_commute D' hS hw hwv j
  have hVW : ∀ ψ, V ψ = ψ → V (W ψ) = W ψ := fun ψ h => by
    rw [← Equiv.Perm.mul_apply, ← hWV, Equiv.Perm.mul_apply, h]
  obtain ⟨p₁, hp₁F, hp₁γ⟩ := Finset.exists_mem_ne
    (s := Finset.univ.filter fun ψ => V ψ = ψ) (by omega) γ
  obtain ⟨p₃, hp₃F, hp₃⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {γ, p₁, W p₁}) (lt_of_le_of_lt Finset.card_le_three hcard)
  have hV₁ : V p₁ = p₁ := (Finset.mem_filter.mp hp₁F).2
  have hV₃ : V p₃ = p₃ := (Finset.mem_filter.mp hp₃F).2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₃
  obtain ⟨hp₃γ, hp₃₁, hp₃₂⟩ := hp₃
  set p₂ := W p₁ with hp₂
  set p₄ := W p₃ with hp₄
  have hW₂ : W p₂ = p₁ := hWW p₁
  have hW₄ : W p₄ = p₃ := hWW p₃
  have hWγ : W γ = γ := (hγW γ).mpr rfl
  have h₂γ : p₂ ≠ γ := fun h => hp₁γ (by rw [← hW₂, h, hWγ])
  have h₁₂ : p₁ ≠ p₂ := fun h => hp₁γ ((hγW p₁).mp h.symm)
  have h₄γ : p₄ ≠ γ := fun h => hp₃γ (by rw [← hW₄, h, hWγ])
  have h₄₃ : p₄ ≠ p₃ := fun h => hp₃γ ((hγW p₃).mp h)
  have h₄₁ : p₄ ≠ p₁ := fun h => hp₃₂ (by rw [← hW₄, h])
  have h₄₂ : p₄ ≠ p₂ := fun h => hp₃₁ (by rw [← hW₄, h, hW₂])
  have hV₂ : V p₂ = p₂ := hVW p₁ hV₁
  have hV₄ : V p₄ = p₄ := hVW p₃ hV₃
  set s₂₃ := Equiv.swap p₂ p₃
  set s₀ := Equiv.swap γ p₂
  set s₂₄ := Equiv.swap p₂ p₄
  have hc₂₃ : s₂₃ * V = V * s₂₃ := swap_mul_comm_of_fixed hV₂ hV₃
  have hc₀ : s₀ * V = V * s₀ := swap_mul_comm_of_fixed hγV hV₂
  have hc₂₄ : s₂₄ * V = V * s₂₄ := swap_mul_comm_of_fixed hV₂ hV₄
  have hc₄₀ : s₂₄ * s₀ * V = V * (s₂₄ * s₀) := by
    rw [mul_assoc, hc₀, ← mul_assoc, hc₂₄, mul_assoc]
  have hWR : W ∈ (D'.ρ j).range := ⟨_, rfl⟩
  have hreal : ∀ c : Equiv.Perm (D'.Ψc j), c * V = V * c →
      ∃ c' ∈ longInvSwap G Ω α C.β,
        c' ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
          C.BlockAct D' c' (Function.update (fun k => D'.ρ k
            ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩) j (c * W * c⁻¹)) :=
    fun c hc => C.exists_realize hS D' hw hwv j (C.conj_mem_range_of_alternating D' hj hWR c)
      (conj_mem_longInv hWJ c) (conj_mul_comm hWV hc)
  obtain ⟨c₁, hc₁, hc₁V, hc₁B⟩ := hreal 1 (by rw [one_mul, mul_one])
  obtain ⟨c₂, hc₂, hc₂V, hc₂B⟩ := hreal s₂₃ hc₂₃
  obtain ⟨c₃, hc₃, hc₃V, hc₃B⟩ := hreal s₀ hc₀
  obtain ⟨c₄, hc₄, hc₄V, hc₄B⟩ := hreal (s₂₄ * s₀) hc₄₀
  have hB₁ := C.mem_stabB hc₁ hc₁V
  have hB₂ := C.mem_stabB hc₂ hc₂V
  have hB₃ := C.mem_stabB hc₃ hc₃V
  have hB₄ := C.mem_stabB hc₄ hc₄V
  have hL := (hc₁B.mul C D' hB₂ hc₂B).mul C D' (mul_mem hB₃ hB₄) (hc₃B.mul C D' hB₄ hc₄B)
  have hR := (hc₃B.mul C D' hB₄ hc₄B).mul C D' (mul_mem hB₁ hB₂) (hc₁B.mul C D' hB₂ hc₂B)
  obtain ⟨γ₀, -, hγ₀Δ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  obtain ⟨δ, hδ, hδc⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j hV₁
  have h := hL.apply_eq C D' (mul_mem (mul_mem hB₁ hB₂) (mul_mem hB₃ hB₄)) hR hδ
    (C.pair_commute_B hS hc₁ hc₁V hc₂ hc₂V hc₃ hc₃V hc₄ hc₄V hδ) j
  have hi₂₃ : s₂₃⁻¹ = s₂₃ := Equiv.swap_inv _ _
  have hi₀ : s₀⁻¹ = s₀ := Equiv.swap_inv _ _
  have hi₂₄ : s₂₄⁻¹ = s₂₄ := Equiv.swap_inv _ _
  simp only [hδc, Pi.mul_apply, Function.update_self, Equiv.Perm.mul_apply, one_mul, inv_one,
    mul_one, mul_inv_rev, hi₂₃, hi₀, hi₂₄] at h
  have e₁ : s₂₃ p₁ = p₁ := Equiv.swap_apply_of_ne_of_ne h₁₂ (Ne.symm hp₃₁)
  have e₂ : s₂₄ p₁ = p₁ := Equiv.swap_apply_of_ne_of_ne h₁₂ h₄₁.symm
  have e₃ : s₀ p₁ = p₁ := Equiv.swap_apply_of_ne_of_ne hp₁γ h₁₂
  have e₄ : s₂₄ γ = γ := Equiv.swap_apply_of_ne_of_ne h₂γ.symm h₄γ.symm
  have e₅ : s₀ p₄ = p₄ := Equiv.swap_apply_of_ne_of_ne h₄γ h₄₂
  have e₆ : s₀ p₃ = p₃ := Equiv.swap_apply_of_ne_of_ne hp₃γ hp₃₂
  have l₁ : W (s₂₃ (W (s₂₃ p₁))) = p₄ := by
    rw [e₁, show s₂₃ (W p₁) = p₃ from Equiv.swap_apply_left _ _]
  have l₂ : s₂₄ (s₀ (W (s₀ (s₂₄ p₁)))) = γ := by
    rw [e₂, e₃, show s₀ (W p₁) = γ from Equiv.swap_apply_right _ _, e₄]
  have l₃ : s₀ (W (s₀ γ)) = p₁ := by
    rw [show s₀ γ = p₂ from Equiv.swap_apply_left _ _, hW₂, e₃]
  have r₁ : s₂₄ (s₀ (W (s₀ (s₂₄ p₄)))) = p₄ := by
    rw [show s₂₄ p₄ = p₂ from Equiv.swap_apply_right _ _,
      show s₀ p₂ = γ from Equiv.swap_apply_right _ _, hWγ,
      show s₀ γ = p₂ from Equiv.swap_apply_left _ _,
      show s₂₄ p₂ = p₄ from Equiv.swap_apply_left _ _]
  have r₂ : s₀ (W (s₀ p₄)) = p₃ := by rw [e₅, hW₄, e₆]
  rw [l₂, l₃, l₁, r₁, r₂] at h
  exact h₄₃ h

theorem eq_of_one_lt_card_fixed (hS : Sec4Setting G Ω)
    {w : G} (hw : w ∈ longInvSwap G Ω α C.β) (hwv : w * v = v * w) {j₁ j₂ : D'.ι}
    (hj₁ : D'.M j₁ = alternatingGroup (D'.Ψc j₁)) (hj₂ : D'.M j₂ = alternatingGroup (D'.Ψc j₂))
    (h₁ : 1 < (Finset.univ.filter fun ψ => D'.ρ j₁ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card)
    (h₂ : 1 < (Finset.univ.filter fun ψ => D'.ρ j₂ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card) :
    j₁ = j₂ := by
  by_contra hne
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩ with hwH
  have hdata : ∀ j : D'.ι, D'.M j = alternatingGroup (D'.Ψc j) →
      1 < (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card →
      ∃ (γ p q : D'.Ψc j) (y : Equiv.Perm (D'.Ψc j)) (c : G),
        D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ γ = γ ∧
        c ∈ longInvSwap G Ω α C.β ∧
        c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧
        C.BlockAct D' c (Function.update (fun k => D'.ρ k wH) j y) ∧
        (D'.ρ j wH * y) γ = p ∧ (D'.ρ j wH * y) p = q ∧ (D'.ρ j wH * y) q = γ ∧
        γ ≠ p ∧ γ ≠ q ∧ p ≠ q := by
    intro j hj hcard
    set V := D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ with hVdef
    set W := D'.ρ j wH with hWdef
    obtain ⟨γ, hγW', hγV'⟩ := C.exists_fixed_w D' hS hw hwv j
    have hγW : ∀ ψ, W ψ = ψ ↔ ψ = γ := hγW'
    have hγV : V γ = γ := hγV'
    have hWJ : W ∈ longInv (Equiv.Perm (D'.Ψc j)) (D'.Ψc j) :=
      D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) j
    have hWW : ∀ ψ, W (W ψ) = ψ := fun ψ => by
      rw [← Equiv.Perm.mul_apply, mul_self_eq_one_of_mem_longInv hWJ, Equiv.Perm.one_apply]
    have hWV : W * V = V * W := C.rho_w_commute D' hS hw hwv j
    obtain ⟨p, hpF, hpγ⟩ := Finset.exists_mem_ne
      (s := Finset.univ.filter fun ψ => V ψ = ψ) hcard γ
    have hVp : V p = p := (Finset.mem_filter.mp hpF).2
    have hc : Equiv.swap γ p * V = V * Equiv.swap γ p := swap_mul_comm_of_fixed hγV hVp
    obtain ⟨c, hc', hcV, hcB⟩ := C.exists_realize hS D' hw hwv j
      (C.conj_mem_range_of_alternating D' hj ⟨wH, rfl⟩ (Equiv.swap γ p))
      (conj_mem_longInv hWJ (Equiv.swap γ p)) (conj_mul_comm hWV hc)
    obtain ⟨e₁, e₂, e₃, d₁, d₂, d₃⟩ := cycle3_of_swap hWW hγW hpγ
    exact ⟨γ, p, W p, _, c, hγV, hc', hcV, hcB, e₁, e₂, e₃, d₁, d₂, d₃⟩
  obtain ⟨γ₁, p₁, q₁, y₁, c₁, hγ₁, hc₁, hc₁V, hc₁B, e₁₁, e₁₂, e₁₃, d₁₁, d₁₂, d₁₃⟩ :=
    hdata j₁ hj₁ h₁
  obtain ⟨γ₂, p₂, q₂, y₂, c₂, hγ₂, hc₂, hc₂V, hc₂B, e₂₁, e₂₂, e₂₃, d₂₁, d₂₂, d₂₃⟩ :=
    hdata j₂ hj₂ h₂
  have hwV : w ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    mem_centralizer_zpowers_iff.mpr hwv
  have hBw := C.mem_stabB hw hwV
  have hB₁ := C.mem_stabB hc₁ hc₁V
  have hB₂ := C.mem_stabB hc₂ hc₂V
  have hwB : C.BlockAct D' w fun k => D'.ρ k wH := C.blockAct_w D' hS hw
  have hg₁ := hwB.mul C D' hB₁ hc₁B
  have hg₂ := hwB.mul C D' hB₂ hc₂B
  have hBg₁ : w * c₁ ∈ C.stabB := mul_mem hBw hB₁
  have hBg₂ : w * c₂ ∈ C.stabB := mul_mem hBw hB₂
  obtain ⟨x, y, k, l, hxy⟩ := C.exists_zpow_pair hS hw hwV hc₁ hc₁V hw hwV hc₂ hc₂V
  have hBh : (w * c₁) ^ x * (w * c₂) ^ y ∈ C.stabB :=
    mul_mem (zpow_mem hBg₁ x) (zpow_mem hBg₂ y)
  have hh := (hg₁.zpow C D' hBg₁ x).mul C D' (zpow_mem hBg₂ y) (hg₂.zpow C D' hBg₂ y)
  have hhk := hh.zpow C D' hBh k
  have hhl := hh.zpow C D' hBh l
  obtain ⟨γ₀, -, hγ₀Δ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j₁ hγ₁
  obtain ⟨δ, hδ, hδc⟩ := C.exists_mem_B_coord D' hS (γ₀ := δ₁) hδ₁ j₂ hγ₂
  have hδ₁' : D'.coord δ j₁ = γ₁ := by
    rw [hδc, Function.update_of_ne hne, hδ₁c, Function.update_self]
  have hδ₂' : D'.coord δ j₂ = γ₂ := by rw [hδc, Function.update_self]
  have hline := ((C.mem_holtDelta_iff hS ⟨δ, hδ⟩).mp δ.2).1
  obtain ⟨hK, hL⟩ := hxy ⟨δ, hδ⟩ hline
  have hW₁ : D'.ρ j₁ wH * D'.ρ j₁ wH = 1 :=
    mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) j₁)
  have hW₂ : D'.ρ j₂ wH * D'.ρ j₂ wH = 1 :=
    mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) j₂)
  have E₁ := hg₁.apply_eq C D' hBg₁ hhk hδ hK j₁
  have E₂ := hg₁.apply_eq C D' hBg₁ hhk hδ hK j₂
  have E₃ := hg₂.apply_eq C D' hBg₂ hhl hδ hL j₁
  have E₄ := hg₂.apply_eq C D' hBg₂ hhl hδ hL j₂
  simp only [Pi.mul_apply, Pi.pow_apply, Function.update_self, Function.update_of_ne hne,
    Function.update_of_ne (Ne.symm hne), hW₁, hW₂, one_zpow, mul_one, one_mul, ← zpow_mul,
    hδ₁', hδ₂', Equiv.Perm.one_apply] at E₁ E₂ E₃ E₄
  rw [e₁₁] at E₁
  rw [e₂₁] at E₄
  have m₁ := ((zpow_apply_three_iff e₁₁ e₁₂ e₁₃ d₁₁ d₁₂ d₁₃ (x * k)).2).mp E₁.symm
  have m₂ := ((zpow_apply_three_iff e₂₁ e₂₂ e₂₃ d₂₁ d₂₂ d₂₃ (y * k)).1).mp E₂.symm
  have m₃ := ((zpow_apply_three_iff e₁₁ e₁₂ e₁₃ d₁₁ d₁₂ d₁₃ (x * l)).1).mp E₃.symm
  have m₄ := ((zpow_apply_three_iff e₂₁ e₂₂ e₂₃ d₂₁ d₂₂ d₂₃ (y * l)).2).mp E₄.symm
  have hA := Int.mul_emod (x * k) (y * l) 3
  have hB := Int.mul_emod (x * l) (y * k) 3
  rw [m₁, m₄] at hA
  rw [m₃, m₂] at hB
  have hAB : x * k * (y * l) = x * l * (y * k) := by ring
  rw [hAB] at hA
  omega

end Prop23

end P49Config

end CFSG.Holt.H78
