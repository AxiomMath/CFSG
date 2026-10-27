module

public import CFSG.Holt.H78.Sec4Prop49Blocks
import CFSG.Holt.H78.Sec4Lemma42
import CFSG.Holt.H78.Sec4KnownKV
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

namespace P49Config

section Prop23

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)
  (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))

include C

theorem card_fixed_emod_four (hS : Sec4Setting G Ω) {w : G} (hw : w ∈ longInvSwap G Ω α C.β)
    (hwv' : w * v ∈ longInvSwap G Ω α C.β) (j : D'.ι) :
    (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card % 4 =
      Fintype.card (D'.Ψc j) % 4 := by
  set xH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨C.vHat, C.vHat_mem_jHull hS⟩
  set wH : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hw)⟩
  set w'H : jHull (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β) :=
    ⟨_, mem_jHull_of_mem_longInv (C.twoPointElt_mem_longInv hS hwv')⟩
  have he : xH = wH * w'H := Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (by
    show v • (δ : Ω) = w • ((w * v) • (δ : Ω))
    rw [← mul_smul, ← mul_assoc, mul_self_eq_one_of_mem_longInv hw.1, one_mul])))
  have hWJ := D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hw) j
  have hW'J := D'.rho_mem_longInv (C.twoPointElt_mem_longInv hS hwv') j
  have hsign : Equiv.Perm.sign (D'.ρ j xH) = 1 := by
    rw [he, map_mul, map_mul, sign_eq_of_mem_longInv_perm hWJ hW'J, Int.units_mul_self]
  have hsq : D'.ρ j xH ^ 2 = 1 := by
    rw [← map_pow, show xH ^ 2 = 1 from Subtype.ext (by rw [sq]; exact C.vHat_mul_vHat),
      map_one]
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, neg_one_pow_eq_one_iff_even (by decide)] at hsign
  have h2 := Equiv.Perm.two_dvd_card_support hsq
  have hfix := Equiv.Perm.card_fixedPoints (D'.ρ j xH)
  rw [Equiv.Perm.sum_cycleType] at hfix
  have hle : (D'.ρ j xH).support.card ≤ Fintype.card (D'.Ψc j) := Finset.card_le_univ _
  have hcard : (Finset.univ.filter fun ψ => D'.ρ j xH ψ = ψ).card =
      Fintype.card (Function.fixedPoints (D'.ρ j xH)) := by
    rw [← Fintype.card_subtype]
    rfl
  rw [hcard, hfix]
  obtain ⟨m, hm⟩ := hsign
  obtain ⟨d, hd⟩ := h2
  omega

theorem prop_2_3 (hS : Sec4Setting G Ω) :
    (∀ j, IsNaturalSE (D'.M j) →
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1) ∧
    (∀ j, (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card % 4 =
      Fintype.card (D'.Ψc j) % 4) ∧
    (∀ j, D'.M j = alternatingGroup (D'.Ψc j) →
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card ≤ 3) ∧
    (∀ j j', 1 < (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card →
      1 < (Finset.univ.filter fun ψ => D'.ρ j' ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card →
        j = j') := by
  obtain ⟨w, hw, hwv, hwv'⟩ := C.exists_mem_longInvSwap_mul hS
  have hSE : ∀ j, IsNaturalSE (D'.M j) →
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1 :=
    fun j hj => by
      obtain ⟨γ, hγ, huniq⟩ := C.existsUnique_fixed_of_isNaturalSE D' hS hw hwv hj
      exact Finset.card_eq_one.mpr ⟨γ, Finset.ext fun ψ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨huniq ψ, fun h => h ▸ hγ⟩⟩
  have halt : ∀ j, 1 < (Finset.univ.filter fun ψ =>
      D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card → D'.M j = alternatingGroup (D'.Ψc j) :=
    fun j h => by
      rcases D'.factor j with ⟨hA, -⟩ | hj
      · exact hA
      · exact absurd (hSE j hj) (by omega)
  exact ⟨hSE, fun j => C.card_fixed_emod_four D' hS hw hwv' j,
    fun j hj => C.card_fixed_le_three_of_alternating D' hS hw hwv hj,
    fun j j' h h' => C.eq_of_one_lt_card_fixed D' hS hw hwv (halt j h) (halt j' h') h h'⟩

theorem mem_orbit_of_coord (hS : Sec4Setting G Ω) (j₀ : D'.ι)
    (h1 : ∀ j, j ≠ j₀ →
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1)
    {γ γ' : holtDelta G Ω α C.β} (hγ : (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v))
    (hγ' : (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) (h₀ : D'.coord γ j₀ = D'.coord γ' j₀) :
    γ' ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ := by
  refine (D'.coord_eq_iff γ γ').mp (funext fun j => ?_)
  rcases eq_or_ne j j₀ with rfl | hj
  · exact h₀
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (h1 j hj)
    have m : ∀ ε : holtDelta G Ω α C.β, (ε : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
        D'.coord ε j = a := fun ε hε => by
      have hm : D'.coord ε j ∈ Finset.univ.filter fun ψ =>
          D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.mem_fixSet_iff_rho hS D' ε).mp hε j⟩
      rw [ha] at hm
      exact Finset.mem_singleton.mp hm
    rw [m γ hγ, m γ' hγ']

theorem orbit_iff_of_card_eq_one (hS : Sec4Setting G Ω)
    (h1 : ∀ j,
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1)
    (γ : holtDelta G Ω α C.β) (hγ : (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v))
    (γ' : holtDelta G Ω α C.β) :
    γ' ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ ↔
      (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
  constructor
  · intro h
    have hc := (D'.coord_eq_iff γ γ').mpr h
    refine (C.mem_fixSet_iff_rho hS D' γ').mpr fun j => ?_
    rw [← hc]
    exact (C.mem_fixSet_iff_rho hS D' γ).mp hγ j
  · intro h'
    refine (D'.coord_eq_iff γ γ').mp (funext fun j => ?_)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (h1 j)
    have m : ∀ ε : holtDelta G Ω α C.β, (ε : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
        D'.coord ε j = a := fun ε hε => by
      have hm : D'.coord ε j ∈ Finset.univ.filter fun ψ =>
          D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.mem_fixSet_iff_rho hS D' ε).mp hε j⟩
      rw [ha] at hm
      exact Finset.mem_singleton.mp hm
    rw [m γ hγ, m γ' h']

theorem exists_three_orbits (hS : Sec4Setting G Ω) {j₀ : D'.ι}
    (h3 : (Finset.univ.filter fun ψ => D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 3)
    (h1 : ∀ j, j ≠ j₀ →
      (Finset.univ.filter fun ψ => D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1) :
    ∃ γ₁ γ₂ γ₃ : holtDelta G Ω α C.β,
      (γ₁ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ (γ₂ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
      (γ₃ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
      γ₂ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
      γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
      γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∧
      ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∨
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∨
        δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₃ := by
  obtain ⟨a, b, c, hab, hac, hbc, hF⟩ := Finset.card_eq_three.mp h3
  have hfix : ∀ x, x ∈ ({a, b, c} : Finset (D'.Ψc j₀)) →
      D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ x = x := fun x hx => by
    rw [← hF] at hx
    exact (Finset.mem_filter.mp hx).2
  obtain ⟨γ₀, -, hγ₀Δ, -, -⟩ := C.exists_mem_holtDelta_ne hS
  obtain ⟨δa, hδa, hδac⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j₀
    (hfix a (by simp))
  obtain ⟨δb, hδb, hδbc⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j₀
    (hfix b (by simp))
  obtain ⟨δc, hδc, hδcc⟩ := C.exists_mem_B_coord D' hS (γ₀ := ⟨γ₀, hγ₀Δ⟩) γ₀.2 j₀
    (hfix c (by simp))
  have ca : D'.coord δa j₀ = a := by rw [hδac, Function.update_self]
  have cb : D'.coord δb j₀ = b := by rw [hδbc, Function.update_self]
  have cc : D'.coord δc j₀ = c := by rw [hδcc, Function.update_self]
  have hne : ∀ {ε ε' : holtDelta G Ω α C.β}, D'.coord ε j₀ ≠ D'.coord ε' j₀ →
      ε' ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) ε :=
    fun h hm => h (congrFun ((D'.coord_eq_iff _ _).mpr hm) j₀)
  refine ⟨δa, δb, δc, hδa, hδb, hδc, hne (by rw [ca, cb]; exact hab),
    hne (by rw [ca, cc]; exact hac), hne (by rw [cb, cc]; exact hbc), fun δ hδ => ?_⟩
  have hδF : D'.coord δ j₀ ∈ ({a, b, c} : Finset (D'.Ψc j₀)) := by
    rw [← hF]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.mem_fixSet_iff_rho hS D' δ).mp hδ j₀⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hδF
  rcases hδF with h | h | h
  · exact Or.inl (C.mem_orbit_of_coord D' hS j₀ h1 hδa hδ (by rw [ca, h]))
  · exact Or.inr (Or.inl (C.mem_orbit_of_coord D' hS j₀ h1 hδb hδ (by rw [cb, h])))
  · exact Or.inr (Or.inr (C.mem_orbit_of_coord D' hS j₀ h1 hδc hδ (by rw [cc, h])))

end Prop23

end P49Config

section Steps

variable (G : Type) [Group G] (Ω : Type) [MulAction G Ω]

@[expose] def P49Step94 : Prop :=
  ∀ {α : Ω} {v : G} (C : P49Config G Ω α v), ¬ ∃ γ₁ γ₂ γ₃ : holtDelta G Ω α C.β,
    (γ₁ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧ (γ₂ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
    (γ₃ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) ∧
    γ₂ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
    γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∧
    γ₃ ∉ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∧
    ∀ δ : holtDelta G Ω α C.β, (δ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₁ ∨
      δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₂ ∨
      δ ∈ orbit (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)) γ₃

@[expose] def P49Step95 : Prop :=
  ∀ {α : Ω} {v : G} (C : P49Config G Ω α v),
    ¬ IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)

@[expose] def P49Step96 : Prop :=
  ∀ {α β : Ω}, α ≠ β → ∀ (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) (k : D'.ι),
    D'.M k = alternatingGroup (D'.Ψc k) → 9 ≤ Fintype.card (D'.Ψc k) → False

@[expose] def P49Step97b : Prop :=
  ∀ {α : Ω} {v : G} (C : P49Config G Ω α v)
    (D' : HoltData (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β)),
    Nonempty D'.ι → (∀ k, IsNaturalSE (D'.M k)) →
    (∀ γ : holtDelta G Ω α C.β, (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
      ∀ γ' : holtDelta G Ω α C.β, γ' ∈ orbit (jOddCore (twoPointSection G Ω α C.β)
        (holtDelta G Ω α C.β)) γ ↔ (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v)) →
    (∀ k, Fintype.card (D'.Ψc k) = 5) →
      Fintype.card D'.ι ≤ 1 ∧ Odd (Nat.card (twoPointKernel G Ω α C.β))

end Steps

section TwoComponents

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.false_of_isNaturalSE_of_ne (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (D' : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)) {i l : D'.ι} (hil : i ≠ l)
    (hi : IsNaturalSE (D'.M i)) (h5 : Fintype.card (D'.Ψc i) ≠ 5) (hl : IsNaturalSE (D'.M l)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := three_le_card_holtDelta_of_holtData hS.star D'
  obtain ⟨γ⟩ : Nonempty (holtDelta G Ω α β) := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨n, e, f, hA⟩ := IsNaturalSE.exists_isBenderAction hl
  have hcard : 3 ≤ (longInvAt (D'.M l) (D'.Ψc l) (D'.coord γ l)).ncard := by
    rw [hA.ncard_longInvAt]
    have := hA.four_le_q
    omega
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero
    (s := longInvAt (D'.M l) (D'.Ψc l) (D'.coord γ l)) (by omega)
  obtain ⟨y', hy', hyy'⟩ := Set.exists_ne_of_one_lt_ncard
    (s := longInvAt (D'.M l) (D'.Ψc l) (D'.coord γ l)) (by omega) y
  set Y : Equiv.Perm (D'.Ψc l) := (y : Equiv.Perm (D'.Ψc l)) with hYdef
  set Y' : Equiv.Perm (D'.Ψc l) := (y' : Equiv.Perm (D'.Ψc l)) with hY'def
  have hYJ : Y ∈ longInv (Equiv.Perm (D'.Ψc l)) (D'.Ψc l) := mem_longInv_subgroup_iff.mp hy.1
  have hY'J : Y' ∈ longInv (Equiv.Perm (D'.Ψc l)) (D'.Ψc l) := mem_longInv_subgroup_iff.mp hy'.1
  have hYY : Y * Y = 1 := mul_self_eq_one_of_mem_longInv hYJ
  have hY'Y' : Y' * Y' = 1 := mul_self_eq_one_of_mem_longInv hY'J
  have hYY' : Y * Y' = Y' * Y := hl.commute_of_mem_mulLongInvClosure
    (hl.mem_mulLongInvClosure_of_mul_self y.2 hy.2 hYY)
    (hl.mem_mulLongInvClosure_of_mul_self y'.2 hy'.2 hY'Y')
  have hP2 : (Y * Y') * (Y * Y') = 1 := by
    rw [mul_assoc, ← mul_assoc Y', ← hYY', mul_assoc, hY'Y', mul_one, hYY]
  have hP1 : Y * Y' ≠ 1 := fun h => hyy' (Subtype.ext (by
    show Y' = Y
    rw [← inv_eq_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hYY]))
  have hrange : (D'.ρ l).range = D'.M l :=
    D'.range_rho_of_not_isOuterFactor hl.not_isOuterFactor
  set T : ∀ k, Equiv.Perm (D'.Ψc k) := fun k => D'.ρ k D'.tHull with hT
  have hreal : ∀ Z : Equiv.Perm (D'.Ψc l), Z ∈ D'.M l →
      Z ∈ longInv (Equiv.Perm (D'.Ψc l)) (D'.Ψc l) →
      ∃ x : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β),
        (x : twoPointSection G Ω α β) ∈ longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) ∧
          ∀ k, D'.ρ k x = Function.update T l Z k := fun Z hZM hZJ =>
    D'.exists_mem_longInv_rho_eq _ (fun k => by
      rcases eq_or_ne k l with rfl | hk
      · rw [Function.update_self, hrange]
        exact hZM
      · rw [Function.update_of_ne hk]
        exact ⟨_, rfl⟩) (fun k => by
      rcases eq_or_ne k l with rfl | hk
      · rw [Function.update_self]
        exact hZJ
      · rw [Function.update_of_ne hk]
        exact D'.rho_mem_longInv D'.t_mem k)
  obtain ⟨x₁, hx₁, hρ₁⟩ := hreal Y y.2 hYJ
  obtain ⟨x₂, hx₂, hρ₂⟩ := hreal Y' y'.2 hY'J
  have hx₁₂S : ((x₁ * x₂ : jHull _ _) : twoPointSection G Ω α β) ∈ D'.socPre :=
    D'.mul_mem_socPre_of_mem_longInv (hS.star_twoPoint hαβ h3)
      (hS.holtTheorem1Below_twoPoint h3) hx₁ hx₂
  have hρl : D'.ρ l (x₁ * x₂) = Y * Y' := by
    rw [map_mul, hρ₁, hρ₂, Function.update_self, Function.update_self]
  have hρk : ∀ k, k ≠ l → D'.ρ k (x₁ * x₂) = 1 := fun k hk => by
    rw [map_mul, hρ₁, hρ₂, Function.update_of_ne hk, Function.update_of_ne hk]
    exact mul_self_eq_one_of_mem_longInv (D'.rho_mem_longInv D'.t_mem k)
  obtain ⟨c₁, hc₁, hc₁x⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mp hx₁
  obtain ⟨c₂, hc₂, hc₂x⟩ := (hS.mem_longInv_twoPointSection_iff hαβ h3 _).mp hx₂
  have hgα : (c₁ * c₂) • α = α := by rw [mul_smul, hc₂.2, smul_eq_of_mem_longInvSwap hc₁]
  have hgβ : (c₁ * c₂) • β = β := by rw [mul_smul, smul_eq_of_mem_longInvSwap hc₂, hc₁.2]
  have hgX : c₁ * c₂ ∈ stabilizer G ({α, β} : Set Ω) := stabilizer_inf_le_stabilizer_pair α β
    (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr hgα, mem_stabilizer_iff.mpr hgβ⟩)
  set gs : stabilizer G ({α, β} : Set Ω) := ⟨c₁ * c₂, hgX⟩
  have hgimg : twoPointHom G Ω α β gs =
      (((x₁ * x₂ : jHull _ _) : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) :=
    Equiv.ext fun δ => Subtype.ext (by
      show (c₁ * c₂) • (δ : Ω) = ((((x₁ : twoPointSection G Ω α β) : Equiv.Perm _)
        (((x₂ : twoPointSection G Ω α β) : Equiv.Perm _) δ) : holtDelta G Ω α β) : Ω)
      rw [hc₁x, hc₂x, mul_smul])
  obtain ⟨k₂, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c₁ * c₂)).ne'
  set u := (c₁ * c₂) ^ m with hu
  set EH : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) := (x₁ * x₂) ^ m with hEH
  have hu2 : u ^ 2 ^ k₂ = 1 := by
    rw [hu, ← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have huE : ∀ δ : holtDelta G Ω α β,
      u • (δ : Ω) = (((EH : twoPointSection G Ω α β) • δ : holtDelta G Ω α β) : Ω) := fun δ => by
    have hpow : twoPointHom G Ω α β (gs ^ m) =
        ((EH : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) := by
      rw [map_pow, hgimg]
      rfl
    rw [show u = ((gs ^ m : stabilizer G ({α, β} : Set Ω)) : G) from rfl,
      ← coe_twoPointHom_apply, hpow]
    rfl
  have hYm : (Y * Y') ^ m = Y * Y' := by
    obtain ⟨t, rfl⟩ := hm
    rw [pow_succ, pow_mul, sq, hP2, one_pow, one_mul]
  have hEl : D'.ρ l EH = Y * Y' := by rw [hEH, map_pow, hρl, hYm]
  have hEk : ∀ k, k ≠ l → D'.ρ k EH = 1 := fun k hk => by rw [hEH, map_pow, hρk k hk, one_pow]
  have hES : (EH : twoPointSection G Ω α β) ∈ D'.socPre := by
    rw [hEH, Subgroup.coe_pow]
    exact pow_mem hx₁₂S m
  have hE2O : ((EH : twoPointSection G Ω α β)) ^ 2 ∈
      jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) := by
    rw [← D'.socPre_inf_jOrbitKernel]
    refine ⟨pow_mem hES 2, ?_⟩
    have h := (D'.mem_jOrbitKernel_iff_rho (h := EH ^ 2)).mpr fun k => by
      rw [map_pow]
      rcases eq_or_ne k l with rfl | hk
      · rw [hEl, sq, hP2]
      · rw [hEk k hk, one_pow]
    exact h
  have hpow : twoPointHom G Ω α β (gs ^ m) =
      ((EH : twoPointSection G Ω α β) : Equiv.Perm (holtDelta G Ω α β)) := by
    rw [map_pow, hgimg]
    rfl
  have hEpow : (EH : twoPointSection G Ω α β) ^ 2 ^ k₂ = 1 := by
    have h1 : (gs ^ m) ^ 2 ^ k₂ = 1 := Subtype.ext hu2
    have h2 := congrArg (twoPointHom G Ω α β) h1
    rw [map_pow, map_one, hpow] at h2
    exact Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])
  have hE22 : ((EH : twoPointSection G Ω α β) ^ 2) ^ 2 ^ k₂ = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hEpow, one_pow]
  have hE1 : ((EH : twoPointSection G Ω α β)) ^ 2 = 1 := by
    have hodd : Odd (orderOf ((EH : twoPointSection G Ω α β) ^ 2)) :=
      Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ hE2O)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hE22)
    rw [hj] at hodd
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by rw [hj, pow_zero])
    · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩))
  have hEne : (EH : twoPointSection G Ω α β) ≠ 1 := fun h => hP1 (by
    rw [← hEl, show EH = 1 from Subtype.ext h, map_one])
  have hE2 : orderOf (EH : twoPointSection G Ω α β) = 2 := orderOf_eq_prime hE1 hEne
  have hYγ : Y (D'.coord γ l) = D'.coord γ l := hy.2
  have hY'γ : Y' (D'.coord γ l) = D'.coord γ l := hy'.2
  have hfix : ∀ δ : holtDelta G Ω α β, (∀ j, j ≠ i → D'.coord δ j = D'.coord γ j) →
      (EH : twoPointSection G Ω α β) • δ = δ := fun δ hδ => by
    have hc : D'.coord δ = D'.coord ((EH : twoPointSection G Ω α β) • δ) := funext fun k => by
      rw [D'.coord_smul EH δ k]
      rcases eq_or_ne k l with rfl | hk
      · rw [hEl, Equiv.Perm.mul_apply, hδ k (Ne.symm hil), hY'γ, hYγ]
      · rw [hEk k hk, Equiv.Perm.one_apply]
    exact (hS.lemma_2_4_iv_twoPointSection h3 D' EH.2 hE2 ((D'.coord_eq_iff _ _).mp hc)).1 hES δ
      (mem_orbit_self δ)
  have hP : IsPGroup 2 (Subgroup.zpowers u) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hu2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hV1 : Subgroup.zpowers u ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    intro h1
    refine hEne (Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_))
    show (((EH : twoPointSection G Ω α β) • δ : holtDelta G Ω α β) : Ω) = (δ : Ω)
    rw [← huE δ, h1, one_smul]
  have huα : u • α = α := by
    rw [hu, ← mem_stabilizer_iff]
    exact pow_mem (mem_stabilizer_iff.mpr hgα) m
  have huβ : u • β = β := by
    rw [hu, ← mem_stabilizer_iff]
    exact pow_mem (mem_stabilizer_iff.mpr hgβ) m
  refine hS.false_of_line_subset_fixSet hαβ D' hi h5 γ hP hV1
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨mem_stabilizer_iff.mpr huα,
      mem_stabilizer_iff.mpr huβ⟩)) fun δ hδ => ?_
  rw [mem_fixSet_iff_le_stabilizer, Subgroup.zpowers_le, mem_stabilizer_iff, huE δ, hfix δ hδ]

end TwoComponents

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.prop_4_9_of (hS : Sec4Setting G Ω) (h94 : P49Step94 G Ω)
    (h95 : P49Step95 G Ω) (h96 : P49Step96 G Ω) (h97b : P49Step97b G Ω)
    {α : Ω} {v : G} (hv : IsTypeL G Ω α v)
    (hO : CFSG.pPrimeCore 2 (typeLSection G Ω v) = ⊥)
    (D : HoltData (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)))
    (hSE : ∀ k, IsNaturalSE (factorImage _ _ (D.L k) (D.ρ k))) (i : D.ι)
    {a b : fixSet Ω (Subgroup.zpowers v)} (ha : (a : Ω) = α) (hab : D.coord a i ≠ D.coord b i)
    (hab' : ∀ j ≠ i, D.coord a j = D.coord b j) :
    Odd (Nat.card (twoPointKernel G Ω α b)) ∧
      ∃ D' : HoltData (twoPointSection G Ω α b) (holtDelta G Ω α b),
        Fintype.card D'.ι = 1 ∧ (∀ k, IsNaturalSE (factorImage _ _ (D'.L k) (D'.ρ k))) ∧
        ∀ γ : holtDelta G Ω α b, (γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) →
          ∀ γ' : holtDelta G Ω α b, γ' ∈ orbit (jOddCore (twoPointSection G Ω α b)
            (holtDelta G Ω α b)) γ ↔ (γ' : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
  set C : P49Config G Ω α v := ⟨hv, D, hO, hSE, i, a, b, ha, hab, hab'⟩ with hC
  have h3 := C.three_le_card_holtDelta hS
  obtain ⟨D'⟩ := hS.holtData_twoPoint h3
  obtain ⟨hSE', hpar, halt3, huniq⟩ := C.prop_2_3 D' hS
  have hodd : ∀ j, (Finset.univ.filter fun ψ =>
      D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card % 2 = 1 := fun j => by
    have h1 := hpar j
    have h2 := Nat.odd_iff.mp (D'.odd_card_Ψc j)
    omega
  have hall : ∀ j, (Finset.univ.filter fun ψ =>
      D'.ρ j ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 1 := by
    by_contra hne
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hne
    have hgt : 1 < (Finset.univ.filter fun ψ =>
        D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card := by
      have := hodd j₀
      omega
    have hj₀alt : D'.M j₀ = alternatingGroup (D'.Ψc j₀) := by
      rcases D'.factor j₀ with ⟨hA, -⟩ | hj
      · exact hA
      · exact absurd (hSE' j₀ hj) hj₀
    have h3' : (Finset.univ.filter fun ψ =>
        D'.ρ j₀ ⟨C.vHat, C.vHat_mem_jHull hS⟩ ψ = ψ).card = 3 := by
      have := halt3 j₀ hj₀alt
      have := hodd j₀
      omega
    refine h94 C (C.exists_three_orbits D' hS h3' fun j hj => ?_)
    by_contra h
    have := hodd j
    exact hj (huniq j j₀ (by omega) hgt)
  have hB := C.orbit_iff_of_card_eq_one D' hS hall
  have hne : Nonempty D'.ι := by
    rcases isEmpty_or_nonempty D'.ι with h | h
    · exact absurd (D'.isEmpty_ι_iff.mp h) (h95 C)
    · exact h
  have hSEall : ∀ k, IsNaturalSE (D'.M k) := fun k => by
    rcases D'.factor k with ⟨hA, h7⟩ | hk
    · exfalso
      have hm := hpar k
      rw [hall k] at hm
      exact h96 C.ne D' k hA (by omega)
    · exact hk
  obtain ⟨k₀⟩ := hne
  by_cases h5all : ∀ k, Fintype.card (D'.Ψc k) = 5
  · obtain ⟨hle, hT⟩ := h97b C D' ⟨k₀⟩ hSEall hB h5all
    have hpos : 0 < Fintype.card D'.ι := Fintype.card_pos_iff.mpr ⟨k₀⟩
    exact ⟨hT, D', by omega, hSEall, hB⟩
  · obtain ⟨k₁, hk₁⟩ := not_forall.mp h5all
    have hcard1 : Fintype.card D'.ι = 1 := Fintype.card_eq_one_iff.mpr ⟨k₁, fun k => by
      by_contra hk
      exact hS.false_of_isNaturalSE_of_ne C.ne D' (Ne.symm hk) (hSEall k₁) hk₁ (hSEall k)⟩
    exact ⟨(hS.lemma_4_2 C.ne D' k₁ (hSEall k₁) hk₁).1, D', hcard1, hSEall, hB⟩

end Main

end CFSG.Holt.H78
