module

public import CFSG.GF2Type.Widths1112.Co2Module.Blocks
public import CFSG.GF2Type.Widths1112.Co2Module.Matrices
public import CFSG.Monster.GMS.Griess13.Gluing
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open Finset

section TwoPower

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem co2u_add_self (x : V) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) x, h2, zero_smul]

private theorem co2u_eq_of_add_eq_zero {x y : V} (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [co2u_add_self y, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]

private theorem co2u_exists_coeffs (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W = 2) {x : V} (hx : x ∈ W) (hx0 : x ≠ 0)
    {S : V} (hS : S ∈ W) (hSx : ∀ a : ZMod 2, a • x ≠ S) {y : V} (hy : y ∈ W) :
    ∃ a b : ZMod 2, y = a • x + b • S := by
  haveI : FiniteDimensional (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  let bx : W := ⟨x, hx⟩
  let bS : W := ⟨S, hS⟩
  have hbx0 : bx ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hli : LinearIndependent (ZMod 2) ![bx, bS] := by
    rw [LinearIndependent.pair_iff' hbx0]
    intro a ha
    exact hSx a (congrArg Subtype.val ha)
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) W := by
    simp [hW]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hy' : (⟨y, hy⟩ : W) ∈ Submodule.span (ZMod 2) (Set.range ![bx, bS]) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hy'
  refine ⟨c 0, c 1, ?_⟩
  have := congrArg Subtype.val hc
  simpa [Fin.sum_univ_two, bx, bS] using this.symm

theorem fixes_line_of_two_power (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W = 2) (T A : Module.End (ZMod 2) V)
    (hTW : ∀ y ∈ W, T y ∈ W) (hT : ∀ y ∈ W, T (T y) + T y + y = 0)
    (hAW : ∀ y ∈ W, A y ∈ W) (hAT : ∀ y ∈ W, A (T y) = T (A y)) (k : ℕ)
    (hA : ∀ y ∈ W, (A ^ (2 ^ k)) y = y) :
    ∀ y ∈ W, A y = y := by
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hcancel : ∀ x y : V, x + y + x = y := by
    intro x y
    rw [add_right_comm, co2u_add_self, zero_add]
  have hcancel2 : ∀ x y : V, x + (x + y) = y := by
    intro x y
    rw [← add_assoc, co2u_add_self, zero_add]
  have hpos : 0 < Module.finrank (ZMod 2) W := by rw [hW]; norm_num
  haveI : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos hpos
  obtain ⟨⟨y₀, hy₀⟩, hy₀ne'⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hy₀ne : y₀ ≠ 0 := fun h => hy₀ne' (Subtype.ext h)
  have hTT : T (T y₀) = T y₀ + y₀ :=
    co2u_eq_of_add_eq_zero (by rw [← add_assoc]; exact hT y₀ hy₀)
  have hSne0 : T y₀ ≠ 0 := by
    intro h
    have h1 := hT y₀ hy₀
    rw [h] at h1
    simp only [map_zero, zero_add] at h1
    exact hy₀ne h1
  have hSne_y0 : T y₀ ≠ y₀ := by
    intro h
    have h1 := hT y₀ hy₀
    simp only [h] at h1
    rw [co2u_add_self y₀, zero_add] at h1
    exact hy₀ne h1
  have hTy0 : T y₀ ∈ W := hTW y₀ hy₀
  have hSx : ∀ a : ZMod 2, a • y₀ ≠ T y₀ := by
    intro a ha
    rcases hcases a with rfl | rfl
    · rw [zero_smul] at ha
      exact hSne0 ha.symm
    · rw [one_smul] at ha
      exact hSne_y0 ha.symm
  have hdec : ∀ y ∈ W, ∃ a b : ZMod 2, y = a • y₀ + b • T y₀ :=
    fun y hy => co2u_exists_coeffs W hW hy₀ hy₀ne hTy0 hSx hy
  have hr3 : 2 ^ k % 3 ≠ 0 := by
    intro h
    have h3dvd : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
    omega
  have hr12 : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by omega
  have hfix_of_cube : (A ^ 3) y₀ = y₀ → (A ^ (2 ^ k % 3)) y₀ = y₀ := by
    intro h3
    have hper : ∀ n : ℕ, (A ^ (3 * n)) y₀ = y₀ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show 3 * (n + 1) = 3 * n + 3 by omega, pow_add, Module.End.mul_apply, h3, ih]
    have hshift : ∀ r q : ℕ, (A ^ (r + 3 * q)) y₀ = (A ^ r) y₀ := by
      intro r q
      rw [pow_add, Module.End.mul_apply, hper q]
    have h1 := hshift (2 ^ k % 3) (2 ^ k / 3)
    rw [Nat.mod_add_div, hA y₀ hy₀] at h1
    exact h1.symm
  obtain ⟨a, b, hab⟩ := hdec (A y₀) (hAW y₀ hy₀)
  rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
  ·
    exfalso
    simp only [zero_smul, add_zero] at hab
    have hpk : 0 < 2 ^ k := pow_pos (by norm_num) k
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ k = m + 1 := ⟨2 ^ k - 1, by omega⟩
    have hpow : (A ^ (2 ^ k)) y₀ = 0 := by
      rw [hm, pow_succ, Module.End.mul_apply, hab, map_zero]
    exact hy₀ne ((hA y₀ hy₀).symm.trans hpow)
  ·
    exfalso
    simp only [zero_smul, one_smul, zero_add] at hab
    have hAS : A (T y₀) = T y₀ + y₀ := by rw [hAT y₀ hy₀, hab, hTT]
    have hz : A (T y₀ + y₀) = y₀ := by
      rw [map_add, hAS, hab]
      exact hcancel _ _
    have h3 : (A ^ 3) y₀ = y₀ := by
      rw [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply, hab, hAS, hz]
    have hf := hfix_of_cube h3
    rcases hr12 with h1 | h1
    · rw [h1, pow_one, hab] at hf
      exact hSne_y0 hf
    · rw [h1, pow_two, Module.End.mul_apply, hab, hAS] at hf
      exact hSne0 (add_right_cancel (hf.trans (zero_add y₀).symm))
  ·
    simp only [one_smul, zero_smul, add_zero] at hab
    have hAS : A (T y₀) = T y₀ := by rw [hAT y₀ hy₀, hab]
    intro y hy
    obtain ⟨c, d, hcd⟩ := hdec y hy
    rw [hcd, map_add, map_smul, map_smul, hab, hAS]
  ·
    exfalso
    simp only [one_smul] at hab
    have hAS : A (T y₀) = y₀ := by
      rw [hAT y₀ hy₀, hab, map_add, hTT]
      exact hcancel2 _ _
    have hz : A (y₀ + T y₀) = T y₀ := by
      rw [map_add, hab, hAS]
      exact hcancel _ _
    have h3 : (A ^ 3) y₀ = y₀ := by
      rw [pow_succ, pow_succ, pow_one, Module.End.mul_apply, Module.End.mul_apply, hab, hz, hAS]
    have hf := hfix_of_cube h3
    rcases hr12 with h1 | h1
    · rw [h1, pow_one, hab] at hf
      exact hSne0 (add_left_cancel (hf.trans (add_zero y₀).symm))
    · rw [h1, pow_two, Module.End.mul_apply, hab, hz] at hf
      exact hSne_y0 hf

end TwoPower

section Perfect

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem rep_inv_apply_apply_aux (ρ : Representation (ZMod 2) Γ V) (g : Γ) (y : V) :
    ρ g⁻¹ (ρ g y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem rep_apply_inv_apply_aux (ρ : Representation (ZMod 2) Γ V) (g : Γ) (y : V) :
    ρ g (ρ g⁻¹ y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private def planeAction (ρ : Representation (ZMod 2) Γ V) (W : Submodule (ZMod 2) V)
    (P : Subgroup Γ) (hPW : ∀ p ∈ P, ∀ y ∈ W, ρ p y ∈ W) : P →* Equiv.Perm W where
  toFun p :=
    { toFun := fun y => ⟨ρ (p : Γ) y.1, hPW (p : Γ) p.2 y.1 y.2⟩
      invFun := fun y => ⟨ρ ((p : Γ)⁻¹) y.1, hPW ((p : Γ)⁻¹) (P.inv_mem p.2) y.1 y.2⟩
      left_inv := fun y => Subtype.ext (rep_inv_apply_apply_aux ρ (p : Γ) y.1)
      right_inv := fun y => Subtype.ext (rep_apply_inv_apply_aux ρ (p : Γ) y.1) }
  map_one' := Equiv.ext fun y => Subtype.ext (by simp)
  map_mul' p q := Equiv.ext fun y => Subtype.ext (by simp [Module.End.mul_apply])

private theorem perfect_map_trivial_of_solvable {G H : Type*} [Group G] [Group H]
    [Group.IsSolvable H] [Group.IsPerfect G] (f : G →* H) (g : G) : f g = 1 := by
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra h
    haveI : Nontrivial f.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have h1 : (⟨f g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem perfect_fixes_plane (ρ : Representation (ZMod 2) Γ V) (W : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W = 2) (P : Subgroup Γ) (hP : P ≤ ⁅P, P⁆)
    (hPW : ∀ p ∈ P, ∀ y ∈ W, ρ p y ∈ W) :
    ∀ p ∈ P, ∀ y ∈ W, ρ p y = y := by
  haveI hfin : Module.Finite (ZMod 2) W := Module.finite_of_finrank_pos (by omega)
  have hcard : Nat.card W = 4 := by
    have h : Nat.card W = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) W :=
      Module.natCard_eq_pow_finrank
    rw [hW, Nat.card_zmod] at h
    norm_num at h
    exact h
  haveI : Finite W := Nat.finite_of_card_ne_zero (by omega)
  haveI : Group.IsSolvable (Equiv.Perm W) := Equiv.Perm.isSolvable hcard.le
  haveI : Group.IsPerfect P :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le_self P) hP)
  intro p hp y hy
  have h1 := perfect_map_trivial_of_solvable (planeAction ρ W P hPW) (⟨p, hp⟩ : P)
  have h2 := congrArg (fun σ : Equiv.Perm W => ((σ ⟨y, hy⟩ : W) : V)) h1
  exact h2

end Perfect

section Stab

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ι : AddChar F3Vec Γ)

@[expose] def stabSubgroup (w : F3Vec) : Subgroup Γ where
  carrier := {g | ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 3), ConjAct ι g A ∧ Matrix.vecMul w A = w}
  mul_mem' := by
    rintro g₁ g₂ ⟨A₁, h₁, hw₁⟩ ⟨A₂, h₂, hw₂⟩
    exact ⟨A₁ * A₂, h₁.mul h₂, by rw [← Matrix.vecMul_vecMul, hw₁, hw₂]⟩
  one_mem' := ⟨1, ConjAct.one, Matrix.vecMul_one w⟩
  inv_mem' := by
    rintro g ⟨A, h, hw⟩
    refine ⟨A⁻¹, h.inv, ?_⟩
    have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
    calc Matrix.vecMul w A⁻¹ = Matrix.vecMul (Matrix.vecMul w A) A⁻¹ := by rw [hw]
      _ = w := by rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hdet, Matrix.vecMul_one]

@[expose] def normSubgroup : Subgroup Γ where
  carrier := {g | ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 3), ConjAct ι g A}
  mul_mem' := by
    rintro g₁ g₂ ⟨A₁, h₁⟩ ⟨A₂, h₂⟩
    exact ⟨A₁ * A₂, h₁.mul h₂⟩
  one_mem' := ⟨1, ConjAct.one⟩
  inv_mem' := by
    rintro g ⟨A, h⟩
    exact ⟨A⁻¹, h.inv⟩

theorem mem_normSubgroup {g : Γ} :
    g ∈ normSubgroup ι ↔ ∃ A : Matrix (Fin 4) (Fin 4) (ZMod 3), ConjAct ι g A := Iff.rfl

variable {ι}

theorem stab_apply_mem (ρ : Representation (ZMod 2) Γ V) {w₁ : F3Vec} {g : Γ}
    (hg : g ∈ stabSubgroup ι w₁) {y : V} (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ρ g y ∈ LinearMap.range (eK ρ ι w₁) := by
  obtain ⟨A, hA, hw⟩ := hg
  have h := range_eK_eq_map ρ hA (w := w₁) (w' := w₁) (c := 1) one_ne_zero
    (by rw [one_smul]; exact hw)
  rw [h]
  exact Submodule.mem_map_of_mem hy

theorem stab_apply_comm (ρ : Representation (ZMod 2) Γ V) {w₁ v₀ : F3Vec} {g : Γ}
    (hg : g ∈ stabSubgroup ι w₁) (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {y : V}
    (hy : y ∈ LinearMap.range (eK ρ ι w₁)) :
    ρ g (ρ (ι v₀) y) = ρ (ι v₀) (ρ g y) := by
  have hgy := stab_apply_mem ρ hg hy
  obtain ⟨A, hA, hw⟩ := hg
  have h1 : ρ g (ρ (ι v₀) y) = ρ (ι (A.mulVec v₀)) (ρ g y) := by
    have := LinearMap.congr_fun (congrArg ρ (hA.mul_apply v₀)) y
    simpa using this
  have hc : (w₁ ⬝ᵥ A.mulVec v₀) * (w₁ ⬝ᵥ v₀)⁻¹ = 1 := by
    rw [Matrix.dotProduct_mulVec, hw]
    exact mul_inv_cancel₀ hv₀
  have hval : (1 : ZMod 3).val = 1 := rfl
  rw [h1, apply_ι_of_mem_range_eK ρ ι hv₀ _ hgy, hc, hval, pow_one]

theorem norm_apply_mem_range_piE (ρ : Representation (ZMod 2) Γ V) {g : Γ}
    (hg : g ∈ normSubgroup ι) {y : V} (hy : y ∈ LinearMap.range (piE ρ ι)) :
    ρ g y ∈ LinearMap.range (piE ρ ι) := by
  obtain ⟨A, hA⟩ := hg
  obtain ⟨z, rfl⟩ := hy
  refine ⟨ρ g z, ?_⟩
  have := LinearMap.congr_fun (conj_mul_piE ρ hA) z
  rw [Module.End.mul_apply, Module.End.mul_apply] at this
  rw [this]

theorem closure_fixes_block [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) Γ V)
    {w₁ v₀ : F3Vec} (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w₁)) = 2)
    (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {S : Set Γ} (hS : S ⊆ (stabSubgroup ι w₁ : Set Γ))
    (h2 : ∀ s ∈ S, ∃ k : ℕ, s ^ (2 ^ k) = 1) :
    ∀ q ∈ Subgroup.closure S, ∀ y ∈ LinearMap.range (eK ρ ι w₁), ρ q y = y := by
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ stabSubgroup ι w₁ ∧ ∀ y ∈ LinearMap.range (eK ρ ι w₁), ρ g y = y}
      mul_mem' := fun {g h} hg hh => by
        obtain ⟨hg1, hg2⟩ := hg
        obtain ⟨hh1, hh2⟩ := hh
        refine ⟨(stabSubgroup ι w₁).mul_mem hg1 hh1, fun y hy => ?_⟩
        rw [map_mul, Module.End.mul_apply, hh2 y hy, hg2 y hy]
      one_mem' := by
        refine ⟨(stabSubgroup ι w₁).one_mem, fun y _ => ?_⟩
        simp
      inv_mem' := fun {g} hg => by
        obtain ⟨hg1, hg2⟩ := hg
        refine ⟨(stabSubgroup ι w₁).inv_mem hg1, fun y hy => ?_⟩
        calc ρ g⁻¹ y = ρ g⁻¹ (ρ g y) := by rw [hg2 y hy]
          _ = y := CFSG.Monster.GMS.Griess13.rho_inv_apply_apply ρ g y }
  have hKmem : ∀ g : Γ, g ∈ K ↔
      g ∈ stabSubgroup ι w₁ ∧ ∀ y ∈ LinearMap.range (eK ρ ι w₁), ρ g y = y :=
    fun g => Iff.rfl
  have hSK : S ⊆ (K : Set Γ) := by
    intro s hs
    have hsStab : s ∈ stabSubgroup ι w₁ := hS hs
    obtain ⟨k, hk⟩ := h2 s hs
    have hpow : ρ (s ^ (2 ^ k)) = ρ s ^ (2 ^ k) := map_pow ρ s (2 ^ k)
    have hA : ∀ z ∈ LinearMap.range (eK ρ ι w₁), (ρ s ^ (2 ^ k)) z = z := by
      intro z _
      rw [← hpow, hk, map_one, Module.End.one_apply]
    refine (hKmem s).mpr ⟨hsStab, fun y hy => ?_⟩
    exact fixes_line_of_two_power (LinearMap.range (eK ρ ι w₁)) hdim (ρ (ι v₀)) (ρ s)
      (fun z hz => apply_mem_range_eK ρ ι w₁ v₀ hz)
      (fun z hz => by
        have h := one_add_apply_eq_zero ρ ι hv₀ hz
        rw [← h]
        abel)
      (fun z hz => stab_apply_mem ρ hsStab hz)
      (fun z hz => stab_apply_comm ρ hsStab hv₀ hz)
      k hA y hy
  have hcl : Subgroup.closure S ≤ K := (Subgroup.closure_le K).mpr hSK
  intro q hq y hy
  exact ((hKmem q).mp (hcl hq)).2 y hy

end Stab

section Transfer

variable {Γ : Type*} [Group Γ] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) Γ V) (ι : AddChar F3Vec Γ)

theorem pow_apply_eq_coef {T : Module.End (ZMod 2) V} {x : V} (hT2 : T (T x) = x + T x)
    (c : ZMod 3) : (T ^ c.val) x = coef c 0 • x + coef c 1 • T x := by
  rcases zmod_three_cases c with rfl | rfl | rfl
  · simp [coef]
  · have h1 : (1 : ZMod 3).val = 1 := rfl
    simp [coef, h1]
  · have h1 : (-1 : ZMod 3).val = 2 := rfl
    have h2 : ¬ ((-1 : ZMod 3) = 0) := by decide
    have h3 : ¬ ((-1 : ZMod 3) = 1) := by decide
    have h4 : coef (-1 : ZMod 3) = ![1, 1] := by
      unfold coef
      rw [if_neg h2, if_neg h3]
    rw [h1, h4]
    simp [pow_two, hT2]

theorem rho_apply_basis22 (b : Fin 2 ⊕ (Fin 10 × Fin 2) → V) {r : Fin 10 → Γ}
    {w₁ v₀ : F3Vec} (hv₀ : w₁ ⬝ᵥ v₀ ≠ 0) {x : V}
    (hb : ∀ i j, b (Sum.inr (i, j)) = ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x))
    (hx : x ∈ LinearMap.range (eK ρ ι w₁)) {n : Γ} {σ : Fin 10 → Fin 10}
    {u : Fin 10 → Fin 2 → F3Vec} {s : Fin 10 → Fin 2 → Γ}
    (hdec : ∀ (i : Fin 10) (j : Fin 2), n * r i * ι v₀ ^ (j : ℕ) = r (σ i) * ι (u i j) * s i j)
    (hs : ∀ i j, ρ (s i j) x = x) (i : Fin 10) (j : Fin 2) :
    ρ n (b (Sum.inr (i, j))) =
      coef ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹) 0 • b (Sum.inr (σ i, 0)) +
        coef ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹) 1 • b (Sum.inr (σ i, 1)) := by
  have hT2 := apply_sq_of_mem_range_eK ρ ι hv₀ hx
  have h1 : ρ n (b (Sum.inr (i, j))) =
      ρ (r (σ i)) ((ρ (ι v₀) ^ ((w₁ ⬝ᵥ u i j) * (w₁ ⬝ᵥ v₀)⁻¹).val) x) := by
    rw [hb i j]
    have e : ρ n (ρ (r i) ((ρ (ι v₀) ^ (j : ℕ)) x)) = ρ (n * r i * ι v₀ ^ (j : ℕ)) x := by
      rw [map_mul, map_mul, map_pow, Module.End.mul_apply, Module.End.mul_apply]
    rw [e, hdec i j, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hs i j,
      apply_ι_of_mem_range_eK ρ ι hv₀ (u i j) hx]
  rw [h1, pow_apply_eq_coef hT2, map_add, map_smul, map_smul, hb (σ i) 0, hb (σ i) 1]
  simp

end Transfer

end CFSG.GF2Type.Widths1112.Co2Module
