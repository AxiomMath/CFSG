module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

namespace Fixed

open Subgroup

variable {V Γ : Type*} [Group V] [Group Γ] (ρ : Γ →* MulAut V)

theorem rho_mul_apply (g h : Γ) (x : V) : ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul]; rfl

theorem rho_one_apply (x : V) : ρ 1 x = x := by
  rw [map_one]; rfl

theorem rho_inv_rho_apply (g : Γ) (x : V) : ρ g⁻¹ (ρ g x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, rho_one_apply]

theorem rho_rho_inv_apply (g : Γ) (x : V) : ρ g (ρ g⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, rho_one_apply]

theorem eq_one_of_apply_eq {g : Γ} (h : ∀ v : V, ρ g v = v) : ρ g = 1 :=
  MulEquiv.ext h

@[expose] def fixedSubgroup (T : Subgroup Γ) : Subgroup V where
  carrier := {v | ∀ g ∈ T, ρ g v = v}
  one_mem' g _ := map_one (ρ g)
  mul_mem' {a b} ha hb g hg := by rw [map_mul, ha g hg, hb g hg]
  inv_mem' {a} ha g hg := by rw [map_inv, ha g hg]

@[expose] def fixedSubgroupAut (τ : MulAut V) : Subgroup V where
  carrier := {v | τ v = v}
  one_mem' := map_one τ
  mul_mem' {a b} (ha : τ a = a) (hb : τ b = b) := by
    show τ (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' {a} (ha : τ a = a) := by
    show τ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedSubgroupAut {τ : MulAut V} {v : V} : v ∈ fixedSubgroupAut τ ↔ τ v = v :=
  Iff.rfl

theorem apply_mem_fixedSubgroup_of_comm {T₁ T₂ : Subgroup Γ}
    (hcomm : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a) {g : Γ} (hg : g ∈ T₂) {u : V}
    (hu : u ∈ fixedSubgroup ρ T₁) : ρ g u ∈ fixedSubgroup ρ T₁ := by
  intro h hh
  rw [← rho_mul_apply, hcomm h hh g hg, rho_mul_apply, hu h hh]

theorem apply_mem_fixedSubgroup_self {T : Subgroup Γ} {g : Γ} (hg : g ∈ T) {u : V}
    (hu : u ∈ fixedSubgroup ρ T) : ρ g u ∈ fixedSubgroup ρ T := by
  rw [hu g hg]; exact hu

theorem fixedSubgroup_ne_top {S : Subgroup Γ} (hc : Nat.card S = 20160)
    (hf : ∀ g ∈ S, ρ g = 1 → g = 1) : fixedSubgroup ρ S ≠ ⊤ := by
  intro h
  have hS : S ≠ ⊥ := by
    intro hb
    rw [Subgroup.eq_bot_iff_card] at hb
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS
  apply ha
  have h1 : ρ a = 1 := by
    apply eq_one_of_apply_eq
    intro v
    have hv : v ∈ fixedSubgroup ρ S := by rw [h]; trivial
    exact hv a a.2
  exact Subtype.ext (hf a a.2 h1)

theorem apply_mem_fixedSubgroup_of_conj {S1 S2 : Subgroup Γ} {z : Γ} (hz : z * z = 1)
    (hz21 : ∀ g ∈ S2, z * g * z⁻¹ ∈ S1) {u : V} (hu : u ∈ fixedSubgroup ρ S1) :
    ρ z u ∈ fixedSubgroup ρ S2 := by
  intro h hh
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hmem := hz21 h hh
  have h1 : h * z = z * (z * h * z⁻¹) := by
    rw [hz', ← mul_assoc, ← mul_assoc, hz, one_mul]
  rw [← rho_mul_apply, h1, rho_mul_apply, hu _ hmem]

@[expose] def actPerm (S : Subgroup Γ) (X : Subgroup V) (hX : ∀ g ∈ S, ∀ x ∈ X, ρ g x ∈ X) :
    S →* Equiv.Perm {x : V // x ∈ X ∧ x ≠ 1} where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, hX g g.2 x x.2.1,
        fun h => x.2.2 (by rw [← rho_inv_rho_apply ρ g x, h, map_one])⟩
      invFun := fun x => ⟨ρ g⁻¹ x, hX g⁻¹ (inv_mem g.2) x x.2.1,
        fun h => x.2.2 (by rw [← rho_rho_inv_apply ρ g x, h, map_one])⟩
      left_inv := fun x => Subtype.ext (rho_inv_rho_apply ρ g x)
      right_inv := fun x => Subtype.ext (rho_rho_inv_apply ρ g x) }
  map_one' := by
    ext x
    exact rho_one_apply ρ x
  map_mul' g h := by
    ext x
    exact rho_mul_apply ρ g h x

theorem card_ne_one_add_one (X : Subgroup V) [Finite X] :
    Nat.card {x : V // x ∈ X ∧ x ≠ 1} + 1 = Nat.card X := by
  have h1 : Nat.card {x : V // x ∈ X ∧ x ≠ 1} = Set.ncard ((X : Set V) \ {1}) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  have h2 : Set.ncard (X : Set V) = Nat.card X := Nat.card_coe_set_eq _ |>.symm
  rw [h1, Set.ncard_sdiff_singleton_of_mem (one_mem X), ← h2]
  have : 0 < Set.ncard (X : Set V) := by
    rw [h2]; exact Nat.card_pos
  omega

theorem small_action {S : Subgroup Γ} (hS : IsSimpleGroup S) (hc : Nat.card S = 20160)
    {X : Subgroup V} [Finite X] (hX : ∀ g ∈ S, ∀ x ∈ X, ρ g x ∈ X) (hcard : Nat.card X ≤ 8) :
    ∀ g ∈ S, ∀ x ∈ X, ρ g x = x := by
  classical
  have hfin : Finite {x : V // x ∈ X ∧ x ≠ 1} := by
    refine Finite.of_injective (fun x : {x : V // x ∈ X ∧ x ≠ 1} => (⟨x.1, x.2.1⟩ : X)) ?_
    intro a b h
    exact Subtype.ext (congrArg (fun y : X => y.1) h)
  have hker := hS.eq_bot_or_eq_top_of_normal (actPerm ρ S X hX).ker
  rcases hker with h | h
  · exfalso
    have hinj : Function.Injective (actPerm ρ S X hX) := (MonoidHom.ker_eq_bot_iff _).1 h
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, hc] at h1
    have h2 := card_ne_one_add_one X
    have h3 : (Nat.card {x : V // x ∈ X ∧ x ≠ 1}).factorial ≤ (7 : ℕ).factorial :=
      Nat.factorial_le (by omega)
    have h4 : (7 : ℕ).factorial = 5040 := by decide
    omega
  · intro g hg x hx
    by_cases hx1 : x = 1
    · subst hx1; exact map_one _
    · have h5 : actPerm ρ S X hX ⟨g, hg⟩ = 1 := by
        rw [← MonoidHom.mem_ker, h]; trivial
      have h6 := congrArg (fun p => (p ⟨x, hx, hx1⟩ : {x : V // x ∈ X ∧ x ≠ 1}).1) h5
      simpa [actPerm] using h6

theorem eq_bot_of_small {S : Subgroup Γ} (hS : IsSimpleGroup S) (hc : Nat.card S = 20160)
    (hbot : fixedSubgroup ρ S = ⊥) {X : Subgroup V} [Finite X]
    (hX : ∀ g ∈ S, ∀ x ∈ X, ρ g x ∈ X) (hcard : Nat.card X ≤ 8) : X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : x ∈ fixedSubgroup ρ S := fun g hg => small_action ρ hS hc hX hcard g hg x hx
  rw [hbot] at h
  exact h

theorem exists_hom_of_comm (hVc : ∀ a b : V, a * b = b * a) (τ : MulAut V) :
    ∃ φ : V →* V, ∀ v, φ v = τ v * v⁻¹ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hVc }
  exact ⟨(τ : V →* V) * (MonoidHom.id V)⁻¹, fun v => rfl⟩

theorem card_cases (c : ℕ) (hdvd : c ∣ 256) (hmod : 256 ≡ c [MOD 7]) :
    c = 4 ∨ c = 32 ∨ c = 256 := by
  have h : c ∣ 2 ^ 8 := by norm_num; exact hdvd
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  interval_cases k <;> simp [Nat.ModEq] at hmod ⊢

theorem closure_inv {s : Set V} {T : Subgroup Γ} (hs : ∀ h ∈ T, ∀ x ∈ s, ρ h x ∈ s) :
    ∀ h ∈ T, ∀ x ∈ closure s, ρ h x ∈ closure s := by
  intro h hh x hx
  have : closure s ≤ (closure s).comap (ρ h : V →* V) := by
    rw [closure_le]
    intro y hy
    exact subset_closure (hs h hh y hy)
  exact this hx

theorem fixedSubgroup_inf_eq_bot (hV2 : ∀ a : V, a * a = 1) {S1 S2 : Subgroup Γ}
    (horder : ∀ U : Subgroup V, (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256) :
    fixedSubgroup ρ S1 ⊓ fixedSubgroup ρ S2 = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  by_contra hne
  have hu1 : u ≠ 1 := by simpa using hne
  have hinv : ∀ T : Subgroup Γ, (∀ g ∈ T, ρ g u = u) →
      ∀ g ∈ T, ∀ x ∈ zpowers u, ρ g x ∈ zpowers u := by
    intro T hT g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, hT g hg]
    exact zpow_mem (mem_zpowers u) k
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hV2 u) hu1
  have h := horder (zpowers u) (hinv S1 hu.1) (hinv S2 hu.2)
  rw [Nat.card_zpowers, hord] at h
  omega

section Finite

variable [Finite V]

theorem card_modEq_card_fixed (τ : MulAut V) (hτ : τ ^ 7 = 1) :
    Nat.card V ≡ Nat.card {v : V // τ v = v} [MOD 7] := by
  classical
  have := Fintype.ofFinite V
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hσ : MulAut.toPerm V τ ^ 7 = 1 := by
    rw [← map_pow, hτ, map_one]
  let f : Function.End V := fun v => τ v
  have hf : f ^ 7 ^ 1 = 1 := by
    have h1 : (⇑(MulAut.toPerm V τ ^ 7) : V → V) = id := by
      rw [hσ]; rfl
    rw [Equiv.Perm.coe_pow] at h1
    exact h1
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  exact h

theorem main_aux (hVc : ∀ a b : V, a * b = b * a) (hV : Nat.card V = 256)
    {S1 : Subgroup Γ} (hS1 : IsSimpleGroup S1) (hc1 : Nat.card S1 = 20160)
    (hbot : fixedSubgroup ρ S1 = ⊥) (τ : MulAut V) (hτ7 : τ ^ 7 = 1) (hτ1 : τ ≠ 1)
    (hcommτ : ∀ g ∈ S1, ∀ v, ρ g (τ v) = τ (ρ g v)) : False := by
  have hmod := card_modEq_card_fixed τ hτ7
  have hC : Nat.card (fixedSubgroupAut τ) = Nat.card {v : V // τ v = v} := rfl
  have hdvd : Nat.card (fixedSubgroupAut τ) ∣ 256 := hV ▸ Subgroup.card_subgroup_dvd_card _
  have hcases := card_cases (Nat.card (fixedSubgroupAut τ)) hdvd (by rw [hC, ← hV]; exact hmod)
  obtain ⟨φ, hφ⟩ := exists_hom_of_comm hVc τ
  have hker : φ.ker = fixedSubgroupAut τ := by
    ext v
    rw [MonoidHom.mem_ker, hφ, mem_fixedSubgroupAut, mul_inv_eq_one]
  have hrange : ∀ g ∈ S1, ∀ x ∈ φ.range, ρ g x ∈ φ.range := by
    rintro g hg _ ⟨v, rfl⟩
    exact ⟨ρ g v, by rw [hφ, hφ, map_mul, hcommτ g hg, map_inv]⟩
  have hCinv : ∀ g ∈ S1, ∀ x ∈ fixedSubgroupAut τ, ρ g x ∈ fixedSubgroupAut τ := by
    intro g hg x hx
    rw [mem_fixedSubgroupAut] at *
    rw [← hcommτ g hg, hx]
  have hcardprod := Subgroup.card_ker_mul_card_range φ
  rw [hker, hV] at hcardprod
  rcases hcases with h4 | h32 | h256
  · have := eq_bot_of_small ρ hS1 hc1 hbot hCinv (by omega)
    rw [this] at h4
    simp at h4
  · rw [h32] at hcardprod
    have h8 : Nat.card φ.range = 8 := by omega
    have := eq_bot_of_small ρ hS1 hc1 hbot hrange (by omega)
    rw [this] at h8
    simp at h8
  · have htop : fixedSubgroupAut τ = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, h256, hV]
    apply hτ1
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ fixedSubgroupAut τ := by rw [htop]; trivial
    exact hv

theorem fixedSubgroup_card_ne_one (hVc : ∀ a b : V, a * b = b * a) (hV : Nat.card V = 256)
    {S1 S2 : Subgroup Γ} (hS1 : IsSimpleGroup S1) (hc1 : Nat.card S1 = 20160)
    (hc2 : Nat.card S2 = 20160) (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a)
    (hf2 : ∀ g ∈ S2, ρ g = 1 → g = 1) : Nat.card (fixedSubgroup ρ S1) ≠ 1 := by
  intro h1
  have hbot : fixedSubgroup ρ S1 = ⊥ := (Subgroup.eq_bot_iff_card _).2 h1
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite S2 := Nat.finite_of_card_ne_zero (by rw [hc2]; norm_num)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := S2) 7 (by rw [hc2]; norm_num)
  have ht7 : (t : Γ) ^ 7 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    exact congrArg Subtype.val h
  refine main_aux ρ hVc hV hS1 hc1 hbot (ρ t) ?_ ?_ ?_
  · rw [← map_pow, ht7, map_one]
  · intro h
    have h' := hf2 t t.2 h
    have : t = 1 := Subtype.ext h'
    rw [this, orderOf_one] at ht
    omega
  · intro g hg v
    rw [← rho_mul_apply, ← rho_mul_apply, hcomm g hg t t.2]

theorem fixedSubgroup_card_eq_sixteen (hVc : ∀ a b : V, a * b = b * a) (hV : Nat.card V = 256)
    {S1 S2 : Subgroup Γ} (hS1 : IsSimpleGroup S1) (hc1 : Nat.card S1 = 20160)
    (hc2 : Nat.card S2 = 20160) (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a)
    (hf1 : ∀ g ∈ S1, ρ g = 1 → g = 1) (hf2 : ∀ g ∈ S2, ρ g = 1 → g = 1)
    (horder : ∀ U : Subgroup V, (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256) :
    Nat.card (fixedSubgroup ρ S1) = 16 := by
  have hinv1 : ∀ g ∈ S1, ∀ u ∈ fixedSubgroup ρ S1, ρ g u ∈ fixedSubgroup ρ S1 :=
    fun g hg u hu => apply_mem_fixedSubgroup_self ρ hg hu
  have hinv2 : ∀ g ∈ S2, ∀ u ∈ fixedSubgroup ρ S1, ρ g u ∈ fixedSubgroup ρ S1 :=
    fun g hg u hu => apply_mem_fixedSubgroup_of_comm ρ hcomm hg hu
  rcases horder _ hinv1 hinv2 with h | h | h
  · exact absurd h (fixedSubgroup_card_ne_one ρ hVc hV hS1 hc1 hc2 hcomm hf2)
  · exact h
  · exfalso
    apply fixedSubgroup_ne_top ρ hc1 hf1
    rw [← Subgroup.card_eq_iff_eq_top, h, hV]

theorem fixedSubgroup_sup_eq_top (hV : Nat.card V = 256) {S1 S2 : Subgroup Γ}
    (h1 : Nat.card (fixedSubgroup ρ S1) = 16) (h2 : Nat.card (fixedSubgroup ρ S2) = 16)
    (hinf : fixedSubgroup ρ S1 ⊓ fixedSubgroup ρ S2 = ⊥) :
    fixedSubgroup ρ S1 ⊔ fixedSubgroup ρ S2 = ⊤ :=
  (Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [h1, h2, hV])
    (disjoint_iff.2 hinf)).sup_eq_top

theorem closure_eq_fixedSubgroup {S1 S2 : Subgroup Γ} (hc1 : Nat.card S1 = 20160)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hf1 : ∀ g ∈ S1, ρ g = 1 → g = 1)
    (horder : ∀ U : Subgroup V, (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256)
    (hD1 : Nat.card (fixedSubgroup ρ S2) = 16)
    (htop : fixedSubgroup ρ S2 ⊔ fixedSubgroup ρ S1 = ⊤) :
    closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} =
      fixedSubgroup ρ S2 := by
  have hD1inv : ∀ g ∈ S1, ∀ u ∈ fixedSubgroup ρ S2, ρ g u ∈ fixedSubgroup ρ S2 :=
    fun g hg u hu => apply_mem_fixedSubgroup_of_comm ρ
      (fun a ha b hb => (hcomm b hb a ha).symm) hg hu
  have hsub : closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} ≤
      fixedSubgroup ρ S2 := by
    rw [closure_le]
    rintro x ⟨g, hg, u, hu, rfl⟩
    exact mul_mem (hD1inv g hg u hu) (inv_mem hu)
  have hsinv : ∀ h ∈ S1, ∀ x ∈ {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹},
      ρ h x ∈ {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} := by
    rintro h hh x ⟨g, hg, u, hu, rfl⟩
    refine ⟨h * g * h⁻¹, mul_mem (mul_mem hh hg) (inv_mem hh), ρ h u, hD1inv h hh u hu, ?_⟩
    rw [map_mul, map_inv, rho_mul_apply, rho_mul_apply, rho_inv_rho_apply]
  have hQ1 := closure_inv ρ hsinv
  have hQ2 : ∀ h ∈ S2,
      ∀ x ∈ closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹},
      ρ h x ∈ closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} := by
    intro h hh x hx
    rw [hsub hx h hh]
    exact hx
  have hle := Subgroup.card_le_of_le hsub
  rcases horder _ hQ1 hQ2 with h | h | h
  · exfalso
    have hbot : closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} = ⊥ :=
      (Subgroup.eq_bot_iff_card _).2 h
    have hfix : ∀ g ∈ S1, ρ g = 1 := by
      intro g hg
      apply eq_one_of_apply_eq
      have hD1fix : fixedSubgroup ρ S2 ≤ fixedSubgroupAut (ρ g) := by
        intro u hu
        have hmem : ρ g u * u⁻¹ ∈
            closure {x : V | ∃ g ∈ S1, ∃ u ∈ fixedSubgroup ρ S2, x = ρ g u * u⁻¹} :=
          subset_closure ⟨g, hg, u, hu, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact mul_inv_eq_one.1 hmem
      have hD2fix : fixedSubgroup ρ S1 ≤ fixedSubgroupAut (ρ g) := fun u hu => hu g hg
      intro v
      have hv : v ∈ fixedSubgroup ρ S2 ⊔ fixedSubgroup ρ S1 := by rw [htop]; trivial
      exact sup_le hD1fix hD2fix hv
    have hS : S1 = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      exact hf1 g hg (hfix g hg)
    rw [hS] at hc1
    simp at hc1
  · exact Subgroup.eq_of_le_of_card_ge hsub (by omega)
  · omega

end Finite

end Fixed

open Fixed

theorem exists_fixed_decomposition
    {V Γ : Type} [Group V] [Finite V] [Group Γ] (ρ : Γ →* MulAut V)
    (hVc : ∀ a b : V, a * b = b * a) (hV2 : ∀ a : V, a * a = 1) (hV : Nat.card V = 256)
    (S1 S2 : Subgroup Γ) (hS1 : IsSimpleGroup S1) (hS2 : IsSimpleGroup S2)
    (hc1 : Nat.card S1 = 20160) (hc2 : Nat.card S2 = 20160)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a)
    (hf1 : ∀ g ∈ S1, ρ g = 1 → g = 1) (hf2 : ∀ g ∈ S2, ρ g = 1 → g = 1)
    (z : Γ) (hz : z * z = 1)
    (hz12 : ∀ g ∈ S1, z * g * z⁻¹ ∈ S2) (hz21 : ∀ g ∈ S2, z * g * z⁻¹ ∈ S1)
    (horder : ∀ U : Subgroup V, (∀ g ∈ S1, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ g ∈ S2, ∀ u ∈ U, ρ g u ∈ U) →
      Nat.card U = 1 ∨ Nat.card U = 16 ∨ Nat.card U = 256) :
    ∃ D1 D2 : Subgroup V, Nat.card D1 = 16 ∧ Nat.card D2 = 16 ∧ D1 ⊓ D2 = ⊥ ∧ D1 ⊔ D2 = ⊤ ∧
      (∀ g ∈ S2, ∀ u ∈ D1, ρ g u = u) ∧ (∀ g ∈ S1, ∀ u ∈ D2, ρ g u = u) ∧
      (∀ g ∈ S1, ∀ u ∈ D1, ρ g u ∈ D1) ∧ (∀ g ∈ S2, ∀ u ∈ D2, ρ g u ∈ D2) ∧
      (∀ u ∈ D1, ρ z u ∈ D2) ∧ (∀ u ∈ D2, ρ z u ∈ D1) ∧
      Subgroup.closure {x : V | ∃ g ∈ S1, ∃ u ∈ D1, x = ρ g u * u⁻¹} = D1 := by
  have hcomm' : ∀ a ∈ S2, ∀ b ∈ S1, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have h1 : Nat.card (fixedSubgroup ρ S1) = 16 :=
    fixedSubgroup_card_eq_sixteen ρ hVc hV hS1 hc1 hc2 hcomm hf1 hf2 horder
  have h2 : Nat.card (fixedSubgroup ρ S2) = 16 :=
    fixedSubgroup_card_eq_sixteen ρ hVc hV hS2 hc2 hc1 hcomm' hf2 hf1
      fun U hU2 hU1 => horder U hU1 hU2
  have hinf : fixedSubgroup ρ S2 ⊓ fixedSubgroup ρ S1 = ⊥ := by
    rw [inf_comm]
    exact fixedSubgroup_inf_eq_bot ρ hV2 horder
  have htop : fixedSubgroup ρ S2 ⊔ fixedSubgroup ρ S1 = ⊤ :=
    fixedSubgroup_sup_eq_top ρ hV h2 h1 hinf
  refine ⟨fixedSubgroup ρ S2, fixedSubgroup ρ S1, h2, h1, hinf, htop, ?_, ?_, ?_, ?_, ?_, ?_,
    closure_eq_fixedSubgroup ρ hc1 hcomm hf1 horder h2 htop⟩
  · exact fun g hg u hu => hu g hg
  · exact fun g hg u hu => hu g hg
  · exact fun g hg u hu => apply_mem_fixedSubgroup_of_comm ρ hcomm' hg hu
  · exact fun g hg u hu => apply_mem_fixedSubgroup_of_comm ρ hcomm hg hu
  · exact fun u hu => apply_mem_fixedSubgroup_of_conj ρ hz hz12 hu
  · exact fun u hu => apply_mem_fixedSubgroup_of_conj ρ hz hz21 hu

end CFSG.EvenSporadicStandard.M24Std.DResH
