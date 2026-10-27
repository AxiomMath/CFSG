module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryUnipotentCentralizer
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLargeTorus

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Counting

theorem card_modEq_card_fixedPoints_iterate {X : Type*} [Finite X] (g : X → X) {r m : ℕ}
    [Fact r.Prime] (hg : ∀ x, g^[r ^ m] x = x) :
    Nat.card X ≡ Nat.card {x // g x = x} [MOD r] := by
  classical
  have := Fintype.ofFinite X
  let g' : Function.End X := g
  have hpow : ∀ (n : ℕ) (x : X), (g' ^ n) x = g^[n] x := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero]; rfl
    | succ n ih =>
      intro x
      rw [pow_succ]
      show (g' ^ n) (g x) = _
      rw [ih, Function.iterate_succ_apply]
  have hg' : g' ^ r ^ m = 1 := by
    funext x
    rw [hpow]
    exact hg x
  have h1 := Equiv.Perm.card_fixedPoints_modEq hg'
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1
  exact h1

theorem exists_fixedPoint_ne {X : Type*} [Finite X] (g : X → X) {r m n : ℕ} [Fact r.Prime]
    (hg : ∀ x, g^[r ^ m] x = x) (hX : Nat.card X = r ^ (n + 1)) (x₀ : X) (h₀ : g x₀ = x₀) :
    ∃ x, g x = x ∧ x ≠ x₀ := by
  by_contra hcon
  push Not at hcon
  have h1 := card_modEq_card_fixedPoints_iterate g hg
  have h2 : Nat.card {x // g x = x} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨⟨x₀, h₀⟩⟩⟩
  rw [h2, hX] at h1
  have h3 : r ∣ r ^ (n + 1) := dvd_pow_self r (by omega)
  have h4 := (Nat.modEq_zero_iff_dvd.2 h3).symm.trans h1
  have h5 : r ∣ 1 := Nat.modEq_zero_iff_dvd.1 h4.symm
  exact (Fact.out : r.Prime).one_lt.ne' (Nat.dvd_one.1 h5)

end Counting

section Lam

variable {K : Type} [Field K] (J : HermitianForm 3 K)

noncomputable def lamUnit : Kˣ →* Kˣ :=
  MonoidHom.mk' (fun k => k * (Units.map J.conj.toMonoidHom k)⁻¹ ^ 2) fun a b => by
    simp only [map_mul, mul_inv, mul_pow]
    exact mul_mul_mul_comm _ _ _ _

theorem coe_lamUnit (k : Kˣ) :
    ((lamUnit J k : Kˣ) : K) = (k : K) * (J.conj (k : K))⁻¹ ^ 2 := by
  simp [lamUnit]

theorem lamUnit_eq_pow {p f : ℕ} (hconj : ∀ x : K, J.conj x = x ^ (p ^ f)) (hq : 1 ≤ p ^ f)
    (k : Kˣ) : lamUnit J k = (k⁻¹) ^ (2 * p ^ f - 1) := by
  apply Units.ext
  rw [coe_lamUnit, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hconj]
  have ha : (k : K) ≠ 0 := k.ne_zero
  have hn : 2 * p ^ f - 1 + 1 = 2 * p ^ f := Nat.sub_add_cancel (by omega)
  rw [inv_pow, ← pow_mul']
  field_simp
  have h2 : (k : K) ^ (2 * p ^ f) = (k : K) ^ (2 * p ^ f - 1) * k := by rw [← pow_succ, hn]
  rw [h2, one_div, inv_pow]
  field_simp

variable [Finite K] {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2)
  (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem lt_card_range_lamUnit (hq : 2 < p ^ f) : p ^ f - 1 < Nat.card (lamUnit J).range := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
  have hrange : (lamUnit J).range = (powMonoidHom (2 * p ^ f - 1) : Kˣ →* Kˣ).range := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k⁻¹, (lamUnit_eq_pow J hconj (by omega) k).symm⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y⁻¹, by rw [lamUnit_eq_pow J hconj (by omega), inv_inv]; rfl⟩
  rw [hrange, IsCyclic.card_powMonoidHom_range, CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
  generalize p ^ f = q at hq ⊢
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 3 := ⟨q - 3, by omega⟩
  have e1 : (q' + 3) ^ 2 - 1 = q' ^ 2 + 6 * q' + 8 := by
    have : (q' + 3) ^ 2 = q' ^ 2 + 6 * q' + 9 := by ring
    omega
  have e2 : 2 * (q' + 3) - 1 = 2 * q' + 5 := by omega
  rw [e1, e2]
  set g := Nat.gcd (q' ^ 2 + 6 * q' + 8) (2 * q' + 5) with hg
  have hg3 : g ∣ 3 := by
    have h1 : g ∣ q' ^ 2 + 6 * q' + 8 := Nat.gcd_dvd_left _ _
    have h2 : g ∣ 2 * q' + 5 := Nat.gcd_dvd_right _ _
    have h3 : g ∣ (2 * q' + 5) * (2 * q' + 7) := h2.mul_right _
    have h4 : (2 * q' + 5) * (2 * q' + 7) = 4 * (q' ^ 2 + 6 * q' + 8) + 3 := by ring
    rw [h4] at h3
    exact (Nat.dvd_add_right (h1.mul_left 4)).1 h3
  have hg_le : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg3
  have hdiv : (q' ^ 2 + 6 * q' + 8) / g * g = q' ^ 2 + 6 * q' + 8 :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  by_contra hcon
  push Not at hcon
  have h5 : q' ^ 2 + 6 * q' + 8 ≤ (q' + 3 - 1) * g := by
    calc q' ^ 2 + 6 * q' + 8 = (q' ^ 2 + 6 * q' + 8) / g * g := hdiv.symm
      _ ≤ (q' + 3 - 1) * g := Nat.mul_le_mul_right g hcon
  have h6 : (q' + 3 - 1) * g ≤ (q' + 2) * 3 := Nat.mul_le_mul (by omega) hg_le
  nlinarith

end Lam

section Mult

variable {K : Type} [Field K] [Finite K]

def multSubfield (W : AddSubgroup K) : Subfield K where
  carrier := {x | ∀ a ∈ W, x * a ∈ W}
  zero_mem' := by intro a ha; simp
  one_mem' := by intro a ha; simpa using ha
  add_mem' := by
    intro x y hx hy a ha
    rw [add_mul]
    exact W.add_mem (hx a ha) (hy a ha)
  neg_mem' := by
    intro x hx a ha
    rw [neg_mul]
    exact W.neg_mem (hx a ha)
  mul_mem' := by
    intro x y hx hy a ha
    rw [mul_assoc]
    exact hx _ (hy a ha)
  inv_mem' := by
    intro x hx a ha
    by_cases hx0 : x = 0
    · simp [hx0]
    · have : Fintype K := Fintype.ofFinite K
      have hpow : ∀ n : ℕ, ∀ b ∈ W, x ^ n * b ∈ W := by
        intro n
        induction n with
        | zero => intro b hb; simpa using hb
        | succ n ih =>
          intro b hb
          rw [pow_succ, mul_comm (x ^ n) x, mul_assoc]
          exact hx _ (ih b hb)
      have hc : 2 ≤ Fintype.card K := Fintype.one_lt_card
      have h1 : x⁻¹ = x ^ (Fintype.card K - 2) := by
        have h2 := FiniteField.pow_card_sub_one_eq_one x hx0
        have h3 : x * x ^ (Fintype.card K - 2) = 1 := by
          rw [← pow_succ', show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega, h2]
        exact inv_eq_of_mul_eq_one_right h3
      rw [h1]
      exact hpow _ a ha

end Mult

section Irr

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

omit [Fact p.Prime] in
def fstSet (V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : AddSubgroup K where
  carrier := {a | ∃ z : Coord J, z.1.1 = a ∧ root J hJ z ∈ V}
  zero_mem' := ⟨1, rfl, by rw [map_one]; exact V.one_mem⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl, hz⟩ ⟨w, rfl, hw⟩
    exact ⟨z * w, rfl, by rw [map_mul]; exact V.mul_mem hz hw⟩
  neg_mem' := by
    rintro _ ⟨z, rfl, hz⟩
    exact ⟨z⁻¹, rfl, by rw [map_inv]; exact V.inv_mem hz⟩

include hK hfix

theorem root_mem_iff_fst_mem {V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hZV : rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ V) (z : Coord J) :
    root J hJ z ∈ V ↔ z.1.1 ∈ fstSet J hJ V := by
  constructor
  · intro h
    exact ⟨z, rfl, h⟩
  · rintro ⟨w, hw, hwV⟩
    have h1 : root J hJ (z * w⁻¹) ∈ V := by
      refine hZV ((root_mem_center_iff J hJ hK hfix _).2 ?_)
      show z.1.1 + (-w.1.1) = 0
      rw [hw]; ring
    have h2 : root J hJ z = root J hJ (z * w⁻¹) * root J hJ w := by
      rw [← map_mul, inv_mul_cancel_right]
    rw [h2]
    exact V.mul_mem h1 hwV

omit [Finite K] [Fact p.Prime] hK hfix in
theorem lam_mul_mem_fstSet {V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ V, t * v * t⁻¹ ∈ V) (k : Kˣ) {a : K}
    (ha : a ∈ fstSet J hJ V) : ((lamUnit J k : Kˣ) : K) * a ∈ fstSet J hJ V := by
  obtain ⟨z, rfl, hz⟩ := ha
  refine ⟨hermitianTorusAction J k z, ?_, ?_⟩
  · rw [torusAction_val, coe_lamUnit]
    dsimp only
    ring
  · rw [← torus_mul_root_mul_inv J hJ k z]
    exact hT _ (torus_mem_torusGroup J hJ k) _ hz

theorem eq_center_or_eq_rootGroup_of_torus_invariant (hq : 2 < p ^ f)
    {V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hZV : rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ V)
    (hVR : V ≤ rootGroup J hJ) (hT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    V = rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∨ V = rootGroup J hJ := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hM : multSubfield (fstSet J hJ V) = ⊤ := by
    rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.closure_eq_top h
      (lt_card_range_lamUnit J hK hfix hq), Subfield.closure_le]
    rintro _ ⟨u, ⟨k, rfl⟩, rfl⟩
    intro a ha
    exact lam_mul_mem_fstSet J hJ hT k ha
  by_cases hV : ∃ a ∈ fstSet J hJ V, a ≠ 0
  · right
    obtain ⟨a, ha, ha0⟩ := hV
    refine le_antisymm hVR fun g hg => ?_
    obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hg
    rw [root_mem_iff_fst_mem J hJ hK hfix hZV]
    have hx : z.1.1 / a ∈ multSubfield (fstSet J hJ V) := by rw [hM]; trivial
    have := hx a ha
    rwa [div_mul_cancel₀ _ ha0] at this
  · left
    push Not at hV
    refine le_antisymm (fun v hv => ?_) hZV
    obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 (hVR hv)
    exact (root_mem_center_iff J hJ hK hfix z).2
      (hV _ ((root_mem_iff_fst_mem J hJ hK hfix hZV z).1 hv))

theorem eq_bot_or_eq_center_of_torus_invariant
    {V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hVZ : V ≤ rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ V, t * v * t⁻¹ ∈ V) :
    V = ⊥ ∨ V = rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  by_cases hV : ∃ v ∈ V, v ≠ 1
  · right
    obtain ⟨v, hv, hv1⟩ := hV
    refine le_antisymm hVZ fun g hg => ?_
    obtain ⟨z₀, rfl⟩ := (mem_rootGroup J hJ).1 (Subgroup.mem_inf.1 (hVZ hv)).1
    have hz₀ : z₀.1.1 = 0 := (root_mem_center_iff J hJ hK hfix z₀).1 (hVZ hv)
    have hb₀ : z₀.1.2 ≠ 0 := fun h => hv1 (by
      rw [show z₀ = 1 from coord_ext J (by rw [hz₀]; rfl) (by rw [h]; rfl), map_one])
    obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 (Subgroup.mem_inf.1 hg).1
    have hz : z.1.1 = 0 := (root_mem_center_iff J hJ hK hfix z).1 hg
    have hb : z.1.2 + J.conj z.1.2 = 0 := by
      have := z.2
      rw [hz] at this
      simpa using this
    have hb₀' : z₀.1.2 + J.conj z₀.1.2 = 0 := by
      have := z₀.2
      rw [hz₀] at this
      simpa using this
    set c := z.1.2 / z₀.1.2 with hc
    have hcσ : J.conj c = c := by
      rw [hc, map_div₀]
      have h1 : J.conj z.1.2 = -z.1.2 := by linear_combination hb
      have h2 : J.conj z₀.1.2 = -z₀.1.2 := by linear_combination hb₀'
      have h3 : z₀.1.2 ≠ 0 := hb₀
      rw [h1, h2]
      field_simp
    by_cases hc0 : c = 0
    · have : z.1.2 = 0 := by
        rw [hc, div_eq_zero_iff] at hc0
        exact hc0.resolve_right hb₀
      rw [show z = 1 from coord_ext J (by rw [hz]; rfl) (by rw [this]; rfl), map_one]
      exact V.one_mem
    · obtain ⟨k₀, hk₀⟩ := hσ.exists_norm (d := c⁻¹) (by rw [map_inv₀, hcσ])
      have hk0 : k₀ ≠ 0 := by
        rintro rfl
        rw [map_zero, zero_mul] at hk₀
        exact inv_ne_zero hc0 hk₀.symm
      have hact : hermitianTorusAction J (Units.mk0 k₀ hk0) z₀ = z := by
        apply coord_ext
        · rw [torusAction_val]
          dsimp only
          simp only [Units.val_mk0]
          rw [hz₀, hz, zero_mul, zero_mul]
        · rw [torusAction_val]
          dsimp only
          have h4 : (J.conj k₀)⁻¹ * k₀⁻¹ = c := by rw [← mul_inv, hk₀, inv_inv]
          simp only [Units.val_mk0]
          rw [mul_assoc, h4, hc]
          field_simp
      rw [← hact, ← torus_mul_root_mul_inv J hJ]
      exact hT _ (torus_mem_torusGroup J hJ _) _ hv
  · left
    push Not at hV
    exact eq_bot_iff.2 fun v hv => (Subgroup.mem_bot).2 (hV v hv)

end Irr

section Lang

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

omit [Fact p.Prime] in
theorem eq_one_of_generator_comm (hq : 2 < p ^ f) {g : Kˣ}
    (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g) {z : Coord J}
    (h : torus J hJ g * root J hJ z * (torus J hJ g)⁻¹ = root J hJ z) : z = 1 := by
  have hconj := huppert_II_10_4_conj_eq_frobenius J (p ^ f) hK hfix
  rw [torus_mul_root_mul_inv, (root_injective J hJ).eq_iff] at h
  have hlam : lamUnit J g ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := exists_ne_one_scalar J hK hfix hq
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg k)
    apply hk
    rw [← coe_lamUnit, map_zpow, h1, one_zpow, Units.val_one]
  have hlam' : ((lamUnit J g : Kˣ) : K) ≠ 1 := fun h1 => hlam (Units.ext h1)
  have hN : J.conj (g : K) * (g : K) ≠ 1 := by
    intro h1
    have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg,
        CFSG.ClassicalGroups.Unitary.card_units_of_card hK]
    have h2 : g ^ (p ^ f + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← hconj]
      exact h1
    have h3 := Nat.le_of_dvd (by omega) (hord ▸ orderOf_dvd_of_pow_eq_one h2)
    generalize p ^ f = q at hq h3
    have h4 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
    rw [sq] at h3
    omega
  have h1 := congrArg (fun y : Coord J => (y : K × K).1) h
  have h2 := congrArg (fun y : Coord J => (y : K × K).2) h
  simp only [torusAction_val] at h1 h2
  have hg0 : (g : K) ≠ 0 := g.ne_zero
  have hz1 : z.1.1 = 0 := by
    have : z.1.1 * (((lamUnit J g : Kˣ) : K) - 1) = 0 := by
      rw [coe_lamUnit]
      linear_combination h1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hlam')
  have hz2 : z.1.2 = 0 := by
    have : z.1.2 * ((J.conj (g : K) * (g : K))⁻¹ - 1) = 0 := by
      rw [mul_inv]
      linear_combination h2
    refine (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 fun h3 => hN ?_)
    exact inv_eq_one.1 h3
  exact coord_ext J (by rw [hz1]; rfl) (by rw [hz2]; rfl)

omit [Fact p.Prime] in
theorem exists_conj_eq_on_torus (hq : 2 < p ^ f)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hα : ∀ k : Kˣ, torus J hJ k * (α (torus J hJ k))⁻¹ ∈ rootGroup J hJ) :
    ∃ u ∈ rootGroup J hJ, ∀ t ∈ torusGroup J hJ, α t = u * t * u⁻¹ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set t₁ := torus J hJ g with ht₁
  have ht₁N : t₁ ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ g)
  have hconjR : ∀ r ∈ rootGroup J hJ, t₁ * r * t₁⁻¹ ∈ rootGroup J hJ := fun r hr =>
    (Subgroup.mem_normalizer_iff.1 ht₁N r).1 hr
  let Ψ : rootGroup J hJ → rootGroup J hJ := fun u =>
    ⟨u * (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹),
      Subgroup.mul_mem _ u.2 (hconjR _ (Subgroup.inv_mem _ u.2))⟩
  have hΨinj : Function.Injective Ψ := by
    intro u u' h
    have h1 : (u : ProjectiveSpecialUnitaryMatrixGroup J) *
        (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹) =
        (u' : ProjectiveSpecialUnitaryMatrixGroup J) *
          (t₁ * (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹) :=
      congrArg Subtype.val h
    have hw : t₁ * ((u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u) * t₁⁻¹ =
        (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u := by
      have h2 : (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u =
          t₁ * (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹ *
            (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹)⁻¹ := by
        calc (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u
            = (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * (u *
              (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹)) *
                (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹)⁻¹ := by group
          _ = _ := by rw [h1]; group
      calc t₁ * ((u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u) * t₁⁻¹
          = t₁ * (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹ *
              (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹)⁻¹ := by group
        _ = (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u := h2.symm
    obtain ⟨z, hz⟩ := (mem_rootGroup J hJ).1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ u'.2) u.2)
    have hz1 : z = 1 := eq_one_of_generator_comm J hJ hK hfix hq hg (by rw [hz]; exact hw)
    apply Subtype.ext
    have : (u' : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * u = 1 := by rw [← hz, hz1, map_one]
    exact (inv_mul_eq_one.1 this).symm
  have hΨsurj : Function.Surjective Ψ := Finite.injective_iff_surjective.1 hΨinj
  obtain ⟨c, hcR, hc⟩ : ∃ c ∈ rootGroup J hJ, c = t₁ * (α t₁)⁻¹ := ⟨_, hα g, rfl⟩
  obtain ⟨u, hu⟩ := hΨsurj ⟨c⁻¹, Subgroup.inv_mem _ hcR⟩
  refine ⟨u, u.2, fun t ht => ?_⟩
  have hu' : (u : ProjectiveSpecialUnitaryMatrixGroup J) *
      (t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ * t₁⁻¹) = c⁻¹ := congrArg Subtype.val hu
  have hα₁ : α t₁ = u * t₁ * (u : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ := by
    have : α t₁ = c⁻¹ * t₁ := by rw [hc]; group
    rw [this, ← hu']
    group
  obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).1 ht
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg k)
  rw [map_zpow, ← ht₁, map_zpow, hα₁, conj_zpow]

end Lang

section PElement

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

omit [Finite K] [Fact p.Prime] in
noncomputable def fstHom : ↥(rootGroup J hJ) →* Multiplicative K :=
  (coordFst J).comp (rootCoord J hJ).symm.toMonoidHom

omit [Finite K] [Fact p.Prime] in
theorem fstHom_root (z : Coord J) :
    fstHom J hJ ⟨root J hJ z, root_mem_rootGroup J hJ z⟩ = Multiplicative.ofAdd z.1.1 := by
  have : rootCoord J hJ z = ⟨root J hJ z, root_mem_rootGroup J hJ z⟩ := Subtype.ext rfl
  simp only [fstHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← this,
    MulEquiv.symm_apply_apply]
  rfl

include hK hfix

theorem fstHom_surjective : Function.Surjective (fstHom J hJ) := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  intro a
  obtain ⟨z, hz⟩ := exists_coord_fst J hσ (Multiplicative.toAdd a)
  exact ⟨⟨root J hJ z, root_mem_rootGroup J hJ z⟩, by rw [fstHom_root, hz]; rfl⟩

theorem fstHom_eq_one_iff (x : ↥(rootGroup J hJ)) :
    fstHom J hJ x = 1 ↔ (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hx
  rw [fstHom_root, root_mem_center_iff J hJ hK hfix]
  show Multiplicative.ofAdd z.1.1 = 1 ↔ z.1.1 = 0
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]

omit [Finite K] [Fact p.Prime] hK hfix in
theorem fstHom_conj (k : Kˣ) (y : ↥(rootGroup J hJ))
    (hy : torus J hJ k * (y : ProjectiveSpecialUnitaryMatrixGroup J) * (torus J hJ k)⁻¹ ∈
      rootGroup J hJ) :
    fstHom J hJ ⟨torus J hJ k * (y : ProjectiveSpecialUnitaryMatrixGroup J) * (torus J hJ k)⁻¹, hy⟩
      = Multiplicative.ofAdd (((lamUnit J k : Kˣ) : K) * Multiplicative.toAdd (fstHom J hJ y)) := by
  obtain ⟨y, hyR⟩ := y
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hyR
  have h1 : (⟨torus J hJ k * root J hJ z * (torus J hJ k)⁻¹, hy⟩ : ↥(rootGroup J hJ)) =
      ⟨root J hJ (hermitianTorusAction J k z), root_mem_rootGroup J hJ _⟩ :=
    Subtype.ext (torus_mul_root_mul_inv J hJ k z)
  show fstHom J hJ ⟨torus J hJ k * root J hJ z * (torus J hJ k)⁻¹, hy⟩ = _
  rw [h1, fstHom_root, fstHom_root, toAdd_ofAdd, torusAction_val, coe_lamUnit]
  show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  congr 1
  ring

theorem eq_conj_of_pElement (hq : 2 < p ^ f) (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    {m : ℕ} (hαp : α ^ p ^ m = 1) (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ)
    (hαT : ∀ t ∈ torusGroup J hJ, α t = t) :
    ∃ r ∈ rootGroup J hJ, α = MulAut.conj r := by
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hmapR : (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact hαR r hr
    · rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
  have hαsymm : ∀ r ∈ rootGroup J hJ, α.symm r ∈ rootGroup J hJ := by
    intro r hr
    rw [← hmapR] at hr
    obtain ⟨r', hr', rfl⟩ := hr
    simpa using hr'
  have hαZ : ∀ z ∈ rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      α z ∈ rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    intro z hz
    refine Subgroup.mem_inf.2 ⟨hαR z (Subgroup.mem_inf.1 hz).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 (α.symm r) (hαsymm r hr)
    calc r * α z = α (α.symm r * z) := by simp
      _ = α (z * α.symm r) := by rw [h1]
      _ = α z * r := by simp
  set Z : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    rootGroup J hJ ⊓ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) with hZdef
  have hTZ : ∀ t ∈ torusGroup J hJ, ∀ v ∈ Z, t * v * t⁻¹ ∈ Z := by
    intro t ht v hv
    have htN := torusGroup_le_normalizer_rootGroup J hJ ht
    refine Subgroup.mem_inf.2
      ⟨(Subgroup.mem_normalizer_iff.1 htN v).1 (Subgroup.mem_inf.1 hv).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : t⁻¹ * r * t ∈ rootGroup J hJ := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem htN) r).1 hr
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hv).2 _ hr'
    calc r * (t * v * t⁻¹) = t * ((t⁻¹ * r * t) * v) * t⁻¹ := by group
      _ = t * (v * (t⁻¹ * r * t)) * t⁻¹ := by rw [h1]
      _ = (t * v * t⁻¹) * r := by group
  let gZ : ↥Z → ↥Z := fun z => ⟨α z, hαZ z z.2⟩
  have hgZ : ∀ (n : ℕ) (z : ↥Z), ((gZ^[n] z : ↥Z) : ProjectiveSpecialUnitaryMatrixGroup J) =
      (α ^ n) z := by
    intro n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih]
  have hgZp : ∀ z, gZ^[p ^ m] z = z := by
    intro z
    apply Subtype.ext
    rw [hgZ, hαp]
    rfl
  let CZ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (α.toMonoidHom.eqLocus (MonoidHom.id _)) ⊓ Z
  have hCZT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ CZ, t * v * t⁻¹ ∈ CZ := by
    intro t ht v hv
    refine Subgroup.mem_inf.2 ⟨?_, hTZ t ht v (Subgroup.mem_inf.1 hv).2⟩
    have hv1 : α v = v := (Subgroup.mem_inf.1 hv).1
    show α (t * v * t⁻¹) = t * v * t⁻¹
    rw [map_mul, map_mul, map_inv, hαT t ht, hv1]
  have hCZ : CZ = Z := by
    rcases eq_bot_or_eq_center_of_torus_invariant J hJ hK hfix (V := CZ) inf_le_right hCZT with
      h | h
    · exfalso
      obtain ⟨z, hz, hz1⟩ := exists_fixedPoint_ne gZ (r := p) (m := m) (n := f - 1) hgZp
        (by rw [card_center_rootGroup J hJ hK hfix, Nat.sub_add_cancel hf1]) 1 (by
          apply Subtype.ext
          exact map_one α) 
      apply hz1
      apply Subtype.ext
      have : (z : ProjectiveSpecialUnitaryMatrixGroup J) ∈ CZ :=
        Subgroup.mem_inf.2 ⟨congrArg Subtype.val hz, z.2⟩
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact h
  have hαZfix : ∀ z ∈ Z, α z = z := fun z hz => by
    have : z ∈ CZ := hCZ ▸ hz
    exact (Subgroup.mem_inf.1 this).1
  let φ := fstHom J hJ
  let αR : ↥(rootGroup J hJ) →* ↥(rootGroup J hJ) :=
    (α.toMonoidHom.comp (rootGroup J hJ).subtype).codRestrict (rootGroup J hJ) fun x =>
      hαR x x.2
  have hαR_coe : ∀ x : ↥(rootGroup J hJ), ((αR x : ↥(rootGroup J hJ)) :
      ProjectiveSpecialUnitaryMatrixGroup J) = α x := fun x => rfl
  have hker : φ.ker ≤ (φ.comp αR).ker := by
    intro x hx
    have hxZ := (fstHom_eq_one_iff J hJ hK hfix x).1 hx
    show φ (αR x) = 1
    have : αR x = x := Subtype.ext (hαZfix x hxZ)
    rw [this]
    exact hx
  let ᾱ : Multiplicative K →* Multiplicative K :=
    MonoidHom.liftOfSurjective φ (fstHom_surjective J hJ hK hfix) ⟨φ.comp αR, hker⟩
  have hᾱ : ∀ x, ᾱ (φ x) = φ (αR x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ.comp αR, hker⟩ x
  have hfR : ∀ (n : ℕ) (x : ↥(rootGroup J hJ)),
      (((fun y => αR y)^[n] x : ↥(rootGroup J hJ)) : ProjectiveSpecialUnitaryMatrixGroup J) =
        (α ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih]
      rfl
  have hφiter : ∀ (n : ℕ) (x : ↥(rootGroup J hJ)),
      φ ((fun y => αR y)^[n] x) = (fun a => ᾱ a)^[n] (φ x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hᾱ]
  have hᾱp : ∀ a, (fun a => ᾱ a)^[p ^ m] a = a := by
    intro a
    obtain ⟨x, rfl⟩ := fstHom_surjective J hJ hK hfix a
    rw [← hφiter]
    congr 1
    apply Subtype.ext
    rw [hfR, hαp]
    rfl
  obtain ⟨a, ha, ha1⟩ := exists_fixedPoint_ne (fun a => ᾱ a) (r := p) (m := m) (n := 2 * f - 1)
    hᾱp (by
      rw [Nat.card_congr Multiplicative.toAdd, hK, ← pow_mul,
        show f * 2 = 2 * f - 1 + 1 by omega]) 1 (map_one ᾱ)
  obtain ⟨x₀, rfl⟩ := fstHom_surjective J hJ hK hfix a
  let X : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    ((φ.comp αR).eqLocus φ).map (rootGroup J hJ).subtype
  have hXmem : ∀ x : ↥(rootGroup J hJ), (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ X ↔
      φ (αR x) = φ x := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  have hZX : Z ≤ X := by
    intro z hz
    have hzR : z ∈ rootGroup J hJ := (Subgroup.mem_inf.1 hz).1
    have := (hXmem ⟨z, hzR⟩).2 (by
      have : αR ⟨z, hzR⟩ = ⟨z, hzR⟩ := Subtype.ext (hαZfix z hz)
      rw [this])
    exact this
  have hXR : X ≤ rootGroup J hJ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hXT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ X, t * v * t⁻¹ ∈ X := by
    intro t ht v hv
    obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).1 ht
    have hvR : v ∈ rootGroup J hJ := hXR hv
    have hvx := (hXmem ⟨v, hvR⟩).1 hv
    have htN := torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k)
    have hy : torus J hJ k * v * (torus J hJ k)⁻¹ ∈ rootGroup J hJ :=
      (Subgroup.mem_normalizer_iff.1 htN v).1 hvR
    have hαv : α v ∈ rootGroup J hJ := hαR v hvR
    have hy' : torus J hJ k * α v * (torus J hJ k)⁻¹ ∈ rootGroup J hJ :=
      (Subgroup.mem_normalizer_iff.1 htN (α v)).1 hαv
    refine (hXmem ⟨_, hy⟩).2 ?_
    have h1 : αR ⟨torus J hJ k * v * (torus J hJ k)⁻¹, hy⟩ =
        ⟨torus J hJ k * α v * (torus J hJ k)⁻¹, hy'⟩ := by
      apply Subtype.ext
      show α (torus J hJ k * v * (torus J hJ k)⁻¹) = _
      rw [map_mul, map_mul, map_inv, hαT _ (torus_mem_torusGroup J hJ k)]
    rw [h1, fstHom_conj J hJ k ⟨α v, hαv⟩ hy', fstHom_conj J hJ k ⟨v, hvR⟩ hy]
    show Multiplicative.ofAdd (_ * Multiplicative.toAdd (φ (αR ⟨v, hvR⟩))) = _
    rw [hvx]
  have hXne : X ≠ Z := by
    intro h
    have : (x₀ : ProjectiveSpecialUnitaryMatrixGroup J) ∈ X := (hXmem x₀).2 (by
      rw [← hᾱ]
      exact ha)
    rw [h] at this
    exact ha1 ((fstHom_eq_one_iff J hJ hK hfix x₀).2 this)
  have hXR' : X = rootGroup J hJ := by
    rcases eq_center_or_eq_rootGroup_of_torus_invariant J hJ hK hfix hq hZX hXR hXT with h | h
    · exact absurd h hXne
    · exact h
  have hαR_phi : ∀ x : ↥(rootGroup J hJ), φ (αR x) = φ x := fun x =>
    (hXmem x).1 (by rw [hXR']; exact x.2)
  have hδZ : ∀ x : ↥(rootGroup J hJ), α x * (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ ∈ Z := by
    intro x
    have h1 : φ (αR x * x⁻¹) = 1 := by rw [map_mul, map_inv, hαR_phi, mul_inv_cancel]
    exact (fstHom_eq_one_iff J hJ hK hfix _).1 h1
  let δ : ↥(rootGroup J hJ) →* ProjectiveSpecialUnitaryMatrixGroup J :=
    MonoidHom.mk' (fun x => α x * (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) fun x y => by
      have hc : Commute (x : ProjectiveSpecialUnitaryMatrixGroup J)
          (α y * (y : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hδZ y)).2 x x.2
      have hc' := hc.inv_left.eq
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
      calc α x * α y * ((y : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ *
            (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹)
          = α x * ((α y * (y : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) *
              (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) := by group
        _ = α x * ((x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ *
              (α y * (y : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹)) := by rw [← hc']
        _ = (α x * (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) *
              (α y * (y : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹) := by group
  let C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (α.toMonoidHom.eqLocus (MonoidHom.id _)) ⊓ rootGroup J hJ
  have hZC : Z ≤ C := fun z hz => Subgroup.mem_inf.2 ⟨hαZfix z hz, (Subgroup.mem_inf.1 hz).1⟩
  have hCR : C ≤ rootGroup J hJ := inf_le_right
  have hCT : ∀ t ∈ torusGroup J hJ, ∀ v ∈ C, t * v * t⁻¹ ∈ C := by
    intro t ht v hv
    have htN := torusGroup_le_normalizer_rootGroup J hJ ht
    refine Subgroup.mem_inf.2
      ⟨?_, (Subgroup.mem_normalizer_iff.1 htN v).1 (Subgroup.mem_inf.1 hv).2⟩
    have hv1 : α v = v := (Subgroup.mem_inf.1 hv).1
    show α (t * v * t⁻¹) = t * v * t⁻¹
    rw [map_mul, map_mul, map_inv, hαT t ht, hv1]
  have hC : C = rootGroup J hJ := by
    rcases eq_center_or_eq_rootGroup_of_torus_invariant J hJ hK hfix hq hZC hCR hCT with h | h
    · exfalso
      have hker_le : ∀ x : ↥(rootGroup J hJ), δ x = 1 →
          (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ Z := by
        intro x hx
        have h1 : α x * (x : ProjectiveSpecialUnitaryMatrixGroup J)⁻¹ = 1 := hx
        have h2 : α x = x := mul_inv_eq_one.1 h1
        have h3 : (x : ProjectiveSpecialUnitaryMatrixGroup J) ∈ C := Subgroup.mem_inf.2 ⟨h2, x.2⟩
        rwa [h] at h3
      have hrange_le : δ.range ≤ Z := by
        rintro _ ⟨x, rfl⟩
        exact hδZ x
      have h1 : Nat.card δ.ker ≤ Nat.card Z := by
        refine Nat.card_le_card_of_injective
          (fun x => ⟨(x : ↥(rootGroup J hJ)).1, hker_le x x.2⟩) ?_
        intro a b hab
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1)
      have h2 : Nat.card δ.range ≤ Nat.card Z := Subgroup.card_le_of_le hrange_le
      have h3 := Subgroup.card_ker_mul_card_range δ
      rw [card_rootGroup_eq J hJ hK hfix] at h3
      have h4 : Nat.card Z = p ^ f := card_center_rootGroup J hJ hK hfix
      have h5 : p ^ (3 * f) ≤ p ^ f * p ^ f := by
        rw [← h3]
        calc Nat.card δ.ker * Nat.card δ.range ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul h1 h2
          _ = p ^ f * p ^ f := by rw [h4]
      have h6 : p ^ f * p ^ f = p ^ (2 * f) := by
        rw [← pow_add]
        congr 1
        ring
      rw [h6] at h5
      have h7 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (show 2 * f < 3 * f by omega)
      omega
    · exact h
  have hfixR : ∀ r ∈ rootGroup J hJ, α r = r := by
    intro r hr
    have hrC : r ∈ C := by rw [hC]; exact hr
    exact (Subgroup.mem_inf.1 hrC).1
  exact eq_conj_of_fixes_rootGroup J hJ hK hfix hq α hfixR

end PElement

section Center

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hJ hK hfix

theorem center_eq_bot (hq : 2 < p ^ f) :
    Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  have := isSimpleGroup_psu J (p ^ f) hK hfix hq
  rcases (Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J)).normal_of_characteristic
    |>.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hw : weyl J hJ ∈ Subgroup.center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [h]; trivial
    have hwN : weyl J hJ ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro r
      have : weyl J hJ * r * (weyl J hJ)⁻¹ = r := by
        rw [← Subgroup.mem_center_iff.1 hw r, mul_inv_cancel_right]
      rw [this]
    rw [normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq] at hwN
    exact weyl_not_mem_stabilizer J hJ hwN

end Center

end CFSG.AGLEmbedding.UnitaryModel
