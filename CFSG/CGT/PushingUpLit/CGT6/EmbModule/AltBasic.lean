module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm Subgroup

theorem mem_closure_threeCycles_fix {n : ℕ} (x₀ : Fin n) (σ : Perm (Fin n))
    (hσ : σ ∈ alternatingGroup (Fin n)) (hx : σ x₀ = x₀) :
    σ ∈ Subgroup.closure {c : Perm (Fin n) | c.IsThreeCycle ∧ c x₀ = x₀} := by
  classical
  let p : Fin n → Prop := fun x => x ≠ x₀
  have h1 : ∀ x, p (σ x) ↔ p x := by
    intro x
    simp only [p]
    constructor
    · intro h hx'
      apply h
      rw [hx', hx]
    · intro h hx'
      apply h
      apply σ.injective
      rw [hx', hx]
  have h2 : ∀ x, σ x ≠ x → p x := by
    intro x hx' hxx
    apply hx'
    rw [hxx, hx]
  have hsign : sign (σ.subtypePerm h1) = 1 := by
    rw [sign_subtypePerm σ h1 h2]
    exact mem_alternatingGroup.mp hσ
  have hmem : σ.subtypePerm h1 ∈ alternatingGroup {x // p x} := mem_alternatingGroup.mpr hsign
  rw [← closure_three_cycles_eq_alternating] at hmem
  have key : ∀ τ ∈ Subgroup.closure {c : Perm {x // p x} | c.IsThreeCycle},
      (ofSubtype : Perm {x // p x} →* Perm (Fin n)) τ ∈
        Subgroup.closure {c : Perm (Fin n) | c.IsThreeCycle ∧ c x₀ = x₀} := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem c hc =>
      apply Subgroup.subset_closure
      refine ⟨?_, ?_⟩
      · rw [← card_support_eq_three_iff, support_ofSubtype, Finset.card_map]
        exact card_support_eq_three_iff.mpr hc
      · exact ofSubtype_apply_of_not_mem c (by simp [p])
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  have := key _ hmem
  rwa [ofSubtype_subtypePerm h1 h2] at this

theorem exists_alt_apply {n : ℕ} (hn : Odd n) (x y : Fin n) :
    ∃ σ ∈ alternatingGroup (Fin n), σ x = y := by
  classical
  by_cases hxy : x = y
  · exact ⟨1, one_mem _, by simp [hxy]⟩
  · have h3 : 3 ≤ n := by
      have : 2 ≤ n := by
        by_contra h
        have h1 : n ≤ 1 := by omega
        have := x.2
        have := y.2
        apply hxy
        ext
        omega
      obtain ⟨k, hk⟩ := hn
      omega
    have : ∃ z : Fin n, z ≠ x ∧ z ≠ y := by
      by_contra hcon
      push Not at hcon
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {x, y} := by
        intro z _
        by_cases hz : z = x
        · simp [hz]
        · simp [hcon z hz]
      have := Finset.card_le_card hsub
      simp at this
      have h2 : ({x, y} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨z, hzx, hzy⟩ := this
    refine ⟨swap x y * swap y z, ?_, ?_⟩
    · rw [mem_alternatingGroup, map_mul, sign_swap hxy, sign_swap (Ne.symm hzy)]
      decide
    · simp [Equiv.swap_apply_of_ne_of_ne, hxy, Ne.symm hzx]

theorem stab_hom_trivial {Γ : Type*} [Group Γ] {n : ℕ} (θ : Γ →* Perm (Fin n))
    (hev : ∀ g, θ g ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ g = σ)
    {M : Type*} [CommGroup M] (hM : ∀ m : M, m ^ 2 = 1) (x₀ : Fin n) (χ : Γ → M)
    (hχ : ∀ g h, θ g x₀ = x₀ → θ h x₀ = x₀ → χ (g * h) = χ g * χ h)
    (hker : ∀ k, θ k = 1 → χ k = 1) :
    ∀ g, θ g x₀ = x₀ → χ g = 1 := by
  classical
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1 (by simp) (by simp)
    simpa using h
  let K : Subgroup Γ :=
    { carrier := {g | θ g x₀ = x₀ ∧ χ g = 1}
      one_mem' := ⟨by simp, hχ1⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨by rw [map_mul, Perm.mul_apply, hb.1, ha.1], ?_⟩
        rw [hχ a b ha.1 hb.1, ha.2, hb.2, mul_one]
      inv_mem' := fun {a} ha => by
        refine ⟨?_, ?_⟩
        · rw [map_inv]
          have := ha.1
          rw [Perm.inv_eq_iff_eq]
          exact this.symm
        · have h := hχ a⁻¹ a (by rw [map_inv, Perm.inv_eq_iff_eq]; exact ha.1.symm) ha.1
          rw [inv_mul_cancel, hχ1, ha.2, mul_one] at h
          exact h.symm }
  have hgen : ∀ c : Perm (Fin n), c.IsThreeCycle ∧ c x₀ = x₀ → c ∈ K.map θ := by
    rintro c ⟨hc3, hcx⟩
    obtain ⟨g, hg⟩ := hsurj c hc3.mem_alternatingGroup
    refine ⟨g, ⟨?_, ?_⟩, hg⟩
    · rw [hg]; exact hcx
    · have hg1 : θ g x₀ = x₀ := by rw [hg]; exact hcx
      have h2 : χ (g * g) = χ g * χ g := hχ g g hg1 hg1
      have h3 : χ (g * g * g) = χ g * χ g * χ g := by
        rw [hχ (g * g) g (by rw [map_mul, Perm.mul_apply, hg1, hg1]) hg1, h2]
      have h4 : θ (g * g * g) = 1 := by
        rw [map_mul, map_mul, hg]
        have : c ^ 3 = 1 := by
          rw [← hc3.orderOf]
          exact pow_orderOf_eq_one c
        simpa [pow_succ] using this
      have h5 := hker _ h4
      rw [h3] at h5
      have h6 : χ g ^ 2 = 1 := hM _
      have h7 : χ g * χ g = 1 := by rw [← pow_two]; exact h6
      rw [h7, one_mul] at h5
      exact h5
  have hS : Subgroup.closure {c : Perm (Fin n) | c.IsThreeCycle ∧ c x₀ = x₀} ≤ K.map θ :=
    (Subgroup.closure_le _).mpr hgen
  intro g hg
  have hmem := hS (mem_closure_threeCycles_fix x₀ (θ g) (hev g) hg)
  obtain ⟨k, hk, hkg⟩ := hmem
  have hgk : θ (g * k⁻¹) = 1 := by rw [map_mul, map_inv, hkg]; simp
  have hx : θ (g * k⁻¹) x₀ = x₀ := by rw [hgk]; rfl
  have h1 := hχ (g * k⁻¹) k hx hk.1
  rw [inv_mul_cancel_right, hker _ hgk, hk.2, one_mul] at h1
  exact h1

theorem zmod_two_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem zmod_two_swap (a b d : ZMod 2) (h : a = b + d) : b = a + d := by
  revert a b d
  decide

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

theorem multiplicative_zmod_two_sq (m : Multiplicative (ZMod 2)) : m ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul]
  exact zmod_two_add_self _

theorem cocycle_perm {Γ : Type*} [Group Γ] {n : ℕ} (hn : Odd n) (θ : Γ →* Perm (Fin n))
    (hev : ∀ g, θ g ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ g = σ) (x₀ : Fin n)
    (c : Γ → Fin n → ZMod 2)
    (hc : ∀ g h y, c (g * h) y = c g y + c h ((θ g)⁻¹ y))
    (hker : ∀ k, θ k = 1 → c k x₀ = 0) :
    ∃ m : Fin n → ZMod 2, ∀ g y, c g y = m y + m ((θ g)⁻¹ y) := by
  classical
  have hstab : ∀ g, θ g x₀ = x₀ → c g x₀ = 0 := by
    refine fun g hg => ?_
    have := stab_hom_trivial (M := Multiplicative (ZMod 2)) θ hev hsurj
      multiplicative_zmod_two_sq x₀ (fun g => Multiplicative.ofAdd (c g x₀))
      (fun g h hg hh => by
        show Multiplicative.ofAdd (c (g * h) x₀) = Multiplicative.ofAdd (c g x₀) *
          Multiplicative.ofAdd (c h x₀)
        rw [hc g h x₀]
        have : (θ g)⁻¹ x₀ = x₀ := by rw [Perm.inv_eq_iff_eq]; exact hg.symm
        rw [this]
        rfl)
      (fun k hk => by
        show Multiplicative.ofAdd (c k x₀) = 1
        rw [hker k hk]
        rfl) g hg
    exact Multiplicative.ofAdd.injective this
  have hex : ∀ y, ∃ k : Γ, θ k x₀ = y := by
    intro y
    obtain ⟨σ, hσ, hσy⟩ := exists_alt_apply hn x₀ y
    obtain ⟨k, hk⟩ := hsurj σ hσ
    exact ⟨k, by rw [hk]; exact hσy⟩
  choose k hk using hex
  let m : Fin n → ZMod 2 := fun y => c (k y) y
  have hwd : ∀ g y, θ g x₀ = y → c g y = m y := by
    intro g y hg
    have hstabg : θ ((k y)⁻¹ * g) x₀ = x₀ := by
      rw [map_mul, map_inv, Perm.mul_apply, hg, Perm.inv_eq_iff_eq]
      exact (hk y).symm
    have h1 := hc (k y) ((k y)⁻¹ * g) y
    rw [mul_inv_cancel_left] at h1
    have h2 : (θ (k y))⁻¹ y = x₀ := by
      rw [Perm.inv_eq_iff_eq]; exact (hk y).symm
    rw [h2, hstab _ hstabg, add_zero] at h1
    exact h1
  refine ⟨m, fun g y => ?_⟩
  have h1 := hc g (g⁻¹ * k y) y
  rw [mul_inv_cancel_left] at h1
  have hk' : θ (g⁻¹ * k y) x₀ = (θ g)⁻¹ y := by
    rw [map_mul, map_inv, Perm.mul_apply, hk y]
  have h2 := hwd (g⁻¹ * k y) ((θ g)⁻¹ y) hk'
  have h3 : c (k y) y = m y := rfl
  rw [h2, h3] at h1
  exact zmod_two_swap _ _ _ h1

@[expose] def fvecAdd (n : ℕ) (x : Fin n) : Fin n → ZMod 2 := fun y => if y = x then 0 else 1

theorem sum_fvecAdd {n : ℕ} (hn : Odd n) (x : Fin n) : ∑ y, fvecAdd n x y = 0 := by
  classical
  unfold fvecAdd
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (Finset.univ.filter (fun y : Fin n => ¬ y = x)).card = n - 1 := by
    rw [Finset.filter_not, Finset.filter_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [Finset.card_univ_sdiff]
    simp
  rw [h1]
  obtain ⟨k, hk⟩ := hn
  have : n - 1 = 2 * k := by omega
  rw [this]
  push_cast
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

@[expose] def fvec {n : ℕ} (hn : Odd n) (x : Fin n) : ↥(coreMod n) :=
  ⟨Multiplicative.ofAdd (fvecAdd n x), by
    rw [mem_coreMod]; exact sum_fvecAdd hn x⟩

theorem coreAct_fvec {n : ℕ} (hn : Odd n) (σ : Perm (Fin n)) (x : Fin n) :
    coreAct n σ (fvec hn x) = fvec hn (σ x) := by
  apply Subtype.ext
  show permAct n σ (Multiplicative.ofAdd (fvecAdd n x)) = Multiplicative.ofAdd (fvecAdd n (σ x))
  apply Multiplicative.toAdd.injective
  funext y
  simp only [permAct_apply, toAdd_ofAdd, fvecAdd]
  by_cases h : y = σ x
  · simp [h]
  · have : σ.symm y ≠ x := by
      intro h'
      apply h
      rw [← h']
      simp
    simp [h, this]

theorem prod_fvec {n : ℕ} (hn : Odd n) (v : ↥(coreMod n)) :
    (∏ x : Fin n, if Multiplicative.toAdd (v : PermMod n) x = 1 then fvec hn x else 1) = v := by
  classical
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext y
  rw [show (((∏ x : Fin n, if Multiplicative.toAdd (v : PermMod n) x = 1 then fvec hn x else 1 :
      ↥(coreMod n))) : PermMod n) = ∏ x : Fin n, ((if Multiplicative.toAdd (v : PermMod n) x = 1
        then fvec hn x else 1 : ↥(coreMod n)) : PermMod n) from map_prod (coreMod n).subtype _ _,
    toAdd_prod, Finset.sum_apply]
  have hv := v.2
  rw [mem_coreMod] at hv
  have key : ∀ x : Fin n, Multiplicative.toAdd
      ((if Multiplicative.toAdd (v : PermMod n) x = 1 then fvec hn x else 1 : ↥(coreMod n)) :
        PermMod n) y =
      Multiplicative.toAdd (v : PermMod n) x +
        (if y = x then Multiplicative.toAdd (v : PermMod n) x else 0) := by
    intro x
    rcases zmod_two_cases (Multiplicative.toAdd (v : PermMod n) x) with h | h
    · simp [h]
    · by_cases hy : y = x
      · simp [h, hy, fvec, fvecAdd, zmod_two_one_add_one]
      · simp [h, hy, fvec, fvecAdd]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, hv, zero_add]
  simp

theorem core_fixed_eq_one {n : ℕ} (hn : Odd n) (w : ↥(coreMod n))
    (h : ∀ σ ∈ alternatingGroup (Fin n), coreAct n σ w = w) : w = 1 := by
  have hc : ∀ x y : Fin n, Multiplicative.toAdd (w : PermMod n) x =
      Multiplicative.toAdd (w : PermMod n) y := by
    intro x y
    obtain ⟨σ, hσ, hσx⟩ := exists_alt_apply hn y x
    have := congrArg (fun z : ↥(coreMod n) => Multiplicative.toAdd (z : PermMod n) x) (h σ hσ)
    simp only [coreAct_coe, permAct_apply] at this
    have hx : σ⁻¹ x = y := by rw [Perm.inv_eq_iff_eq]; exact hσx.symm
    rw [hx] at this
    exact this.symm
  have hn0 : 0 < n := hn.pos
  let x₀ : Fin n := ⟨0, hn0⟩
  have hsum := w.2
  rw [mem_coreMod] at hsum
  have : ∑ i, Multiplicative.toAdd (w : PermMod n) i =
      ∑ _i : Fin n, Multiplicative.toAdd (w : PermMod n) x₀ :=
    Finset.sum_congr rfl fun i _ => hc i x₀
  rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  obtain ⟨k, hk⟩ := hn
  have h1 : (n : ZMod 2) = 1 := by
    rw [hk]; push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  rw [h1, one_mul] at hsum
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  funext y
  rw [hc y x₀, hsum]
  rfl

theorem fvec_ne_one {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) (x : Fin n) : fvec hn x ≠ 1 := by
  intro h
  have : ∃ y : Fin n, y ≠ x := by
    by_cases hx : x.1 = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
  obtain ⟨y, hy⟩ := this
  have := congrArg (fun z : ↥(coreMod n) => Multiplicative.toAdd (z : PermMod n) y) h
  simp [fvec, fvecAdd, hy] at this

theorem alt_hom_trivial {Γ : Type*} [Group Γ] {n : ℕ} (θ : Γ →* Perm (Fin n))
    (hev : ∀ g, θ g ∈ alternatingGroup (Fin n))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin n), ∃ g, θ g = σ)
    {M : Type*} [CommGroup M] (hM : ∀ m : M, m ^ 2 = 1) (χ : Γ → M)
    (hχ : ∀ g h, χ (g * h) = χ g * χ h) (hker : ∀ k, θ k = 1 → χ k = 1) :
    ∀ g, χ g = 1 := by
  classical
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1 1
    simpa using h
  let K : Subgroup Γ :=
    { carrier := {g | χ g = 1}
      one_mem' := hχ1
      mul_mem' := fun {a b} ha hb => by
        show χ (a * b) = 1
        rw [hχ a b, show χ a = 1 from ha, show χ b = 1 from hb, mul_one]
      inv_mem' := fun {a} ha => by
        show χ a⁻¹ = 1
        have h := hχ a⁻¹ a
        rw [inv_mul_cancel, hχ1, show χ a = 1 from ha, mul_one] at h
        exact h.symm }
  have hgen : ∀ c ∈ {c : Perm (Fin n) | c.IsThreeCycle}, c ∈ K.map θ := by
    intro c hc3
    obtain ⟨g, hg⟩ := hsurj c (Equiv.Perm.IsThreeCycle.mem_alternatingGroup hc3)
    refine ⟨g, ?_, hg⟩
    show χ g = 1
    have h2 : χ (g * g) = χ g * χ g := hχ g g
    have h3 : χ (g * g * g) = χ g * χ g * χ g := by rw [hχ (g * g) g, h2]
    have h4 : θ (g * g * g) = 1 := by
      rw [map_mul, map_mul, hg]
      have : c ^ 3 = 1 := by
        rw [← hc3.orderOf]
        exact pow_orderOf_eq_one c
      simpa [pow_succ] using this
    have h5 := hker _ h4
    rw [h3] at h5
    have h7 : χ g * χ g = 1 := by rw [← pow_two]; exact hM _
    rw [h7, one_mul] at h5
    exact h5
  have hS : alternatingGroup (Fin n) ≤ K.map θ := by
    rw [← closure_three_cycles_eq_alternating]
    exact (Subgroup.closure_le _).mpr hgen
  intro g
  obtain ⟨k, hk, hkg⟩ := hS (hev g)
  have hgk : θ (g * k⁻¹) = 1 := by rw [map_mul, map_inv, hkg]; simp
  have h1 := hχ (g * k⁻¹) k
  rw [inv_mul_cancel_right, hker _ hgk, show χ k = 1 from hk, one_mul] at h1
  exact h1

end CFSG.CGT.PushingUpLit.CGT6
