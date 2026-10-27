module

public import CFSG.LieType.Steinberg.CentralExt.RootLift
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LieType.Steinberg.RankTwo.Statement

public section

open Matrix CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SL
open CFSG.LieType.Steinberg.RankTwo
open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

attribute [local instance] TorusLift.centerCommGroup

variable {m : ℕ} {F : Type} [Field F]

variable (F) in
@[expose] noncomputable def tv (i j : Fin (m + 1)) (c : F) : SpecialLinearGroup (Fin (m + 1)) F :=
  if h : i ≠ j then SpecialLinearGroup.transvection h c else 1

theorem tv_of_ne {i j : Fin (m + 1)} (h : i ≠ j) (c : F) :
    tv F i j c = SpecialLinearGroup.transvection h c := dite_eq_left h

theorem x_eq_tv (γ : Fin m → ℤ) (c : F) : x m F γ c = tv F (pairOf m γ).1 (pairOf m γ).2 c := rfl

theorem tv_add {i j : Fin (m + 1)} (h : i ≠ j) (c d : F) :
    tv F i j (c + d) = tv F i j c * tv F i j d := by
  rw [tv_of_ne h, tv_of_ne h, tv_of_ne h, SpecialLinearGroup.transvection_add]

theorem conj_tv {g : SpecialLinearGroup (Fin (m + 1)) F} {d : Fin (m + 1) → F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d) {i j : Fin (m + 1)}
    (h : i ≠ j) (c : F) : g * tv F i j c * g⁻¹ = tv F i j (d i * (d j)⁻¹ * c) := by
  rw [tv_of_ne h, tv_of_ne h, conj_transvection_of_coe_eq_diagonal hg h]
  congr 1
  ring

theorem commute_of_coe_eq_diagonal {g g' : SpecialLinearGroup (Fin (m + 1)) F}
    {d d' : Fin (m + 1) → F} (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d)
    (hg' : (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d') : g' * g * g'⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (g' : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
  rw [hg, hg', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext r
  exact mul_comm _ _

theorem diag_ne_zero {g : SpecialLinearGroup (Fin (m + 1)) F} {d : Fin (m + 1) → F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d) (r : Fin (m + 1)) :
    d r ≠ 0 :=
  SpecialLinearGroup.diagonal_neZero d (by rw [← hg]; exact g.2) r

@[expose] noncomputable def diagT (u : Fˣ) (i j : Fin (m + 1)) :
    SpecialLinearGroup (Fin (m + 1)) F :=
  if h : i ≠ j then SpecialLinearGroup.diag2nUnit h u else 1

theorem coe_diagT (u : Fˣ) {i j : Fin (m + 1)} (h : i ≠ j) :
    ((diagT u i j : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (fun r => if r = i then (u : F) else if r = j then (u : F)⁻¹ else 1) := by
  rw [diagT, dite_eq_left h, SpecialLinearGroup.diag2nUnit_coe, Units.val_inv_eq_inv_val]

theorem coe_diagT_mul (u : Fˣ) {a b a' b' : Fin (m + 1)} (h : a ≠ b) (h' : a' ≠ b') :
    ((diagT u a b * diagT u a' b' : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      diagonal (fun r => (if r = a then (u : F) else if r = b then (u : F)⁻¹ else 1) *
        (if r = a' then (u : F) else if r = b' then (u : F)⁻¹ else 1)) := by
  change (diagT u a b : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * (diagT u a' b' : Matrix _ _ F) = _
  rw [coe_diagT u h, coe_diagT u h', diagonal_mul_diagonal]

theorem tv_commute {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s t : F) : tv F i j s * tv F k l t = tv F k l t * tv F i j s := by
  rw [tv_of_ne hij, tv_of_ne hkl]
  exact (SpecialLinearGroup.commute_transvection hij hkl hjk hli s t).eq

theorem tv_chain {i j l : Fin (m + 1)} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t : F) :
    ⁅tv F i j s, tv F j l t⁆ = tv F i l (s * t) := by
  rw [tv_of_ne hij, tv_of_ne hjl, tv_of_ne hil]
  exact SpecialLinearGroup.commutatorElement_transvection hij hjl hil s t

@[expose] def Separating (m : ℕ) (F : Type) [Field F] : Prop :=
  ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → ¬(k = i ∧ l = j) → ¬(k = j ∧ l = i) →
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧ d i * (d j)⁻¹ ≠ 1

@[expose] def SeparatingOverlap (m : ℕ) (F : Type) [Field F] : Prop :=
  ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → ¬(k = i ∧ l = j) → ¬(k = j ∧ l = i) →
    (k = i ∨ k = j ∨ l = i ∨ l = j) →
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧ d i * (d j)⁻¹ ≠ 1

theorem Separating.overlap (h : Separating m F) : SeparatingOverlap m F :=
  fun i j k l hij hkl hne hne' _ => h i j k l hij hkl hne hne'

theorem sep_of_free (v : Fˣ) (hv : (v : F) ≠ 1) {i j k l r : Fin (m + 1)} (hij : i ≠ j)
    (hne : ¬(k = i ∧ l = j)) (hne' : ¬(k = j ∧ l = i)) (hri : r ≠ i) (hrj : r ≠ j)
    (hrk : r ≠ k) (hrl : r ≠ l) :
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧
        d i * (d j)⁻¹ ≠ 1 := by
  by_cases hi : k = i ∨ l = i
  · have hjk : k ≠ j := fun e => by
      rcases hi with hi | hi
      · exact hij (hi.symm.trans e)
      · exact hne' ⟨e, hi⟩
    have hjl : l ≠ j := fun e => by
      rcases hi with hi | hi
      · exact hne ⟨hi, e⟩
      · exact hij (hi.symm.trans e)
    refine ⟨_, _, coe_diagT v hrj, ?_, ?_⟩
    · simp [hrk.symm, hjk, hrl.symm, hjl]
    · simpa [hri.symm, hij, hrj.symm] using hv
  · push Not at hi
    refine ⟨_, _, coe_diagT v hri.symm, ?_, ?_⟩
    · simp [hi.1, hrk.symm, hi.2, hrl.symm]
    · simpa [hij.symm, hrj.symm] using hv

theorem sep_of_disjoint (v : Fˣ) (hv : (v : F) ^ 2 ≠ 1) {i j k l : Fin (m + 1)} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧
        d i * (d j)⁻¹ ≠ 1 := by
  refine ⟨_, _, coe_diagT v hij, ?_, ?_⟩
  · simp [hki, hkj, hli, hlj]
  · simpa [hij.symm, sq] using hv

theorem sep_of_overlap (u : Fˣ) (hu : (u : F) ^ 3 ≠ 1) {i j k l : Fin (m + 1)} (hij : i ≠ j)
    (hkl : k ≠ l) (hne : ¬(k = i ∧ l = j)) (hne' : ¬(k = j ∧ l = i))
    (hov : k = i ∨ k = j ∨ l = i ∨ l = j) :
    ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧
        d i * (d j)⁻¹ ≠ 1 := by
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  suffices h : ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧
        d i * (d j)⁻¹ = (u : F) ^ 3 by
    obtain ⟨g, d, hg, hkl', hd⟩ := h
    exact ⟨g, d, hg, hkl', hd ▸ hu⟩
  by_cases hki : k = i
  ·
    rw [hki] at hkl ⊢
    have hlj : l ≠ j := fun e => hne ⟨hki, e⟩
    refine ⟨_, _, coe_diagT_mul u hij hlj, ?_, ?_⟩
    · simp [hkl, hkl.symm, hlj, hij]
    · simp [hij, hij.symm, hlj.symm, hkl]
      field_simp
  by_cases hkj : k = j
  ·
    rw [hkj] at hkl ⊢
    have hli : l ≠ i := fun e => hne' ⟨hkj, e⟩
    refine ⟨_, _, coe_diagT_mul u hij hli.symm, ?_, ?_⟩
    · simp [hkl, hkl.symm, hli, hij.symm]
    · simp [hij.symm, hkl]
      field_simp
  by_cases hli : l = i
  ·
    rw [hli] at hkl ⊢
    refine ⟨_, _, coe_diagT_mul u hij hkj, ?_, ?_⟩
    · simp [hkl, hkl.symm, hkj, hij]
    · simp [hij, hij.symm, Ne.symm hkj, hkl.symm]
      field_simp
  have hlj : l = j := by tauto
  rw [hlj] at hkl ⊢
  refine ⟨_, _, coe_diagT_mul u hij (Ne.symm hki), ?_, ?_⟩
  · simp [hkl, hkl.symm, hki, hij.symm]
  · simp [hij.symm, hkl.symm]
    field_simp

theorem exists_ne_ne (hm : 2 ≤ m) (i j : Fin (m + 1)) : ∃ o : Fin (m + 1), o ≠ i ∧ o ≠ j := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon ⟨0, by omega⟩
  have h1 := hcon ⟨1, by omega⟩
  have h2 := hcon ⟨2, by omega⟩
  simp only [ne_eq, Fin.ext_iff, imp_iff_not_or, not_not] at h0 h1 h2
  omega

theorem exists_ne3 (hm : 3 ≤ m) (a b c : Fin (m + 1)) :
    ∃ r : Fin (m + 1), r ≠ a ∧ r ≠ b ∧ r ≠ c := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon ⟨0, by omega⟩
  have h1 := hcon ⟨1, by omega⟩
  have h2 := hcon ⟨2, by omega⟩
  have h3 := hcon ⟨3, by omega⟩
  simp only [ne_eq, Fin.ext_iff, imp_iff_not_or, not_not] at h0 h1 h2 h3
  omega

theorem exists_ne4 (hm : 4 ≤ m) (a b c e : Fin (m + 1)) :
    ∃ r : Fin (m + 1), r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ e := by
  by_contra hcon
  push Not at hcon
  have h0 := hcon ⟨0, by omega⟩
  have h1 := hcon ⟨1, by omega⟩
  have h2 := hcon ⟨2, by omega⟩
  have h3 := hcon ⟨3, by omega⟩
  have h4 := hcon ⟨4, by omega⟩
  simp only [ne_eq, Fin.ext_iff, imp_iff_not_or, not_not] at h0 h1 h2 h3 h4
  omega

theorem separating_of_cube (u : Fˣ) (hu : (u : F) ^ 3 ≠ 1)
    (hm : m = 2 ∨ ∃ v : Fˣ, (v : F) ^ 2 ≠ 1) : Separating m F := by
  intro i j k l hij hkl hne hne'
  by_cases hov : k = i ∨ k = j ∨ l = i ∨ l = j
  · exact sep_of_overlap u hu hij hkl hne hne' hov
  push Not at hov
  rcases hm with rfl | ⟨v, hv⟩
  · exfalso
    obtain ⟨h1, h2, h3, h4⟩ := hov
    simp only [ne_eq, Fin.ext_iff] at h1 h2 h3 h4 hij hkl
    omega
  · exact sep_of_disjoint v hv hij hov.1 hov.2.1 hov.2.2.1 hov.2.2.2

theorem separating_of_sq (hm : 3 ≤ m) (v : Fˣ) (hv : (v : F) ^ 2 ≠ 1) : Separating m F := by
  intro i j k l hij hkl hne hne'
  have hv1 : (v : F) ≠ 1 := fun h => hv (by rw [h, one_pow])
  by_cases hov : k = i ∨ k = j ∨ l = i ∨ l = j
  · obtain ⟨r, hri, hrj, hrk, hrl⟩ : ∃ r : Fin (m + 1), r ≠ i ∧ r ≠ j ∧ r ≠ k ∧ r ≠ l := by
      rcases hov with h | h | h | h
      · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j l
        exact ⟨r, h1, h2, fun e => h1 (e.trans h), h3⟩
      · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j l
        exact ⟨r, h1, h2, fun e => h2 (e.trans h), h3⟩
      · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j k
        exact ⟨r, h1, h2, h3, fun e => h1 (e.trans h)⟩
      · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j k
        exact ⟨r, h1, h2, h3, fun e => h2 (e.trans h)⟩
    exact sep_of_free v hv1 hij hne hne' hri hrj hrk hrl
  push Not at hov
  exact sep_of_disjoint v hv hij hov.1 hov.2.1 hov.2.2.1 hov.2.2.2

theorem separating_of_free (hm : 4 ≤ m) (v : Fˣ) (hv : (v : F) ≠ 1) : Separating m F := by
  intro i j k l hij hkl hne hne'
  obtain ⟨r, hri, hrj, hrk, hrl⟩ := exists_ne4 hm i j k l
  exact sep_of_free v hv hij hne hne' hri hrj hrk hrl

theorem separatingOverlap_of_three_le (hm : 3 ≤ m) (v : Fˣ) (hv : (v : F) ≠ 1) :
    SeparatingOverlap m F := by
  intro i j k l hij hkl hne hne' hov
  obtain ⟨r, hri, hrj, hrk, hrl⟩ : ∃ r : Fin (m + 1), r ≠ i ∧ r ≠ j ∧ r ≠ k ∧ r ≠ l := by
    rcases hov with h | h | h | h
    · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j l
      exact ⟨r, h1, h2, fun e => h1 (e.trans h), h3⟩
    · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j l
      exact ⟨r, h1, h2, fun e => h2 (e.trans h), h3⟩
    · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j k
      exact ⟨r, h1, h2, h3, fun e => h1 (e.trans h)⟩
    · obtain ⟨r, h1, h2, h3⟩ := exists_ne3 hm i j k
      exact ⟨r, h1, h2, h3, fun e => h2 (e.trans h)⟩
  exact sep_of_free v hv hij hne hne' hri hrj hrk hrl

theorem exists_unit_sq_cube_ne_one [Finite F] (hF : 5 ≤ Nat.card F) :
    ∃ u : Fˣ, (u : F) ^ 2 ≠ 1 ∧ (u : F) ^ 3 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  refine ⟨g, fun h => ?_, fun h => ?_⟩
  · have h' : g ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h')
    omega
  · have h' : g ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h')
    omega

theorem separating_of_five_le [Finite F] (hF : 5 ≤ Nat.card F) : Separating m F := by
  obtain ⟨u, hu2, hu3⟩ := exists_unit_sq_cube_ne_one hF
  exact separating_of_cube u hu3 (Or.inr ⟨u, hu2⟩)

theorem separating_of_card [Finite F] (hm : 2 ≤ m) (h2 : Nat.card F ≠ 2)
    (h4 : ¬(m = 2 ∧ Nat.card F = 4)) (h3 : ¬(m = 3 ∧ Nat.card F = 3)) : Separating m F := by
  have : Fintype F := Fintype.ofFinite F
  have hF2 : 2 ≤ Nat.card F := by
    rw [← Fintype.card_eq_nat_card]
    exact Fintype.one_lt_card
  rcases (show 5 ≤ Nat.card F ∨ Nat.card F = 4 ∨ Nat.card F = 3 by omega) with hF | hF | hF
  · exact separating_of_five_le hF
  ·
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hord : orderOf g = 3 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    have hg2 : (g : F) ^ 2 ≠ 1 := fun h => by
      have h' : g ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have := Nat.le_of_dvd (by norm_num) (hord ▸ orderOf_dvd_of_pow_eq_one h')
      omega
    exact separating_of_sq (by omega) g hg2
  ·
    have hch : ringChar F ≠ 2 := fun h => by
      have := FiniteField.even_card_of_char_two h
      rw [Fintype.card_eq_nat_card, hF] at this
      exact absurd this (by decide)
    have hne : (-1 : F) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two hch
    rcases (show m = 2 ∨ 4 ≤ m by omega) with rfl | hm4
    · refine separating_of_cube (-1) ?_ (Or.inl rfl)
      rw [Units.val_neg, Units.val_one, show ((-1 : F)) ^ 3 = -1 by ring]
      exact hne
    · exact separating_of_free hm4 (-1) (by simpa using hne)

section Lift

variable {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}

theorem commute_commutatorElement (hcen : π.ker ≤ Subgroup.center E) {a b c : E}
    (ha : π c * π a = π a * π c) (hb : π c * π b = π b * π c) : c * ⁅a, b⁆ = ⁅a, b⁆ * c := by
  have hza : a⁻¹ * (c * a * c⁻¹) ∈ π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [ha, mul_inv_cancel_right, inv_mul_cancel]
  have hzb : b⁻¹ * (c * b * c⁻¹) ∈ π.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hb, mul_inv_cancel_right, inv_mul_cancel]
  have e : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [conjugate_commutatorElement]
    calc ⁅c * a * c⁻¹, c * b * c⁻¹⁆ = ⁅a * (a⁻¹ * (c * a * c⁻¹)), b * (b⁻¹ * (c * b * c⁻¹))⁆ := by
          rw [mul_inv_cancel_left, mul_inv_cancel_left]
      _ = ⁅a, b⁆ := by
          rw [TorusLift.commutatorElement_mul_central_left (hcen hza),
            TorusLift.commutatorElement_mul_central_right (hcen hzb)]
  calc c * ⁅a, b⁆ = c * ⁅a, b⁆ * c⁻¹ * c := by group
    _ = ⁅a, b⁆ * c := by rw [e]

variable (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π)

include hcen in
theorem commPairing_eq_zero (hm : 2 ≤ m) {i j : Fin (m + 1)} (h : i ≠ j) :
    TorusLift.commPairing hcen hπ (tv_add (F := F) h) = 0 := by
  obtain ⟨o, hoi, hoj⟩ := exists_ne_ne hm i j
  refine AddMonoidHom.ext fun s => AddMonoidHom.ext fun t => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [TorusLift.commPairing_apply, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, toMul_zero,
    Subgroup.coe_one]
  set a := TorusLift.lift hπ (tv F i o s)
  set b := TorusLift.lift hπ (tv F o j 1)
  set c := TorusLift.lift hπ (tv F i j t)
  have hab : π ⁅a, b⁆ = tv F i j s := by
    rw [map_commutatorElement, TorusLift.map_lift, TorusLift.map_lift,
      tv_chain hoi.symm hoj h, mul_one]
  rw [TorusLift.commutatorElement_eq_of_map_eq hcen ((TorusLift.map_lift hπ _).trans hab.symm)
    rfl, commutatorElement_eq_one_iff_mul_comm]
  refine (commute_commutatorElement hcen ?_ ?_).symm
  · rw [TorusLift.map_lift, TorusLift.map_lift]
    exact tv_commute h hoi.symm h.symm hoi t s
  · rw [TorusLift.map_lift, TorusLift.map_lift]
    exact tv_commute h hoj hoj.symm h.symm t 1

variable (π) in
@[expose] def IsRootLift (i j : Fin (m + 1)) (Y : F → E) : Prop :=
  (∀ s t, Y (s + t) = Y s * Y t) ∧ (∀ s, π (Y s) = tv F i j s) ∧
    ∀ (g : SpecialLinearGroup (Fin (m + 1)) F) (d : Fin (m + 1) → F),
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d → ∀ e : E, π e = g →
        ∀ s, e * Y s * e⁻¹ = Y (d i * (d j)⁻¹ * s)

include hcen hπ in
theorem exists_isRootLift (hm : 2 ≤ m) {i j : Fin (m + 1)} (h : i ≠ j)
    {g : SpecialLinearGroup (Fin (m + 1)) F} {d : Fin (m + 1) → F}
    (hg : (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d) (ha : d i * (d j)⁻¹ ≠ 1) :
    ∃ Y : F → E, IsRootLift π i j Y :=
  ⟨TorusLift.canonLift hπ (x := tv F i j) g (d i * (d j)⁻¹),
    TorusLift.canonLift_add hcen hπ (tv_add h) (commPairing_eq_zero hcen hπ hm h) (conj_tv hg h) ha,
    TorusLift.map_canonLift hπ (tv_add h) (conj_tv hg h) ha,
    fun _ _ hg' _ he s => TorusLift.conj_canonLift hcen hπ (commute_of_coe_eq_diagonal hg hg')
      (conj_tv hg' h) he s⟩

variable (π) in
open _root_.Classical in
@[expose] noncomputable def X (i j : Fin (m + 1)) : F → E :=
  if h : ∃ Y : F → E, IsRootLift π i j Y then h.choose else fun _ => 1

theorem X_isRootLift {i j : Fin (m + 1)} (h : ∃ Y : F → E, IsRootLift π i j Y) :
    IsRootLift π i j (X π i j) := by
  classical
  rw [X, dite_eq_left h]
  exact h.choose_spec

variable (hm : 2 ≤ m) (hsep : SeparatingOverlap m F)
include hcen hπ hm hsep

theorem X_spec {i j : Fin (m + 1)} (h : i ≠ j) : IsRootLift π i j (X π i j) := by
  obtain ⟨o, hoi, hoj⟩ := exists_ne_ne hm i j
  obtain ⟨g, d, hg, -, ha⟩ := hsep i j i o h hoi.symm (fun e => hoj e.2) (fun e => h e.1)
    (Or.inl rfl)
  exact X_isRootLift (exists_isRootLift hcen hπ hm h hg ha)

theorem X_commute_of_sep {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (hgd : ∃ g : SpecialLinearGroup (Fin (m + 1)) F, ∃ d : Fin (m + 1) → F,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = diagonal d ∧ d k = d l ∧ d i * (d j)⁻¹ ≠ 1)
    (s t : F) : X π i j s * X π k l t = X π k l t * X π i j s := by
  obtain ⟨hXa, hXπ, hXe⟩ := X_spec hcen hπ hm hsep hij
  obtain ⟨-, hYπ, hYe⟩ := X_spec hcen hπ hm hsep hkl
  obtain ⟨g, d, hg, hdkl, ha⟩ := hgd
  obtain ⟨e, he⟩ := hπ g
  refine RootLift.commute_lifts hcen hXa hXπ hYπ (fun s t => tv_commute hij hkl hjk hli s t) ha
    (hXe g d hg e he) (fun t => ?_) s t
  rw [hYe g d hg e he, hdkl, mul_inv_cancel₀ (diag_ne_zero hg l), one_mul]

theorem X_commute_overlap {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (hov : k = i ∨ k = j ∨ l = i ∨ l = j) (s t : F) :
    X π i j s * X π k l t = X π k l t * X π i j s := by
  by_cases heq : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hXa, -, -⟩ := X_spec hcen hπ hm hsep hij
    rw [← hXa, ← hXa, add_comm]
  exact X_commute_of_sep hcen hπ hm hsep hij hkl hjk hli
    (hsep i j k l hij hkl heq (fun e => hjk e.1.symm) hov) s t

theorem X_chain {i j l : Fin (m + 1)} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t : F) :
    ⁅X π i j s, X π j l t⁆ = X π i l (1 * s * t) := by
  obtain ⟨hXa, hXπ, hXe⟩ := X_spec hcen hπ hm hsep hij
  obtain ⟨-, hYπ, hYe⟩ := X_spec hcen hπ hm hsep hjl
  obtain ⟨hZa, hZπ, hZe⟩ := X_spec hcen hπ hm hsep hil
  obtain ⟨g, d, hg, hdjl, ha⟩ := hsep i j j l hij hjl (fun e => hij e.1.symm)
    (fun e => hil e.2.symm) (Or.inr (Or.inl rfl))
  obtain ⟨e, he⟩ := hπ g
  refine RootLift.commutator_lifts_eq hcen hXa hZa hXπ hYπ hZπ (C := 1)
    (fun s t => by rw [one_mul]; exact tv_chain hij hjl hil s t)
    (fun s r => X_commute_overlap hcen hπ hm hsep hij hil hij.symm hil.symm (Or.inl rfl) s r) ha
    (hXe g d hg e he) (fun t => ?_) (fun r => ?_) s t
  · rw [hYe g d hg e he, hdjl, mul_inv_cancel₀ (diag_ne_zero hg l), one_mul]
  · rw [hZe g d hg e he, ← hdjl]

end Lift

theorem X_commute {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hcen : π.ker ≤ Subgroup.center E) (hπ : Function.Surjective π) (hm : 2 ≤ m)
    (hsep : Separating m F) {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (s t : F) : X π i j s * X π k l t = X π k l t * X π i j s := by
  by_cases heq : k = i ∧ l = j
  · exact X_commute_overlap hcen hπ hm hsep.overlap hij hkl hjk hli (Or.inl heq.1) s t
  exact X_commute_of_sep hcen hπ hm hsep.overlap hij hkl hjk hli
    (hsep i j k l hij hkl heq fun e => hjk e.1.symm) s t

section Section

variable {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
  (Y : Fin (m + 1) → Fin (m + 1) → F → E)

@[expose] noncomputable def yL (γ : Fin m → ℤ) : F → E :=
  Y (pairOf m γ).1 (pairOf m γ).2

private theorem list_eq_singleton' {l : List (ℕ × ℕ)} (hl : l.Nodup)
    (h : ∀ p, p ∈ l ↔ p = (1, 1)) : l = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton _)).2
    fun p => by rw [h, List.mem_singleton])

variable (hadd : ∀ i j : Fin (m + 1), i ≠ j → ∀ s t, Y i j (s + t) = Y i j s * Y i j t)
  (hcomm : ∀ i j k l : Fin (m + 1), i ≠ j → k ≠ l → j ≠ k → l ≠ i → ∀ s t,
    Y i j s * Y k l t = Y k l t * Y i j s)
  (hchain : ∀ i j l : Fin (m + 1), i ≠ j → j ≠ l → i ≠ l → ∀ s t,
    ⁅Y i j s, Y j l t⁆ = Y i l (1 * s * t))
include hadd hcomm hchain

theorem commutatorFormula_yL (O : CommOrder (Φ (m := m) (F := F))) :
    CommutatorFormula (yL Y) O (commC (m := m)) := by
  intro α hα β hβ hαβ c d
  obtain ⟨hij, hα'⟩ := pairOf_spec (m := m) hα
  obtain ⟨hkl, hβ'⟩ := pairOf_spec (m := m) hβ
  have hmem := fun p => (O.mem_iff α hα β hβ hαβ p).trans (mem_expPairs_iff hα hβ hαβ p)
  have hnopp : ¬((pairOf m α).1 = (pairOf m β).2 ∧ (pairOf m α).2 = (pairOf m β).1) := by
    rintro ⟨e1, e2⟩
    apply hαβ
    apply toStd_injective m
    rw [toStd_add, hα', hβ', e1, e2, toStd_zero]
    abel
  by_cases hc : Chain α β
  · have hl : O.list α β = [(1, 1)] :=
      list_eq_singleton' (O.nodup α β) fun p => (hmem p).trans (and_iff_left hc)
    rw [hl, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one]
    rcases hc with hc | hc
    ·
      have hil : (pairOf m α).1 ≠ (pairOf m β).2 := fun e => hnopp ⟨e, hc⟩
      have hsum : toStd m (α + β) = Pi.single (pairOf m α).1 1 - Pi.single (pairOf m β).2 1 := by
        rw [toStd_add, hα', hβ', hc]
        abel
      have hp := pairOf_eq hil hsum
      simp only [yL, hp, commC_of_eq hc, Int.cast_one]
      rw [← hc]
      exact hchain _ _ _ hij (hc ▸ hkl) hil c d
    ·
      have hji : (pairOf m β).1 ≠ (pairOf m α).2 := fun e => hnopp ⟨hc.symm, e.symm⟩
      have hnc : (pairOf m α).2 ≠ (pairOf m β).1 := fun e => hji e.symm
      have hsum : toStd m (α + β) = Pi.single (pairOf m β).1 1 - Pi.single (pairOf m α).2 1 := by
        rw [toStd_add, hα', hβ', hc]
        abel
      have hp := pairOf_eq hji hsum
      simp only [yL, hp, commC_of_ne hnc]
      rw [hc, ← commutatorElement_inv, hchain _ _ _ (hc ▸ hkl) hij hji d c,
        ← TorusLift.x_neg (hadd _ _ hji)]
      congr 1
      push_cast
      ring
  · have hl : O.list α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
      hc ((hmem p).1 hp).2
    rw [hl, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _ _ _ hij hkl (fun e => hc (Or.inl e)) (fun e => hc (Or.inr e)) c d

variable (hmap : ∀ i j : Fin (m + 1), i ≠ j → ∀ s, π (Y i j s) = tv F i j s)
include hmap

theorem exists_section_of_lifts [Finite F] (hm : 2 ≤ m) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (rootDatum m F).isFiniteType
    (Dv := (rootDatum m F).divisible) rfl
  have hx : PresentationB (Φ := Φ (m := m) (F := F)) (x m F) := presentationB hm
  obtain ⟨σ, hσ, -⟩ := existsUnique_hom_of_presentationB hx O (commutatorFormula O)
    (⟨fun _ hγ c d => hadd _ _ (pairOf_spec (m := m) hγ).1 c d,
      commutatorFormula_yL Y hadd hcomm hchain O⟩ : ChevRels O (commC (m := m)) (yL Y))
  refine ⟨σ, fun g => ?_⟩
  have hid : π.comp σ = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense (closure_range_eq_top_of_presentationB hx O) ?_
    intro g hg
    obtain ⟨γ, hγ, c, rfl⟩ : ∃ γ, γ ∈ (Φ (m := m) (F := F)).roots ∧ ∃ c, x m F γ c = g := by
      simpa using hg
    rw [MonoidHom.comp_apply, hσ γ hγ c, MonoidHom.id_apply]
    exact (hmap _ _ (pairOf_spec (m := m) hγ).1 c).trans (x_eq_tv γ c).symm
  exact DFunLike.congr_fun hid g

end Section

theorem sl_exists_section_of_separating [Finite F] (hm : 2 ≤ m) (hsep : Separating m F)
    {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g :=
  exists_section_of_lifts (X π) (fun _ _ h => (X_spec hcen hπ hm hsep.overlap h).1)
    (fun _ _ _ _ hij hkl hjk hli => X_commute hcen hπ hm hsep hij hkl hjk hli)
    (fun _ _ _ hij hjl hil => X_chain hcen hπ hm hsep.overlap hij hjl hil)
    (fun _ _ h => (X_spec hcen hπ hm hsep.overlap h).2.1) hm

theorem sl_exists_section_of_central [Finite F] (hm : 2 ≤ m) (hF : 5 ≤ Nat.card F)
    {E : Type*} [Group E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g :=
  sl_exists_section_of_separating hm (separating_of_five_le hF) hπ hcen

theorem sl_hopfMultiplier_mulEquiv_ker_of_split (hm : 2 ≤ m)
    (hsplit : ∀ (E : Type) [Group E] (π : E →* SpecialLinearGroup (Fin (m + 1)) F),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g)
    {X : Type} [Group X] (q : SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    Nonempty (CFSG.RankThree.PerfectCover.hopfMultiplier X ≃* q.ker) := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) F) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have : Group.IsPerfect X := Group.IsPerfect.ofSurjective hq
  exact ⟨MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker
    fun π hπ hcen => hsplit _ π hπ hcen)⟩

theorem sl_hopfMultiplier_mulEquiv_ker_of_separating [Finite F] (hm : 2 ≤ m)
    (hsep : Separating m F) {X : Type} [Group X] (q : SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    Nonempty (CFSG.RankThree.PerfectCover.hopfMultiplier X ≃* q.ker) :=
  sl_hopfMultiplier_mulEquiv_ker_of_split hm
    (fun _ _ _ hπ hcen => sl_exists_section_of_separating hm hsep hπ hcen) q hq hker

theorem sl_hopfMultiplier_mulEquiv_ker [Finite F] (hm : 2 ≤ m) (hF : 5 ≤ Nat.card F)
    {X : Type} [Group X] (q : SpecialLinearGroup (Fin (m + 1)) F →* X)
    (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) :
    Nonempty (CFSG.RankThree.PerfectCover.hopfMultiplier X ≃* q.ker) :=
  sl_hopfMultiplier_mulEquiv_ker_of_separating hm (separating_of_five_le hF) q hq hker

end CFSG.LieType.Steinberg.CentralExt.SLClosed
