module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Steinberg.PartBAssembly
public import CFSG.LieType.Steinberg.Presentation

public noncomputable section

namespace CFSG.LieType.Steinberg.SL

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.RootSystem
open scoped commutatorElement

section Single

variable {ι : Type*} [DecidableEq ι]

theorem single_sub_single_apply_le (r s x : ι) :
    (Pi.single r 1 - Pi.single s 1 : ι → ℤ) x ≤ 1 := by
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> omega

theorem neg_one_le_single_sub_single_apply (r s x : ι) :
    -1 ≤ (Pi.single r 1 - Pi.single s 1 : ι → ℤ) x := by
  simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs <;> omega

theorem eq_of_single_sub_single_apply_eq_one {r s x : ι}
    (h : (Pi.single r 1 - Pi.single s 1 : ι → ℤ) x = 1) : x = r := by
  simp only [Pi.sub_apply, Pi.single_apply] at h
  split_ifs at h with h1 <;> first | exact h1 | omega

theorem single_sub_single_inj {i j i' j' : ι} (hij : i ≠ j)
    (h : (Pi.single i 1 - Pi.single j 1 : ι → ℤ) = Pi.single i' 1 - Pi.single j' 1) :
    i = i' ∧ j = j' := by
  have h₁ := congrFun h i
  have h₂ := congrFun h j
  simp only [Pi.sub_apply, Pi.single_apply] at h₁ h₂
  grind

theorem coeff_eq_one {i j k l r s : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hnot : ¬ (i = l ∧ j = k)) {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : a • (Pi.single i 1 - Pi.single j 1 : ι → ℤ) + b • (Pi.single k 1 - Pi.single l 1) =
      Pi.single r 1 - Pi.single s 1) :
    a = 1 ∧ b = 1 ∧ (j = k ∨ l = i) := by
  have hv : ∀ x, a * ((if x = i then 1 else 0) - (if x = j then 1 else 0)) +
      b * ((if x = k then 1 else 0) - (if x = l then 1 else 0)) =
        (Pi.single r 1 - Pi.single s 1 : ι → ℤ) x := fun x => by
    rw [← h]
    simp [Pi.single_apply]
  have hub := fun x => (hv x).trans_le (single_sub_single_apply_le r s x)
  have hlb := fun x => (neg_one_le_single_sub_single_apply r s x).trans_eq (hv x).symm
  have hik : i ≠ k := by
    rintro rfl
    have := hub i
    simp [hij, hkl] at this
    omega
  have hjl : j ≠ l := by
    rintro rfl
    have := hlb j
    simp [Ne.symm hij, Ne.symm hkl] at this
    omega
  by_cases hil : i = l
  · subst hil
    have hjk : j ≠ k := fun h' => hnot ⟨rfl, h'⟩
    have h1 := hlb j
    have h2 := hub k
    simp [Ne.symm hij, hjk, Ne.symm hik, Ne.symm hjk] at h1 h2
    exact ⟨by omega, by omega, Or.inr rfl⟩
  · by_cases hjk : j = k
    · subst hjk
      have h1 := hub i
      have h2 := hlb l
      simp [hij, hil, Ne.symm hil, Ne.symm hjl] at h1 h2
      exact ⟨by omega, by omega, Or.inl rfl⟩
    · exfalso
      have h1 := hv i
      have h2 := hv k
      simp [hij, hik, hil, Ne.symm hik, hkl, Ne.symm hjk] at h1 h2
      have ha1 : a = 1 := by
        have := hub i
        simp [hij, hik, hil] at this
        have := hlb i
        omega
      have hb1 : b = 1 := by
        have := hub k
        simp [Ne.symm hik, Ne.symm hjk, hkl] at this
        omega
      rw [ha1] at h1
      rw [hb1] at h2
      exact hik ((eq_of_single_sub_single_apply_eq_one h1.symm).trans
        (eq_of_single_sub_single_apply_eq_one h2.symm).symm)

end Single

variable (m : ℕ) (F : Type) [Field F]

theorem toStd_add (v w : Fin m → ℤ) : toStd m (v + w) = toStd m v + toStd m w := by
  rw [← sub_neg_eq_add, toStd_sub, toStd_neg, sub_neg_eq_add]

open _root_.Classical in
@[expose] def pairOf (γ : Fin m → ℤ) : Fin (m + 1) × Fin (m + 1) :=
  if h : ∃ p : Fin (m + 1) × Fin (m + 1), p.1 ≠ p.2 ∧
      toStd m γ = Pi.single p.1 1 - Pi.single p.2 1 then h.choose else (0, 0)

variable {m} in
theorem pairOf_spec {γ : Fin m → ℤ} (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    (pairOf m γ).1 ≠ (pairOf m γ).2 ∧
      toStd m γ = Pi.single (pairOf m γ).1 1 - Pi.single (pairOf m γ).2 1 := by
  classical
  rw [roots_eq] at hγ
  obtain ⟨i, j, hij, h⟩ := hγ
  have he : ∃ p : Fin (m + 1) × Fin (m + 1), p.1 ≠ p.2 ∧
      toStd m γ = Pi.single p.1 1 - Pi.single p.2 1 := ⟨(i, j), hij, h⟩
  unfold pairOf
  rw [dite_eq_left he]
  exact he.choose_spec

variable {m} in
theorem pairOf_eq {γ : Fin m → ℤ} {i j : Fin (m + 1)} (hij : i ≠ j)
    (h : toStd m γ = Pi.single i 1 - Pi.single j 1) : pairOf m γ = (i, j) := by
  have hγ : γ ∈ roots (isFiniteType_A m) ∅ := by
    rw [roots_eq]
    exact ⟨i, j, hij, h⟩
  obtain ⟨-, h'⟩ := pairOf_spec hγ
  obtain ⟨e1, e2⟩ := single_sub_single_inj hij (h.symm.trans h')
  exact Prod.ext e1.symm e2.symm

@[expose] def x (γ : Fin m → ℤ) (c : F) : SpecialLinearGroup (Fin (m + 1)) F :=
  if h : (pairOf m γ).1 ≠ (pairOf m γ).2 then SpecialLinearGroup.transvection h c else 1

variable {m F}

theorem x_eq {γ : Fin m → ℤ} {i j : Fin (m + 1)} (hij : i ≠ j)
    (h : toStd m γ = Pi.single i 1 - Pi.single j 1) (c : F) :
    x m F γ c = SpecialLinearGroup.transvection hij c := by
  have hp := pairOf_eq hij h
  unfold x
  have hne : (pairOf m γ).1 ≠ (pairOf m γ).2 := by rw [hp]; exact hij
  rw [dite_eq_left hne]
  have e1 : (pairOf m γ).1 = i := by rw [hp]
  have e2 : (pairOf m γ).2 = j := by rw [hp]
  subst e1 e2
  rfl

theorem isParametrization :
    IsParametrization (Φ := RootSystem.ofCartan (rootDatum m F).isFiniteType
      (rootDatum m F).divisible) (rootDatum m F).rootGroup (x m F) := by
  intro γ hγ
  obtain ⟨hij, hst⟩ := pairOf_spec (m := m) hγ
  have hx := x_eq (F := F) hij hst
  refine ⟨fun g => ?_, fun c d => ?_, fun c d hcd => ?_⟩
  · change g ∈ rootGroup m F γ ↔ _
    rw [rootGroup_eq m F hij hst, mem_rootSubgroup]
    simp only [hx]
  · rw [hx, hx, hx, SpecialLinearGroup.transvection_add]
  · rw [hx, hx] at hcd
    exact SpecialLinearGroup.transvection_injective hij hcd

abbrev Φ : RootSystem (Fin m) :=
  RootSystem.ofCartan (rootDatum m F).isFiniteType (rootDatum m F).divisible

theorem Φ_roots : (Φ (m := m) (F := F)).roots = roots (isFiniteType_A m) ∅ := rfl

@[expose] def Chain (α β : Fin m → ℤ) : Prop :=
  (pairOf m α).2 = (pairOf m β).1 ∨ (pairOf m β).2 = (pairOf m α).1

private theorem not_opp {α β : Fin m → ℤ} (hα : α ∈ roots (isFiniteType_A m) ∅)
    (hβ : β ∈ roots (isFiniteType_A m) ∅) (hαβ : α + β ≠ 0) :
    ¬ ((pairOf m α).1 = (pairOf m β).2 ∧ (pairOf m α).2 = (pairOf m β).1) := by
  rintro ⟨e1, e2⟩
  apply hαβ
  apply toStd_injective m
  rw [toStd_add, (pairOf_spec hα).2, (pairOf_spec hβ).2, e1, e2, toStd_zero]
  abel

theorem mem_expPairs_iff {α β : Fin m → ℤ} (hα : α ∈ roots (isFiniteType_A m) ∅)
    (hβ : β ∈ roots (isFiniteType_A m) ∅) (hαβ : α + β ≠ 0) (p : ℕ × ℕ) :
    p ∈ expPairs (Φ (m := m) (F := F)) α β ↔ p = (1, 1) ∧ Chain α β := by
  obtain ⟨hij, hα'⟩ := pairOf_spec hα
  obtain ⟨hkl, hβ'⟩ := pairOf_spec hβ
  constructor
  · rintro ⟨hp1, hp2, hr⟩
    rw [Φ_roots, roots_eq] at hr
    obtain ⟨r, s, -, hrs⟩ := hr
    rw [toStd_add, ← natCast_zsmul, ← natCast_zsmul, toStd_smul, toStd_smul, hα', hβ'] at hrs
    obtain ⟨ha, hb, hc⟩ := coeff_eq_one hij hkl (not_opp hα hβ hαβ) (by omega) (by omega) hrs
    exact ⟨Prod.ext (by omega) (by omega), hc⟩
  · rintro ⟨rfl, hc⟩
    refine ⟨one_pos, one_pos, ?_⟩
    rw [one_smul, one_smul, Φ_roots, roots_eq]
    rcases hc with hc | hc
    · refine ⟨(pairOf m α).1, (pairOf m β).2, fun e => not_opp hα hβ hαβ ⟨e, hc⟩, ?_⟩
      rw [toStd_add, hα', hβ', hc]
      abel
    · refine ⟨(pairOf m β).1, (pairOf m α).2, fun e => not_opp hα hβ hαβ ⟨hc.symm, e.symm⟩, ?_⟩
      rw [toStd_add, hα', hβ', hc]
      abel

@[expose] def commC (α β : Fin m → ℤ) (_ : ℕ × ℕ) : ℤ :=
  if (pairOf m α).2 = (pairOf m β).1 then 1 else -1

theorem commC_natAbs (α β : Fin m → ℤ) (p : ℕ × ℕ) : (commC α β p).natAbs = 1 := by
  unfold commC
  split_ifs <;> rfl

theorem commC_of_eq {α β : Fin m → ℤ} (h : (pairOf m α).2 = (pairOf m β).1) (p : ℕ × ℕ) :
    commC α β p = 1 := by
  simp only [commC, h, ↓reduceIte]

theorem commC_of_ne {α β : Fin m → ℤ} (h : (pairOf m α).2 ≠ (pairOf m β).1) (p : ℕ × ℕ) :
    commC α β p = -1 := by
  simp only [commC, h, ↓reduceIte]

private theorem comm_chain {i j k l : Fin (m + 1)} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l)
    (hk : k = j) (c d : F) :
    ⁅SpecialLinearGroup.transvection hij c, SpecialLinearGroup.transvection hkl d⁆ =
      SpecialLinearGroup.transvection hil (c * d) := by
  subst hk
  exact SpecialLinearGroup.commutatorElement_transvection hij hkl hil c d

private theorem transvection_inv {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    (SpecialLinearGroup.transvection hij c)⁻¹ = SpecialLinearGroup.transvection hij (-c) := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← SpecialLinearGroup.transvection_add, neg_add_cancel,
    SpecialLinearGroup.transvection_coeff_zero]

private theorem list_eq_singleton {l : List (ℕ × ℕ)} (hl : l.Nodup) (h : ∀ p, p ∈ l ↔ p = (1, 1)) :
    l = [(1, 1)] :=
  List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hl (List.nodup_singleton _)).2
    fun p => by rw [h, List.mem_singleton])

theorem commutatorFormula (O : CommOrder (Φ (m := m) (F := F))) :
    CommutatorFormula (x m F) O (commC (m := m)) := by
  intro α hα β hβ hαβ c d
  obtain ⟨hij, hα'⟩ := pairOf_spec (m := m) hα
  obtain ⟨hkl, hβ'⟩ := pairOf_spec (m := m) hβ
  have hmem := fun p => (O.mem_iff α hα β hβ hαβ p).trans (mem_expPairs_iff hα hβ hαβ p)
  rw [x_eq hij hα', x_eq hkl hβ']
  by_cases hc : Chain α β
  · have hl : O.list α β = [(1, 1)] :=
      list_eq_singleton (O.nodup α β) fun p => (hmem p).trans (and_iff_left hc)
    rw [hl, List.map_singleton, List.prod_singleton, one_smul, one_smul, pow_one, pow_one]
    rcases hc with hc | hc
    · have hil : (pairOf m α).1 ≠ (pairOf m β).2 := fun e => not_opp hα hβ hαβ ⟨e, hc⟩
      have hsum : toStd m (α + β) = Pi.single (pairOf m α).1 1 - Pi.single (pairOf m β).2 1 := by
        rw [toStd_add, hα', hβ', hc]
        abel
      rw [x_eq hil hsum, commC_of_eq hc, Int.cast_one, one_mul]
      exact comm_chain hij hkl hil hc.symm c d
    · have hji : (pairOf m β).1 ≠ (pairOf m α).2 := fun e => not_opp hα hβ hαβ ⟨hc.symm, e.symm⟩
      have hnc : (pairOf m α).2 ≠ (pairOf m β).1 := fun e => hji e.symm
      have hsum : toStd m (α + β) = Pi.single (pairOf m β).1 1 - Pi.single (pairOf m α).2 1 := by
        rw [toStd_add, hα', hβ', hc]
        abel
      rw [x_eq hji hsum, commC_of_ne hnc, ← commutatorElement_inv,
        comm_chain hkl hij hji hc.symm d c, transvection_inv]
      congr 1
      push_cast
      ring
  · have hl : O.list α β = [] := List.eq_nil_iff_forall_not_mem.2 fun p hp =>
      hc ((hmem p).1 hp).2
    rw [hl, List.map_nil, List.prod_nil, commutatorElement_eq_one_iff_commute]
    exact SpecialLinearGroup.commute_transvection hij hkl (fun e => hc (Or.inl e))
      (fun e => hc (Or.inr e)) c d

section Monomial

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]

@[expose] def monomialMat (π : Equiv.Perm n) (w : n → R) : Matrix n n R :=
  Matrix.of fun a b => if b = π a then w a else 0

theorem monomialMat_mul_single (π : Equiv.Perm n) (w : n → R) (r s : n) (u : R) :
    monomialMat π w * single r s u = single (π.symm r) s (w (π.symm r) * u) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (π a)]
  · simp only [monomialMat, Matrix.of_apply, single_apply, ite_true]
    by_cases h : π a = r
    · subst h
      simp
    · have h' : π.symm r ≠ a := fun e => h (by rw [← e, Equiv.apply_symm_apply])
      have h'' : r ≠ π a := Ne.symm h
      simp [h', h'']
  · intro c _ hc
    simp [monomialMat, hc]
  · simp

theorem single_mul_monomialMat (π : Equiv.Perm n) (w : n → R) (r s : n) (u : R) :
    single r s u * monomialMat π w = single r (π s) (u * w s) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · simp only [monomialMat, Matrix.of_apply, single_apply]
    by_cases ha : r = a
    · by_cases hb : b = π s
      · subst ha hb
        simp
      · simp [ha, hb, Ne.symm hb]
    · simp [ha]
  · intro c _ hc
    simp [Ne.symm hc]
  · simp

theorem monomialMat_mul_transvection (π : Equiv.Perm n) (w : n → R) (r s : n) (u : R)
    (hw : w (π.symm s) ≠ 0) :
    monomialMat π w * transvection r s u =
      transvection (π.symm r) (π.symm s) (w (π.symm r) * u * (w (π.symm s))⁻¹) *
        monomialMat π w := by
  rw [transvection, transvection, mul_add, add_mul, mul_one, one_mul, monomialMat_mul_single,
    single_mul_monomialMat, Equiv.apply_symm_apply, inv_mul_cancel_right₀ hw]

end Monomial

@[expose] def weylScalar (i : Fin m) (t : Fˣ) (a : Fin (m + 1)) : F :=
  if a = i.castSucc then (t : F) else if a = i.succ then -((t⁻¹ : Fˣ) : F) else 1

theorem castSucc_ne_succ (i : Fin m) : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne

theorem toStd_neg_single (i : Fin m) :
    toStd m (-Pi.single i 1) = Pi.single i.succ 1 - Pi.single i.castSucc 1 := by
  rw [toStd_neg, toStd_single, neg_sub]

theorem coe_weylElement (i : Fin m) (t : Fˣ) :
    ((weylElement (x m F) i t : SpecialLinearGroup (Fin (m + 1)) F) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
      monomialMat (Equiv.swap i.castSucc i.succ) (weylScalar (F := F) i t) := by
  have hne := castSucc_ne_succ i
  have hw : weylElement (x m F) i t = SpecialLinearGroup.transvection hne (t : F) *
      SpecialLinearGroup.transvection hne.symm (-((t⁻¹ : Fˣ) : F)) *
        SpecialLinearGroup.transvection hne (t : F) := by
    rw [weylElement, x_eq hne (toStd_single m i), x_eq hne.symm (toStd_neg_single i)]
  rw [hw, ← SpecialLinearGroup.coeMonoidHom_apply, map_mul, map_mul]
  simp only [SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.transvection_coe]
  have ht : (t : F) * ((t⁻¹ : Fˣ) : F) = 1 := Units.mul_inv t
  have ht' : ((t⁻¹ : Fˣ) : F) * (t : F) = 1 := Units.inv_mul t
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hne.symm, add_zero, mul_neg, neg_mul, ht, ht']
  ext a b
  have hne' := Ne.symm hne
  simp only [Matrix.add_apply, single_apply, Matrix.one_apply, monomialMat, Matrix.of_apply,
    weylScalar, Equiv.swap_apply_def]
  by_cases ha : a = i.castSucc
  · subst ha
    by_cases hb : b = i.castSucc
    · subst hb
      simp [hne, hne']
    · by_cases hb' : b = i.succ
      · subst hb'
        simp [hne, hne']
      · simp [hne', hb', Ne.symm hb, Ne.symm hb']
  · by_cases ha' : a = i.succ
    · subst ha'
      by_cases hb : b = i.castSucc
      · subst hb
        simp [hne, hne']
      · by_cases hb' : b = i.succ
        · subst hb'
          simp [hne, hne']
        · simp [hne, hne', hb, Ne.symm hb, Ne.symm hb']
    · by_cases hab : a = b
      · subst hab
        simp [ha, ha', Ne.symm ha, Ne.symm ha']
      · simp [ha, ha', Ne.symm ha, Ne.symm ha', hab, Ne.symm hab]

theorem pairing_eq (i : Fin m) (β : Fin m → ℤ) :
    ∑ j, CartanMatrix.A m i j * β j = toStd m β i.castSucc - toStd m β i.succ := by
  have h := congrFun (toStd_reflection m i β) i.castSucc
  rw [reflection_apply, toStd_sub, toStd_smul, toStd_single] at h
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Function.comp_apply,
    Equiv.swap_apply_left, ↓reduceIte, castSucc_ne_succ i, mul_one, sub_zero] at h
  linarith

theorem toStd_reflection_of_eq (i : Fin m) {β : Fin m → ℤ} {r s : Fin (m + 1)}
    (h : toStd m β = Pi.single r 1 - Pi.single s 1) :
    toStd m (reflection (CartanMatrix.A m) i β) =
      Pi.single (Equiv.swap i.castSucc i.succ r) 1 -
        Pi.single (Equiv.swap i.castSucc i.succ s) 1 := by
  rw [toStd_reflection, h]
  funext a
  simp only [Function.comp_apply, Pi.sub_apply, Pi.single_apply, Equiv.swap_apply_eq_iff]

private theorem weylScalar_ratio (i : Fin m) (t : Fˣ) {r s : Fin (m + 1)} (hrs : r ≠ s) (u : F) :
    weylScalar i t (Equiv.swap i.castSucc i.succ r) * u *
        (weylScalar i t (Equiv.swap i.castSucc i.succ s))⁻¹ =
      (((if r = i.castSucc then -1 else 1) * (if s = i.castSucc then -1 else 1) : ℤ) : F) *
        ((t ^ (-((Pi.single r 1 - Pi.single s 1 : Fin (m + 1) → ℤ) i.castSucc -
          (Pi.single r 1 - Pi.single s 1 : Fin (m + 1) → ℤ) i.succ)) : Fˣ) : F) * u := by
  have hne := castSucc_ne_succ i
  have ht : (t : F) ≠ 0 := t.ne_zero
  simp only [Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Pi.sub_apply,
    Pi.single_apply, weylScalar, Equiv.swap_apply_def]
  by_cases hr : r = i.castSucc
  · subst hr
    by_cases hs : s = i.succ
    · subst hs
      simp [hne, Ne.symm hne]
      field_simp
    · have hs' : s ≠ i.castSucc := Ne.symm hrs
      simp [Ne.symm hne, hs, hs', Ne.symm hs, Ne.symm hs']
  · by_cases hr' : r = i.succ
    · subst hr'
      by_cases hs : s = i.castSucc
      · subst hs
        simp [hne, Ne.symm hne]
        field_simp
      · have hs' : s ≠ i.succ := Ne.symm hrs
        simp [hne, Ne.symm hne, hs, hs', Ne.symm hs, Ne.symm hs']
    · by_cases hs : s = i.castSucc
      · subst hs
        simp [Ne.symm hne, hr, hr', Ne.symm hr, Ne.symm hr']
        field_simp
      · by_cases hs' : s = i.succ
        · subst hs'
          simp [hne, Ne.symm hne, hr, hr', Ne.symm hr, Ne.symm hr']
          field_simp
        · simp [hr, hr', hs, hs', Ne.symm hr, Ne.symm hr', Ne.symm hs, Ne.symm hs']

theorem weyl (i : Fin m) {β : Fin m → ℤ} (hβ : β ∈ roots (isFiniteType_A m) ∅) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (t : Fˣ) (u : F),
      weylElement (x m F) i t * x m F β u * (weylElement (x m F) i t)⁻¹ =
        x m F (reflection (CartanMatrix.A m) i β)
          ((ε : F) * ((t ^ (-(∑ j, CartanMatrix.A m i j * β j)) : Fˣ) : F) * u) := by
  obtain ⟨hrs, hst⟩ := pairOf_spec hβ
  set r := (pairOf m β).1
  set s := (pairOf m β).2
  have hπ : Equiv.swap i.castSucc i.succ r ≠ Equiv.swap i.castSucc i.succ s :=
    (Equiv.swap _ _).injective.ne hrs
  have hrefl := toStd_reflection_of_eq i hst
  refine ⟨(if r = i.castSucc then -1 else 1) * (if s = i.castSucc then -1 else 1), ?_,
    fun t u => ?_⟩
  · by_cases h1 : r = i.castSucc <;> by_cases h2 : s = i.castSucc <;> simp [h1, h2]
  rw [mul_inv_eq_iff_eq_mul, pairing_eq, hst, x_eq hrs hst, x_eq hπ hrefl]
  apply Subtype.val_injective
  change SpecialLinearGroup.coeMonoidHom (_ * _) = SpecialLinearGroup.coeMonoidHom (_ * _)
  rw [map_mul, map_mul]
  simp only [SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.transvection_coe,
    coe_weylElement]
  have hw : weylScalar i t ((Equiv.swap i.castSucc i.succ).symm s) ≠ 0 := by
    simp only [weylScalar]
    split_ifs <;> simp [t.ne_zero]
  have key := monomialMat_mul_transvection (Equiv.swap i.castSucc i.succ) (weylScalar i t) r s u hw
  simp only [Equiv.symm_swap] at key
  rw [← transvection, key, weylScalar_ratio i t hrs u]
  rfl

section RankOne

variable (i : Fin m)

@[expose] def pairEquiv : Fin 2 ≃ {a : Fin (m + 1) // a = i.castSucc ∨ a = i.succ} :=
  Equiv.ofBijective (fun p => if p = 0 then ⟨i.castSucc, Or.inl rfl⟩ else ⟨i.succ, Or.inr rfl⟩)
    ⟨fun p q h => by
      fin_cases p <;> fin_cases q <;> simp_all [Subtype.ext_iff, castSucc_ne_succ i,
        Ne.symm (castSucc_ne_succ i)],
     fun ⟨a, ha⟩ => by
      rcases ha with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩⟩

@[expose] def blockEquiv :
    Fin 2 ⊕ {a : Fin (m + 1) // ¬(a = i.castSucc ∨ a = i.succ)} ≃ Fin (m + 1) :=
  (Equiv.sumCongr (pairEquiv i) (Equiv.refl _)).trans (Equiv.sumCompl _)

theorem pairEquiv_zero : (pairEquiv i 0 : Fin (m + 1)) = i.castSucc := rfl

theorem pairEquiv_one : (pairEquiv i 1 : Fin (m + 1)) = i.succ := rfl

theorem blockEquiv_zero : blockEquiv i (Sum.inl 0) = i.castSucc := by
  simp [blockEquiv, pairEquiv_zero]

theorem blockEquiv_one : blockEquiv i (Sum.inl 1) = i.succ := by
  simp [blockEquiv, pairEquiv_one]

theorem blockEquiv_inr (a : {a : Fin (m + 1) // ¬(a = i.castSucc ∨ a = i.succ)}) :
    blockEquiv i (Sum.inr a) = a := by
  simp [blockEquiv]

@[expose] def blockMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.reindexAlgEquiv F F (blockEquiv i) (Matrix.fromBlocks A 0 0 1)

theorem blockMat_apply (A : Matrix (Fin 2) (Fin 2) F) (p q) :
    blockMat i A (blockEquiv i p) (blockEquiv i q) = Matrix.fromBlocks A 0 0 1 p q := by
  simp [blockMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]

theorem blockMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    blockMat i (A * B) = blockMat i A * blockMat i B := by
  rw [blockMat, blockMat, blockMat, ← map_mul, Matrix.fromBlocks_multiply]
  simp

theorem blockMat_one : blockMat i (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [blockMat, Matrix.fromBlocks_one, map_one]

theorem det_blockMat (A : Matrix (Fin 2) (Fin 2) F) : (blockMat i A).det = A.det := by
  rw [blockMat, Matrix.det_reindexAlgEquiv, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMat_injective : Function.Injective (blockMat (F := F) i) := fun A B h => by
  have h' := (Matrix.reindexAlgEquiv F F (blockEquiv i)).injective h
  exact (Matrix.fromBlocks_inj.1 h').1

variable (F) in
@[expose] def blockHom : Matrix.SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin (m + 1)) F
    where
  toFun A := ⟨blockMat i (A : Matrix (Fin 2) (Fin 2) F), by rw [det_blockMat]; exact A.2⟩
  map_one' := Subtype.ext (by
    change blockMat i ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blockMat_one])
  map_mul' A B := Subtype.ext (by
    change blockMat i ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      blockMat i (A : Matrix (Fin 2) (Fin 2) F) * blockMat i (B : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, blockMat_mul])

theorem blockHom_injective : Function.Injective (blockHom F i) := fun _ _ h =>
  Subtype.ext (blockMat_injective i (congrArg Subtype.val h))

omit [Field F] in
theorem ext_blockEquiv {R : Type*} {M N : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (h : ∀ p q, M (blockEquiv i p) (blockEquiv i q) = N (blockEquiv i p) (blockEquiv i q)) :
    M = N := by
  ext a b
  obtain ⟨p, rfl⟩ := (blockEquiv i).surjective a
  obtain ⟨q, rfl⟩ := (blockEquiv i).surjective b
  exact h p q

theorem blockMat_transvection_upper (c : F) :
    blockMat i (!![1, c; 0, 1]) = transvection i.castSucc i.succ c := by
  have hne := castSucc_ne_succ i
  refine ext_blockEquiv i fun p q => ?_
  rw [blockMat_apply]
  rcases p with p | ⟨a, ha⟩ <;> rcases q with q | ⟨b, hb⟩
  · fin_cases p <;> fin_cases q <;>
      simp [blockEquiv_zero, blockEquiv_one, transvection, hne, Ne.symm hne]
  · push Not at hb
    fin_cases p <;>
      simp [blockEquiv_zero, blockEquiv_one, blockEquiv_inr, transvection, Ne.symm hb.1,
        Ne.symm hb.2]
  · push Not at ha
    fin_cases q <;>
      simp [blockEquiv_zero, blockEquiv_one, blockEquiv_inr, transvection, ha.1, ha.2,
        Ne.symm ha.1]
  · push Not at ha
    simp [blockEquiv_inr, transvection, Matrix.one_apply, Ne.symm ha.1,
      Matrix.fromBlocks_apply₂₂, Subtype.ext_iff]

theorem blockMat_transvection_lower (c : F) :
    blockMat i (!![1, 0; c, 1]) = transvection i.succ i.castSucc c := by
  have hne := castSucc_ne_succ i
  refine ext_blockEquiv i fun p q => ?_
  rw [blockMat_apply]
  rcases p with p | ⟨a, ha⟩ <;> rcases q with q | ⟨b, hb⟩
  · fin_cases p <;> fin_cases q <;>
      simp [blockEquiv_zero, blockEquiv_one, transvection, hne, Ne.symm hne]
  · push Not at hb
    fin_cases p <;>
      simp [blockEquiv_zero, blockEquiv_one, blockEquiv_inr, transvection, Ne.symm hb.1,
        Ne.symm hb.2]
  · push Not at ha
    fin_cases q <;>
      simp [blockEquiv_zero, blockEquiv_one, blockEquiv_inr, transvection, ha.1, ha.2,
        Ne.symm ha.2]
  · push Not at ha
    simp [blockEquiv_inr, transvection, Matrix.one_apply, Ne.symm ha.2,
      Matrix.fromBlocks_apply₂₂, Subtype.ext_iff]

theorem rankOne :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin (m + 1)) F,
      Function.Injective φ ∧ (∀ c, φ (sl2Upper c) = x m F (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = x m F (-Pi.single i 1) c := by
  have hne := castSucc_ne_succ i
  refine ⟨blockHom F i, blockHom_injective i, fun c => ?_, fun c => ?_⟩
  · rw [x_eq hne (toStd_single m i)]
    exact Subtype.ext (blockMat_transvection_upper i c)
  · rw [x_eq hne.symm (toStd_neg_single i)]
    exact Subtype.ext (blockMat_transvection_lower i c)

end RankOne

section Level

variable {n : ℕ} {R : Type*} [CommRing R] (σ : Fin n → ℤ)

@[expose] def IdBelow (h : ℤ) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ a b, σ b - σ a < h → M a b = (1 : Matrix (Fin n) (Fin n) R) a b

variable {σ}

theorem idBelow_one (h : ℤ) : IdBelow σ h (1 : Matrix (Fin n) (Fin n) R) := fun _ _ _ => rfl

theorem idBelow_transvection {h : ℤ} {r s : Fin n} (hlev : h ≤ σ s - σ r) (c : R) :
    IdBelow σ h (transvection r s c) := by
  intro a b hab
  rw [transvection, Matrix.add_apply, single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    omega
  · rw [add_zero]

theorem IdBelow.apply_eq_zero {h : ℤ} {M : Matrix (Fin n) (Fin n) R} (hM : IdBelow σ h M)
    {a b : Fin n} (hab : a ≠ b) (hlev : σ b - σ a < h) : M a b = 0 := by
  rw [hM a b hlev, Matrix.one_apply_ne hab]

theorem IdBelow.apply_self {h : ℤ} (hh : 0 < h) {M : Matrix (Fin n) (Fin n) R}
    (hM : IdBelow σ h M) (a : Fin n) : M a a = 1 := by
  rw [hM a a (by simpa using hh), Matrix.one_apply_eq]

theorem mul_apply_of_idBelow {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) R}
    (hM : IdBelow σ h M) (hN : IdBelow σ h N) {a b : Fin n} (hab : a ≠ b)
    (hlev : σ b - σ a ≤ h) : (M * N) a b = M a b + N a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM.apply_self hh, hN.apply_self hh, one_mul, mul_one, add_comm]
  · intro c _ hc
    by_cases h1 : σ c - σ a < h
    · rw [hM.apply_eq_zero (Ne.symm hc.1) h1, zero_mul]
    · rw [hN.apply_eq_zero hc.2 (by omega), mul_zero]
  · simp
  · simp

theorem idBelow_mul {h : ℤ} (hh : 0 < h) {M N : Matrix (Fin n) (Fin n) R}
    (hM : IdBelow σ h M) (hN : IdBelow σ h N) : IdBelow σ h (M * N) := by
  intro a b hab
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hM.apply_self hh, one_mul, hN a b hab]
  · intro c _ hca
    by_cases h1 : σ c - σ a < h
    · rw [hM.apply_eq_zero (Ne.symm hca) h1, zero_mul]
    · by_cases hcb : c = b
      · subst hcb
        exact absurd hab (by omega)
      · rw [hN.apply_eq_zero hcb (by omega), mul_zero]
  · simp

theorem idBelow_list_prod {h : ℤ} (hh : 0 < h) :
    ∀ {l : List (Matrix (Fin n) (Fin n) R)}, (∀ M ∈ l, IdBelow σ h M) → IdBelow σ h l.prod
  | [], _ => idBelow_one h
  | M :: l, hl => by
    rw [List.prod_cons]
    exact idBelow_mul hh (hl M (List.mem_cons_self ..))
      (idBelow_list_prod hh fun N hN => hl N (List.mem_cons_of_mem _ hN))

theorem list_prod_apply_of_idBelow {h : ℤ} (hh : 0 < h) {a b : Fin n} (hab : a ≠ b)
    (hlev : σ b - σ a ≤ h) :
    ∀ {l : List (Matrix (Fin n) (Fin n) R)}, (∀ M ∈ l, IdBelow σ h M) →
      l.prod a b = (l.map fun M => M a b).sum
  | [], _ => by simp [Matrix.one_apply_ne hab]
  | M :: l, hl => by
    rw [List.prod_cons, List.map_cons, List.sum_cons,
      mul_apply_of_idBelow hh (hl M (List.mem_cons_self ..))
        (idBelow_list_prod hh fun N hN => hl N (List.mem_cons_of_mem _ hN)) hab hlev,
      list_prod_apply_of_idBelow hh hab hlev fun N hN => hl N (List.mem_cons_of_mem _ hN)]

end Level

section Unique

variable {n : ℕ} {R : Type*} [CommRing R] {σ : Fin n → ℤ}

theorem eq_of_prod_transvection_eq {ι : Type*} (p q : ι → Fin n) :
    ∀ (L : List ι), L.Nodup → (∀ γ ∈ L, ∀ δ ∈ L, p γ = p δ → q γ = q δ → γ = δ) →
      (∀ γ ∈ L, 1 ≤ σ (q γ) - σ (p γ)) →
      L.Pairwise (fun γ δ => σ (q γ) - σ (p γ) ≤ σ (q δ) - σ (p δ)) → ∀ c d : ι → R,
      (L.map fun γ => transvection (p γ) (q γ) (c γ)).prod =
        (L.map fun γ => transvection (p γ) (q γ) (d γ)).prod → ∀ γ ∈ L, c γ = d γ
  | [], _, _, _, _, _, _, _ => by simp
  | γ₀ :: L, hnd, hinj, hlev, hsort, c, d, h => by
    rw [List.pairwise_cons] at hsort
    rw [List.nodup_cons] at hnd
    have h₀ := hlev γ₀ (List.mem_cons_self ..)
    have hpq : p γ₀ ≠ q γ₀ := fun e => by rw [e] at h₀; omega
    have hall : ∀ e : ι → R, ∀ M ∈ ((γ₀ :: L).map fun γ => transvection (p γ) (q γ) (e γ)),
        IdBelow σ (σ (q γ₀) - σ (p γ₀)) M := by
      intro e M hM
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hM
      refine idBelow_transvection ?_ _
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exact le_rfl
      · exact hsort.1 γ hγ
    have hentry : ∀ e : ι → R,
        ((γ₀ :: L).map fun γ => transvection (p γ) (q γ) (e γ)).prod (p γ₀) (q γ₀) = e γ₀ := by
      intro e
      rw [list_prod_apply_of_idBelow (by omega) hpq le_rfl (hall e), List.map_cons,
        List.map_cons, List.sum_cons, List.map_map]
      have hrest : ∀ γ ∈ L, transvection (p γ) (q γ) (e γ) (p γ₀) (q γ₀) = 0 := by
        intro γ hγ
        have hne : ¬ (p γ = p γ₀ ∧ q γ = q γ₀) := fun ⟨e1, e2⟩ =>
          hnd.1 (hinj γ (List.mem_cons_of_mem _ hγ) γ₀ (List.mem_cons_self ..) e1 e2 ▸ hγ)
        rw [transvection, Matrix.add_apply, Matrix.one_apply_ne hpq, single_apply, zero_add,
          ite_eq_right_iff]
        exact fun h' => absurd h' hne
      rw [List.sum_eq_zero fun x hx => by
        obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
        exact hrest γ hγ]
      simp [transvection, Matrix.one_apply_ne hpq]
    have hc : c γ₀ = d γ₀ := by rw [← hentry c, ← hentry d, h]
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact hc
    · refine eq_of_prod_transvection_eq p q L hnd.2
        (fun γ hγ δ hδ => hinj γ (List.mem_cons_of_mem _ hγ) δ (List.mem_cons_of_mem _ hδ))
        (fun γ hγ => hlev γ (List.mem_cons_of_mem _ hγ)) hsort.2 c d ?_ γ hγ
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hc] at h
      have hinv : transvection (p γ₀) (q γ₀) (-d γ₀) * transvection (p γ₀) (q γ₀) (d γ₀) = 1 := by
        rw [transvection_mul_transvection_same _ _ hpq, neg_add_cancel, transvection_zero]
      calc (L.map fun γ => transvection (p γ) (q γ) (c γ)).prod
          = transvection (p γ₀) (q γ₀) (-d γ₀) * (transvection (p γ₀) (q γ₀) (d γ₀) *
              (L.map fun γ => transvection (p γ) (q γ) (c γ)).prod) := by
            rw [← mul_assoc, hinv, one_mul]
        _ = (L.map fun γ => transvection (p γ) (q γ) (d γ)).prod := by
            rw [h, ← mul_assoc, hinv, one_mul]

end Unique

private theorem addMonoidHom_ext_single {f g : (Fin m → ℤ) →+ ℤ}
    (h : ∀ l, f (Pi.single l 1) = g (Pi.single l 1)) : f = g := by
  refine AddMonoidHom.functions_ext _ f g fun l c => ?_
  have hx : (Pi.single l c : Fin m → ℤ) = c • Pi.single l 1 := by
    ext j
    by_cases hj : j = l
    · subst hj
      simp
    · simp [hj]
  rw [hx, map_zsmul, map_zsmul, h l]

@[expose] def levelOf (f : (Fin m → ℤ) →+ ℤ) (a : Fin (m + 1)) : ℤ :=
  ∑ b : Fin m, if (b : ℕ) < a then f (Pi.single b 1) else 0

theorem apply_eq_levelOf (f : (Fin m → ℤ) →+ ℤ) (v : Fin m → ℤ) :
    f v = ∑ a : Fin (m + 1), -levelOf f a * toStd m v a := by
  let g : (Fin m → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ a : Fin (m + 1), -levelOf f a * toStd m v a
      map_zero' := by simp [toStd_zero]
      map_add' := fun v w => by simp [toStd_add, mul_add, Finset.sum_add_distrib] }
  have hfg : f = g := addMonoidHom_ext_single fun b => by
    change f (Pi.single b 1) = ∑ a : Fin (m + 1), -levelOf f a * toStd m (Pi.single b 1) a
    rw [toStd_single]
    simp only [Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, levelOf]
    rw [neg_sub_neg, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hcb
      simp only [Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> first | (exfalso; apply hcb; ext; omega) | simp
    · simp
  exact DFunLike.congr_fun hfg v

theorem apply_eq_level (f : (Fin m → ℤ) →+ ℤ) {γ : Fin m → ℤ}
    (hγ : γ ∈ roots (isFiniteType_A m) ∅) :
    f γ = levelOf f (pairOf m γ).2 - levelOf f (pairOf m γ).1 := by
  rw [apply_eq_levelOf, (pairOf_spec hγ).2]
  simp only [Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

theorem prodInjective (f : (Fin m → ℤ) →+ ℤ) (L : List (Fin m → ℤ)) (hL : L.Nodup)
    (hpos : ∀ γ ∈ L, γ ∈ roots (isFiniteType_A m) ∅ ∧ 0 < f γ)
    (hsort : L.Pairwise fun γ δ => f γ ≤ f δ) : ProdInjectiveFor (rootGroup m F) L := by
  intro g g' hg hg' hprod
  have hcoef : ∀ e : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F,
      (∀ γ ∈ L, e γ ∈ rootGroup m F γ) → ∃ c : (Fin m → ℤ) → F, ∀ γ ∈ L,
        (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
          transvection (pairOf m γ).1 (pairOf m γ).2 (c γ) := by
    intro e he
    have : ∀ γ, ∃ c : F, γ ∈ L → (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        transvection (pairOf m γ).1 (pairOf m γ).2 c := by
      intro γ
      by_cases hγ : γ ∈ L
      · obtain ⟨hij, hst⟩ := pairOf_spec (hpos γ hγ).1
        have hmem := he γ hγ
        rw [rootGroup_eq m F hij hst, mem_rootSubgroup] at hmem
        obtain ⟨c, hc⟩ := hmem
        exact ⟨c, fun _ => by rw [← hc, SpecialLinearGroup.transvection_coe]; rfl⟩
      · exact ⟨0, fun h => absurd h hγ⟩
    choose c hc using this
    exact ⟨c, fun γ hγ => hc γ hγ⟩
  obtain ⟨c, hc⟩ := hcoef g hg
  obtain ⟨d, hd⟩ := hcoef g' hg'
  have hcoe : ∀ (e : (Fin m → ℤ) → SpecialLinearGroup (Fin (m + 1)) F) (c' : (Fin m → ℤ) → F),
      (∀ γ ∈ L, (e γ : Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        transvection (pairOf m γ).1 (pairOf m γ).2 (c' γ)) →
      (((L.map e).prod : SpecialLinearGroup (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) =
        (L.map fun γ => transvection (pairOf m γ).1 (pairOf m γ).2 (c' γ)).prod := by
    intro e c' he
    rw [← SpecialLinearGroup.coeMonoidHom_apply, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun γ hγ => he γ hγ)
  have hmat := (hcoe g c hc).symm.trans ((congrArg _ hprod).trans (hcoe g' d hd))
  have hcd := eq_of_prod_transvection_eq (σ := levelOf f) (fun γ => (pairOf m γ).1)
    (fun γ => (pairOf m γ).2) L hL
    (fun γ hγ δ hδ h1 h2 => toStd_injective m (by
      rw [(pairOf_spec (hpos γ hγ).1).2, (pairOf_spec (hpos δ hδ).1).2, h1, h2]))
    (fun γ hγ => by
      have := (hpos γ hγ).2
      rw [apply_eq_level f (hpos γ hγ).1] at this
      omega)
    (hsort.imp_of_mem fun {γ δ} hγ hδ h => by
      rwa [apply_eq_level f (hpos γ hγ).1, apply_eq_level f (hpos δ hδ).1] at h)
    c d hmat
  intro γ hγ
  exact Subtype.ext (by rw [hc γ hγ, hd γ hγ, hcd γ hγ])

theorem cast_eq_commC_of_commutatorFormula {O : CommOrder (Φ (m := m) (F := F))}
    {C : (Fin m → ℤ) → (Fin m → ℤ) → ℕ × ℕ → ℤ} (hC : CommutatorFormula (x m F) O C)
    {α β : Fin m → ℤ} (hα : α ∈ roots (isFiniteType_A m) ∅) (hβ : β ∈ roots (isFiniteType_A m) ∅)
    (hαβ : α + β ≠ 0) (hc : Chain α β) : (C α β (1, 1) : F) = (commC α β (1, 1) : F) := by
  have hl : O.list α β = [(1, 1)] :=
    list_eq_singleton (O.nodup α β) fun p =>
      ((O.mem_iff α hα β hβ hαβ p).trans (mem_expPairs_iff hα hβ hαβ p)).trans (and_iff_left hc)
  have h1 := hC α hα β hβ hαβ 1 1
  have h2 := commutatorFormula (m := m) (F := F) O α hα β hβ hαβ 1 1
  rw [hl, List.map_singleton, List.prod_singleton] at h1 h2
  simp only [one_smul, one_pow, mul_one] at h1 h2
  have hroot : α + β ∈ roots (isFiniteType_A m) ∅ := by
    have := ((mem_expPairs_iff (F := F) hα hβ hαβ (1, 1)).2 ⟨rfl, hc⟩).2.2
    rw [one_smul, one_smul] at this
    exact this
  exact ((isParametrization (m := m) (F := F)) _ hroot).2.2 (h1.symm.trans h2)

theorem rankTwo (hm : 2 ≤ m) {O : CommOrder (Φ (m := m) (F := F))}
    {C : (Fin m → ℤ) → (Fin m → ℤ) → ℕ × ℕ → ℤ} (hC : CommutatorFormula (x m F) O C)
    (i : Fin m) :
    ∃ δ ∈ roots (isFiniteType_A m) ∅, ∃ γ ∈ roots (isFiniteType_A m) ∅, δ + γ ≠ 0 ∧
      ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ (Pi.single i 1 : Fin m → ℤ) = δ + j • γ ∧
        IsUnit (C δ γ (1, j) : F) := by
  obtain ⟨l, hl⟩ : ∃ l : Fin m, (l : ℕ) + 1 = i ∨ (i : ℕ) + 1 = l := by
    by_cases h : (i : ℕ) + 1 < m
    · exact ⟨⟨i + 1, h⟩, Or.inr rfl⟩
    · exact ⟨⟨i - 1, by omega⟩, Or.inl (by simp only; omega)⟩
  have hli : l ≠ i := fun e => by subst e; omega
  have hδ : Pi.single i 1 + Pi.single l 1 ∈ roots (isFiniteType_A m) ∅ := by
    rw [roots_eq]
    rcases hl with hl | hl
    · refine ⟨l.castSucc, i.succ, fun e => ?_, ?_⟩
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      · rw [toStd_add, toStd_single, toStd_single,
          show l.succ = i.castSucc from Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        abel
    · refine ⟨i.castSucc, l.succ, fun e => ?_, ?_⟩
      · have := congrArg Fin.val e
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      · rw [toStd_add, toStd_single, toStd_single,
          show i.succ = l.castSucc from Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        abel
  have hγ : -Pi.single l 1 ∈ roots (isFiniteType_A m) ∅ := by
    rw [roots_eq]
    exact ⟨l.succ, l.castSucc, (castSucc_ne_succ l).symm, toStd_neg_single l⟩
  have hsum : (Pi.single i 1 + Pi.single l 1 + -Pi.single l 1 : Fin m → ℤ) = Pi.single i 1 := by
    abel
  have hne : (Pi.single i 1 + Pi.single l 1 + -Pi.single l 1 : Fin m → ℤ) ≠ 0 := by
    rw [hsum]
    intro h
    have := congrFun h i
    simp at this
  have hchain : Chain (Pi.single i 1 + Pi.single l 1) (-Pi.single l 1) := by
    have h1 := (mem_expPairs_iff (F := F) hδ hγ hne (1, 1)).1
    refine (h1 ⟨one_pos, one_pos, ?_⟩).2
    rw [one_smul, one_smul, hsum]
    exact (RootSystem.ofCartan _ _).single_mem i
  refine ⟨_, hδ, _, hγ, hne, 1, Or.inl rfl, by rw [one_smul, hsum], ?_⟩
  rw [cast_eq_commC_of_commutatorFormula hC hδ hγ hne hchain]
  unfold commC
  split_ifs <;> simp

theorem chevalleyExtras (hm : 2 ≤ m) (O : CommOrder (Φ (m := m) (F := F)))
    (C : (Fin m → ℤ) → (Fin m → ℤ) → ℕ × ℕ → ℤ) (hC : CommutatorFormula (x m F) O C) :
    ChevalleyExtras (rootDatum m F) F (x m F) C O where
  param := isParametrization
  comm := hC
  weyl i _ hβ := weyl i hβ
  rankOne i := rankOne i
  prodInjective f L hL hpos hsort := prodInjective f L hL hpos hsort
  rankTwo i := rankTwo hm hC i

theorem presentationB [Finite F] (hm : 2 ≤ m) :
    PresentationB (Φ := Φ (m := m) (F := F)) (x m F) :=
  presentationB_of rfl
    (fun O => ⟨commC (m := m), fun α _ β _ p _ => by
      simp only [Set.mem_insert_iff]
      exact Or.inl (commC_natAbs (m := m) α β p),
      commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras hm O C hC)
    (bijective_stPi_of (isCTGroupDatum m F) (steinbergExtras m F)).2

theorem redundantR2 [Finite F] (hm : 2 ≤ m) :
    RedundantR2 (Φ (m := m) (F := F)) (rootDatum m F).rootGroup :=
  redundantR2_of rfl (fun O => ⟨commC (m := m), commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras hm O C hC)
    (bijective_stPi_of (isCTGroupDatum m F) (steinbergExtras m F)).2

end CFSG.LieType.Steinberg.SL
