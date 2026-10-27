module

public import CFSG.LieType.Universal.Symplectic
public import CFSG.LieType.RootSystem.Cartan
public import CFSG.LieType.CurtisTits.Reduction
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Weyl
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import CFSG.ClassicalGroups.Symplectic.Model
import CFSG.LieType.Universal.SymplecticRoots.Weyl
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

public section

namespace CFSG.LieType.Universal.Symplectic

open Matrix CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin

@[expose] def cartanC (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
  if i = j then 2
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then
    (if i.val + 2 = n ∧ j.val + 1 = n then -2 else -1)
  else 0

theorem isFiniteType_cartanC (n : ℕ) : TauCeti.IsFiniteType (cartanC n) := by
  have h : cartanC n = CartanMatrix.B n := by
    ext i j
    simp only [cartanC, CartanMatrix.B, Matrix.of_apply]
    split_ifs <;> omega
  rw [h]
  exact TauCeti.isFiniteType_cartanMatrix_B n

@[expose] def toStd (n : ℕ) (v : Fin n → ℤ) : Fin n → ℤ := fun a =>
  (if a.val + 1 = n then 2 else 1) * v a -
    (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0)

@[expose] def stdVec {n : ℕ} : RootSubgroupIndex n → Fin n → ℤ
  | .positiveLong i => 2 • Pi.single i 1
  | .negativeLong i => -(2 • Pi.single i 1)
  | .difference i j _ => Pi.single i 1 - Pi.single j 1
  | .positiveSum i j _ => Pi.single i 1 + Pi.single j 1
  | .negativeSum i j _ => -(Pi.single i 1 + Pi.single j 1)

variable (n : ℕ) (F : Type) [Field F]

noncomputable def equivStatedSp : TauCeti.GLSymplecticFin n F ≃* StatedSp n F :=
  (mulEquivGLSymplectic n F).trans (MulEquiv.subgroupCongr
    (CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := F)).symm)

@[expose] noncomputable def rootGroup (γ : Fin n → ℤ) : Subgroup (StatedSp n F) :=
  ⨆ (r : RootSubgroupIndex n) (_ : stdVec r = toStd n γ),
    (r.hom (R := F)).range.map (equivStatedSp n F).toMonoidHom

@[expose] noncomputable def weylRep (k : Fin n) : StatedSp n F :=
  equivStatedSp n F
    (if h : k.val + 1 < n then
      differenceShortRootWeylElement (R := F) (i := k) (j := ⟨k.val + 1, h⟩)
        (Fin.ne_of_val_ne (by simp))
    else positiveLongRootWeylElement k)

@[expose] def corootVec (k : Fin n) (c : Fˣ) : Fin n → Fˣ := fun a =>
  if a = k then c else if a.val = k.val + 1 then c⁻¹ else 1

@[expose] noncomputable def torus (k : Fin n) : Subgroup (StatedSp n F) :=
  (Subgroup.closure (Set.range fun c : Fˣ => diagonal (R := F) (corootVec n F k c))).map
    (equivStatedSp n F).toMonoidHom

private def toStdLin : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := toStd n
  map_add' v w := by
    funext a
    simp only [toStd, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [toStd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem toStdLin_apply (v : Fin n → ℤ) : toStdLin n v = toStd n v := rfl

private theorem toStd_neg (v : Fin n → ℤ) : toStd n (-v) = -toStd n v :=
  map_neg (toStdLin n) v

private theorem toStd_smul (c : ℤ) (v : Fin n → ℤ) : toStd n (c • v) = c • toStd n v :=
  map_zsmul (toStdLin n) c v

private theorem toStd_single_of_lt {k : Fin n} (h : k.val + 1 < n) :
    toStd n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  simp only [toStd, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem toStd_single_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) :
    toStd n (Pi.single k 1) = 2 • Pi.single k 1 := by
  funext a
  simp only [toStd, Pi.smul_apply, Pi.single_apply, Fin.ext_iff, nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs <;> omega

private theorem toStd_apply_eq (v : Fin n → ℤ) (k : Fin n) :
    toStd n v k = (if k.val + 1 = n then 2 else 1) * v k -
      (if h : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0) := rfl

private theorem toStd_injective : Function.Injective (toStd n) := by
  intro v w h
  have hc : ∀ k : Fin n, (if k.val + 1 = n then (2 : ℤ) else 1) ≠ 0 := fun k => by
    split_ifs <;> norm_num
  have key : ∀ d (k : Fin n), k.val = d → v k = w k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have := congrFun h k
      rw [toStd_apply_eq, toStd_apply_eq, dite_eq_right (by omega),
        dite_eq_right (by omega)] at this
      exact mul_left_cancel₀ (hc k) (by linarith)
    | succ d ih =>
      intro k hk
      have := congrFun h k
      rw [toStd_apply_eq, toStd_apply_eq, dite_eq_left (by omega), dite_eq_left (by omega),
        ih ⟨k.val - 1, by omega⟩ (by simp only; omega)] at this
      exact mul_left_cancel₀ (hc k) (by linarith)
  funext k
  exact key k.val k rfl

private def stdRefl (k : Fin n) (e : Fin n → ℤ) : Fin n → ℤ :=
  if h : k.val + 1 < n then e ∘ Equiv.swap k ⟨k.val + 1, h⟩
  else fun a => (if a = k then -1 else 1) * e a

private theorem stdRefl_of_lt {k : Fin n} (h : k.val + 1 < n) (e : Fin n → ℤ) :
    stdRefl n k e = e ∘ Equiv.swap k ⟨k.val + 1, h⟩ := dite_eq_left h

private theorem stdRefl_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (e : Fin n → ℤ) :
    stdRefl n k e = fun a => (if a = k then -1 else 1) * e a := dite_eq_right h

private theorem toStd_sub (v w : Fin n → ℤ) : toStd n (v - w) = toStd n v - toStd n w :=
  map_sub (toStdLin n) v w

private theorem coroot_cartanC_of_lt {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanC n) k v = toStd n v k - toStd n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartanC n) k =
      ((LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ) - LinearMap.proj (⟨k.val + 1, h⟩ : Fin n)).comp
        (toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdLin_apply, toStd, cartanC, Matrix.of_apply,
      Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem coroot_cartanC_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanC n) k v = toStd n v k := by
  have key : coroot (cartanC n) k = (LinearMap.proj k).comp (toStdLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.coe_single, coroot_single,
      toStdLin_apply, toStd, cartanC, Matrix.of_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

private theorem toStd_reflection (k : Fin n) (v : Fin n → ℤ) :
    toStd n (reflection (cartanC n) k v) = stdRefl n k (toStd n v) := by
  rw [reflection_apply_coroot, toStd_sub, toStd_smul]
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanC_of_lt n h, toStd_single_of_lt n h, stdRefl_of_lt n h]
    have hne : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · rw [coroot_cartanC_of_not_lt n h, toStd_single_of_not_lt n h, stdRefl_of_not_lt n h]
    funext a
    by_cases ha : a = k
    · subst ha
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, ite_true]
      ring
    · simp [ha]

private theorem stdRefl_of_succ {k k' : Fin n} (h : k.val + 1 = k'.val) (e : Fin n → ℤ) :
    stdRefl n k e = e ∘ Equiv.swap k k' := by
  rw [stdRefl_of_lt n (by omega)]
  congr 3
  exact Fin.ext h

private theorem single_comp_swap (a p q : Fin n) (x : ℤ) :
    Pi.single a x ∘ Equiv.swap p q = Pi.single (Equiv.swap p q a) x := by
  rw [Pi.single_comp_equiv, Equiv.symm_swap]

private theorem mul_single (f : Fin n → ℤ) (a : Fin n) (x : ℤ) :
    (fun b => f b * (Pi.single a x : Fin n → ℤ) b) = Pi.single a (f a * x) := by
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [hb]

private def IsStdRoot (e : Fin n → ℤ) : Prop :=
  ∃ (a b : Fin n) (s t : ℤ), (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧ (a = b → s = t) ∧
    e = Pi.single a s + Pi.single b t

private theorem isStdRoot_toStd_single (k : Fin n) : IsStdRoot n (toStd n (Pi.single k 1)) := by
  by_cases h : k.val + 1 < n
  · refine ⟨k, ⟨k.val + 1, h⟩, 1, -1, Or.inl rfl, Or.inr rfl, fun e => ?_, ?_⟩
    · exact absurd (congrArg Fin.val e) (by simp)
    · rw [toStd_single_of_lt n h, sub_eq_add_neg, Pi.single_neg]
  · exact ⟨k, k, 1, 1, Or.inl rfl, Or.inl rfl, fun _ => rfl,
      by rw [toStd_single_of_not_lt n h, two_nsmul]⟩

private theorem isStdRoot_stdRefl (k : Fin n) {e : Fin n → ℤ} (he : IsStdRoot n e) :
    IsStdRoot n (stdRefl n k e) := by
  obtain ⟨a, b, s, t, hs, ht, hst, rfl⟩ := he
  by_cases h : k.val + 1 < n
  · rw [stdRefl_of_lt n h]
    refine ⟨Equiv.swap k ⟨k.val + 1, h⟩ a, Equiv.swap k ⟨k.val + 1, h⟩ b, s, t, hs, ht,
      fun e => hst ((Equiv.swap _ _).injective e), ?_⟩
    rw [Pi.add_comp, single_comp_swap, single_comp_swap]
  · rw [stdRefl_of_not_lt n h]
    have hsgn : ∀ (c : Fin n) (u : ℤ), (u = 1 ∨ u = -1) →
        ((if c = k then -1 else 1) * u = 1 ∨ (if c = k then -1 else 1) * u = -1) := by
      intro c u hu
      split_ifs <;> rcases hu with rfl | rfl <;> simp
    refine ⟨a, b, (if a = k then -1 else 1) * s, (if b = k then -1 else 1) * t, hsgn a s hs,
      hsgn b t ht, fun e => by subst e; rw [hst rfl], ?_⟩
    funext x
    simp only [Pi.add_apply, mul_add]
    congr 1
    · exact congrFun (mul_single n (fun c => if c = k then -1 else 1) a s) x
    · exact congrFun (mul_single n (fun c => if c = k then -1 else 1) b t) x

private theorem isStdRoot_toStd_weylAction (w : (coxeterMatrix (isFiniteType_cartanC n)).Group)
    (k : Fin n) :
    IsStdRoot n (toStd n (weylAction (isFiniteType_cartanC n) w (Pi.single k 1))) := by
  induction w using (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple_induction_left
    with
  | one => simpa using isStdRoot_toStd_single n k
  | mul_simple_left w l ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]
    exact isStdRoot_stdRefl n l ih

private theorem exists_stdVec_of_isStdRoot {e : Fin n → ℤ} (he : IsStdRoot n e) :
    ∃ r : RootSubgroupIndex n, stdVec r = e := by
  obtain ⟨a, b, s, t, hs, ht, hst, rfl⟩ := he
  by_cases hab : a = b
  · subst hab
    obtain rfl := hst rfl
    rcases hs with rfl | rfl
    · exact ⟨.positiveLong a, by simp only [stdVec, two_nsmul]⟩
    · exact ⟨.negativeLong a, by simp only [stdVec, two_nsmul, Pi.single_neg, neg_add]⟩
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨.positiveSum a b h, rfl⟩
      · exact ⟨.positiveSum b a h, add_comm _ _⟩
    · exact ⟨.difference a b hab, by rw [stdVec, sub_eq_add_neg, Pi.single_neg]⟩
    · exact ⟨.difference b a (Ne.symm hab), by
        rw [stdVec, sub_eq_add_neg, Pi.single_neg, add_comm]⟩
    · rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨.negativeSum a b h, by rw [stdVec, Pi.single_neg, Pi.single_neg, neg_add]⟩
      · exact ⟨.negativeSum b a h, by
          rw [stdVec, Pi.single_neg, Pi.single_neg, neg_add, add_comm]⟩

private def IsStdOrbit (e : Fin n → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartanC n)).Group) (k : Fin n),
    toStd n (weylAction (isFiniteType_cartanC n) w (Pi.single k 1)) = e

private theorem isStdOrbit_toStd_single (k : Fin n) : IsStdOrbit n (toStd n (Pi.single k 1)) :=
  ⟨1, k, by rw [map_one, Module.End.one_apply]⟩

private theorem IsStdOrbit.neg {e : Fin n → ℤ} (he : IsStdOrbit n e) : IsStdOrbit n (-e) := by
  obtain ⟨w, k, rfl⟩ := he
  refine ⟨w * (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple k, k, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStd_neg]

private theorem IsStdOrbit.stdRefl {e : Fin n → ℤ} (he : IsStdOrbit n e) (k : Fin n) :
    IsStdOrbit n (stdRefl n k e) := by
  obtain ⟨w, l, rfl⟩ := he
  refine ⟨(coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple k * w, l, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple, toStd_reflection]

private theorem isStdOrbit_difference (d : ℕ) :
    ∀ i j : Fin n, j.val = i.val + 1 + d → IsStdOrbit n (Pi.single i 1 - Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij
    have h : i.val + 1 < n := by omega
    have e : (⟨i.val + 1, h⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simpa [toStd_single_of_lt n h, e] using isStdOrbit_toStd_single n i
  | succ d ih =>
    intro i j hij
    have hj' : i.val + 1 + d < n := by omega
    have h := (ih i ⟨i.val + 1 + d, hj'⟩ rfl).stdRefl n ⟨i.val + 1 + d, hj'⟩
    rw [stdRefl_of_succ n (k' := j) (by simp only; omega), Pi.sub_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp only; omega))
        (Fin.ne_of_val_ne (by omega))] at h
    exact h

private theorem isStdOrbit_positiveSum (d : ℕ) :
    ∀ i j : Fin n, i < j → j.val + d + 1 = n →
      IsStdOrbit n (Pi.single i 1 + Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij hj
    have h := (isStdOrbit_difference n (j.val - i.val - 1) i j (by
      have : i.val < j.val := hij
      omega)).stdRefl n j
    rw [stdRefl_of_not_lt n (by omega)] at h
    convert h using 1
    have hij' : i ≠ j := hij.ne
    funext x
    by_cases hx : x = j
    · subst hx
      simp [hij'.symm]
    · by_cases hx' : x = i
      · subst hx'
        simp [hij']
      · simp [hx, hx']
  | succ d ih =>
    intro i j hij hj
    have hj' : j.val + 1 < n := by omega
    have h := (ih i ⟨j.val + 1, hj'⟩ (by
      change i.val < j.val + 1
      have : i.val < j.val := hij
      omega) (by simp only; omega)).stdRefl n j
    rw [stdRefl_of_succ n (k' := ⟨j.val + 1, hj'⟩) rfl, Pi.add_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij.ne (Fin.ne_of_val_ne (by
        have : i.val < j.val := hij
        simp only
        omega))] at h
    exact h

private theorem isStdOrbit_positiveLong (d : ℕ) :
    ∀ a : Fin n, a.val + d + 1 = n → IsStdOrbit n (2 • Pi.single a 1) := by
  induction d with
  | zero =>
    intro a ha
    simpa [toStd_single_of_not_lt n (show ¬a.val + 1 < n by omega)] using
      isStdOrbit_toStd_single n a
  | succ d ih =>
    intro a ha
    have ha' : a.val + 1 < n := by omega
    have h := (ih ⟨a.val + 1, ha'⟩ (by simp only; omega)).stdRefl n a
    rw [stdRefl_of_succ n (k' := ⟨a.val + 1, ha'⟩) rfl, Pi.smul_comp, single_comp_swap,
      Equiv.swap_apply_right] at h
    exact h

private theorem isStdOrbit_stdVec (r : RootSubgroupIndex n) : IsStdOrbit n (stdVec r) := by
  cases r with
  | positiveLong a => exact isStdOrbit_positiveLong n (n - 1 - a.val) a (by omega)
  | negativeLong a => exact (isStdOrbit_positiveLong n (n - 1 - a.val) a (by omega)).neg n
  | difference i j hij =>
    rcases lt_or_gt_of_ne hij with h | h
    · exact isStdOrbit_difference n (j.val - i.val - 1) i j (by
        have : i.val < j.val := h
        omega)
    · have := (isStdOrbit_difference n (i.val - j.val - 1) j i (by
        have : j.val < i.val := h
        omega)).neg n
      rwa [neg_sub] at this
  | positiveSum i j hij => exact isStdOrbit_positiveSum n (n - 1 - j.val) i j hij (by omega)
  | negativeSum i j hij =>
    exact (isStdOrbit_positiveSum n (n - 1 - j.val) i j hij (by omega)).neg n

theorem roots_eq : roots (isFiniteType_cartanC n) ∅ =
    {γ | ∃ r : RootSubgroupIndex n, stdVec r = toStd n γ} := by
  ext γ
  constructor
  · rintro (⟨w, k, rfl⟩ | ⟨w, k, hk, -⟩)
    · exact exists_stdVec_of_isStdRoot n (isStdRoot_toStd_weylAction n w k)
    · exact absurd hk (Set.notMem_empty k)
  · rintro ⟨r, hr⟩
    obtain ⟨w, k, hw⟩ := isStdOrbit_stdVec n r
    exact Or.inl ⟨w, k, toStd_injective n (hr.symm.trans hw.symm)⟩

private theorem mem_rootGroup {γ : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n γ) (c : Multiplicative F) :
    equivStatedSp n F (r.hom c) ∈ rootGroup n F γ :=
  (le_iSup₂_of_le (f := fun (r : RootSubgroupIndex n) (_ : stdVec r = toStd n γ) =>
    (r.hom (R := F)).range.map (equivStatedSp n F).toMonoidHom) r hr le_rfl)
      (Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨c, rfl⟩))

private theorem rootGroup_le {γ : Fin n → ℤ} {P : Subgroup (StatedSp n F)}
    (h : ∀ r : RootSubgroupIndex n, stdVec r = toStd n γ → ∀ c : Multiplicative F,
      equivStatedSp n F (r.hom c) ∈ P) :
    rootGroup n F γ ≤ P := by
  refine iSup₂_le fun r hr => ?_
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  exact h r hr c

private theorem positiveLong_mem {γ : Fin n → ℤ} {a : Fin n}
    (h : 2 • Pi.single a 1 = toStd n γ) (c : F) :
    equivStatedSp n F (positiveLongRootTransvectionUnit a c) ∈ rootGroup n F γ := by
  simpa using mem_rootGroup n F (r := .positiveLong a) h (Multiplicative.ofAdd c)

private theorem negativeLong_mem {γ : Fin n → ℤ} {a : Fin n}
    (h : -(2 • Pi.single a 1) = toStd n γ) (c : F) :
    equivStatedSp n F (negativeLongRootTransvectionUnit a c) ∈ rootGroup n F γ := by
  simpa using mem_rootGroup n F (r := .negativeLong a) h (Multiplicative.ofAdd c)

private theorem difference_mem {γ : Fin n → ℤ} {a b : Fin n} (hab : a ≠ b)
    (h : Pi.single a 1 - Pi.single b 1 = toStd n γ) (c : F) :
    equivStatedSp n F (differenceShortRootUnit hab c) ∈ rootGroup n F γ := by
  simpa using mem_rootGroup n F (r := .difference a b hab) h (Multiplicative.ofAdd c)

private theorem stdVec_short_positiveSum {a b : Fin n} (hab : a ≠ b) :
    stdVec (RootSubgroupIndex.short ShortRootFamily.positiveSum a b hab) =
      Pi.single a 1 + Pi.single b 1 := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [RootSubgroupIndex.short_positiveSum_of_lt a b h]
    rfl
  · rw [RootSubgroupIndex.short_positiveSum_swap, RootSubgroupIndex.short_positiveSum_of_lt b a h,
      stdVec, add_comm]

private theorem stdVec_short_negativeSum {a b : Fin n} (hab : a ≠ b) :
    stdVec (RootSubgroupIndex.short ShortRootFamily.negativeSum a b hab) =
      -(Pi.single a 1 + Pi.single b 1) := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [RootSubgroupIndex.short_negativeSum_of_lt a b h]
    rfl
  · rw [RootSubgroupIndex.short_negativeSum_swap, RootSubgroupIndex.short_negativeSum_of_lt b a h,
      stdVec, add_comm]

private theorem ne_succ {k : Fin n} (h : k.val + 1 < n) : k ≠ ⟨k.val + 1, h⟩ :=
  Fin.ne_of_val_ne (by simp)

private noncomputable def weylElt (k : Fin n) : TauCeti.GLSymplecticFin n F :=
  if h : k.val + 1 < n then differenceShortRootWeylElement (ne_succ n h)
  else positiveLongRootWeylElement k

private theorem weylRep_eq (k : Fin n) : weylRep n F k = equivStatedSp n F (weylElt n F k) :=
  rfl

private theorem weylElt_of_lt {k : Fin n} (h : k.val + 1 < n) :
    weylElt n F k = differenceShortRootWeylElement (ne_succ n h) :=
  dite_eq_left h

private theorem weylElt_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) :
    weylElt n F k = positiveLongRootWeylElement k :=
  dite_eq_right h

private theorem weylRep_mem_rankOne (k : Fin n) :
    weylRep n F k ∈ CurtisTits.rankOne (rootGroup n F) k := by
  rw [weylRep_eq]
  change weylElt n F k ∈ (CurtisTits.rankOne (rootGroup n F) k).comap
    (equivStatedSp n F).toMonoidHom
  by_cases h : k.val + 1 < n
  · rw [weylElt_of_lt n F h]
    apply differenceShortRootWeylElement_mem
    · exact Subgroup.mem_sup_left (difference_mem n F _ (toStd_single_of_lt n h).symm 1)
    · refine Subgroup.mem_sup_right (difference_mem n F _ ?_ (-1))
      rw [toStd_neg, toStd_single_of_lt n h, neg_sub]
  · rw [weylElt_of_not_lt n F h]
    apply positiveLongRootWeylElement_mem
    · exact Subgroup.mem_sup_left (positiveLong_mem n F (toStd_single_of_not_lt n h).symm 1)
    · refine Subgroup.mem_sup_right (negativeLong_mem n F ?_ (-1))
      rw [toStd_neg, toStd_single_of_not_lt n h]

private theorem weylElt_conj (k : Fin n) (r : RootSubgroupIndex n) (c : Multiplicative F) :
    ∃ (r' : RootSubgroupIndex n) (c' : Multiplicative F),
      weylElt n F k * r.hom c * (weylElt n F k)⁻¹ = r'.hom c' ∧
        stdVec r' = stdRefl n k (stdVec r) := by
  by_cases h : k.val + 1 < n
  · rw [weylElt_of_lt n F h, stdRefl_of_lt n h]
    have hk := ne_succ n h
    cases r with
    | positiveLong a =>
      refine ⟨.positiveLong (Equiv.swap k ⟨k.val + 1, h⟩ a), c, ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply]
        exact shortWeyl_conj_positiveLong hk a _
      · simp only [stdVec]
        rw [Pi.smul_comp, single_comp_swap]
    | negativeLong a =>
      refine ⟨.negativeLong (Equiv.swap k ⟨k.val + 1, h⟩ a), c, ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply]
        exact shortWeyl_conj_negativeLong hk a _
      · simp only [stdVec]
        rw [Pi.neg_comp, Pi.smul_comp, single_comp_swap]
    | difference a b hab =>
      refine ⟨.difference _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab),
        Multiplicative.ofAdd ((if a = k then -1 else 1) * (if b = k then -1 else 1) *
          Multiplicative.toAdd c), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply, toAdd_ofAdd]
        exact shortWeyl_conj_difference hk hab _
      · simp only [stdVec]
        rw [Pi.sub_comp, single_comp_swap, single_comp_swap]
    | positiveSum a b hab =>
      refine ⟨.short .positiveSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne),
        Multiplicative.ofAdd ((if a = k then -1 else 1) * (if b = k then -1 else 1) *
          Multiplicative.toAdd c), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_positiveSum,
          positiveSumShortRootHom_apply, RootSubgroupIndex.hom_positiveSum, toAdd_ofAdd]
        exact shortWeyl_conj_positiveSum hk hab.ne _
      · rw [stdVec_short_positiveSum]
        simp only [stdVec]
        rw [Pi.add_comp, single_comp_swap, single_comp_swap]
    | negativeSum a b hab =>
      refine ⟨.short .negativeSum _ _ ((Equiv.swap k ⟨k.val + 1, h⟩).injective.ne hab.ne),
        Multiplicative.ofAdd ((if a = k then -1 else 1) * (if b = k then -1 else 1) *
          Multiplicative.toAdd c), ?_, ?_⟩
      · simp only [RootSubgroupIndex.hom_short, ShortRootFamily.hom_negativeSum,
          negativeSumShortRootHom_apply, RootSubgroupIndex.hom_negativeSum, toAdd_ofAdd]
        exact shortWeyl_conj_negativeSum hk hab.ne _
      · rw [stdVec_short_negativeSum]
        simp only [stdVec]
        rw [Pi.neg_comp, Pi.add_comp, single_comp_swap, single_comp_swap]
  · rw [weylElt_of_not_lt n F h, stdRefl_of_not_lt n h]
    have hmax : ∀ a : Fin n, a ≠ k → a.val < k.val := fun a ha => by
      have := Fin.val_ne_of_ne ha
      omega
    cases r with
    | positiveLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.negativeLong k, Multiplicative.ofAdd (-Multiplicative.toAdd c), ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv]
          exact positiveLongRootWeylElement_mul_positiveLongRootTransvectionUnit_mul_inv k _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
      · refine ⟨.positiveLong a, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, positiveLongRootTransvectionHom_apply]
          exact longWeyl_conj_positiveLong_of_ne ha.symm _
        · funext x
          simp only [stdVec, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
    | negativeLong a =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.positiveLong k, Multiplicative.ofAdd (-Multiplicative.toAdd c), ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveLong, RootSubgroupIndex.hom_negativeLong,
            positiveLongRootTransvectionHom_apply, negativeLongRootTransvectionHom_apply,
            toAdd_ofAdd]
          rw [positiveLongRootWeylElement_inv]
          exact positiveLongRootWeylElement_mul_negativeLongRootTransvectionUnit_mul_inv k _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
      · refine ⟨.negativeLong a, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_negativeLong, negativeLongRootTransvectionHom_apply]
          exact longWeyl_conj_negativeLong_of_ne ha.symm _
        · funext x
          simp only [stdVec, Pi.neg_apply, nsmul_eq_mul]
          split_ifs <;> simp_all
    | difference a b hab =>
      rcases eq_or_ne k a with rfl | ha
      · refine ⟨.short .negativeSum k b hab, Multiplicative.ofAdd (-Multiplicative.toAdd c), ?_,
          ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_negativeSum, differenceShortRootHom_apply,
            negativeSumShortRootHom_apply, toAdd_ofAdd]
          exact longWeyl_conj_difference_left hab _
        · rw [stdVec_short_negativeSum]
          funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.short .positiveSum a k hab, Multiplicative.ofAdd (-Multiplicative.toAdd c), ?_,
          ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_short,
            ShortRootFamily.hom_positiveSum, differenceShortRootHom_apply,
            positiveSumShortRootHom_apply, toAdd_ofAdd]
          exact longWeyl_conj_difference_right hab _
        · rw [stdVec_short_positiveSum]
          funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.difference a b hab, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply]
          exact longWeyl_conj_difference_of_ne hab ha.symm hb.symm _
        · funext x
          simp only [stdVec, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
    | positiveSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference a k hab.ne, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_positiveSum,
            differenceShortRootHom_apply, positiveSumShortRootHom_apply]
          exact longWeyl_conj_positiveSum_right hab.ne _
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.positiveSum a b hab, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_positiveSum, positiveSumShortRootHom_apply]
          exact longWeyl_conj_positiveSum_of_ne hab.ne ha hb.symm _
        · funext x
          simp only [stdVec, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all
    | negativeSum a b hab =>
      have ha : a ≠ k := fun e => by
        have := hmax b (fun e' => by subst e e'; exact lt_irrefl _ hab)
        have : a.val < b.val := hab
        omega
      rcases eq_or_ne k b with rfl | hb
      · refine ⟨.difference k a hab.ne.symm, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_difference, RootSubgroupIndex.hom_negativeSum,
            differenceShortRootHom_apply, negativeSumShortRootHom_apply]
          exact longWeyl_conj_negativeSum_right hab.ne _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
          split_ifs <;> simp_all
      · refine ⟨.negativeSum a b hab, c, ?_, ?_⟩
        · simp only [RootSubgroupIndex.hom_negativeSum, negativeSumShortRootHom_apply]
          exact longWeyl_conj_negativeSum_of_ne hab.ne ha hb.symm _
        · funext x
          simp only [stdVec, Pi.neg_apply, Pi.add_apply, Pi.single_apply]
          split_ifs <;> simp_all

private theorem weylRep_conj_mem (k : Fin n) (γ : Fin n → ℤ)
    (_ : γ ∈ roots (isFiniteType_cartanC n) ∅) (x : StatedSp n F) (hx : x ∈ rootGroup n F γ) :
    weylRep n F k * x * (weylRep n F k)⁻¹ ∈ rootGroup n F
      (weylAction (isFiniteType_cartanC n)
        ((coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem.simple k) γ) := by
  rw [weylAction_simple]
  have hle : rootGroup n F γ ≤ (rootGroup n F (reflection (cartanC n) k γ)).comap
      (MulAut.conj (weylRep n F k)).toMonoidHom := by
    refine rootGroup_le n F fun r hr c => ?_
    obtain ⟨r', c', heq, hstd⟩ := weylElt_conj n F k r c
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, weylRep_eq, ← map_inv,
      ← map_mul, ← map_mul, heq]
    exact mem_rootGroup n F (by rw [hstd, hr, toStd_reflection]) c'
  exact hle hx

private theorem cartanC_of_succ {i j : Fin n} (h : i.val + 1 = j.val) :
    cartanC n i j = if j.val + 1 = n then -2 else -1 := by
  have hij : i ≠ j := fun e => by subst e; omega
  simp only [cartanC, Matrix.of_apply, ite_eq_right hij, ite_eq_left (Or.inl h)]
  by_cases hj : j.val + 1 = n
  · rw [ite_eq_left ⟨by omega, hj⟩, ite_eq_left hj]
  · rw [ite_eq_right (fun h' => hj h'.2), ite_eq_right hj]

private theorem cartanC_of_pred {i j : Fin n} (h : j.val + 1 = i.val) : cartanC n i j = -1 := by
  have hij : i ≠ j := fun e => by subst e; omega
  simp only [cartanC, Matrix.of_apply, ite_eq_right hij, ite_eq_left (Or.inr h)]
  rw [ite_eq_right (fun h' => by omega)]

private theorem cartanC_of_far {i j : Fin n} (hij : i ≠ j) (h₁ : i.val + 1 ≠ j.val)
    (h₂ : j.val + 1 ≠ i.val) : cartanC n i j = 0 := by
  simp only [cartanC, Matrix.of_apply, ite_eq_right hij]
  rw [ite_eq_right (by omega)]

private theorem coxeterMatrix_cartanC_apply (i j : Fin n) :
    coxeterMatrix (isFiniteType_cartanC n) i j =
      TauCeti.coxeterOrder (cartanC n i j * cartanC n j i) :=
  TauCeti.coxeterMatrixOfCartanMatrix_apply _ _ _ i j

private theorem coxeterMatrix_of_succ_short {i j : Fin n} (h : i.val + 1 = j.val)
    (hj : j.val + 1 < n) : coxeterMatrix (isFiniteType_cartanC n) i j = 3 := by
  rw [coxeterMatrix_cartanC_apply, cartanC_of_succ n h, cartanC_of_pred n h,
    ite_eq_right (by omega), show (-1 : ℤ) * -1 = 1 by norm_num, TauCeti.coxeterOrder_one]

private theorem coxeterMatrix_of_succ_long {i j : Fin n} (h : i.val + 1 = j.val)
    (hj : ¬j.val + 1 < n) : coxeterMatrix (isFiniteType_cartanC n) i j = 4 := by
  rw [coxeterMatrix_cartanC_apply, cartanC_of_succ n h, cartanC_of_pred n h,
    ite_eq_left (by omega), show (-2 : ℤ) * -1 = 2 by norm_num, TauCeti.coxeterOrder_two]

private theorem coxeterMatrix_of_far {i j : Fin n} (hij : i ≠ j) (h₁ : i.val + 1 ≠ j.val)
    (h₂ : j.val + 1 ≠ i.val) : coxeterMatrix (isFiniteType_cartanC n) i j = 2 := by
  rw [coxeterMatrix_cartanC_apply, cartanC_of_far n hij h₁ h₂, zero_mul,
    TauCeti.coxeterOrder_zero]

private theorem prod_map_weylRep (ω : List (Fin n)) :
    (ω.map (weylRep n F)).prod = equivStatedSp n F ((ω.map (weylElt n F)).prod) := by
  rw [map_list_prod, List.map_map]
  rfl

private theorem weylElt_braid_of_lt {i j : Fin n} (hij : i < j) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanC n)) i j).map
        (weylElt n F)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanC n)) j i).map
        (weylElt n F)).prod := by
  have hij' : i.val < j.val := hij
  have hi : i.val + 1 < n := by omega
  have hsymm := (coxeterMatrix (isFiniteType_cartanC n)).symmetric j i
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, hsymm]
  by_cases hadj : i.val + 1 = j.val
  · by_cases hj : j.val + 1 < n
    ·
      rw [show (coxeterMatrix (isFiniteType_cartanC n)).M i j = 3 from
        coxeterMatrix_of_succ_short n hadj hj]
      show ([j, i, j].map (weylElt n F)).prod = ([i, j, i].map (weylElt n F)).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        weylElt_of_lt n F hi, weylElt_of_lt n F hj]
      obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hadj.symm
      simpa only [mul_assoc] using (shortWeyl_braid (R := F) (ne_succ n hi) (ne_succ n hj)
        (Fin.ne_of_val_ne (by simp only; omega))).symm
    ·
      rw [show (coxeterMatrix (isFiniteType_cartanC n)).M i j = 4 from
        coxeterMatrix_of_succ_long n hadj hj]
      show ([i, j, i, j].map (weylElt n F)).prod = ([j, i, j, i].map (weylElt n F)).prod
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        weylElt_of_lt n F hi, weylElt_of_not_lt n F hj]
      obtain rfl : j = ⟨i.val + 1, hi⟩ := Fin.ext hadj.symm
      simpa only [mul_assoc] using shortWeyl_longWeyl_braid (R := F) (ne_succ n hi)
  ·
    rw [show (coxeterMatrix (isFiniteType_cartanC n)).M i j = 2 from
      coxeterMatrix_of_far n hij.ne hadj (by omega)]
    show ([i, j].map (weylElt n F)).prod = ([j, i].map (weylElt n F)).prod
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      weylElt_of_lt n F hi]
    by_cases hj : j.val + 1 < n
    · rw [weylElt_of_lt n F hj]
      exact shortWeyl_comm (ne_succ n hi) (ne_succ n hj) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by simp only; omega)) (Fin.ne_of_val_ne (by simp only; omega))
        (Fin.ne_of_val_ne (by simp only; omega))
    · rw [weylElt_of_not_lt n F hj]
      exact shortWeyl_comm_longWeyl (ne_succ n hi) (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by simp only; omega))

private theorem weylRep_braid (i j : Fin n) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanC n)) i j).map
        (weylRep n F)).prod =
      ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartanC n)) j i).map
        (weylRep n F)).prod := by
  rw [prod_map_weylRep, prod_map_weylRep]
  congr 1
  rcases lt_trichotomy i j with h | rfl | h
  · exact weylElt_braid_of_lt n F h
  · rfl
  · exact (weylElt_braid_of_lt n F h).symm

private theorem corootVec_of_lt {k : Fin n} (h : k.val + 1 < n) (c : Fˣ) :
    corootVec n F k c = fun a => if a = k then c else if a = ⟨k.val + 1, h⟩ then c⁻¹ else 1 := by
  funext a
  simp only [corootVec, Fin.ext_iff]

private theorem corootVec_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (c : Fˣ) :
    corootVec n F k c = Pi.mulSingle k c := by
  funext a
  simp only [corootVec, Pi.mulSingle_apply]
  split_ifs with h₁ h₂ <;> first | rfl | (exfalso; omega)

private theorem diagonal_mem_torus (k : Fin n) (c : Fˣ) :
    equivStatedSp n F (diagonal (corootVec n F k c)) ∈ torus n F k :=
  Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨c, rfl⟩)

private theorem torus_le_rankOne (k : Fin n) :
    torus n F k ≤ CurtisTits.rankOne (rootGroup n F) k := by
  rw [torus, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  change equivStatedSp n F (diagonal (corootVec n F k c)) ∈
    rootGroup n F (Pi.single k 1) ⊔ rootGroup n F (-Pi.single k 1)
  by_cases h : k.val + 1 < n
  · have h₁ : ∀ x : F, equivStatedSp n F (differenceShortRootUnit (ne_succ n h) x) ∈
        rootGroup n F (Pi.single k 1) ⊔ rootGroup n F (-Pi.single k 1) := fun x =>
      Subgroup.mem_sup_left (difference_mem n F _ (toStd_single_of_lt n h).symm x)
    have h₂ : ∀ x : F, equivStatedSp n F (differenceShortRootUnit (ne_succ n h).symm x) ∈
        rootGroup n F (Pi.single k 1) ⊔ rootGroup n F (-Pi.single k 1) := fun x =>
      Subgroup.mem_sup_right (difference_mem n F _
        (by rw [toStd_neg, toStd_single_of_lt n h, neg_sub]) x)
    rw [corootVec_of_lt n F h, diagonal_twoPoint_eq (ne_succ n h)]
    simp only [map_mul]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h₁ _) (h₂ _)) (h₁ _)) (h₁ _)) (h₂ _))
      (h₁ _)
  · have h₁ : ∀ x : F, equivStatedSp n F (positiveLongRootTransvectionUnit k x) ∈
        rootGroup n F (Pi.single k 1) ⊔ rootGroup n F (-Pi.single k 1) := fun x =>
      Subgroup.mem_sup_left (positiveLong_mem n F (toStd_single_of_not_lt n h).symm x)
    have h₂ : ∀ x : F, equivStatedSp n F (negativeLongRootTransvectionUnit k x) ∈
        rootGroup n F (Pi.single k 1) ⊔ rootGroup n F (-Pi.single k 1) := fun x =>
      Subgroup.mem_sup_right (negativeLong_mem n F
        (by rw [toStd_neg, toStd_single_of_not_lt n h]) x)
    rw [corootVec_of_not_lt n F h, diagonal_mulSingle_eq]
    simp only [map_mul]
    exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h₁ _) (h₂ _)) (h₁ _)) (h₁ _)) (h₂ _))
      (h₁ _)

private theorem weylRep_sq_mem (k : Fin n) : weylRep n F k ^ 2 ∈ torus n F k := by
  rw [weylRep_eq, ← map_pow]
  refine Subgroup.mem_map_of_mem _ ?_
  by_cases h : k.val + 1 < n
  · rw [weylElt_of_lt n F h, shortWeyl_sq (ne_succ n h)]
    exact inv_mem (Subgroup.subset_closure ⟨-1, by dsimp only; rw [corootVec_of_lt n F h]⟩)
  · rw [weylElt_of_not_lt n F h, longWeyl_sq]
    exact inv_mem (Subgroup.subset_closure ⟨-1, by dsimp only; rw [corootVec_of_not_lt n F h]⟩)

private theorem diagonal_conj_mem (t : Fin n → Fˣ) (γ : Fin n → ℤ) (x : StatedSp n F)
    (hx : x ∈ rootGroup n F γ) :
    equivStatedSp n F (diagonal t) * x * (equivStatedSp n F (diagonal t))⁻¹ ∈
      rootGroup n F γ := by
  have hle : rootGroup n F γ ≤ (rootGroup n F γ).comap
      (MulAut.conj (equivStatedSp n F (diagonal t))).toMonoidHom := by
    refine rootGroup_le n F fun r hr c => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← map_inv, ← map_mul,
      ← map_mul, diagonal_mul_rootSubgroup_mul_inv]
    exact mem_rootGroup n F hr _
  exact hle hx

private theorem torus_conj_mem (k : Fin n) (γ : Fin n → ℤ)
    (_ : γ ∈ roots (isFiniteType_cartanC n) ∅) (h : StatedSp n F) (hh : h ∈ torus n F k)
    (x : StatedSp n F) (hx : x ∈ rootGroup n F γ) : h * x * h⁻¹ ∈ rootGroup n F γ := by
  have hN : torus n F k ≤ Subgroup.normalizer (rootGroup n F γ : Set (StatedSp n F)) := by
    rw [torus, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    change equivStatedSp n F (diagonal (corootVec n F k c)) ∈
      Subgroup.normalizer (rootGroup n F γ : Set (StatedSp n F))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨diagonal_conj_mem n F _ γ y, fun hy => ?_⟩
    have := diagonal_conj_mem n F (corootVec n F k c)⁻¹ γ _ hy
    have e : ∀ g : StatedSp n F, g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := fun g => by group
    rwa [map_inv, map_inv, e] at this
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) x).mp hx

private def cvec (k : Fin n) : Fin n → ℤ := fun a =>
  if a = k then 1 else if a.val = k.val + 1 then -1 else 0

private theorem corootVec_eq_zpow (k : Fin n) (c : Fˣ) :
    corootVec n F k c = fun a => c ^ cvec n k a := by
  funext a
  simp only [corootVec, cvec]
  split_ifs <;> simp

private theorem stdRefl_cvec (j k : Fin n) :
    stdRefl n j (cvec n k) = cvec n k + (-cartanC n k j) • cvec n j := by
  funext a
  by_cases h : j.val + 1 < n
  · rw [stdRefl_of_lt n h]
    simp only [Function.comp_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases ha : a = j
    · subst ha
      rw [Equiv.swap_apply_left]
      simp only [cvec, cartanC, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    by_cases ha' : a = ⟨j.val + 1, h⟩
    · subst ha'
      rw [Equiv.swap_apply_right]
      simp only [cvec, cartanC, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne ha ha']
      simp only [cvec, cartanC, Matrix.of_apply, Fin.ext_iff] at ha ha' ⊢
      split_ifs <;> omega
  · rw [stdRefl_of_not_lt n h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cvec, cartanC, Matrix.of_apply,
      Fin.ext_iff]
    split_ifs <;> omega

private theorem weylElt_conj_diagonal (j : Fin n) (c : Fˣ) (u : Fin n → ℤ) :
    weylElt n F j * diagonal (fun a => c ^ u a) * (weylElt n F j)⁻¹ =
      diagonal (fun a => c ^ stdRefl n j u a) := by
  by_cases h : j.val + 1 < n
  · rw [weylElt_of_lt n F h, differenceShortRootWeylElement_inv,
      differenceShortRootWeylElement_mul_diagonal_mul_inv, stdRefl_of_lt n h]
    rfl
  · rw [weylElt_of_not_lt n F h, positiveLongRootWeylElement_inv,
      positiveLongRootWeylElement_mul_diagonal_mul_inv, stdRefl_of_not_lt n h]
    congr 1
    funext a
    by_cases ha : a = j
    · subst ha
      simp [_root_.zpow_neg]
    · simp [ha]

private theorem weylRep_conj_torus (j k : Fin n) (h : StatedSp n F) (hh : h ∈ torus n F k) :
    weylRep n F j * h * (weylRep n F j)⁻¹ ∈ torus n F j ⊔ torus n F k := by
  have hle : Subgroup.closure (Set.range fun c : Fˣ => diagonal (R := F) (corootVec n F k c)) ≤
      (torus n F j ⊔ torus n F k).comap ((equivStatedSp n F).toMonoidHom.comp
        (MulAut.conj (weylElt n F j)).toMonoidHom) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    change equivStatedSp n F (weylElt n F j * diagonal (corootVec n F k c) *
      (weylElt n F j)⁻¹) ∈ torus n F j ⊔ torus n F k
    have hsplit : (fun a => c ^ (cvec n k + (-cartanC n k j) • cvec n j) a) =
        corootVec n F k c * corootVec n F j c ^ (-cartanC n k j) := by
      funext a
      rw [corootVec_eq_zpow, corootVec_eq_zpow]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
      rw [_root_.zpow_add, mul_comm (-cartanC n k j), _root_.zpow_mul]
      rfl
    rw [corootVec_eq_zpow n F k, weylElt_conj_diagonal, stdRefl_cvec, hsplit, map_mul, map_zpow,
      map_mul, map_zpow]
    exact mul_mem (Subgroup.mem_sup_right (diagonal_mem_torus n F k c))
      (zpow_mem (Subgroup.mem_sup_left (diagonal_mem_torus n F j c)) _)
  obtain ⟨h', hh', rfl⟩ := hh
  have := hle hh'
  rw [Subgroup.mem_comap] at this
  simpa [weylRep_eq] using this

private theorem dotProduct_eq_of_isStdRoot {e : Fin n → ℤ} (he : IsStdRoot n e) :
    e ⬝ᵥ e = 2 ∨ e ⬝ᵥ e = 4 := by
  obtain ⟨a, b, s, t, hs, ht, hst, rfl⟩ := he
  simp only [add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_apply]
  by_cases hab : a = b
  · subst hab
    obtain rfl := hst rfl
    rcases hs with rfl | rfl <;> norm_num
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hab, Ne.symm hab]

private theorem rootGroup_le_rankOne (i : Fin n) (γ : Fin n → ℤ)
    (hγ : γ ∈ roots (isFiniteType_cartanC n) ∅) (hsupp : ∀ k, k ≠ i → γ k = 0) :
    rootGroup n F γ ≤ CurtisTits.rankOne (rootGroup n F) i := by
  have hγi : γ = γ i • Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp
    · simp [hsupp k hk, hk]
  have hroot : IsStdRoot n (toStd n γ) := by
    rcases hγ with ⟨w, l, rfl⟩ | ⟨w, l, hl, -⟩
    · exact isStdRoot_toStd_weylAction n w l
    · exact absurd hl (Set.notMem_empty l)
  have hN₂ := dotProduct_eq_of_isStdRoot n hroot
  have hN₁ := dotProduct_eq_of_isStdRoot n (isStdRoot_toStd_single n i)
  rw [hγi, toStd_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hN₂
  set c := γ i
  have hcc : 0 ≤ c * c := mul_self_nonneg c
  have hc0 : c ≠ 0 := by
    rintro hc
    rw [hc] at hN₂
    simp at hN₂
  have h₁ : c ≤ 1 := by
    rcases hN₁ with h₁ | h₁ <;> rcases hN₂ with h₂ | h₂ <;> rw [h₁] at h₂ <;> nlinarith
  have h₂ : -1 ≤ c := by
    rcases hN₁ with h₁ | h₁ <;> rcases hN₂ with h₂ | h₂ <;> rw [h₁] at h₂ <;> nlinarith
  rcases (show c = 1 ∨ c = -1 by omega) with h | h
  · rw [hγi, h, one_smul]
    exact le_sup_left
  · rw [hγi, h, neg_one_zsmul]
    exact le_sup_right

private theorem iSup_rootGroup_eq_top :
    ⨆ γ ∈ roots (isFiniteType_cartanC n) ∅, rootGroup n F γ = ⊤ := by
  set T := ⨆ γ ∈ roots (isFiniteType_cartanC n) ∅, rootGroup n F γ
  have hT : T.comap (equivStatedSp n F).toMonoidHom = ⊤ := by
    refine eq_top_of_root_subgroups _ fun r c => ?_
    obtain ⟨w, k, hw⟩ := isStdOrbit_stdVec n r
    have hγ : weylAction (isFiniteType_cartanC n) w (Pi.single k 1) ∈
        roots (isFiniteType_cartanC n) ∅ := Or.inl ⟨w, k, rfl⟩
    exact le_iSup₂_of_le (f := fun γ _ => rootGroup n F γ) _ hγ le_rfl
      (mem_rootGroup n F hw.symm c)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp n F).surjective x
  have hy : y ∈ T.comap (equivStatedSp n F).toMonoidHom := by
    rw [hT]
    exact Subgroup.mem_top y
  exact hy

theorem isCTGroupDatum :
    CFSG.LieType.CurtisTits.IsCTGroupDatum (coxeterMatrix (isFiniteType_cartanC n)).toCoxeterSystem
      (weylAction (isFiniteType_cartanC n)) (roots (isFiniteType_cartanC n) ∅) (rootGroup n F)
      (weylRep n F) (torus n F) where
  n_mem := weylRep_mem_rankOne n F
  conj_mem := weylRep_conj_mem n F
  braid := weylRep_braid n F
  H_le := torus_le_rankOne n F
  sq_mem := weylRep_sq_mem n F
  H_conj_mem := torus_conj_mem n F
  conj_H_mem := weylRep_conj_torus n F
  le_rankOne := rootGroup_le_rankOne n F
  iSup_eq_top := iSup_rootGroup_eq_top n F

end CFSG.LieType.Universal.Symplectic
