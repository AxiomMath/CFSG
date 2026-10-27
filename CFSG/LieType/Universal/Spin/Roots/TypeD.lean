module

public import CFSG.LieType.RootSystem.Basic
public import CFSG.LieType.Steinberg.Basic
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical

public section

namespace CFSG.LieType.Universal.Spin

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg

@[expose] def cartanD (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
  if i = j then 2
  else if (i.val + 1 = j.val ∧ j.val + 1 < n) ∨ (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
      (i.val + 3 = n ∧ j.val + 1 = n) ∨ (j.val + 3 = n ∧ i.val + 1 = n) then -1
  else 0

theorem cartanD_eq (n : ℕ) : cartanD n = CartanMatrix.D n := by
  ext i j
  simp only [cartanD, CartanMatrix.D, Matrix.of_apply]
  split_ifs <;> omega

theorem isFiniteType_cartanD (n : ℕ) : TauCeti.IsFiniteType (cartanD n) := by
  rw [cartanD_eq]
  exact TauCeti.isFiniteType_cartanMatrix_D n

@[expose] def toStdD (n : ℕ) (v : Fin n → ℤ) : Fin n → ℤ := fun a =>
  v a - (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) +
    (if h : a.val + 2 = n then v ⟨a.val + 1, by omega⟩ else 0)

@[expose] def stdReflD (n : ℕ) (k : Fin n) (e : Fin n → ℤ) : Fin n → ℤ :=
  if h : k.val + 1 < n then e ∘ Equiv.swap k ⟨k.val + 1, h⟩
  else fun a => (if a.val + 2 = n ∨ a.val + 1 = n then -1 else 1) *
    e (Equiv.swap ⟨k.val - 1, by omega⟩ k a)

variable (n : ℕ)

private def toStdDLin : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun := toStdD n
  map_add' v w := by
    funext a
    simp only [toStdD, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext a
    simp only [toStdD, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private theorem toStdDLin_apply (v : Fin n → ℤ) : toStdDLin n v = toStdD n v := rfl

theorem toStdD_zero : toStdD n 0 = 0 :=
  map_zero (toStdDLin n)

theorem toStdD_add (v w : Fin n → ℤ) : toStdD n (v + w) = toStdD n v + toStdD n w :=
  map_add (toStdDLin n) v w

theorem toStdD_sub (v w : Fin n → ℤ) : toStdD n (v - w) = toStdD n v - toStdD n w :=
  map_sub (toStdDLin n) v w

theorem toStdD_neg (v : Fin n → ℤ) : toStdD n (-v) = -toStdD n v :=
  map_neg (toStdDLin n) v

theorem toStdD_smul (c : ℤ) (v : Fin n → ℤ) : toStdD n (c • v) = c • toStdD n v :=
  map_zsmul (toStdDLin n) c v

theorem toStdD_single_of_lt {k : Fin n} (h : k.val + 1 < n) :
    toStdD n (Pi.single k 1) = Pi.single k 1 - Pi.single ⟨k.val + 1, h⟩ 1 := by
  funext a
  simp only [toStdD, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem toStdD_single_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (hn : 2 ≤ n) :
    toStdD n (Pi.single k 1) = Pi.single ⟨n - 2, by omega⟩ 1 + Pi.single k 1 := by
  funext a
  simp only [toStdD, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem toStdD_single_of_eq_one (hn : n = 1) (k : Fin n) :
    toStdD n (Pi.single k 1) = Pi.single k 1 := by
  funext a
  simp only [toStdD, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem toStdD_apply_eq (v : Fin n → ℤ) (k : Fin n) :
    toStdD n v k = v k - (if h : 0 < k.val then v ⟨k.val - 1, by omega⟩ else 0) +
      (if h : k.val + 2 = n then v ⟨k.val + 1, by omega⟩ else 0) := rfl

theorem toStdD_injective : Function.Injective (toStdD n) := by
  intro v w h
  have hu : ∀ a, toStdD n (v - w) a = 0 := fun a => by
    rw [toStdD_sub, h, sub_self, Pi.zero_apply]
  suffices hvw : v - w = 0 from sub_eq_zero.mp hvw
  set u := v - w
  have low : ∀ d (k : Fin n), k.val = d → k.val + 2 < n → u k = 0 := by
    intro d
    induction d with
    | zero =>
      intro k hk hkn
      have := hu k
      rwa [toStdD_apply_eq, dite_eq_right (by omega), dite_eq_right (by omega), sub_zero,
        add_zero] at this
    | succ d ih =>
      intro k hk hkn
      have := hu k
      rwa [toStdD_apply_eq, dite_eq_left (by omega), dite_eq_right (by omega),
        ih ⟨k.val - 1, by omega⟩ (by simp only; omega) (by simp only; omega), sub_zero,
        add_zero] at this
  have top : ∀ p q : Fin n, p.val + 2 = n → q.val = p.val + 1 → u p = 0 ∧ u q = 0 := by
    intro p q hp hq
    have h1 := hu p
    have h2 := hu q
    have hX : (if h : 0 < p.val then u ⟨p.val - 1, by omega⟩ else 0) = 0 := by
      split_ifs with h0
      · exact low _ _ rfl (by simp only; omega)
      · rfl
    have e1 : (⟨p.val + 1, by omega⟩ : Fin n) = q := Fin.ext (by simp only; omega)
    have e2 : (⟨q.val - 1, by omega⟩ : Fin n) = p := Fin.ext (by simp only; omega)
    rw [toStdD_apply_eq, dite_eq_left hp, hX, e1] at h1
    rw [toStdD_apply_eq, dite_eq_left (by omega), dite_eq_right (by omega), e2] at h2
    constructor <;> linarith
  funext a
  rw [Pi.zero_apply]
  by_cases ha : a.val + 2 < n
  · exact low a.val a rfl ha
  by_cases ha' : a.val + 2 = n
  · exact (top a ⟨a.val + 1, by omega⟩ ha' rfl).1
  by_cases hn : n = 1
  · have := hu a
    rwa [toStdD_apply_eq, dite_eq_right (by omega), dite_eq_right (by omega), sub_zero,
      add_zero] at this
  · exact (top ⟨n - 2, by omega⟩ a (by simp only; omega) (by simp only; omega)).2

theorem stdReflD_of_lt {k : Fin n} (h : k.val + 1 < n) (e : Fin n → ℤ) :
    stdReflD n k e = e ∘ Equiv.swap k ⟨k.val + 1, h⟩ := dite_eq_left h

theorem stdReflD_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (e : Fin n → ℤ) :
    stdReflD n k e = fun a => (if a.val + 2 = n ∨ a.val + 1 = n then -1 else 1) *
      e (Equiv.swap ⟨k.val - 1, by omega⟩ k a) := dite_eq_right h

theorem coroot_cartanD_of_lt {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanD n) k v = toStdD n v k - toStdD n v ⟨k.val + 1, h⟩ := by
  have key : coroot (cartanD n) k =
      ((LinearMap.proj k : (Fin n → ℤ) →ₗ[ℤ] ℤ) - LinearMap.proj (⟨k.val + 1, h⟩ : Fin n)).comp
        (toStdDLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdDLin_apply, toStdD, cartanD, Matrix.of_apply,
      Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem coroot_cartanD_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (v : Fin n → ℤ) :
    coroot (cartanD n) k v = toStdD n v ⟨k.val - 1, by omega⟩ + toStdD n v k := by
  have key : coroot (cartanD n) k =
      ((LinearMap.proj (⟨k.val - 1, by omega⟩ : Fin n) : (Fin n → ℤ) →ₗ[ℤ] ℤ) +
        LinearMap.proj k).comp (toStdDLin n) := by
    ext l
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.proj_apply,
      LinearMap.coe_single, coroot_single, toStdDLin_apply, toStdD, cartanD, Matrix.of_apply,
      Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega
  exact LinearMap.congr_fun key v

theorem toStdD_reflection (k : Fin n) (v : Fin n → ℤ) :
    toStdD n (reflection (cartanD n) k v) = stdReflD n k (toStdD n v) := by
  rw [reflection_apply_coroot, toStdD_sub, toStdD_smul]
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanD_of_lt n h, toStdD_single_of_lt n h, stdReflD_of_lt n h]
    have hne : (⟨k.val + 1, h⟩ : Fin n) ≠ k := Fin.ne_of_val_ne (by simp)
    funext a
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm hne]
    by_cases ha' : a = ⟨k.val + 1, h⟩
    · subst ha'
      simp [hne]
    · simp [ha, ha', Equiv.swap_apply_of_ne_of_ne ha ha']
  · rw [coroot_cartanD_of_not_lt n h, stdReflD_of_not_lt n h]
    set e := toStdD n v
    by_cases hn : n = 1
    · have hp : (⟨k.val - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp only; omega)
      rw [toStdD_single_of_eq_one n hn, hp, Equiv.swap_self]
      funext a
      rw [show a = k from Fin.ext (by omega)]
      have hsg : (if k.val + 2 = n ∨ k.val + 1 = n then (-1 : ℤ) else 1) = -1 :=
        ite_eq_left (Or.inr (by omega))
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Equiv.refl_apply, hsg,
        Pi.single_eq_same]
      ring
    · obtain ⟨p, hpv⟩ : ∃ p : Fin n, p.val = n - 2 := ⟨⟨n - 2, by omega⟩, rfl⟩
      have hp : (⟨k.val - 1, by omega⟩ : Fin n) = p := Fin.ext (by simp only; omega)
      have hp' : (⟨n - 2, by omega⟩ : Fin n) = p := Fin.ext (by simp only; omega)
      rw [toStdD_single_of_not_lt n h (by omega), hp, hp']
      have hpk : p ≠ k := Fin.ne_of_val_ne (by omega)
      funext a
      by_cases ha : a = k
      · rw [ha]
        have hsg : (if k.val + 2 = n ∨ k.val + 1 = n then (-1 : ℤ) else 1) = -1 :=
          ite_eq_left (Or.inr (by omega))
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hsg,
          Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne' hpk]
        ring
      by_cases ha' : a = p
      · rw [ha']
        have hsg : (if p.val + 2 = n ∨ p.val + 1 = n then (-1 : ℤ) else 1) = -1 :=
          ite_eq_left (Or.inl (by omega))
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hsg,
          Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hpk]
        ring
      · have hav : ¬(a.val + 2 = n ∨ a.val + 1 = n) := by
          rintro (h' | h')
          · exact ha' (Fin.ext (by omega))
          · exact ha (Fin.ext (by omega))
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.single_eq_of_ne ha,
          Pi.single_eq_of_ne ha', smul_eq_mul, Equiv.swap_apply_of_ne_of_ne ha' ha,
          ite_eq_right hav]
        ring

theorem toStdD_reflection_of_lt {k : Fin n} (h : k.val + 1 < n) (v : Fin n → ℤ) :
    toStdD n (reflection (cartanD n) k v) = toStdD n v ∘ Equiv.swap k ⟨k.val + 1, h⟩ := by
  rw [toStdD_reflection, stdReflD_of_lt n h]

theorem toStdD_reflection_of_not_lt {k : Fin n} (h : ¬k.val + 1 < n) (v : Fin n → ℤ) :
    toStdD n (reflection (cartanD n) k v) = fun a =>
      if a.val + 2 = n then -toStdD n v k
      else if a = k then -toStdD n v ⟨k.val - 1, by omega⟩ else toStdD n v a := by
  rw [toStdD_reflection, stdReflD_of_not_lt n h]
  funext a
  by_cases ha : a.val + 2 = n
  · have hp : a = ⟨k.val - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [ite_eq_left (Or.inl ha), ite_eq_left ha, hp, Equiv.swap_apply_left]
    ring
  rw [ite_eq_right ha]
  by_cases hak : a = k
  · subst hak
    rw [ite_eq_left (Or.inr (by omega)), ite_eq_left rfl, Equiv.swap_apply_right]
    ring
  · have hak' : a.val ≠ k.val := fun e => hak (Fin.ext e)
    have hap : a ≠ ⟨k.val - 1, by omega⟩ := fun e => ha (by rw [e]; simp only; omega)
    rw [ite_eq_right hak, ite_eq_right (by omega), Equiv.swap_apply_of_ne_of_ne hap hak]
    ring

private theorem stdReflD_of_succ {k k' : Fin n} (h : k.val + 1 = k'.val) (e : Fin n → ℤ) :
    stdReflD n k e = e ∘ Equiv.swap k k' := by
  rw [stdReflD_of_lt n (by omega)]
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

private theorem sign_mul {u : ℤ} (hu : u = 1 ∨ u = -1) (c : ℤ) (hc : c = 1 ∨ c = -1) :
    c * u = 1 ∨ c * u = -1 := by
  rcases hc with rfl | rfl <;> rcases hu with rfl | rfl <;> simp

private def IsStdRootD (e : Fin n → ℤ) : Prop :=
  ∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
    e = Pi.single i s + Pi.single j t

private theorem isStdRootD_toStdD_single (hn : n ≠ 1) (k : Fin n) :
    IsStdRootD n (toStdD n (Pi.single k 1)) := by
  by_cases h : k.val + 1 < n
  · refine ⟨k, ⟨k.val + 1, h⟩, 1, -1, Fin.ne_of_val_ne (by simp), Or.inl rfl, Or.inr rfl, ?_⟩
    rw [toStdD_single_of_lt n h, sub_eq_add_neg, Pi.single_neg]
  · exact ⟨⟨n - 2, by omega⟩, k, 1, 1, Fin.ne_of_val_ne (by simp only; omega), Or.inl rfl,
      Or.inl rfl, toStdD_single_of_not_lt n h (by omega)⟩

private theorem isStdRootD_signedPerm (σ : Fin n → ℤ) (hσ : ∀ c, σ c = 1 ∨ σ c = -1)
    (τ : Equiv.Perm (Fin n)) {e : Fin n → ℤ} (he : IsStdRootD n e) :
    IsStdRootD n (fun x => σ x * e (τ x)) := by
  obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := he
  have key : ∀ (c : Fin n) (u : ℤ),
      (fun x => σ x * (Pi.single c u : Fin n → ℤ) (τ x)) = Pi.single (τ.symm c) (σ (τ.symm c) * u) := by
    intro c u
    rw [← mul_single n σ, ← Pi.single_comp_equiv]
    rfl
  refine ⟨τ.symm a, τ.symm b, σ (τ.symm a) * s, σ (τ.symm b) * t, τ.symm.injective.ne hab,
    sign_mul hs _ (hσ _), sign_mul ht _ (hσ _), ?_⟩
  funext x
  simp only [Pi.add_apply, mul_add]
  exact congrArg₂ (· + ·) (congrFun (key a s) x) (congrFun (key b t) x)

private theorem isStdRootD_stdReflD (k : Fin n) {e : Fin n → ℤ} (he : IsStdRootD n e) :
    IsStdRootD n (stdReflD n k e) := by
  by_cases h : k.val + 1 < n
  · rw [stdReflD_of_lt n h]
    obtain ⟨a, b, s, t, hab, hs, ht, rfl⟩ := he
    refine ⟨Equiv.swap k ⟨k.val + 1, h⟩ a, Equiv.swap k ⟨k.val + 1, h⟩ b, s, t,
      (Equiv.swap _ _).injective.ne hab, hs, ht, ?_⟩
    rw [Pi.add_comp, single_comp_swap, single_comp_swap]
  · rw [stdReflD_of_not_lt n h]
    exact isStdRootD_signedPerm n _ (fun c => by split_ifs <;> simp) _ he

private theorem isStdRootD_toStdD_weylAction (hn : n ≠ 1)
    (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) (k : Fin n) :
    IsStdRootD n (toStdD n (weylAction (isFiniteType_cartanD n) w (Pi.single k 1))) := by
  induction w using (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple_induction_left
    with
  | one => simpa using isStdRootD_toStdD_single n hn k
  | mul_simple_left w l ih =>
    rw [weylAction_mul_apply, weylAction_simple, toStdD_reflection]
    exact isStdRootD_stdReflD n l ih

private def IsStdOrbitD (e : Fin n → ℤ) : Prop :=
  ∃ (w : (coxeterMatrix (isFiniteType_cartanD n)).Group) (k : Fin n),
    toStdD n (weylAction (isFiniteType_cartanD n) w (Pi.single k 1)) = e

private theorem isStdOrbitD_toStdD_single (k : Fin n) :
    IsStdOrbitD n (toStdD n (Pi.single k 1)) :=
  ⟨1, k, by rw [map_one, Module.End.one_apply]⟩

private theorem IsStdOrbitD.neg {e : Fin n → ℤ} (he : IsStdOrbitD n e) : IsStdOrbitD n (-e) := by
  obtain ⟨w, k, rfl⟩ := he
  refine ⟨w * (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k, k, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg, toStdD_neg]

private theorem IsStdOrbitD.stdReflD {e : Fin n → ℤ} (he : IsStdOrbitD n e) (k : Fin n) :
    IsStdOrbitD n (stdReflD n k e) := by
  obtain ⟨w, l, rfl⟩ := he
  refine ⟨(coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple k * w, l, ?_⟩
  rw [weylAction_mul_apply, weylAction_simple, toStdD_reflection]

private theorem isStdOrbitD_difference (d : ℕ) :
    ∀ i j : Fin n, j.val = i.val + 1 + d → IsStdOrbitD n (Pi.single i 1 - Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij
    have h : i.val + 1 < n := by omega
    have e : (⟨i.val + 1, h⟩ : Fin n) = j := Fin.ext (by simp only; omega)
    simpa [toStdD_single_of_lt n h, e] using isStdOrbitD_toStdD_single n i
  | succ d ih =>
    intro i j hij
    have hj' : i.val + 1 + d < n := by omega
    have h := (ih i ⟨i.val + 1 + d, hj'⟩ rfl).stdReflD n ⟨i.val + 1 + d, hj'⟩
    rw [stdReflD_of_succ n (k' := j) (by simp only; omega), Pi.sub_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by simp only; omega))
        (Fin.ne_of_val_ne (by omega))] at h
    exact h

private theorem isStdOrbitD_positiveSum (d : ℕ) :
    ∀ i j : Fin n, i < j → j.val + d + 1 = n →
      IsStdOrbitD n (Pi.single i 1 + Pi.single j 1) := by
  induction d with
  | zero =>
    intro i j hij hj
    have hij' : i.val < j.val := hij
    by_cases hi : i.val + 2 = n
    · have e : (⟨n - 2, by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
      have := isStdOrbitD_toStdD_single n j
      rwa [toStdD_single_of_not_lt n (by omega) (by omega), e] at this
    · obtain ⟨p, hpv⟩ : ∃ p : Fin n, p.val = j.val - 1 := ⟨⟨j.val - 1, by omega⟩, rfl⟩
      have h := (isStdOrbitD_difference n (j.val - 1 - i.val - 1) i p (by omega)).stdReflD n j
      have hp : (⟨j.val - 1, by omega⟩ : Fin n) = p := Fin.ext (by simp only; omega)
      rw [stdReflD_of_not_lt n (by omega), hp] at h
      convert h using 1
      have hpj : p ≠ j := Fin.ne_of_val_ne (by omega)
      have hip : i ≠ p := Fin.ne_of_val_ne (by omega)
      funext x
      by_cases hx : x = j
      · rw [hx]
        have hsg : (if j.val + 2 = n ∨ j.val + 1 = n then (-1 : ℤ) else 1) = -1 :=
          ite_eq_left (Or.inr (by omega))
        simp only [hsg, Equiv.swap_apply_right, Pi.sub_apply, Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hij.ne', Pi.single_eq_of_ne hip.symm]
        ring
      by_cases hx' : x = i
      · rw [hx']
        have hsg : (if i.val + 2 = n ∨ i.val + 1 = n then (-1 : ℤ) else 1) = 1 :=
          ite_eq_right (by omega)
        simp only [hsg, Equiv.swap_apply_of_ne_of_ne hip hij.ne, Pi.sub_apply, Pi.add_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne hij.ne, Pi.single_eq_of_ne hip]
        ring
      by_cases hx'' : x = p
      · rw [hx'']
        simp only [Equiv.swap_apply_left, Pi.sub_apply, Pi.add_apply,
          Pi.single_eq_of_ne hip.symm, Pi.single_eq_of_ne hpj, Pi.single_eq_of_ne hij.ne',
          Pi.single_eq_of_ne hpj.symm]
        ring
      · rw [Equiv.swap_apply_of_ne_of_ne hx'' hx]
        simp only [Pi.sub_apply, Pi.add_apply, Pi.single_eq_of_ne hx', Pi.single_eq_of_ne hx,
          Pi.single_eq_of_ne hx'']
        ring
  | succ d ih =>
    intro i j hij hj
    have hj' : j.val + 1 < n := by omega
    have h := (ih i ⟨j.val + 1, hj'⟩ (by
      change i.val < j.val + 1
      have : i.val < j.val := hij
      omega) (by simp only; omega)).stdReflD n j
    rw [stdReflD_of_succ n (k' := ⟨j.val + 1, hj'⟩) rfl, Pi.add_comp, single_comp_swap,
      single_comp_swap, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hij.ne (Fin.ne_of_val_ne (by
        have : i.val < j.val := hij
        simp only
        omega))] at h
    exact h

private theorem isStdOrbitD_sub {i j : Fin n} (hij : i ≠ j) :
    IsStdOrbitD n (Pi.single i 1 - Pi.single j 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isStdOrbitD_difference n (j.val - i.val - 1) i j (by
      have : i.val < j.val := h
      omega)
  · have := (isStdOrbitD_difference n (i.val - j.val - 1) j i (by
      have : j.val < i.val := h
      omega)).neg n
    rwa [neg_sub] at this

private theorem isStdOrbitD_add {i j : Fin n} (hij : i ≠ j) :
    IsStdOrbitD n (Pi.single i 1 + Pi.single j 1) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isStdOrbitD_positiveSum n (n - 1 - j.val) i j h (by omega)
  · rw [add_comm]
    exact isStdOrbitD_positiveSum n (n - 1 - i.val) j i h (by omega)

private theorem isStdOrbitD_of_isStdRootD {e : Fin n → ℤ} (he : IsStdRootD n e) :
    IsStdOrbitD n e := by
  obtain ⟨i, j, s, t, hij, hs, ht, rfl⟩ := he
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact isStdOrbitD_add n hij
  · rw [Pi.single_neg, ← sub_eq_add_neg]
    exact isStdOrbitD_sub n hij
  · rw [Pi.single_neg, add_comm, ← sub_eq_add_neg]
    exact isStdOrbitD_sub n hij.symm
  · rw [Pi.single_neg, Pi.single_neg, ← neg_add]
    exact (isStdOrbitD_add n hij).neg n

theorem rootsD_eq (hn : n ≠ 1) : roots (isFiniteType_cartanD n) ∅ =
    {γ | ∃ (i j : Fin n) (s t : ℤ), i ≠ j ∧ (s = 1 ∨ s = -1) ∧ (t = 1 ∨ t = -1) ∧
      toStdD n γ = Pi.single i s + Pi.single j t} := by
  ext γ
  constructor
  · rintro (⟨w, k, rfl⟩ | ⟨w, k, hk, -⟩)
    · exact isStdRootD_toStdD_weylAction n hn w k
    · exact absurd hk (Set.notMem_empty k)
  · intro hγ
    obtain ⟨w, k, hw⟩ := isStdOrbitD_of_isStdRootD n (e := toStdD n γ) hγ
    exact Or.inl ⟨w, k, toStdD_injective n hw.symm⟩

theorem exists_mem_rootsD_toStdD_eq {i j : Fin n} {s t : ℤ} (hij : i ≠ j)
    (hs₁ : s = 1 ∨ s = -1) (ht₁ : t = 1 ∨ t = -1) :
    ∃ γ ∈ roots (isFiniteType_cartanD n) ∅, toStdD n γ = Pi.single i s + Pi.single j t := by
  obtain ⟨w, k, hw⟩ := isStdOrbitD_of_isStdRootD n ⟨i, j, s, t, hij, hs₁, ht₁, rfl⟩
  exact ⟨_, Or.inl ⟨w, k, rfl⟩, hw⟩

theorem ht_eq_sum_toStdD (hn : n ≠ 1) (v : Fin n → ℤ) :
    ht v = ∑ a : Fin n, ((n : ℤ) - 1 - a) * toStdD n v a := by
  let f : (Fin n → ℤ) →+ ℤ :=
    { toFun := ht
      map_zero' := by simp [ht]
      map_add' := fun v w => by simp [ht, Finset.sum_add_distrib] }
  let g : (Fin n → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ a : Fin n, ((n : ℤ) - 1 - a) * toStdD n v a
      map_zero' := by simp [toStdD_zero]
      map_add' := fun v w => by simp [toStdD_add, mul_add, Finset.sum_add_distrib] }
  have hfg : f = g := by
    refine AddMonoidHom.functions_ext _ f g fun k x => ?_
    have hs : (Pi.single k x : Fin n → ℤ) = x • Pi.single k 1 := by
      funext j
      simp [Pi.single_apply]
    change ht (Pi.single k x) = ∑ a : Fin n, ((n : ℤ) - 1 - a) * toStdD n (Pi.single k x) a
    rw [hs, toStdD_smul]
    by_cases h : k.val + 1 < n
    · rw [toStdD_single_of_lt n h]
      simp [ht, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
      ring
    · rw [toStdD_single_of_not_lt n h (by omega)]
      simp [ht, Pi.single_apply, mul_add, Finset.sum_add_distrib]
      have : (k.val : ℤ) + 1 = n := by omega
      have h2 : ((n - 2 : ℕ) : ℤ) = n - 2 := by omega
      rw [h2]
      linear_combination x * this
  exact DFunLike.congr_fun hfg v

theorem ht_of_toStdD_eq_add (hn : n ≠ 1) {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ}
    (h : toStdD n γ = Pi.single i s + Pi.single j t) :
    ht γ = s * ((n : ℤ) - 1 - i) + t * ((n : ℤ) - 1 - j) := by
  rw [ht_eq_sum_toStdD n hn, h]
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem ht_pos_iff_of_toStdD_eq_add (hn : n ≠ 1) {γ : Fin n → ℤ} {i j : Fin n} {s t : ℤ}
    (hij : i < j) (hs₁ : s = 1 ∨ s = -1) (ht₁ : t = 1 ∨ t = -1)
    (h : toStdD n γ = Pi.single i s + Pi.single j t) : 0 < ht γ ↔ s = 1 := by
  rw [ht_of_toStdD_eq_add n hn h]
  have hij' : i.val < j.val := hij
  have hj := j.isLt
  rcases hs₁ with rfl | rfl <;> rcases ht₁ with rfl | rfl <;> omega

end CFSG.LieType.Universal.Spin
