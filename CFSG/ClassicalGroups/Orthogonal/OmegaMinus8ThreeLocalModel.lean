module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

open CFSG.GroupTheory.WeirSylow

variable {K : Type} [Field K]

@[expose] def rotLE (K : Type) [Field K] : (K × K) ≃ₗ[K] (K × K) where
  toFun p := (-p.2, p.1 - p.2)
  invFun p := (p.2 - p.1, -p.1)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

private theorem rotLE_apply (p : K × K) : rotLE K p = (-p.2, p.1 - p.2) := rfl

@[expose] def rotPow (K : Type) [Field K] (k : ZMod 3) : (K × K) ≃ₗ[K] (K × K) :=
  rotLE K ^ k.val

theorem rotLE_pow_three : rotLE K ^ 3 = 1 := by
  refine LinearEquiv.ext fun p => ?_
  change (rotLE K ^ 3) p = p
  rw [LinearEquiv.pow_apply]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, rotLE_apply]
  refine Prod.ext ?_ ?_ <;> ring

private theorem rotLE_pow_mod (n : ℕ) : rotLE K ^ n = rotLE K ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, rotLE_pow_three, one_pow, mul_one]

theorem rotPow_add (a b : ZMod 3) : rotPow K (a + b) = rotPow K a * rotPow K b := by
  unfold rotPow
  rw [ZMod.val_add, ← pow_add]
  exact (rotLE_pow_mod (a.val + b.val)).symm

theorem rotPow_zero : rotPow K 0 = 1 := by
  simp [rotPow]

private theorem rotPow_one_apply (p : K × K) : rotPow K 1 p = rotLE K p := by
  simp only [rotPow, ZMod.val_one, pow_one]

private theorem rotPow_two_apply (p : K × K) : rotPow K 2 p = rotLE K (rotLE K p) := by
  rw [rotPow, ZMod.val_two_eq_two_mod, show (2 : ℕ) % 3 = 2 by norm_num, pow_two,
    LinearEquiv.mul_apply]

private theorem rotPow_apply_zero (k : ZMod 3) : rotPow K k (0 : K × K) = 0 := by
  simp [rotPow]

abbrev ModelSpace (K : Type) [Field K] := (Fin 3 → K × K) × (K × K)

@[expose] def planeVec (i : Fin 3) (p : K × K) : ModelSpace K := (Pi.single i p, 0)

private theorem planeVec_injective (i : Fin 3) : Function.Injective (planeVec (K := K) i) := by
  intro p q h
  have := congrArg (fun x => x.1 i) h
  simpa [planeVec] using this

@[expose] def wVec (p : K × K) : ModelSpace K := (0, p)

@[expose] def cmEquiv (K : Type) [Field K] (v : Fin 3 → ZMod 3) :
    ModelSpace K ≃ₗ[K] ModelSpace K :=
  (LinearEquiv.piCongrRight fun i => rotPow K (v i)).prodCongr (LinearEquiv.refl K (K × K))

theorem cmEquiv_apply (v : Fin 3 → ZMod 3) (x : ModelSpace K) :
    cmEquiv K v x = (fun i => rotPow K (v i) (x.1 i), x.2) :=
  rfl

private theorem cmEquiv_fst_apply (v : Fin 3 → ZMod 3) (x : ModelSpace K) (i : Fin 3) :
    (cmEquiv K v x).1 i = rotPow K (v i) (x.1 i) := rfl

private theorem cmEquiv_snd_apply (v : Fin 3 → ZMod 3) (x : ModelSpace K) :
    (cmEquiv K v x).2 = x.2 := rfl

theorem cmEquiv_apply_wVec (v : Fin 3 → ZMod 3) (p : K × K) : cmEquiv K v (wVec p) = wVec p := by
  refine Prod.ext (funext fun k => ?_) rfl
  simp [cmEquiv_apply, wVec]

theorem cmEquiv_apply_planeVec (v : Fin 3 → ZMod 3) (i : Fin 3) (p : K × K) :
    cmEquiv K v (planeVec i p) = planeVec i (rotPow K (v i) p) := by
  refine Prod.ext (funext fun k => ?_) rfl
  by_cases h : k = i
  · subst h
    simp [cmEquiv_apply, planeVec]
  · simp [cmEquiv_apply, planeVec, Pi.single_apply, h]

theorem cmEquiv_zero : cmEquiv K 0 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  simp [cmEquiv_apply, rotPow_zero]

theorem cmEquiv_add (v w : Fin 3 → ZMod 3) :
    cmEquiv K (v + w) = cmEquiv K v * cmEquiv K w := by
  refine LinearEquiv.ext fun x => ?_
  simp only [cmEquiv_apply, LinearEquiv.mul_apply, Pi.add_apply, rotPow_add]

@[expose] def cm (K : Type) [Field K] :
    Multiplicative (Fin 3 → ZMod 3) →* (ModelSpace K ≃ₗ[K] ModelSpace K) where
  toFun v := cmEquiv K (Multiplicative.toAdd v)
  map_one' := cmEquiv_zero
  map_mul' a b := cmEquiv_add _ _

theorem cm_apply (v : Multiplicative (Fin 3 → ZMod 3)) (x : ModelSpace K) :
    cm K v x = cmEquiv K (Multiplicative.toAdd v) x :=
  rfl

@[expose] noncomputable def rotForm (K : Type) [Field K] : QuadraticForm K (K × K) :=
  binForm (-1) 1

@[expose] def IsSplit (K : Type) [Field K] : Prop := ∃ ω : K, ω ^ 2 + ω + 1 = 0

@[expose] noncomputable def wForm (b c : K) : QuadraticForm K (K × K) :=
  open scoped Classical in if IsSplit K then binForm b c else binForm (-1) 0

@[expose] noncomputable def modelForm (b c : K) : QuadraticForm K (ModelSpace K) :=
  (QuadraticMap.pi fun _ : Fin 3 => rotForm K).prod (wForm b c)

@[expose] noncomputable def modelO (b c : K) : Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K) :=
  TauCeti.QuadraticMap.orthogonalGroup (modelForm b c)

@[expose] noncomputable def modelOmega (b c : K) :
    Subgroup (ModelSpace K ≃ₗ[K] ModelSpace K) :=
  ⁅modelO b c, modelO b c⁆

theorem modelForm_apply (b c : K) (x : ModelSpace K) :
    modelForm b c x = ∑ i, rotForm K (x.1 i) + wForm b c x.2 := by
  rw [modelForm, QuadraticMap.prod_apply, QuadraticMap.pi_apply]

theorem rotForm_rotLE (p : K × K) : rotForm K (rotLE K p) = rotForm K p := by
  simp only [rotForm, binForm_apply, rotLE_apply]
  ring

private theorem rotForm_rotPow (k : ZMod 3) (p : K × K) :
    rotForm K (rotPow K k p) = rotForm K p := by
  unfold rotPow
  have h : ∀ n : ℕ, rotForm K ((rotLE K ^ n) p) = rotForm K p := by
    intro n
    induction n generalizing p with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, LinearEquiv.mul_apply, ih (rotLE K p), rotForm_rotLE]
  exact h k.val

theorem modelForm_cmEquiv (b c : K) (v : Fin 3 → ZMod 3) (x : ModelSpace K) :
    modelForm b c (cmEquiv K v x) = modelForm b c x := by
  rw [modelForm_apply, modelForm_apply, cmEquiv_snd_apply]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [cmEquiv_fst_apply, rotForm_rotPow]

theorem cm_mem_modelO (b c : K) (v : Multiplicative (Fin 3 → ZMod 3)) : cm K v ∈ modelO b c := by
  rw [modelO, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [cm_apply]
  exact modelForm_cmEquiv b c _ x

private theorem zmod_three_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  have hlt := ZMod.val_lt k
  interval_cases h : k.val
  · left; apply ZMod.val_injective 3; simpa [ZMod.val_zero] using h
  · right; left; apply ZMod.val_injective 3; simpa [ZMod.val_one] using h
  · right; right; apply ZMod.val_injective 3
    rw [ZMod.val_two_eq_two_mod]
    norm_num
    exact h

private theorem rotPow_one_zero_eq_self {k : ZMod 3}
    (h : rotPow K k ((1 : K), 0) = ((1 : K), 0)) : k = 0 := by
  rcases zmod_three_cases k with rfl | rfl | rfl
  · rfl
  · exfalso
    have h1 : rotLE K ((1 : K), 0) = ((1 : K), 0) := by rwa [rotPow_one_apply] at h
    have hf : (0 : K) = 1 := by
      simpa [rotLE_apply] using congrArg Prod.fst h1
    exact zero_ne_one hf
  · exfalso
    have h1 : rotLE K (rotLE K ((1 : K), 0)) = ((1 : K), 0) := by rwa [rotPow_two_apply] at h
    have hs : (-1 : K) = 0 := by
      simpa [rotLE_apply] using congrArg Prod.snd h1
    exact one_ne_zero (neg_eq_zero.mp hs)

theorem cm_injective : Function.Injective (cm K) := by
  rw [injective_iff_map_eq_one]
  intro v hv
  apply Multiplicative.toAdd.injective
  funext i
  have h := congrArg (fun e : ModelSpace K ≃ₗ[K] ModelSpace K => e (planeVec i ((1 : K), 0))) hv
  rw [cm_apply, cmEquiv_apply_planeVec] at h
  have h1 : rotPow K (v.toAdd i) ((1 : K), 0) = ((1 : K), 0) :=
    planeVec_injective i (by simpa using h)
  simpa using rotPow_one_zero_eq_self h1

private theorem rotLE_fixed_eq_zero (h3 : (3 : K) ≠ 0) {p : K × K} (hp : rotLE K p = p) :
    p = 0 := by
  have h1 : -p.2 = p.1 := congrArg Prod.fst hp
  have h2 : p.1 - p.2 = p.2 := congrArg Prod.snd hp
  have hz : p.2 = 0 := by
    have : (3 : K) * p.2 = 0 := by linear_combination -h1 - h2
    exact (mul_eq_zero.mp this).resolve_left h3
  have hx : p.1 = 0 := by
    rw [hz, neg_zero] at h1
    exact h1.symm
  exact Prod.ext hx hz

private theorem rotLE_sq_fixed_eq_zero (h3 : (3 : K) ≠ 0) {p : K × K}
    (hp : rotLE K (rotLE K p) = p) : p = 0 := by
  have hfix : rotLE K p = p := by
    have h' : (rotLE K ^ 3) p = rotLE K p := by
      rw [LinearEquiv.pow_apply]
      simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
      exact congrArg (rotLE K) hp
    rw [rotLE_pow_three] at h'
    simpa using h'.symm
  exact rotLE_fixed_eq_zero h3 hfix

private theorem rotPow_fixed_eq_zero (h3 : (3 : K) ≠ 0) {k : ZMod 3} {p : K × K}
    (hk : k ≠ 0) (hp : rotPow K k p = p) : p = 0 := by
  rcases zmod_three_cases k with rfl | rfl | rfl
  · exact absurd rfl hk
  · exact rotLE_fixed_eq_zero h3 (by rwa [rotPow_one_apply] at hp)
  · exact rotLE_sq_fixed_eq_zero h3 (by rwa [rotPow_two_apply] at hp)

theorem cmEquiv_apply_eq_self_iff (h3 : (3 : K) ≠ 0) (v : Fin 3 → ZMod 3) (x : ModelSpace K) :
    cmEquiv K v x = x ↔ ∀ i, v i ≠ 0 → x.1 i = 0 := by
  constructor
  · intro h i hi
    have hcomp : rotPow K (v i) (x.1 i) = x.1 i := by
      simpa [cmEquiv_fst_apply] using congrFun (congrArg Prod.fst h) i
    exact rotPow_fixed_eq_zero h3 hi hcomp
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    simp only [cmEquiv_fst_apply]
    by_cases hi : v i = 0
    · simp [hi, rotPow_zero]
    · rw [h i hi, rotPow_apply_zero]

@[expose] def wExtend (K : Type) [Field K] :
    ((K × K) ≃ₗ[K] (K × K)) →* (ModelSpace K ≃ₗ[K] ModelSpace K) where
  toFun g := (LinearEquiv.refl K (Fin 3 → K × K)).prodCongr g
  map_one' := LinearEquiv.ext fun x => rfl
  map_mul' g h := LinearEquiv.ext fun x => rfl

theorem wExtend_apply (g : (K × K) ≃ₗ[K] (K × K)) (x : ModelSpace K) :
    wExtend K g x = (x.1, g x.2) :=
  rfl

theorem wExtend_apply_wVec (g : (K × K) ≃ₗ[K] (K × K)) (p : K × K) :
    wExtend K g (wVec p) = wVec (g p) :=
  rfl

theorem wExtend_injective : Function.Injective (wExtend K) := fun g h hgh =>
  LinearEquiv.ext fun p => by
    have := congrArg (fun e => (e (wVec p)).2) hgh
    simpa [wExtend_apply, wVec] using this

theorem wExtend_mem_modelO {b c : K} {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (wForm b c)) : wExtend K g ∈ modelO b c := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [modelForm_apply, modelForm_apply, wExtend_apply]
  simp only
  rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem hg]

theorem wExtend_commute_cmEquiv (g : (K × K) ≃ₗ[K] (K × K)) (v : Fin 3 → ZMod 3) :
    Commute (wExtend K g) (cmEquiv K v) :=
  LinearEquiv.ext fun x => rfl

@[expose] def planeExtend (K : Type) [Field K] (i : Fin 3) :
    ((K × K) ≃ₗ[K] (K × K)) →* (ModelSpace K ≃ₗ[K] ModelSpace K) where
  toFun g := (LinearEquiv.piCongrRight (Pi.mulSingle i g)).prodCongr (LinearEquiv.refl K (K × K))
  map_one' := LinearEquiv.ext fun x => by
    refine Prod.ext (funext fun k => ?_) rfl
    simp
  map_mul' g h := LinearEquiv.ext fun x => by
    refine Prod.ext (funext fun k => ?_) rfl
    by_cases hk : k = i
    · subst hk
      simp
    · simp [Pi.mulSingle_apply, hk]

theorem planeExtend_apply (i : Fin 3) (g : (K × K) ≃ₗ[K] (K × K)) (x : ModelSpace K) :
    planeExtend K i g x = (Function.update x.1 i (g (x.1 i)), x.2) := by
  refine Prod.ext (funext fun k => ?_) rfl
  by_cases hk : k = i
  · subst hk
    simp [planeExtend]
  · simp [planeExtend, Pi.mulSingle_apply, hk]

theorem planeExtend_apply_planeVec_self (i : Fin 3) (g : (K × K) ≃ₗ[K] (K × K)) (p : K × K) :
    planeExtend K i g (planeVec i p) = planeVec i (g p) := by
  rw [planeExtend_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  by_cases hk : k = i
  · subst hk
    simp [planeVec]
  · simp [planeVec, Function.update_of_ne hk, Pi.single_apply, hk]

theorem planeExtend_apply_planeVec_of_ne {i j : Fin 3} (hij : j ≠ i) (g : (K × K) ≃ₗ[K] (K × K))
    (p : K × K) : planeExtend K i g (planeVec j p) = planeVec j p := by
  rw [planeExtend_apply]
  refine Prod.ext (funext fun k => ?_) rfl
  by_cases hk : k = i
  · subst hk
    simp [planeVec, Pi.single_apply, hij]
  · simp [planeVec, Function.update_of_ne hk]

theorem planeExtend_injective (i : Fin 3) : Function.Injective (planeExtend K i) := fun g h hgh =>
  LinearEquiv.ext fun p => by
    have := congrArg (fun e => (e (planeVec i p)).1 i) hgh
    simpa [planeExtend_apply, planeVec] using this

theorem planeExtend_mem_modelO {b c : K} (i : Fin 3) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (rotForm K)) :
    planeExtend K i g ∈ modelO b c := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [modelForm_apply, modelForm_apply, planeExtend_apply]
  simp only
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    simp [CFSG.ClassicalGroups.Orthogonal.map_of_mem hg]
  · simp [Function.update_of_ne hk]

theorem planeExtend_commute_cmEquiv (i : Fin 3) {g : (K × K) ≃ₗ[K] (K × K)}
    (hg : Commute g (rotLE K)) (v : Fin 3 → ZMod 3) :
    Commute (planeExtend K i g) (cmEquiv K v) := by
  refine LinearEquiv.ext fun x => Prod.ext (funext fun k => ?_) rfl
  simp only [LinearEquiv.mul_apply, planeExtend_apply, cmEquiv_apply]
  by_cases hk : k = i
  · subst hk
    have hc : Commute g (rotPow K (v k)) := hg.pow_right _
    have := congrArg (fun e => e (x.1 k)) hc.eq
    simpa using this
  · simp [Function.update_of_ne hk]

end CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
