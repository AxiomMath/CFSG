module

public import CFSG.LieType.Universal.Spin.Chevalley.ShortRankOne
import TauCeti.LinearAlgebra.CliffordAlgebra.PBW

public section

namespace CFSG.LieType.Universal.Spin

open CliffordAlgebra QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ}

theorem ι_mul_prod_map_ι_eq_zero {v : V} (hv : Q v = 0) :
    ∀ {L : List V}, v ∈ L → (∀ w ∈ L, polar Q v w = 0) → ι Q v * (L.map (ι Q)).prod = 0
  | [], h, _ => absurd h (List.not_mem_nil)
  | w :: L, h, hL => by
    rw [List.map_cons, List.prod_cons]
    by_cases hw : v = w
    · subst hw
      exact ι_mul_ι_mul_eq_zero Q hv _
    · have hvL : v ∈ L := (List.mem_cons.mp h).resolve_left hw
      rw [← mul_assoc, ι_mul_ι_eq_neg_of_polar_eq_zero Q (hL w List.mem_cons_self), neg_mul,
        mul_assoc, ι_mul_prod_map_ι_eq_zero hv hvL fun w' hw' => hL w' (List.mem_cons_of_mem _ hw'),
        mul_zero, neg_zero]

namespace HypFrame

variable (F : HypFrame Q n)

@[expose] noncomputable def testElt (σ : Fin n → Bool) : CliffordAlgebra Q :=
  (List.ofFn fun m => ι Q (F.vec m (σ m))).prod

theorem testElt_ne_zero (σ : Fin n → Bool) : F.testElt σ ≠ 0 :=
  prod_map_ι_ofFn_ne_zero Q (fun m => F.vec m (σ m)) (F.linearIndependent_vec σ)

theorem ι_vec_mul_testElt (σ : Fin n → Bool) (m : Fin n) :
    ι Q (F.vec m (σ m)) * F.testElt σ = 0 := by
  have h : (List.ofFn fun m => ι Q (F.vec m (σ m))) =
      (List.ofFn fun m => F.vec m (σ m)).map (ι Q) := by
    rw [List.map_ofFn]
    rfl
  rw [testElt, h]
  refine ι_mul_prod_map_ι_eq_zero (F.map_vec m (σ m)) (List.mem_ofFn.mpr ⟨m, rfl⟩) ?_
  intro w hw
  obtain ⟨m', rfl⟩ := List.mem_ofFn.mp hw
  by_cases hm : m = m'
  · subst hm
    exact F.polar_vec_self m (σ m)
  · exact F.polar_vec_of_ne hm _ _

theorem longRoot_mul_testElt {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K)
    {σ : Fin n → Bool} (hσ : σ j = t) :
    (F.longRoot hij s t (.ofAdd c) : CliffordAlgebra Q) * F.testElt σ = F.testElt σ := by
  rw [coe_longRoot, add_mul, one_mul, smul_mul_assoc, mul_assoc, ← hσ, F.ι_vec_mul_testElt,
    mul_zero, smul_zero, add_zero]

theorem longWeyl_mul_testElt {i j : Fin n} (hij : i ≠ j) (s t : Bool) {σ : Fin n → Bool}
    (hσi : σ i = !s) (hσj : σ j = t) :
    (F.longWeyl hij s t : CliffordAlgebra Q) * F.testElt σ = F.testElt σ := by
  rw [longWeyl_eq, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, mul_assoc,
    F.longRoot_mul_testElt hij s t 1 hσj, F.longRoot_mul_testElt hij.symm (!t) (!s) (-1) hσi,
    F.longRoot_mul_testElt hij s t 1 hσj]

theorem polar_sub_sum_vec (v : V) (m : Fin n) (r : Bool) :
    polar Q (v - ∑ m', ∑ r', polar Q v (F.vec m' (!r')) • F.vec m' r') (F.vec m r) = 0 := by
  have h : polar Q (∑ m', ∑ r', polar Q v (F.vec m' (!r')) • F.vec m' r') (F.vec m r) =
      polar Q v (F.vec m r) := by
    rw [← polarBilin_apply_apply]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      polarBilin_apply_apply, smul_eq_mul]
    rw [Finset.sum_eq_single m]
    · rw [Fintype.sum_bool]
      rcases Bool.eq_or_eq_not r true with rfl | rfl
      · simp [polar_vec_vec]
      · simp [polar_vec_vec]
    · intro m' _ hm'
      simp [F.polar_vec_of_ne hm']
    · intro h
      exact absurd (Finset.mem_univ m) h
  rw [polar_sub_left, h, sub_self]

theorem spinAction_eq_of_vec {g h : spinGroup Q}
    (hvec : ∀ m r, spinAction Q g (F.vec m r) = spinAction Q h (F.vec m r))
    (hg : ∀ v, (∀ m r, polar Q v (F.vec m r) = 0) → spinAction Q g v = v)
    (hh : ∀ v, (∀ m r, polar Q v (F.vec m r) = 0) → spinAction Q h v = v) :
    spinAction Q g = spinAction Q h := by
  ext v
  have h0 := F.polar_sub_sum_vec v
  rw [← sub_add_cancel v (∑ m', ∑ r', polar Q v (F.vec m' (!r')) • F.vec m' r'), map_add, map_add,
    hg _ h0, hh _ h0]
  simp only [map_sum, map_smul, hvec]

theorem spinAction_longWeyl_of_orth {i j : Fin n} (hij : i ≠ j) (s t : Bool) {v : V}
    (hv : ∀ m r, polar Q v (F.vec m r) = 0) : spinAction Q (F.longWeyl hij s t) v = v :=
  F.spinAction_longWeyl_of_polar hij s t (hv i) (hv j)

theorem spinAction_longWeyl_braid_vec {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l)
    (s t u : Bool) (m : Fin n) (r : Bool) :
    spinAction Q (F.longWeyl hij s t * F.longWeyl hjl (!t) u * F.longWeyl hij s t) (F.vec m r) =
      spinAction Q (F.longWeyl hjl (!t) u * F.longWeyl hij s t * F.longWeyl hjl (!t) u)
        (F.vec m r) := by
  simp only [map_mul, LinearEquiv.mul_apply, map_smul, spinAction_longWeyl_vec, smul_smul]
  by_cases hmi : m = i
  · subst hmi
    simp [Equiv.swap_apply_of_ne_of_ne, longWeylSign, longWeylBool, hij, hjl, hil, Ne.symm hjl,
      Ne.symm hil]
  · by_cases hmj : m = j
    · subst hmj
      simp [Equiv.swap_apply_of_ne_of_ne, longWeylSign, longWeylBool, hij, hil, Ne.symm hij,
        Ne.symm hjl, Ne.symm hil]
    · by_cases hml : m = l
      · subst hml
        simp [Equiv.swap_apply_of_ne_of_ne, longWeylSign, longWeylBool, hij, hil, Ne.symm hij,
          Ne.symm hjl, Ne.symm hil]
      · simp [Equiv.swap_apply_of_ne_of_ne, longWeylSign, longWeylBool, hmi, hmj, hml]

theorem longWeyl_braid {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) (s t u : Bool)
    (hker : ∀ g : spinGroup Q, spinAction Q g = 1 →
      (g : CliffordAlgebra Q) = 1 ∨ (g : CliffordAlgebra Q) = -1) :
    F.longWeyl hij s t * F.longWeyl hjl (!t) u * F.longWeyl hij s t =
      F.longWeyl hjl (!t) u * F.longWeyl hij s t * F.longWeyl hjl (!t) u := by
  set A := F.longWeyl hij s t
  set B := F.longWeyl hjl (!t) u
  have hact : spinAction Q (A * B * A) = spinAction Q (B * A * B) := by
    refine F.spinAction_eq_of_vec (F.spinAction_longWeyl_braid_vec hij hjl hil s t u) ?_ ?_
    · intro v hv
      simp only [map_mul, LinearEquiv.mul_apply, A, B, F.spinAction_longWeyl_of_orth _ _ _ hv]
    · intro v hv
      simp only [map_mul, LinearEquiv.mul_apply, A, B, F.spinAction_longWeyl_of_orth _ _ _ hv]
  have hε : spinAction Q (A * B * A * (B * A * B)⁻¹) = 1 := by
    rw [map_mul, hact, map_inv, mul_inv_cancel]
  set σ : Fin n → Bool := fun m => if m = i then !s else if m = j then t else u
  have hσi : σ i = !s := by simp [σ]
  have hσj : σ j = t := by simp [σ, Ne.symm hij]
  have hσl : σ l = u := by simp [σ, Ne.symm hil, Ne.symm hjl]
  have hA : (A : CliffordAlgebra Q) * F.testElt σ = F.testElt σ :=
    F.longWeyl_mul_testElt hij s t hσi hσj
  have hB : (B : CliffordAlgebra Q) * F.testElt σ = F.testElt σ :=
    F.longWeyl_mul_testElt hjl (!t) u (by rw [hσj, Bool.not_not]) hσl
  have hR : ((B * A * B : spinGroup Q) : CliffordAlgebra Q) * F.testElt σ = F.testElt σ := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, mul_assoc, hB, hA, hB]
  have hL : ((A * B * A : spinGroup Q) : CliffordAlgebra Q) * F.testElt σ = F.testElt σ := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, mul_assoc, hA, hB, hA]
  have hRinv : (((B * A * B)⁻¹ : spinGroup Q) : CliffordAlgebra Q) * F.testElt σ =
      F.testElt σ := by
    conv_lhs => rw [← hR]
    rw [← mul_assoc, coe_inv_mul_coe, one_mul]
  have hεT : ((A * B * A * (B * A * B)⁻¹ : spinGroup Q) : CliffordAlgebra Q) * F.testElt σ =
      F.testElt σ := by
    rw [Submonoid.coe_mul, mul_assoc, hRinv, hL]
  have hε1 : A * B * A * (B * A * B)⁻¹ = 1 := by
    rcases hker _ hε with h | h
    · exact Subtype.ext h
    · rw [h, neg_one_mul] at hεT
      have h2 : (2 : K) • F.testElt σ = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← hεT]
        exact neg_add_cancel _
      have h20 : (2 : K) = 0 := by
        by_contra h20
        exact F.testElt_ne_zero σ ((smul_eq_zero.mp h2).resolve_left h20)
      apply Subtype.ext
      rw [h, Submonoid.coe_one]
      have h2' : (2 : CliffordAlgebra Q) = 0 := by
        rw [← map_ofNat (algebraMap K (CliffordAlgebra Q)) 2, h20, map_zero]
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2']
  exact mul_inv_eq_one.mp hε1

theorem commute_longWeyl_of_commute {i j : Fin n} (hij : i ≠ j) (s t : Bool) {g : spinGroup Q}
    (h₁ : ∀ c : K, Commute (F.longRoot hij s t (.ofAdd c)) g)
    (h₂ : ∀ c : K, Commute (F.longRoot hij.symm (!t) (!s) (.ofAdd c)) g) :
    Commute (F.longWeyl hij s t) g := by
  rw [longWeyl_eq]
  exact ((h₁ 1).mul_left (h₂ (-1))).mul_left (h₁ 1)

theorem commute_longWeyl_longWeyl_of_disjoint {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (s t u v : Bool) :
    Commute (F.longWeyl hij s t) (F.longWeyl hkl u v) := by
  have key : ∀ (s' t' : Bool) (c : K), Commute (F.longRoot hij s' t' (.ofAdd c))
      (F.longWeyl hkl u v) := fun s' t' c => by
    refine (F.commute_longWeyl_of_commute hkl u v (fun d => ?_) (fun d => ?_)).symm
    · exact (F.commute_longRoot_longRoot_of_disjoint hij hkl hik hil hjk hjl s' t' u v c d).symm
    · exact (F.commute_longRoot_longRoot_of_disjoint hij hkl.symm hil hik hjl hjk s' t' _ _ c
        d).symm
  have key' : ∀ (s' t' : Bool) (c : K), Commute (F.longRoot hij.symm s' t' (.ofAdd c))
      (F.longWeyl hkl u v) := fun s' t' c => by
    rw [longRoot_swap]
    exact key t' s' (-c)
  exact F.commute_longWeyl_of_commute hij s t (key s t) (key' _ _)

theorem commute_longWeyl_longWeyl_flip {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    Commute (F.longWeyl hij s t) (F.longWeyl hij s (!t)) := by
  have h1 : ∀ c d : K, Commute (F.longRoot hij s t (.ofAdd c)) (F.longRoot hij s (!t) (.ofAdd d)) :=
    fun c d => F.commute_longRoot_longRoot_left hij hij s t (!t) c d
  have h2 : ∀ c d : K, Commute (F.longRoot hij s t (.ofAdd c))
      (F.longRoot hij.symm (!(!t)) (!s) (.ofAdd d)) := fun c d => by
    rw [Bool.not_not, F.longRoot_swap hij.symm t (!s) d]
    exact F.commute_longRoot_longRoot_right hij hij s t (!s) c (-d)
  have h3 : ∀ c d : K, Commute (F.longRoot hij.symm (!t) (!s) (.ofAdd c))
      (F.longRoot hij s (!t) (.ofAdd d)) := fun c d => by
    rw [F.longRoot_swap hij s (!t)]
    exact F.commute_longRoot_longRoot_left hij.symm hij.symm (!t) (!s) s c (-d)
  have h4 : ∀ c d : K, Commute (F.longRoot hij.symm (!t) (!s) (.ofAdd c))
      (F.longRoot hij.symm (!(!t)) (!s) (.ofAdd d)) := fun c d => by
    rw [Bool.not_not]
    exact F.commute_longRoot_longRoot_right hij.symm hij.symm (!t) (!s) t c d
  refine F.commute_longWeyl_of_commute hij s t (fun c => ?_) (fun c => ?_)
  · exact (F.commute_longWeyl_of_commute hij s (!t) (fun d => (h1 c d).symm)
      (fun d => (h2 c d).symm)).symm
  · exact (F.commute_longWeyl_of_commute hij s (!t) (fun d => (h3 c d).symm)
      (fun d => (h4 c d).symm)).symm

end HypFrame

namespace OddFrame

variable (F : OddFrame Q n)

theorem commute_shortWeyl_of_commute (i : Fin n) (s : Bool) {g : spinGroup Q}
    (h₁ : ∀ c : K, Commute (F.shortRoot i s (.ofAdd c)) g)
    (h₂ : ∀ c : K, Commute (F.shortRoot i (!s) (.ofAdd c)) g) :
    Commute (F.shortWeyl i s) g := by
  rw [shortWeyl_eq]
  exact ((h₁ 1).mul_left (h₂ 1)).mul_left (h₁ 1)

theorem commute_longWeyl_shortWeyl_of_ne {i j k : Fin n} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (s t u : Bool) : Commute (F.longWeyl hij s t) (F.shortWeyl k u) := by
  refine F.commute_longWeyl_of_commute hij s t (fun c => ?_) (fun c => ?_)
  · exact (F.commute_shortWeyl_of_commute k u
      (fun d => (F.commute_longRoot_shortRoot_of_ne hij hki hkj s t u c d).symm)
      (fun d => (F.commute_longRoot_shortRoot_of_ne hij hki hkj s t (!u) c d).symm)).symm
  · exact (F.commute_shortWeyl_of_commute k u
      (fun d => (F.commute_longRoot_shortRoot_of_ne hij.symm hkj hki _ _ u c d).symm)
      (fun d => (F.commute_longRoot_shortRoot_of_ne hij.symm hkj hki _ _ (!u) c d).symm)).symm

theorem longWeyl_shortWeyl_braid {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longWeyl hij s t * F.shortWeyl j (!t) * F.longWeyl hij s t * F.shortWeyl j (!t) =
      F.shortWeyl j (!t) * F.longWeyl hij s t * F.shortWeyl j (!t) * F.longWeyl hij s t := by
  have hB : (F.shortWeyl j (!t) : CliffordAlgebra Q) =
      ι Q F.z * ι Q (F.vec j (!t) + F.vec j t) := by
    rw [coe_shortWeyl, Bool.not_not]
  have hAz : spinAction Q (F.longWeyl hij s t) F.z = F.z :=
    F.spinAction_longWeyl_of_polar hij s t (fun r => F.polar_z_vec i r)
      (fun r => F.polar_z_vec j r)
  have hAw : spinAction Q (F.longWeyl hij s t) (F.vec j (!t) + F.vec j t) =
      F.vec i s + F.vec i (!s) := by
    rw [map_add, HypFrame.spinAction_longWeyl_vec_right_not, HypFrame.spinAction_longWeyl_vec_right]
  have hm : ((F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹ :
      spinGroup Q) : CliffordAlgebra Q) = ι Q F.z * ι Q (F.vec i s + F.vec i (!s)) := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, hB, coe_mul_ι_mul_ι_mul_coe_inv, hAz, hAw]
  have hhz : spinAction Q (F.longWeyl hij s t * F.longWeyl hij s t) F.z = F.z := by
    rw [F.longWeyl_mul_self, HypFrame.spinAction_longTorus]
    simp
  have hhw : spinAction Q (F.longWeyl hij s t * F.longWeyl hij s t) (F.vec j (!t) + F.vec j t) =
      -(F.vec j (!t) + F.vec j t) := by
    rw [F.longWeyl_mul_self, map_add, HypFrame.spinAction_longTorus_vec,
      HypFrame.spinAction_longTorus_vec]
    simp [longCoroot, Ne.symm hij]
    abel
  have hhB : ((F.longWeyl hij s t * F.longWeyl hij s t : spinGroup Q) : CliffordAlgebra Q) *
      F.shortWeyl j (!t) = -((F.shortWeyl j (!t) : CliffordAlgebra Q) *
        (F.longWeyl hij s t * F.longWeyl hij s t : spinGroup Q)) := by
    refine coe_mul_eq_neg_of_conj Q ?_
    rw [hB, coe_mul_ι_mul_ι_mul_coe_inv, hhz, hhw, map_neg, mul_neg]
  have hmB : ((F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹ :
      spinGroup Q) : CliffordAlgebra Q) * F.shortWeyl j (!t) =
      -((F.shortWeyl j (!t) : CliffordAlgebra Q) *
        (F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹ : spinGroup Q)) := by
    have hww' : polar Q (F.vec i s + F.vec i (!s)) (F.vec j (!t) + F.vec j t) = 0 := by
      simp only [polar_add_left, polar_add_right, F.polar_vec_of_ne hij, add_zero]
    rw [hm, hB, ι_mul_ι_mul_ι_mul_ι_eq_neg Q F.map_z (by simp),
      ι_mul_ι_mul_ι_mul_ι_eq_neg Q F.map_z (by simp),
      ι_mul_ι_eq_neg_of_polar_eq_zero Q hww']
  have hL : F.longWeyl hij s t * F.shortWeyl j (!t) * F.longWeyl hij s t * F.shortWeyl j (!t) =
      F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹ *
        (F.longWeyl hij s t * F.longWeyl hij s t) * F.shortWeyl j (!t) := by group
  have hR : F.shortWeyl j (!t) * F.longWeyl hij s t * F.shortWeyl j (!t) * F.longWeyl hij s t =
      F.shortWeyl j (!t) * (F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹) *
        (F.longWeyl hij s t * F.longWeyl hij s t) := by group
  rw [hL, hR]
  generalize F.longWeyl hij s t * F.shortWeyl j (!t) * (F.longWeyl hij s t)⁻¹ = m at hmB ⊢
  generalize F.longWeyl hij s t * F.longWeyl hij s t = h at hhB ⊢
  generalize F.shortWeyl j (!t) = b at hmB hhB ⊢
  apply Subtype.ext
  simp only [Submonoid.coe_mul]
  calc (m : CliffordAlgebra Q) * h * b = m * (h * b) := mul_assoc _ _ _
    _ = -(m * b * h) := by rw [hhB, mul_neg, mul_assoc]
    _ = b * m * h := by rw [hmB, neg_mul, neg_neg]

end OddFrame

end CFSG.LieType.Universal.Spin
