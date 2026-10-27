module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.SymNatMaxSwap
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {n : ℕ}

@[expose] def suppSub (A : Finset (Fin n)) : Subgroup ↥(coreMod n) where
  carrier := {v | ∀ j ∉ A, vcoord v j = 0}
  one_mem' := fun j _ => vcoord_one j
  mul_mem' := fun {u v} hu hv j hj => by rw [vcoord_mul, hu j hj, hv j hj, add_zero]
  inv_mem' := fun {u} hu j hj => by rw [coreMod_inv_eq]; exact hu j hj

theorem coreAct_mem_suppSub {A : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ setStab A)
    {v : ↥(coreMod n)} (hv : v ∈ suppSub A) : coreAct n σ v ∈ suppSub A := by
  intro j hj
  rw [vcoord_coreAct]
  apply hv
  intro h
  apply hj
  have := (mem_setStab.1 hσ (σ⁻¹ j)).2 h
  simpa using this

theorem coreAct_mul_inv_mem_suppSub {A : Finset (Fin n)} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ j ∉ A, σ j = j) (v : ↥(coreMod n)) : coreAct n σ v * v⁻¹ ∈ suppSub A := by
  intro j hj
  have h : σ⁻¹ j = j := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hσ j hj).symm
  rw [vcoord_mul, vcoord_coreAct, h, coreMod_inv_eq]
  exact CharTwo.add_self_eq_zero _

theorem mem_suppSub_of_norm {A : Finset (Fin n)} {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ j ∉ A, σ j = j) {v : ↥(coreMod n)}
    (h : v * coreAct n σ v * coreAct n (σ ^ 2) v = 1) : v ∈ suppSub A := by
  intro j hj
  have h1 : σ⁻¹ j = j := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hσ j hj).symm
  have h2 : (σ ^ 2)⁻¹ j = j := by
    rw [Equiv.Perm.inv_eq_iff_eq, pow_two, Equiv.Perm.mul_apply, hσ j hj, hσ j hj]
  have := congrArg (fun x => vcoord x j) h
  simp only [vcoord_mul, vcoord_coreAct, h1, h2, vcoord_one] at this
  have e : ∀ x : ZMod 2, x + x + x = x := fun x => by
    rw [CharTwo.add_self_eq_zero, zero_add]
  rwa [e] at this

@[expose] def triCyc (p : Fin 3 → Fin n) : Equiv.Perm (Fin n) := cyc (p 0) (p 2) (p 1)

@[expose] def triSet (p : Fin 3 → Fin n) : Finset (Fin n) := Finset.univ.image p

theorem mem_triSet {p : Fin 3 → Fin n} {j : Fin n} : j ∈ triSet p ↔ ∃ i, p i = j := by
  simp [triSet]

variable {p : Fin 3 → Fin n}

theorem triCyc_apply (hp : Function.Injective p) (i : Fin 3) : triCyc p (p i) = p (i + 1) := by
  have h01 : p 0 ≠ p 1 := fun h => by simpa using hp h
  have h02 : p 0 ≠ p 2 := fun h => by simpa using hp h
  have h12 : p 1 ≠ p 2 := fun h => by simpa using hp h
  fin_cases i
  · exact cyc_apply_first h01 h12.symm
  · exact cyc_apply_third _ _ _
  · exact cyc_apply_second h02 h12.symm

theorem triCyc_apply_of_notMem {j : Fin n} (hj : j ∉ triSet p) : triCyc p j = j := by
  rw [mem_triSet] at hj
  push Not at hj
  exact cyc_apply_of_ne (hj 0).symm (hj 2).symm (hj 1).symm

theorem triCyc_isThreeCycle (hp : Function.Injective p) : (triCyc p).IsThreeCycle := by
  have h01 : p 0 ≠ p 1 := fun h => by simpa using hp h
  have h02 : p 0 ≠ p 2 := fun h => by simpa using hp h
  have h12 : p 1 ≠ p 2 := fun h => by simpa using hp h
  exact cyc_isThreeCycle h02 h01 h12.symm

theorem triCyc_pow_three (hp : Function.Injective p) : triCyc p ^ 3 = 1 := by
  rw [← (triCyc_isThreeCycle hp).orderOf]
  exact pow_orderOf_eq_one _

theorem triCyc_ne_one (hp : Function.Injective p) : triCyc p ≠ 1 := by
  intro h
  have := triCyc_apply hp 0
  rw [h] at this
  have h01 : p 0 ≠ p 1 := fun h => by simpa using hp h
  exact h01 (by simpa using this)

theorem triCyc_mem_setStab (hp : Function.Injective p) : triCyc p ∈ setStab (triSet p) := by
  rw [mem_setStab]
  intro j
  by_cases hj : j ∈ triSet p
  · obtain ⟨i, rfl⟩ := mem_triSet.1 hj
    rw [triCyc_apply hp]
    exact ⟨fun _ => hj, fun _ => mem_triSet.2 ⟨_, rfl⟩⟩
  · rw [triCyc_apply_of_notMem hj]

theorem triCyc_inv_apply (hp : Function.Injective p) (i : Fin 3) :
    (triCyc p)⁻¹ (p (i + 1)) = p i := by
  rw [Equiv.Perm.inv_eq_iff_eq, triCyc_apply hp]

theorem sum_coords_of_mem_suppSub (hp : Function.Injective p) {v : ↥(coreMod n)}
    (hv : v ∈ suppSub (triSet p)) : ∑ i : Fin 3, vcoord v (p i) = 0 := by
  have h1 := sum_vcoord v
  rw [← Finset.sum_subset (Finset.subset_univ (triSet p)) (fun j _ hj => hv j hj),
    triSet, Finset.sum_image (fun i _ i' _ h => hp h)] at h1
  exact h1

theorem eq_one_of_coreAct_triCyc_eq (hp : Function.Injective p) {v : ↥(coreMod n)}
    (hv : v ∈ suppSub (triSet p)) (h : coreAct n (triCyc p) v = v) : v = 1 := by
  have hc : ∀ i : Fin 3, vcoord v (p (i + 1)) = vcoord v (p i) := by
    intro i
    have := congrArg (fun x => vcoord x (p (i + 1))) h
    simp only [vcoord_coreAct, triCyc_inv_apply hp] at this
    exact this.symm
  have h01 : vcoord v (p 1) = vcoord v (p 0) := hc 0
  have h12 : vcoord v (p 2) = vcoord v (p 1) := hc 1
  have hs := sum_coords_of_mem_suppSub hp hv
  rw [Fin.sum_univ_three, h12, h01] at hs
  have h3 : vcoord v (p 0) = 0 := by
    have e : ∀ x : ZMod 2, x + x + x = x := fun x => by
      rw [CharTwo.add_self_eq_zero, zero_add]
    rwa [e] at hs
  apply vcoord_ext
  intro j
  rw [vcoord_one]
  by_cases hj : j ∈ triSet p
  · obtain ⟨i, rfl⟩ := mem_triSet.1 hj
    fin_cases i
    · exact h3
    · simpa [h01] using h3
    · simpa [h12, h01] using h3
  · exact hv j hj

theorem exists_suppSub_of_coords (hp : Function.Injective p) (f : Fin 3 → ZMod 2)
    (hf : ∑ i, f i = 0) : ∃ u ∈ suppSub (triSet p), ∀ i, vcoord u (p i) = f i := by
  classical
  let g : Fin n → ZMod 2 := fun j => ∑ i : Fin 3, if j = p i then f i else 0
  have hg : ∑ j, g j = 0 := by
    simp only [g]
    rw [Finset.sum_comm]
    simp [hf]
  refine ⟨mkEven g hg, fun j hj => ?_, fun k => ?_⟩
  · rw [vcoord_mkEven]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mem_triSet] at hj
    push Not at hj
    simp [(hj i).symm]
  · rw [vcoord_mkEven]
    simp only [g]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik
      simp [hp.ne hik.symm]
    · simp

theorem eq_of_coords_eq {u v : ↥(coreMod n)} (hu : u ∈ suppSub (triSet p))
    (hv : v ∈ suppSub (triSet p)) (h : ∀ i, vcoord u (p i) = vcoord v (p i)) : u = v := by
  apply vcoord_ext
  intro j
  by_cases hj : j ∈ triSet p
  · obtain ⟨i, rfl⟩ := mem_triSet.1 hj
    exact h i
  · rw [hu j hj, hv j hj]

theorem exists_coreAct_triCyc_mul_inv (hp : Function.Injective p) {w : ↥(coreMod n)}
    (hw : w ∈ suppSub (triSet p)) :
    ∃ u ∈ suppSub (triSet p), coreAct n (triCyc p) u * u⁻¹ = w := by
  have hfin : ∀ w0 w1 w2 : ZMod 2, w0 + w1 + w2 = 0 → ∃ u0 u1 u2 : ZMod 2,
      u0 + u1 + u2 = 0 ∧ u0 + u1 = w1 ∧ u1 + u2 = w2 ∧ u2 + u0 = w0 := by decide
  have hs := sum_coords_of_mem_suppSub hp hw
  rw [Fin.sum_univ_three] at hs
  obtain ⟨u0, u1, u2, hu, h01, h12, h20⟩ := hfin _ _ _ hs
  obtain ⟨u, hu', hcoord⟩ := exists_suppSub_of_coords hp ![u0, u1, u2] (by
    rw [Fin.sum_univ_three]
    simpa using hu)
  refine ⟨u, hu', ?_⟩
  apply vcoord_ext
  intro j
  by_cases hj : j ∈ triSet p
  · obtain ⟨i, rfl⟩ := mem_triSet.1 hj
    rw [vcoord_mul, vcoord_coreAct, coreMod_inv_eq]
    fin_cases i
    · have := triCyc_inv_apply hp 2
      have e : ((2 : Fin 3) + 1) = 0 := rfl
      rw [e] at this
      simp only [Fin.zero_eta, Fin.isValue]
      rw [this, hcoord, hcoord]
      simpa using h20
    · have := triCyc_inv_apply hp 0
      have e : ((0 : Fin 3) + 1) = 1 := rfl
      rw [e] at this
      simp only [Fin.mk_one, Fin.isValue]
      rw [this, hcoord, hcoord]
      simpa using h01
    · have := triCyc_inv_apply hp 1
      have e : ((1 : Fin 3) + 1) = 2 := rfl
      rw [e] at this
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [this, hcoord, hcoord]
      simpa using h12
  · have h1 := coreAct_mul_inv_mem_suppSub (A := triSet p) (σ := triCyc p)
      (fun j hj => triCyc_apply_of_notMem hj) u
    rw [h1 j hj, hw j hj]

@[expose] noncomputable def coordHom (hp : Function.Injective p) :
    ↥(suppSub (triSet p)) →* ↥(coreMod 3) where
  toFun v := mkEven (fun i => vcoord (v : ↥(coreMod n)) (p i)) (sum_coords_of_mem_suppSub hp v.2)
  map_one' := by
    apply vcoord_ext
    intro i
    rw [vcoord_mkEven]
    exact vcoord_one _
  map_mul' u v := by
    apply vcoord_ext
    intro i
    rw [vcoord_mul, vcoord_mkEven, vcoord_mkEven, vcoord_mkEven]
    exact vcoord_mul _ _ _

theorem vcoord_coordHom (hp : Function.Injective p) (v : ↥(suppSub (triSet p))) (i : Fin 3) :
    vcoord (coordHom hp v) i = vcoord (v : ↥(coreMod n)) (p i) := rfl

theorem coordHom_bijective (hp : Function.Injective p) : Function.Bijective (coordHom hp) := by
  refine ⟨fun u v h => ?_, fun v => ?_⟩
  · apply Subtype.ext
    apply eq_of_coords_eq u.2 v.2
    intro i
    rw [← vcoord_coordHom hp u, ← vcoord_coordHom hp v, h]
  · obtain ⟨u, hu, hcoord⟩ := exists_suppSub_of_coords hp (fun i => vcoord v i) (sum_vcoord v)
    refine ⟨⟨u, hu⟩, ?_⟩
    apply vcoord_ext
    intro i
    rw [vcoord_coordHom]
    exact hcoord i

theorem coordHom_coreAct (hp : Function.Injective p) {σ : Equiv.Perm (Fin n)}
    {τ : Equiv.Perm (Fin 3)} (h : ∀ i, σ (p i) = p (τ i)) (v : ↥(suppSub (triSet p)))
    (hv : coreAct n σ (v : ↥(coreMod n)) ∈ suppSub (triSet p)) :
    coordHom hp ⟨coreAct n σ (v : ↥(coreMod n)), hv⟩ = coreAct 3 τ (coordHom hp v) := by
  apply vcoord_ext
  intro i
  rw [vcoord_coordHom, vcoord_coreAct, vcoord_coreAct, vcoord_coordHom]
  have : σ⁻¹ (p i) = p (τ⁻¹ i) := by
    rw [Equiv.Perm.inv_eq_iff_eq, h]
    simp
  rw [this]

theorem pairVec_mem_suppSub {a b : Fin n} (ha : a ∈ triSet p) (hb : b ∈ triSet p) :
    pairVec a b ∈ suppSub (triSet p) := by
  intro j hj
  rw [vcoord_pairVec]
  have h1 : j ≠ a := fun h => hj (h ▸ ha)
  have h2 : j ≠ b := fun h => hj (h ▸ hb)
  simp [h1, h2]

theorem p_mem_triSet (i : Fin 3) : p i ∈ triSet p := mem_triSet.2 ⟨i, rfl⟩

theorem eq_one_or_pairVec (hp : Function.Injective p) {v : ↥(coreMod n)}
    (hv : v ∈ suppSub (triSet p)) : v = 1 ∨ v = pairVec (p 0) (p 1) ∨ v = pairVec (p 1) (p 2) ∨
      v = pairVec (p 0) (p 2) := by
  have hs := sum_coords_of_mem_suppSub hp hv
  rw [Fin.sum_univ_three] at hs
  have hfin : ∀ a b c : ZMod 2, a + b + c = 0 → (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 0) ∨
      (a = 0 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1) := by decide
  have hmem : ∀ a b : Fin 3, pairVec (p a) (p b) ∈ suppSub (triSet p) := fun a b =>
    pairVec_mem_suppSub (p_mem_triSet a) (p_mem_triSet b)
  have hc : ∀ a b i : Fin 3, vcoord (pairVec (p a) (p b)) (p i) =
      (if i = a then 1 else 0) + (if i = b then 1 else 0) := by
    intro a b i
    rw [vcoord_pairVec]
    simp [hp.eq_iff]
  rcases hfin _ _ _ hs with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · left
    apply eq_of_coords_eq hv (suppSub (triSet p)).one_mem
    intro i
    rw [vcoord_one]
    fin_cases i <;> assumption
  · right; left
    apply eq_of_coords_eq hv (hmem 0 1)
    intro i
    rw [hc]
    fin_cases i <;> simp [*]
  · right; right; left
    apply eq_of_coords_eq hv (hmem 1 2)
    intro i
    rw [hc]
    fin_cases i <;> simp [*]
  · right; right; right
    apply eq_of_coords_eq hv (hmem 0 2)
    intro i
    rw [hc]
    fin_cases i <;> simp [*]

theorem swap_mul_triCyc_mul_swap (hp : Function.Injective p) :
    Equiv.swap (p 0) (p 2) * triCyc p * Equiv.swap (p 0) (p 2) = (triCyc p)⁻¹ := by
  have h01 : p 0 ≠ p 1 := fun h => by simpa using hp h
  have h02 : p 0 ≠ p 2 := fun h => by simpa using hp h
  have h12 : p 1 ≠ p 2 := fun h => by simpa using hp h
  have h := conj_cyc (Equiv.swap (p 0) (p 2)) (p 0) (p 2) (p 1)
  rw [Equiv.swap_inv] at h
  rw [triCyc, h, Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne h01.symm h12, cyc_inv]
  exact cyc_swap12 h02 h01 h12.symm

end CFSG.CGT.PushingUpLit.BHS6
