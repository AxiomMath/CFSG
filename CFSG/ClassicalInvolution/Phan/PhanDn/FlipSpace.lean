module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LieType.BorelTits.UnitaryForm
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def dFlip (σ : K ≃+* K) (v : Fin n ⊕ Fin n → K) : Fin n ⊕ Fin n → K :=
  fun x => match x with
    | .inl i => σ (v (.inr i))
    | .inr i => σ (v (.inl i))

@[simp] theorem dFlip_apply_inl (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    dFlip σ v (.inl i) = σ (v (.inr i)) := rfl

@[simp] theorem dFlip_apply_inr (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    dFlip σ v (.inr i) = σ (v (.inl i)) := rfl

theorem dFlip_add (u v : Fin n ⊕ Fin n → K) : dFlip σ (u + v) = dFlip σ u + dFlip σ v := by
  ext x; cases x <;> simp [dFlip]

theorem dFlip_smul (a : K) (v : Fin n ⊕ Fin n → K) : dFlip σ (a • v) = σ a • dFlip σ v := by
  ext x; cases x <;> simp [dFlip]

theorem dFlip_dFlip (hσ : ∀ x, σ (σ x) = x) (v : Fin n ⊕ Fin n → K) : dFlip σ (dFlip σ v) = v := by
  ext x; cases x <;> simp [dFlip, hσ]

theorem quadPlus_dFlip (v : Fin n ⊕ Fin n → K) :
    quadPlus n K (dFlip σ v) = σ (quadPlus n K v) := by
  rw [quadPlus_apply, quadPlus_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dFlip_apply_inl, dFlip_apply_inr, map_mul]
  ring

theorem polar_dFlip (u v : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (dFlip σ u) (dFlip σ v) = σ (polar (quadPlus n K) u v) := by
  rw [polar_quadPlus, polar_quadPlus, map_sum]
  simp only [map_add, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dFlip_apply_inl, dFlip_apply_inr, dFlip_apply_inl, dFlip_apply_inr]
  ring

@[expose] noncomputable def flipHerm (σ : K ≃+* K) (u v : Fin n ⊕ Fin n → K) : K :=
  polar (quadPlus n K) u (dFlip σ v)

theorem flipHerm_apply (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ u v = ∑ i, (u (.inl i) * σ (v (.inl i)) + u (.inr i) * σ (v (.inr i))) := by
  rw [flipHerm, polar_quadPlus]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dFlip_apply_inl, dFlip_apply_inr]
  ring

theorem flipHerm_add_left (u u' v : Fin n ⊕ Fin n → K) :
    flipHerm σ (u + u') v = flipHerm σ u v + flipHerm σ u' v := by
  rw [flipHerm_apply, flipHerm_apply, flipHerm_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem flipHerm_add_right (u v v' : Fin n ⊕ Fin n → K) :
    flipHerm σ u (v + v') = flipHerm σ u v + flipHerm σ u v' := by
  rw [flipHerm_apply, flipHerm_apply, flipHerm_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, map_add]
  ring

theorem flipHerm_smul_left (a : K) (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ (a • u) v = a * flipHerm σ u v := by
  rw [flipHerm_apply, flipHerm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem flipHerm_smul_right (a : K) (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ u (a • v) = σ a * flipHerm σ u v := by
  rw [flipHerm_apply, flipHerm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

@[simp] theorem flipHerm_neg_left (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ (-u) v = -flipHerm σ u v := by
  rw [flipHerm_apply, flipHerm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply, neg_mul]
  ring

@[simp] theorem flipHerm_neg_right (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ u (-v) = -flipHerm σ u v := by
  rw [flipHerm_apply, flipHerm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply, map_neg, mul_neg]
  ring

theorem flipHerm_sub_left (u u' v : Fin n ⊕ Fin n → K) :
    flipHerm σ (u - u') v = flipHerm σ u v - flipHerm σ u' v := by
  rw [sub_eq_add_neg, flipHerm_add_left, flipHerm_neg_left, ← sub_eq_add_neg]

theorem flipHerm_sub_right (u v v' : Fin n ⊕ Fin n → K) :
    flipHerm σ u (v - v') = flipHerm σ u v - flipHerm σ u v' := by
  rw [sub_eq_add_neg, flipHerm_add_right, flipHerm_neg_right, ← sub_eq_add_neg]

@[simp] theorem flipHerm_zero_left (v : Fin n ⊕ Fin n → K) : flipHerm σ 0 v = 0 := by
  rw [flipHerm_apply]; simp

@[simp] theorem flipHerm_zero_right (u : Fin n ⊕ Fin n → K) : flipHerm σ u 0 = 0 := by
  rw [flipHerm_apply]; simp

theorem flipHerm_conj (hσ : ∀ x, σ (σ x) = x) (u v : Fin n ⊕ Fin n → K) :
    σ (flipHerm σ u v) = flipHerm σ v u := by
  rw [flipHerm_apply, flipHerm_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_mul, map_mul, hσ, hσ]
  ring

theorem flipHerm_self_mem_fixed (hσ : ∀ x, σ (σ x) = x) (v : Fin n ⊕ Fin n → K) :
    σ (flipHerm σ v v) = flipHerm σ v v :=
  flipHerm_conj hσ v v

theorem flipHerm_eq_zero_iff (hσ : ∀ x, σ (σ x) = x) {u v : Fin n ⊕ Fin n → K} :
    flipHerm σ u v = 0 ↔ flipHerm σ v u = 0 := by
  constructor
  · intro h
    rw [← flipHerm_conj hσ, h, map_zero]
  · intro h
    rw [← flipHerm_conj hσ] at h
    exact (map_eq_zero_iff σ σ.injective).mp h

theorem flipHerm_dFlip_dFlip (hσ : ∀ x, σ (σ x) = x) (u v : Fin n ⊕ Fin n → K) :
    flipHerm σ (dFlip σ u) (dFlip σ v) = σ (flipHerm σ u v) := by
  rw [flipHerm_apply, flipHerm_apply, map_sum]
  simp only [map_add, map_mul, hσ]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [dFlip_apply_inl, dFlip_apply_inr, hσ]
  ring

@[expose] def stdE (i : Fin n) : Fin n ⊕ Fin n → K := Pi.single (.inl i) 1

@[expose] def stdF (i : Fin n) : Fin n ⊕ Fin n → K := Pi.single (.inr i) 1

@[simp] theorem stdE_inl (i j : Fin n) : stdE (K := K) i (.inl j) = if j = i then 1 else 0 := by
  simp [stdE, Pi.single_apply, eq_comm]

@[simp] theorem stdE_inr (i j : Fin n) : stdE (K := K) i (.inr j) = 0 := by
  simp [stdE]

@[simp] theorem stdF_inl (i j : Fin n) : stdF (K := K) i (.inl j) = 0 := by
  simp [stdF]

@[simp] theorem stdF_inr (i j : Fin n) : stdF (K := K) i (.inr j) = if j = i then 1 else 0 := by
  simp [stdF, Pi.single_apply, eq_comm]

theorem dFlip_stdE (i : Fin n) : dFlip σ (stdE (K := K) i) = stdF (K := K) i := by
  ext x
  cases x <;> simp [dFlip]

theorem dFlip_stdF (i : Fin n) : dFlip σ (stdF (K := K) i) = stdE (K := K) i := by
  ext x
  cases x <;> simp [dFlip]

theorem flipHerm_stdE_stdE (i j : Fin n) :
    flipHerm σ (stdE (K := K) i) (stdE (K := K) j) = if i = j then 1 else 0 := by
  rw [flipHerm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [stdE, hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem flipHerm_stdF_stdF (i j : Fin n) :
    flipHerm σ (stdF (K := K) i) (stdF (K := K) j) = if i = j then 1 else 0 := by
  rw [flipHerm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [stdF, hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem flipHerm_stdE_stdF (i j : Fin n) :
    flipHerm σ (stdE (K := K) i) (stdF (K := K) j) = 0 := by
  rw [flipHerm_apply]
  simp [stdE, stdF]

theorem flipHerm_stdF_stdE (i j : Fin n) :
    flipHerm σ (stdF (K := K) i) (stdE (K := K) j) = 0 := by
  rw [flipHerm_apply]
  simp [stdE, stdF]

theorem flipHerm_stdE_right (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    flipHerm σ u (stdE (K := K) i) = u (.inl i) := by
  rw [flipHerm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [stdE, hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem flipHerm_stdF_right (u : Fin n ⊕ Fin n → K) (i : Fin n) :
    flipHerm σ u (stdF (K := K) i) = u (.inr i) := by
  rw [flipHerm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [stdF, hk]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem eq_zero_of_flipHerm {u : Fin n ⊕ Fin n → K} (h : ∀ v, flipHerm σ u v = 0) : u = 0 := by
  funext x
  cases x with
  | inl i =>
    have := h (stdE (K := K) i)
    rwa [flipHerm_stdE_right] at this
  | inr i =>
    have := h (stdF (K := K) i)
    rwa [flipHerm_stdF_right] at this

theorem quadPlus_stdE (i : Fin n) : quadPlus n K (stdE (K := K) i) = 0 := by
  rw [quadPlus_apply]
  simp [stdE]

theorem quadPlus_stdF (i : Fin n) : quadPlus n K (stdF (K := K) i) = 0 := by
  rw [quadPlus_apply]
  simp [stdF]

theorem polar_stdE_stdF (i j : Fin n) :
    polar (quadPlus n K) (stdE (K := K) i) (stdF (K := K) j) = if i = j then 1 else 0 := by
  rw [polar_quadPlus]
  rw [Finset.sum_eq_single j]
  · simp [eq_comm]
  · intro k _ hk
    simp [stdE, stdF, hk]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

@[expose] def flipOrth (σ : K ≃+* K) (U : Submodule K (Fin n ⊕ Fin n → K)) :
    Submodule K (Fin n ⊕ Fin n → K) where
  carrier := {v | ∀ u ∈ U, flipHerm σ u v = 0}
  zero_mem' u _ := flipHerm_zero_right u
  add_mem' {v w} hv hw u hu := by rw [flipHerm_add_right, hv u hu, hw u hu, add_zero]
  smul_mem' a v hv u hu := by rw [flipHerm_smul_right, hv u hu, mul_zero]

theorem mem_flipOrth {U : Submodule K (Fin n ⊕ Fin n → K)} {v : Fin n ⊕ Fin n → K} :
    v ∈ flipOrth σ U ↔ ∀ u ∈ U, flipHerm σ u v = 0 := Iff.rfl

theorem flipOrth_bot : flipOrth σ (⊥ : Submodule K (Fin n ⊕ Fin n → K)) = ⊤ := by
  ext v
  simp [mem_flipOrth]

theorem flipOrth_sup (U U' : Submodule K (Fin n ⊕ Fin n → K)) :
    flipOrth σ (U ⊔ U') = flipOrth σ U ⊓ flipOrth σ U' := by
  ext v
  constructor
  · intro h
    exact ⟨fun u hu => h u (Submodule.mem_sup_left hu),
      fun u hu => h u (Submodule.mem_sup_right hu)⟩
  · rintro ⟨h1, h2⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [flipHerm_add_left, h1 a ha, h2 b hb, add_zero]

theorem mem_flipOrth_span_singleton {a v : Fin n ⊕ Fin n → K} :
    v ∈ flipOrth σ (K ∙ a) ↔ flipHerm σ a v = 0 := by
  constructor
  · intro h
    exact h a (Submodule.mem_span_singleton_self a)
  · intro h u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [flipHerm_smul_left, h, mul_zero]

theorem span_sup_inf_flipOrth (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} {a : Fin n ⊕ Fin n → K} (haU : a ∈ U)
    (ha : flipHerm σ a a ≠ 0) :
    K ∙ a ⊔ (U ⊓ flipOrth σ (K ∙ a)) = U := by
  apply le_antisymm
  · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr haU) inf_le_left
  · intro v hv
    set c : K := σ (flipHerm σ a v / flipHerm σ a a) with hc
    have hca : flipHerm σ a (c • a) = flipHerm σ a v := by
      rw [flipHerm_smul_right, hc, hσ, div_mul_cancel₀ _ ha]
    have hw : v - c • a ∈ U := Submodule.sub_mem _ hv (Submodule.smul_mem _ _ haU)
    have horth : flipHerm σ a (v - c • a) = 0 := by
      rw [flipHerm_sub_right, hca, sub_self]
    have hmem : v - c • a ∈ flipOrth σ (K ∙ a) :=
      mem_flipOrth_span_singleton.mpr horth
    have hvc : v = c • a + (v - c • a) := by abel
    rw [hvc]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
      (Submodule.mem_span_singleton_self a))) (Submodule.mem_sup_right ⟨hw, hmem⟩)

theorem disjoint_span_flipOrth {a : Fin n ⊕ Fin n → K} (ha : flipHerm σ a a ≠ 0) :
    Disjoint (K ∙ a) (flipOrth σ (K ∙ a)) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have h := mem_flipOrth_span_singleton.mp hv'
  rw [flipHerm_smul_right] at h
  rcases mul_eq_zero.mp h with hc | h
  · rw [(map_eq_zero_iff σ σ.injective).mp hc, zero_smul]
  · exact absurd h ha

structure IsFlipflopSub (σ : K ≃+* K) (U : Submodule K (Fin n ⊕ Fin n → K)) : Prop where
  total : ∀ u ∈ U, quadPlus n K u = 0
  nondeg : ∀ u ∈ U, (∀ v ∈ U, flipHerm σ u v = 0) → u = 0

def IsFlipflopPt (σ : K ≃+* K) (p : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  IsFlipflopSub σ p ∧ Module.finrank K p = 1

theorem IsFlipflopSub.inf_flipOrth_span (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) {a : Fin n ⊕ Fin n → K}
    (haU : a ∈ U) (ha : flipHerm σ a a ≠ 0) :
    IsFlipflopSub σ (U ⊓ flipOrth σ (K ∙ a)) where
  total u hu := hU.total u hu.1
  nondeg u hu hper := by
    refine hU.nondeg u hu.1 fun t ht => ?_
    have hsplit : t ∈ K ∙ a ⊔ (U ⊓ flipOrth σ (K ∙ a)) := by
      rw [span_sup_inf_flipOrth hσ haU ha]
      exact ht
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hsplit
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hua : flipHerm σ u a = 0 := by
      have h := (mem_flipOrth_span_singleton.mp hu.2)
      rw [← flipHerm_conj hσ] at h
      exact (map_eq_zero_iff σ σ.injective).mp h
    rw [flipHerm_add_right, flipHerm_smul_right, hua, mul_zero, zero_add]
    exact hper y hy

theorem exists_anisotropic_of_isFlipflopSub (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) (hne0 : U ≠ ⊥) :
    ∃ v ∈ U, flipHerm σ v v ≠ 0 := by
  by_contra! hcon
  obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
  refine hv0 (hU.nondeg v hvU ?_)
  intro t ht
  obtain ⟨c, hc⟩ := hne
  have h1 : flipHerm σ (t + v) (t + v) = 0 := hcon _ (U.add_mem ht hvU)
  have h2 : flipHerm σ (t + c • v) (t + c • v) = 0 := hcon _ (U.add_mem ht (U.smul_mem c hvU))
  have h1' : flipHerm σ t v + σ (flipHerm σ t v) = 0 := by
    have h := h1
    simp only [flipHerm_add_left, flipHerm_add_right, hcon t ht, hcon v hvU,
      (flipHerm_conj hσ t v).symm, add_zero, zero_add] at h
    linear_combination h
  have h2' : σ c * flipHerm σ t v + c * σ (flipHerm σ t v) = 0 := by
    have h := h2
    rw [flipHerm_add_left t (c • v) (t + c • v),
      flipHerm_add_right t t (c • v), flipHerm_add_right (c • v) t (c • v),
      hcon t ht, hcon (c • v) (U.smul_mem c hvU), flipHerm_smul_right c t v,
      flipHerm_smul_left c v t, (flipHerm_conj hσ t v).symm] at h
    simp only [add_zero, zero_add] at h
    linear_combination h
  have hkey : (c - σ c) * σ (flipHerm σ t v) = 0 := by
    linear_combination h2' - σ c * h1'
  have hcne : c - σ c ≠ 0 := sub_ne_zero.mpr hc.symm
  have hzero : σ (flipHerm σ t v) = 0 := (mul_eq_zero.mp hkey).resolve_left hcne
  exact (flipHerm_eq_zero_iff hσ).mpr ((map_eq_zero_iff σ σ.injective).mp hzero)

theorem inf_flipOrth_eq_bot (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) :
    U ⊓ flipOrth σ U = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  exact hU.nondeg v hv.1 fun w hw => (flipHerm_eq_zero_iff hσ).mpr (hv.2 w hw)

theorem sup_flipOrth_eq_top (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) :
    U ⊔ flipOrth σ U = ⊤ := by
  classical
  have hmain : ∀ (m : ℕ) (U : Submodule K (Fin n ⊕ Fin n → K)),
      Module.finrank K U = m → IsFlipflopSub σ U → U ⊔ flipOrth σ U = ⊤ := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro U hdim hU
      by_cases hbot : U = ⊥
      · subst hbot
        rw [flipOrth_bot, sup_top_eq]
      · obtain ⟨a, haU, ha⟩ := exists_anisotropic_of_isFlipflopSub hσ hne hU hbot
        have ha0 : a ≠ 0 := fun h => ha (by rw [h, flipHerm_zero_right])
        let U' : Submodule K (Fin n ⊕ Fin n → K) := U ⊓ flipOrth σ (K ∙ a)
        have hsplit : K ∙ a ⊔ U' = U := span_sup_inf_flipOrth hσ haU ha
        have hU' : IsFlipflopSub σ U' := hU.inf_flipOrth_span hσ haU ha
        have hdisj : Disjoint (K ∙ a) U' :=
          (disjoint_span_flipOrth ha).mono_right inf_le_right
        have hdimU : Module.finrank K U = Module.finrank K (K ∙ a) + Module.finrank K U' := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ a) U'
          rw [hdisj.eq_bot, finrank_bot, add_zero] at h
          rwa [hsplit] at h
        have hspan1 : Module.finrank K (K ∙ a) = 1 := finrank_span_singleton ha0
        have hdim' : Module.finrank K U' < m := by
          rw [hdim] at hdimU
          omega
        have hIH := ih (Module.finrank K U') hdim' U' rfl hU'
        have hamb : K ∙ a ⊔ flipOrth σ (K ∙ a) = ⊤ := by
          have h := span_sup_inf_flipOrth hσ (U := ⊤) (a := a) Submodule.mem_top ha
          simpa using h
        have hW : flipOrth σ (K ∙ a) = U' ⊔ (flipOrth σ (K ∙ a) ⊓ flipOrth σ U') := by
          apply le_antisymm
          · intro w hw
            have hwtop : w ∈ U' ⊔ flipOrth σ U' := by rw [hIH]; exact Submodule.mem_top
            obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hwtop
            have hzW : z ∈ flipOrth σ (K ∙ a) := by
              have hz' : z = (u + z) - u := by abel
              rw [hz']
              exact Submodule.sub_mem _ hw hu.2
            exact Submodule.add_mem _ (Submodule.mem_sup_left hu)
              (Submodule.mem_sup_right ⟨hzW, hz⟩)
          · refine sup_le ?_ ?_
            · exact inf_le_right
            · exact inf_le_left
        have hhermU : flipOrth σ U = flipOrth σ (K ∙ a) ⊓ flipOrth σ U' := by
          rw [← hsplit, flipOrth_sup]
        rw [hhermU, ← hsplit]
        rw [sup_assoc, ← hW]
        exact hamb
  exact hmain (Module.finrank K U) U rfl hU

theorem isFlipflopSub_span_singleton_iff {v : Fin n ⊕ Fin n → K} (hv : v ≠ 0) :
    IsFlipflopSub σ (K ∙ v) ↔ quadPlus n K v = 0 ∧ flipHerm σ v v ≠ 0 := by
  constructor
  · intro hU
    refine ⟨hU.total v (Submodule.mem_span_singleton_self v), ?_⟩
    intro hvv
    refine hv (hU.nondeg v (Submodule.mem_span_singleton_self v) ?_)
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [flipHerm_smul_right, hvv, mul_zero]
  · rintro ⟨hq, hh⟩
    constructor
    · intro u hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [QuadraticMap.map_smul]
      simp [hq]
    · intro u hu hper
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
      have h1 := hper v (Submodule.mem_span_singleton_self v)
      rw [flipHerm_smul_left] at h1
      have hc : c = 0 := (mul_eq_zero.mp h1).resolve_right hh
      rw [hc, zero_smul]

theorem isFlipflopPt_span_singleton_iff {v : Fin n ⊕ Fin n → K} (hv : v ≠ 0) :
    IsFlipflopPt σ (K ∙ v) ↔ quadPlus n K v = 0 ∧ flipHerm σ v v ≠ 0 := by
  simp [IsFlipflopPt, finrank_span_singleton hv, isFlipflopSub_span_singleton_iff hv]

theorem stdE_inr_eq_zero_of_mem_span {u : Fin n ⊕ Fin n → K}
    (hu : u ∈ Submodule.span K (Set.range (stdE (K := K) (n := n)))) (i : Fin n) :
    u (.inr i) = 0 := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    simp [stdE]
  | zero => simp
  | add u v hu hv ihu ihv => simp [ihu, ihv]
  | smul a u hu ihu => simp [ihu]

theorem isFlipflopSub_span_stdE :
    IsFlipflopSub σ (Submodule.span K (Set.range (stdE (K := K) (n := n)))) where
  total u hu := by
    rw [quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [stdE_inr_eq_zero_of_mem_span hu i, mul_zero]
  nondeg u hu hper := by
    funext x
    cases x with
    | inl i =>
      have h := hper (stdE (K := K) i) (Submodule.subset_span ⟨i, rfl⟩)
      rwa [flipHerm_stdE_right] at h
    | inr i => exact stdE_inr_eq_zero_of_mem_span hu i

@[expose] def stdAlt (i : Fin n) : Fin n ⊕ Fin n → K :=
  if (i : ℕ) + 1 < n then stdE (K := K) i else stdF (K := K) i

theorem stdAlt_of_lt {i : Fin n} (h : (i : ℕ) + 1 < n) : stdAlt (K := K) i = stdE i := by
  rw [stdAlt, if_pos h]

theorem stdAlt_of_not_lt {i : Fin n} (h : ¬ (i : ℕ) + 1 < n) : stdAlt (K := K) i = stdF i := by
  rw [stdAlt, if_neg h]

theorem stdAlt_inr_eq_zero_of_mem_span {u : Fin n ⊕ Fin n → K}
    (hu : u ∈ Submodule.span K (Set.range (stdAlt (K := K) (n := n)))) {i : Fin n}
    (hi : (i : ℕ) + 1 < n) : u (.inr i) = 0 := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    by_cases hj : (j : ℕ) + 1 < n
    · rw [stdAlt_of_lt hj]
      simp [stdE]
    · rw [stdAlt_of_not_lt hj]
      have hij : i ≠ j := by
        intro h
        subst h
        omega
      simp [stdF, hij]
  | zero => simp
  | add u v hu hv ihu ihv => simp [ihu, ihv]
  | smul a u hu ihu => simp [ihu]

theorem stdAlt_inl_eq_zero_of_mem_span {u : Fin n ⊕ Fin n → K}
    (hu : u ∈ Submodule.span K (Set.range (stdAlt (K := K) (n := n)))) {i : Fin n}
    (hi : ¬ (i : ℕ) + 1 < n) : u (.inl i) = 0 := by
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    by_cases hj : (j : ℕ) + 1 < n
    · rw [stdAlt_of_lt hj]
      have hij : i ≠ j := by
        intro h
        subst h
        omega
      simp [stdE, hij]
    · rw [stdAlt_of_not_lt hj]
      simp [stdF]
  | zero => simp
  | add u v hu hv ihu ihv => simp [ihu, ihv]
  | smul a u hu ihu => simp [ihu]

theorem last_eq_of_not_lt {i : Fin n} (hn : 1 ≤ n) (hi : ¬ (i : ℕ) + 1 < n) :
    i = ⟨n - 1, by omega⟩ := by
  apply Fin.ext
  simp only
  omega

theorem isFlipflopSub_span_stdAlt (hn : 1 ≤ n) :
    IsFlipflopSub σ (Submodule.span K (Set.range (stdAlt (K := K) (n := n)))) where
  total u hu := by
    rw [quadPlus_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) + 1 < n
    · rw [stdAlt_inr_eq_zero_of_mem_span hu hi, mul_zero]
    · rw [stdAlt_inl_eq_zero_of_mem_span hu hi, zero_mul]
  nondeg u hu hper := by
    funext x
    cases x with
    | inl i =>
      by_cases hi : (i : ℕ) + 1 < n
      · have hmem : stdE (K := K) i ∈
            Submodule.span K (Set.range (stdAlt (K := K) (n := n))) := by
          rw [← stdAlt_of_lt hi]
          exact Submodule.subset_span ⟨i, rfl⟩
        have h := hper (stdE (K := K) i) hmem
        rwa [flipHerm_stdE_right] at h
      · rw [last_eq_of_not_lt hn hi]
        exact stdAlt_inl_eq_zero_of_mem_span hu (i := ⟨n - 1, by omega⟩) (by simp; omega)
    | inr i =>
      by_cases hi : (i : ℕ) + 1 < n
      · exact stdAlt_inr_eq_zero_of_mem_span hu hi
      · rw [last_eq_of_not_lt hn hi]
        have hmem : stdF (K := K) ⟨n - 1, by omega⟩ ∈
            Submodule.span K (Set.range (stdAlt (K := K) (n := n))) := by
          rw [← stdAlt_of_not_lt (i := ⟨n - 1, by omega⟩) (by simp; omega)]
          exact Submodule.subset_span ⟨_, rfl⟩
        have h := hper (stdF (K := K) ⟨n - 1, by omega⟩) hmem
        rwa [flipHerm_stdF_right] at h

theorem range_stdAlt (hn : 1 ≤ n) :
    Set.range (stdAlt (K := K) (n := n)) =
      stdE (K := K) '' {i : Fin n | (i : ℕ) + 1 < n} ∪
        {stdF (K := K) ⟨n - 1, by omega⟩} := by
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : (i : ℕ) + 1 < n
    · left
      exact ⟨i, hi, (stdAlt_of_lt hi).symm⟩
    · right
      rw [Set.mem_singleton_iff, last_eq_of_not_lt hn hi,
        stdAlt_of_not_lt (i := ⟨n - 1, by omega⟩) (by simp; omega)]
  · rintro (⟨i, hi, rfl⟩ | hv)
    · exact ⟨i, stdAlt_of_lt hi⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact ⟨⟨n - 1, by omega⟩, stdAlt_of_not_lt (by simp; omega)⟩

theorem isFlipflopSub_span_stdE_union_stdF_last (hn : 1 ≤ n) :
    IsFlipflopSub σ (Submodule.span K
      (stdE (K := K) '' {i : Fin n | (i : ℕ) + 1 < n} ∪
        {stdF (K := K) ⟨n - 1, by omega⟩})) := by
  rw [← range_stdAlt (K := K) (n := n) hn]
  exact isFlipflopSub_span_stdAlt hn

@[expose] noncomputable def flipHermSesq (σ : K ≃+* K) :
    (Fin n ⊕ Fin n → K) →ₛₗ[(σ : K →+* K)] (Fin n ⊕ Fin n → K) →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (σ : K →+* K) (RingHom.id K) (fun u v => flipHerm σ v u)
    (fun u₁ u₂ v => by rw [flipHerm_add_right])
    (fun c u v => by rw [flipHerm_smul_right]; rfl)
    (fun u v₁ v₂ => by rw [flipHerm_add_left])
    (fun c u v => by rw [flipHerm_smul_left]; rfl)

theorem flipHermSesq_apply (u v : Fin n ⊕ Fin n → K) : flipHermSesq σ u v = flipHerm σ v u := rfl

theorem flipHermSesq_isSymm (hσ : ∀ x, σ (σ x) = x) : (flipHermSesq (n := n) σ).IsSymm :=
  LinearMap.IsSymm.mk fun u v => by
    rw [flipHermSesq_apply, flipHermSesq_apply]
    exact flipHerm_conj hσ v u

theorem flipHermSesq_separatingLeft (hσ : ∀ x, σ (σ x) = x) :
    (flipHermSesq (n := n) σ).SeparatingLeft := by
  intro u hu
  change ∀ y, flipHerm σ y u = 0 at hu
  refine eq_zero_of_flipHerm (σ := σ) (n := n) fun v => ?_
  exact (flipHerm_eq_zero_iff hσ).mpr (hu v)

theorem exists_orthonormal_basis (hσ : ∀ x, σ (σ x) = x) (hne : ∃ c, σ c ≠ c)
    (hN : ∀ a, σ a = a → a ≠ 0 → ∃ x, x * σ x = a)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) K U,
      ∀ i j, flipHerm σ ((b i : U) : Fin n ⊕ Fin n → K) ((b j : U) : Fin n ⊕ Fin n → K) =
        if i = j then 1 else 0 := by
  classical
  let B : U →ₛₗ[(σ : K →+* K)] U →ₗ[K] K := (flipHermSesq (n := n) σ).domRestrict₁₂ U U
  have hB : B.IsSymm := LinearMap.IsSymm.domRestrict (flipHermSesq_isSymm (σ := σ) hσ) U
  have hsep : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hU.nondeg (u : Fin n ⊕ Fin n → K) u.2 fun v hv => ?_)
    have h := hu ⟨v, hv⟩
    change flipHerm σ v (u : Fin n ⊕ Fin n → K) = 0 at h
    exact (flipHerm_eq_zero_iff hσ).mpr h
  obtain ⟨c₀, hc₀⟩ := hne
  obtain ⟨e, he⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_orthonormal_basis_of_norm
    (B := B) hB hsep hc₀ (fun d hd hd0 => by
      obtain ⟨x, hx⟩ := hN d hd hd0
      exact ⟨x, by rwa [mul_comm]⟩)
  refine ⟨e, fun i j => ?_⟩
  have h := he j i
  change flipHerm σ ((e i : U) : Fin n ⊕ Fin n → K) ((e j : U) : Fin n ⊕ Fin n → K) =
    if j = i then 1 else 0 at h
  simpa [eq_comm] using h

section Unitary

open CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_mul_unitaryInvolution_eq_of_fixed (hK : Nat.card K = (p ^ f) ^ 2) {d : K}
    (hd : unitaryInvolution K p f d = d) (hd0 : d ≠ 0) :
    ∃ x : K, x * unitaryInvolution K p f x = d := by
  obtain ⟨x, hx⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hK hd hd0
  exact ⟨x, by simpa [mul_comm] using hx⟩

theorem exists_orthonormal_basis_unitaryInvolution (hK : Nat.card K = (p ^ f) ^ 2)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub (unitaryInvolution K p f) U) :
    ∃ b : Module.Basis (Fin (Module.finrank K U)) K U,
      ∀ i j, flipHerm (unitaryInvolution K p f) ((b i : U) : Fin n ⊕ Fin n → K)
        ((b j : U) : Fin n ⊕ Fin n → K) = if i = j then 1 else 0 := by
  have hσ := (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := p) (f := f) hK).invol
  exact exists_orthonormal_basis (σ := unitaryInvolution K p f) hσ
    (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
      (p := p) (f := f) hK).exists_ne
    (fun a ha ha0 => exists_mul_unitaryInvolution_eq_of_fixed hK ha ha0) hU

theorem sup_flipOrth_eq_top_unitaryInvolution (hK : Nat.card K = (p ^ f) ^ 2)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub (unitaryInvolution K p f) U) :
    U ⊔ flipOrth (unitaryInvolution K p f) U = ⊤ := by
  have h := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
    (p := p) (f := f) hK
  exact sup_flipOrth_eq_top h.invol h.exists_ne hU

end Unitary

end CFSG.ClassicalInvolution.PhanDn
