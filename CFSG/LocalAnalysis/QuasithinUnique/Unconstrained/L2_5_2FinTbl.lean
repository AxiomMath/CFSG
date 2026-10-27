module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTools

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace Tbl

open Equiv


@[expose] def tbl {n : ℕ} (σ : Perm (Fin n)) : List ℕ := (List.finRange n).map fun i => ((σ i : Fin n) : ℕ)

@[expose] def mulT (a b : List ℕ) : List ℕ := b.map fun j => a.getD j 0

@[expose] def invT (n : ℕ) (a : List ℕ) : List ℕ := (List.range n).map fun j => a.idxOf j

variable {n : ℕ}

theorem length_tbl (σ : Perm (Fin n)) : (tbl σ).length = n := by simp [tbl]

theorem tbl_getD (σ : Perm (Fin n)) (i : Fin n) : (tbl σ).getD (i : ℕ) 0 = (σ i : ℕ) := by
  have hi : (i : ℕ) < (tbl σ).length := by rw [length_tbl]; exact i.2
  rw [List.getD_eq_getElem _ _ hi]
  simp [tbl]

theorem tbl_mul (σ τ : Perm (Fin n)) : tbl (σ * τ) = mulT (tbl σ) (tbl τ) := by
  unfold mulT tbl
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Perm.coe_mul]
  have := tbl_getD σ (τ i)
  simp [tbl] at this ⊢

theorem tbl_one : tbl (1 : Perm (Fin n)) = List.range n := by
  simp [tbl]

theorem tbl_injective : Function.Injective (tbl : Perm (Fin n) → List ℕ) := by
  intro σ τ h
  ext i
  have h1 := tbl_getD σ i
  have h2 := tbl_getD τ i
  rw [h] at h1
  have : ((σ i : Fin n) : ℕ) = ((τ i : Fin n) : ℕ) := by rw [← h1, h2]
  exact congrArg _ (Fin.ext this)

theorem nodup_tbl (σ : Perm (Fin n)) : (tbl σ).Nodup := by
  unfold tbl
  refine List.Nodup.map ?_ (List.nodup_finRange n)
  intro i j hij
  exact σ.injective (Fin.ext hij)

theorem tbl_inv (σ : Perm (Fin n)) : tbl σ⁻¹ = invT n (tbl σ) := by
  unfold invT
  apply List.ext_getElem
  · simp [tbl]
  · intro j h1 h2
    have hj : j < n := by simpa [tbl] using h1
    have hk : ((σ⁻¹ ⟨j, hj⟩ : Fin n) : ℕ) < (tbl σ).length := by
      rw [length_tbl]; exact (σ⁻¹ ⟨j, hj⟩).2
    have hget : (tbl σ)[((σ⁻¹ ⟨j, hj⟩ : Fin n) : ℕ)] = j := by
      have := tbl_getD σ (σ⁻¹ ⟨j, hj⟩)
      rw [List.getD_eq_getElem _ _ hk] at this
      rw [this]; simp
    have hidx := List.Nodup.idxOf_getElem (nodup_tbl σ) ((σ⁻¹ ⟨j, hj⟩ : Fin n) : ℕ) hk
    rw [hget] at hidx
    have hL : (tbl σ⁻¹)[j] = ((σ⁻¹ ⟨j, hj⟩ : Fin n) : ℕ) := by simp [tbl]
    have hR : (List.map (fun j => List.idxOf j (tbl σ)) (List.range n))[j] =
        List.idxOf j (tbl σ) := by simp
    rw [hL, hR, hidx]

theorem tbl_mem_permutations (σ : Perm (Fin n)) : tbl σ ∈ (List.range n).permutations := by
  rw [List.mem_permutations]
  have h := σ.map_finRange_perm.map (fun i : Fin n => (i : ℕ))
  simpa [tbl, List.map_map, Function.comp_def] using h



structure TabGroup (n : ℕ) where
  elts : List (Perm (Fin n))
  one_mem : List.range n ∈ elts.map tbl
  mul_mem : ∀ a ∈ elts.map tbl, ∀ b ∈ elts.map tbl, mulT a b ∈ elts.map tbl
  inv_mem : ∀ a ∈ elts.map tbl, invT n a ∈ elts.map tbl

namespace TabGroup

variable (T : TabGroup n)

@[expose] def tabs : List (List ℕ) := T.elts.map tbl

@[expose] def sub : Subgroup (Perm (Fin n)) where
  carrier := {σ | tbl σ ∈ T.tabs}
  mul_mem' := by
    intro a b ha hb
    show tbl (a * b) ∈ T.tabs
    rw [tbl_mul]
    exact T.mul_mem _ ha _ hb
  one_mem' := by
    show tbl (1 : Perm (Fin n)) ∈ T.tabs
    rw [tbl_one]
    exact T.one_mem
  inv_mem' := by
    intro a ha
    show tbl a⁻¹ ∈ T.tabs
    rw [tbl_inv]
    exact T.inv_mem _ ha

theorem mem_sub {σ : Perm (Fin n)} : σ ∈ T.sub ↔ tbl σ ∈ T.tabs := Iff.rfl

theorem mem_sub_iff_mem_elts {σ : Perm (Fin n)} : σ ∈ T.sub ↔ σ ∈ T.elts := by
  rw [mem_sub, tabs, List.mem_map]
  constructor
  · rintro ⟨τ, hτ, h⟩
    rw [tbl_injective h] at hτ
    exact hτ
  · intro h
    exact ⟨σ, h, rfl⟩

theorem real {a : List ℕ} (ha : a ∈ T.tabs) : ∃ σ ∈ T.sub, tbl σ = a := by
  obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp ha
  exact ⟨σ, (mem_sub_iff_mem_elts T).mpr hσ, rfl⟩

end TabGroup

@[expose] def commT (n : ℕ) (y w : List ℕ) : List ℕ := mulT (mulT (mulT y w) (invT n y)) (invT n w)

@[expose] def commTabs (n : ℕ) (tabs : List (List ℕ)) : List (List ℕ) :=
  tabs.flatMap fun y => tabs.map fun w => commT n y w

@[expose] def vTabs (n : ℕ) (tabs : List (List ℕ)) : List (List ℕ) :=
  tabs.filter fun x => (commTabs n tabs).all fun c => decide (mulT x c = mulT c x)

theorem tbl_comm (y w : Perm (Fin n)) :
    tbl (y * w * y⁻¹ * w⁻¹) = commT n (tbl y) (tbl w) := by
  simp only [commT, tbl_mul, tbl_inv]

theorem mul_comm_iff_tbl (σ c : Perm (Fin n)) :
    σ * c = c * σ ↔ mulT (tbl σ) (tbl c) = mulT (tbl c) (tbl σ) := by
  constructor
  · intro h
    rw [← tbl_mul, ← tbl_mul, h]
  · intro h
    apply tbl_injective
    rw [tbl_mul, tbl_mul]
    exact h

theorem mem_commCentralizer_sub (T : TabGroup n) (σ : Perm (Fin n)) :
    σ ∈ commCentralizer T.sub ↔ tbl σ ∈ vTabs n T.tabs := by
  unfold vTabs
  rw [List.mem_filter]
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    unfold commTabs at hc
    simp only [List.mem_flatMap, List.mem_map] at hc
    obtain ⟨y', hy', w', hw', rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := T.real hy'
    obtain ⟨w, hw, rfl⟩ := T.real hw'
    have h1 := (mul_comm_iff_tbl σ (y * w * y⁻¹ * w⁻¹)).mp (h y hy w hw)
    rw [tbl_comm] at h1
    exact decide_eq_true h1
  · rintro ⟨hσ, h⟩
    refine ⟨hσ, fun y hy w hw => ?_⟩
    have hc : commT n (tbl y) (tbl w) ∈ commTabs n T.tabs := by
      unfold commTabs
      simp only [List.mem_flatMap, List.mem_map]
      exact ⟨tbl y, hy, tbl w, hw, rfl⟩
    have h1 := of_decide_eq_true ((List.all_eq_true.mp h) _ hc)
    rw [← tbl_comm] at h1
    exact (mul_comm_iff_tbl σ (y * w * y⁻¹ * w⁻¹)).mpr h1




end Tbl

end CFSG.QuasithinUnique.Unc25G2
