module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourLines
public import CFSG.LieType.Chevalley.C2E6MinusSixPoints
import all CFSG.Fischer.F4
public import Mathlib.Tactic.Polynomial.Basic

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def pointMap (P : Submodule K V) : Submodule (ZMod 2) X :=
  ((L P).restrictScalars (ZMod 2) ⊓ W₀).map psiLin

@[expose] def lineMap (ℓ : Submodule K V) : Submodule (ZMod 2) X :=
  ((M ℓ).restrictScalars (ZMod 2) ⊓ W₀).map psiLin

theorem coe_pointMap (P : Submodule K V) :
    (pointMap P : Set X) = Ψ '' {w : W₀ | w.1 ∈ L P} := by
  ext x
  simp only [pointMap, Submodule.map_coe, Set.mem_image, SetLike.mem_coe, Submodule.mem_inf,
    Submodule.restrictScalars_mem, Set.mem_ofPred_eq, Subtype.exists, Ψ_apply]
  constructor
  · rintro ⟨w, ⟨hw, hw₀⟩, rfl⟩
    exact ⟨w, hw₀, hw, rfl⟩
  · rintro ⟨w, hw₀, hw, rfl⟩
    exact ⟨w, ⟨hw, hw₀⟩, rfl⟩

theorem coe_lineMap (ℓ : Submodule K V) :
    (lineMap ℓ : Set X) = Ψ '' {w : W₀ | w.1 ∈ M ℓ} := by
  ext x
  simp only [lineMap, Submodule.map_coe, Set.mem_image, SetLike.mem_coe, Submodule.mem_inf,
    Submodule.restrictScalars_mem, Set.mem_ofPred_eq, Subtype.exists, Ψ_apply]
  constructor
  · rintro ⟨w, ⟨hw, hw₀⟩, rfl⟩
    exact ⟨w, hw₀, hw, rfl⟩
  · rintro ⟨w, hw₀, hw, rfl⟩
    exact ⟨w, ⟨hw, hw₀⟩, rfl⟩

theorem wedge_add_left (x x' v : V) : wedge (x + x') v = wedge x v + wedge x' v := by
  funext p
  fin_cases p <;> simp [wedge] <;> ring

theorem wedge_add_right (x v v' : V) : wedge x (v + v') = wedge x v + wedge x v' :=
  (wedgeL x).map_add v v'

theorem wedge_self (x : V) : wedge x x = 0 := by
  funext p
  fin_cases p <;> simp [wedge] <;> ring

theorem wedge_swap (x v : V) : wedge v x = -wedge x v := by
  funext p
  fin_cases p <;> simp [wedge] <;> ring

theorem L_span_pair (a b : V) : L (Submodule.span K {a, b}) = K ∙ wedge a b := by
  refine le_antisymm ?_ ?_
  · rw [L, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨c₁ * d₂ - c₂ * d₁, ?_⟩
    simp only [wedge_add_left, wedge_add_right, wedge_smul_left, wedge_smul_right, wedge_self,
      wedge_swap a b, smul_zero, zero_add, add_zero, smul_neg, smul_smul]
    module
  · rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span ⟨a, Submodule.subset_span (by simp), b,
      Submodule.subset_span (by simp), rfl⟩

theorem fixed_span_singleton {w v : W}
    (hfix : ∀ c : K, T (c • w) = c • w → c • w = 0 ∨ c • w = v) (hv : T v = v)
    (hvw : v ∈ K ∙ w) : (K ∙ w).restrictScalars (ZMod 2) ⊓ W₀ = (ZMod 2) ∙ v := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_W₀,
    mem_span_singleton_zmod_two]
  constructor
  · rintro ⟨hx, hTx⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact hfix c hTx
  · rintro (rfl | rfl)
    · exact ⟨Submodule.zero_mem _, map_zero T⟩
    · exact ⟨hvw, hv⟩

theorem fixed_span_pair {w₁ w₂ : W} (h₁ : T w₁ = w₁) (h₂ : T w₂ = w₂)
    (hfix : ∀ c₁ c₂ : K, T (c₁ • w₁ + c₂ • w₂) = c₁ • w₁ + c₂ • w₂ →
      c₁ • w₁ + c₂ • w₂ = 0 ∨ c₁ • w₁ + c₂ • w₂ = w₁ ∨ c₁ • w₁ + c₂ • w₂ = w₂ ∨
        c₁ • w₁ + c₂ • w₂ = w₁ + w₂) :
    (Submodule.span K {w₁, w₂}).restrictScalars (ZMod 2) ⊓ W₀ =
      Submodule.span (ZMod 2) {w₁, w₂} := by
  ext x
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_W₀, mem_span_pair_zmod_two]
  constructor
  · rintro ⟨hx, hTx⟩
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    exact hfix c₁ c₂ hTx
  · have hm₁ : w₁ ∈ Submodule.span K {w₁, w₂} := Submodule.subset_span (by simp)
    have hm₂ : w₂ ∈ Submodule.span K {w₁, w₂} := Submodule.subset_span (by simp)
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨Submodule.zero_mem _, map_zero T⟩
    · exact ⟨hm₁, h₁⟩
    · exact ⟨hm₂, h₂⟩
    · exact ⟨Submodule.add_mem _ hm₁ hm₂, by rw [map_add, h₁, h₂]⟩

@[expose] def pw (j : Fin 27) : W := wedge (uVec (plA j)) (uVec (plB j))

@[expose] def cP : Fin 27 → Fin 4 :=
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1,
    1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 2, 2]

@[expose] def vP (j : Fin 27) : W := kc (cP j) • pw j

@[expose] def sigma : Fin 27 → Fin 27 :=
  ![0, 2, 1, 4, 3, 7, 6, 11, 12, 18, 17, 24, 23, 5, 9,
    10, 8, 13, 14, 16, 15, 20, 19, 22, 21, 26, 25]

theorem T_smul_pw : ∀ (j : Fin 27) (c : K), T (c • pw j) = c • pw j →
    c • pw j = 0 ∨ c • pw j = vP j := by
  decide +kernel

theorem T_vP : ∀ j, T (vP j) = vP j := by decide +kernel

theorem vP_ne_zero : ∀ j, vP j ≠ 0 := by decide +kernel

theorem psiLin_vP : ∀ j, psiLin (vP j) = ptVec (sigma j) := by decide +kernel

theorem L_uPlane (j : Fin 27) : L (uPlane j) = K ∙ pw j := L_span_pair _ _

theorem fixed_L_uPlane (j : Fin 27) :
    (L (uPlane j)).restrictScalars (ZMod 2) ⊓ W₀ = (ZMod 2) ∙ vP j := by
  rw [L_uPlane]
  exact fixed_span_singleton (T_smul_pw j) (T_vP j)
    (Submodule.mem_span_singleton.mpr ⟨kc (cP j), rfl⟩)

theorem pointMap_uPlane (j : Fin 27) : pointMap (uPlane j) = ptSub (sigma j) := by
  rw [pointMap, fixed_L_uPlane, Submodule.map_span, Set.image_singleton, psiLin_vP]
  rfl

@[expose] def pCode : Fin 45 → Fin 4 → Fin 4 :=
  ![![0, 0, 1, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 3], ![0, 0, 1, 2],
    ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 0], ![0, 0, 1, 3],
    ![0, 0, 1, 0], ![0, 0, 1, 2], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 3],
    ![0, 0, 1, 2], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 0],
    ![0, 0, 1, 3], ![0, 0, 1, 0], ![0, 0, 1, 2], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1],
    ![0, 0, 1, 3], ![0, 0, 1, 2], ![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 0, 1, 1], ![0, 0, 1, 3],
    ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 0, 1], ![0, 0, 1, 3], ![0, 0, 1, 2], ![0, 0, 1, 1],
    ![0, 0, 1, 2], ![0, 0, 1, 1], ![0, 0, 1, 3]]

@[expose] def qCode : Fin 45 → Fin 4 → Fin 4 :=
  ![![0, 1, 0, 0], ![0, 1, 0, 0], ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 1, 0, 0],
    ![1, 0, 0, 0], ![0, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 3], ![0, 1, 0, 3],
    ![0, 1, 0, 2], ![0, 1, 0, 2], ![0, 1, 0, 0], ![1, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 0],
    ![0, 1, 0, 0], ![1, 1, 0, 0], ![0, 1, 0, 1], ![1, 0, 1, 0], ![0, 1, 0, 1], ![0, 1, 0, 3],
    ![0, 1, 0, 3], ![0, 1, 0, 2], ![0, 1, 0, 2], ![1, 0, 3, 0], ![1, 3, 0, 0], ![1, 0, 3, 0],
    ![0, 1, 0, 1], ![0, 1, 0, 1], ![0, 1, 0, 3], ![0, 1, 0, 3], ![0, 1, 0, 2], ![0, 1, 0, 2],
    ![1, 0, 2, 0], ![1, 2, 0, 0], ![1, 0, 2, 0], ![0, 1, 0, 1], ![0, 1, 0, 1], ![0, 1, 0, 3],
    ![0, 1, 0, 3], ![0, 1, 0, 2], ![0, 1, 0, 2]]

@[expose] def pVec (k : Fin 45) : V := vc (pCode k)

@[expose] def qVec (k : Fin 45) : V := vc (qCode k)

@[expose] def lw₁ (k : Fin 45) : W := wedge (uVec k) (pVec k)

@[expose] def lw₂ (k : Fin 45) : W := wedge (uVec k) (qVec k)

@[expose] def nPt : Fin 45 → Fin 27 :=
  ![1, 2, 3, 11, 17, 23, 2, 1, 7, 14, 1, 20, 1, 26, 5,
    3, 14, 20, 26, 2, 5, 7, 11, 5, 17, 5, 23, 3, 2, 7,
    20, 23, 11, 26, 14, 17, 3, 2, 7, 17, 26, 14, 23, 11, 20]

@[expose] def mPt : Fin 45 → Fin 27 :=
  ![0, 3, 0, 0, 0, 0, 1, 9, 4, 13, 15, 19, 21, 25, 6,
    9, 6, 6, 6, 11, 13, 10, 9, 19, 15, 25, 21, 21, 23, 22,
    9, 13, 19, 15, 21, 25, 15, 17, 16, 13, 9, 15, 19, 25, 21]

@[expose] def tau : Fin 45 → Fin 45 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 8, 18, 9, 19, 20,
    13, 24, 25, 26, 10, 21, 27, 30, 22, 31, 23, 32, 15, 12, 29,
    34, 41, 38, 39, 44, 35, 14, 11, 28, 42, 33, 43, 36, 37, 40]

theorem herm_pVec : ∀ k, herm (uVec k) (pVec k) = 0 := by decide +kernel

theorem herm_qVec : ∀ k, herm (uVec k) (qVec k) = 0 := by decide +kernel

theorem linearIndependent_upq_aux : ∀ (k : Fin 45) (c₁ c₂ c₃ : K),
    c₁ • uVec k + c₂ • pVec k + c₃ • qVec k = 0 → c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  decide +kernel

theorem exists_herm_single_ne : ∀ k : Fin 45, ∃ i : Fin 4, herm (Pi.single i 1) (uVec k) ≠ 0 := by
  decide +kernel

theorem T_lw₁ : ∀ k, T (lw₁ k) = lw₁ k := by decide +kernel

theorem T_lw₂ : ∀ k, T (lw₂ k) = lw₂ k := by decide +kernel

theorem fix_lw : ∀ (k : Fin 45) (c₁ c₂ : K),
    T (c₁ • lw₁ k + c₂ • lw₂ k) = c₁ • lw₁ k + c₂ • lw₂ k →
      c₁ • lw₁ k + c₂ • lw₂ k = 0 ∨ c₁ • lw₁ k + c₂ • lw₂ k = lw₁ k ∨
        c₁ • lw₁ k + c₂ • lw₂ k = lw₂ k ∨ c₁ • lw₁ k + c₂ • lw₂ k = lw₁ k + lw₂ k := by
  decide +kernel

theorem psiLin_lw₁ : ∀ k, psiLin (lw₁ k) = ptVec (nPt k) := by decide +kernel

theorem psiLin_lw₂ : ∀ k, psiLin (lw₂ k) = ptVec (mPt k) := by decide +kernel

theorem ptOn_nPt : ∀ k, PtOn (nPt k) (tau k) := by decide

theorem ptOn_mPt : ∀ k, PtOn (mPt k) (tau k) := by decide

theorem nPt_ne_mPt : ∀ k, nPt k ≠ mPt k := by decide

theorem mem_perp_uLine {k : Fin 45} {v : V} : v ∈ perp (uLine k) ↔ herm (uVec k) v = 0 := by
  rw [mem_perp]
  constructor
  · intro h
    exact h _ (Submodule.mem_span_singleton_self _)
  · intro h x hx
    obtain ⟨c, rfl⟩ := mem_uLine.mp hx
    rw [herm_smul_left, h, mul_zero]

@[expose] def hermL (u : V) : V →ₗ[K] K where
  toFun v := herm v u
  map_add' v v' := herm_add_left v v' u
  map_smul' c v := herm_smul_left c v u

theorem bar_eq_zero_iff {a : K} : bar a = 0 ↔ a = 0 := by
  revert a
  decide

theorem perp_uLine_eq_ker (k : Fin 45) : perp (uLine k) = LinearMap.ker (hermL (uVec k)) := by
  ext v
  rw [mem_perp_uLine, LinearMap.mem_ker]
  change herm (uVec k) v = 0 ↔ herm v (uVec k) = 0
  rw [herm_swap v, bar_eq_zero_iff]

theorem finrank_perp_uLine (k : Fin 45) : finrank K (perp (uLine k)) = 3 := by
  have hsurj : Function.Surjective (hermL (uVec k)) := by
    obtain ⟨i, hi⟩ := exists_herm_single_ne k
    intro t
    refine ⟨(t / herm (Pi.single i 1) (uVec k)) • Pi.single i 1, ?_⟩
    change herm _ (uVec k) = t
    rw [herm_smul_left, div_mul_cancel₀ t hi]
  have h := LinearMap.finrank_range_add_finrank_ker (hermL (uVec k))
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fin_fun] at h
  rw [perp_uLine_eq_ker]
  omega

theorem finrank_span_upq (k : Fin 45) :
    finrank K (Submodule.span K {uVec k, pVec k, qVec k}) = 3 := by
  have hli : LinearIndependent K ![uVec k, pVec k, qVec k] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    obtain ⟨h0, h1, h2⟩ := linearIndependent_upq_aux k (g 0) (g 1) (g 2) hg
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have h := finrank_span_eq_card hli
  rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union, Set.singleton_union, Fintype.card_fin] at h

theorem perp_uLine (k : Fin 45) :
    perp (uLine k) = Submodule.span K {uVec k, pVec k, qVec k} := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rw [SetLike.mem_coe, mem_perp_uLine]
    rcases hv with rfl | rfl | rfl
    · exact herm_uVec_self k
    · exact herm_pVec k
    · exact herm_qVec k
  · rw [finrank_span_upq, finrank_perp_uLine]

theorem M_uLine (k : Fin 45) : M (uLine k) = Submodule.span K {lw₁ k, lw₂ k} := by
  rw [M_eq_map (ℓ := uLine k) (x := uVec k) rfl, perp_uLine, Submodule.map_span]
  have : (wedgeL (uVec k)) '' {uVec k, pVec k, qVec k} = {0, lw₁ k, lw₂ k} := by
    rw [Set.image_insert_eq, Set.image_pair, wedgeL_apply, wedgeL_apply, wedgeL_apply,
      wedge_self]
    rfl
  rw [this, Submodule.span_insert_zero]

theorem fixed_M_uLine (k : Fin 45) :
    (M (uLine k)).restrictScalars (ZMod 2) ⊓ W₀ = Submodule.span (ZMod 2) {lw₁ k, lw₂ k} := by
  rw [M_uLine]
  exact fixed_span_pair (T_lw₁ k) (T_lw₂ k) (fix_lw k)

theorem lineMap_uLine (k : Fin 45) : lineMap (uLine k) = lnSub (tau k) := by
  rw [lineMap, fixed_M_uLine, Submodule.map_span, Set.image_pair, psiLin_lw₁, psiLin_lw₂]
  exact span_ptVec_eq_lnSub (ptOn_nPt k) (ptOn_mPt k) (nPt_ne_mPt k)

theorem sigma_injective : Function.Injective sigma := by
  intro j j' h
  revert j j'
  decide

theorem tau_injective : Function.Injective tau := by
  intro k k' h
  revert k k'
  decide

theorem sigma_surjective : Function.Surjective sigma :=
  Finite.surjective_of_injective sigma_injective

theorem tau_surjective : Function.Surjective tau :=
  Finite.surjective_of_injective tau_injective

theorem uOn_iff_ptOn : ∀ (k : Fin 45) (j : Fin 27), UOn k j ↔ PtOn (sigma j) (tau k) := by
  decide +kernel

end CFSG.LieType.Chevalley.C2E6Overlap
