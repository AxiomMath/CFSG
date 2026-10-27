module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47fCenter

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def hset (h : ℤ) : Set (Fin Tag.G2.rank → ℤ) :=
  {α | IsRoot .G2 α ∧ 0 < height α ∧ h ≤ height α}

@[expose] def wset : Set (Fin Tag.G2.rank → ℤ) :=
  {α | IsRoot .G2 α ∧ 0 < height α ∧ α ≠ ![0, 1]}

@[expose] def lA : List (Fin Tag.G2.rank → ℤ) :=
  [![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]]

@[expose] def lW : List (Fin Tag.G2.rank → ℤ) := [![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]]

@[expose] def l2 : List (Fin Tag.G2.rank → ℤ) := [![1, 1], ![1, 2], ![1, 3], ![2, 3]]

@[expose] def l3 : List (Fin Tag.G2.rank → ℤ) := [![1, 2], ![1, 3], ![2, 3]]

@[expose] def l4 : List (Fin Tag.G2.rank → ℤ) := [![1, 3], ![2, 3]]

@[expose] def l5 : List (Fin Tag.G2.rank → ℤ) := [![2, 3]]

theorem mem_iff_of_filter {P : (Fin Tag.G2.rank → ℤ) → Prop}
    {inst : DecidablePred P} {l : List (Fin Tag.G2.rank → ℤ)}
    (h : (rootFinset .G2).filter P = l.toFinset) (α : Fin Tag.G2.rank → ℤ) :
    α ∈ l ↔ IsRoot .G2 α ∧ P α := by
  rw [← List.mem_toFinset, ← h, Finset.mem_filter, mem_rootFinset]

theorem mem_lA_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ lA ↔ α ∈ hset 1 := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ (1 : ℤ) ≤ height β) =
      lA.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ (1 : ℤ) ≤ height β) h α

theorem mem_lW_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ lW ↔ α ∈ wset := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ β ≠ ![0, 1]) =
      lW.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ β ≠ ![0, 1]) h α

theorem mem_l2_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ l2 ↔ α ∈ hset 2 := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ (2 : ℤ) ≤ height β) =
      l2.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ (2 : ℤ) ≤ height β) h α

theorem mem_l3_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ l3 ↔ α ∈ hset 3 := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ (3 : ℤ) ≤ height β) =
      l3.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ (3 : ℤ) ≤ height β) h α

theorem mem_l4_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ l4 ↔ α ∈ hset 4 := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ (4 : ℤ) ≤ height β) =
      l4.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ (4 : ℤ) ≤ height β) h α

theorem mem_l5_iff (α : Fin Tag.G2.rank → ℤ) :
    α ∈ l5 ↔ α ∈ hset 5 := by
  have h : (rootFinset .G2).filter (fun β => 0 < height β ∧ (5 : ℤ) ≤ height β) =
      l5.toFinset := by decide +kernel
  exact mem_iff_of_filter (P := fun β => 0 < height β ∧ (5 : ℤ) ≤ height β) h α

theorem lA_nodup : lA.Nodup := by decide

theorem lW_nodup : lW.Nodup := by decide

theorem l2_nodup : l2.Nodup := by decide

theorem l3_nodup : l3.Nodup := by decide

theorem l4_nodup : l4.Nodup := by decide

theorem l5_nodup : l5.Nodup := by decide

theorem hset_pos {h : ℤ} : ∀ α ∈ hset h, IsRoot .G2 α ∧ 0 < height α := fun _ hα => ⟨hα.1, hα.2.1⟩

theorem hset_closed {h : ℤ} (hh : 1 ≤ h) :
    ∀ α ∈ hset h, ∀ β ∈ hset h, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .G2 (a • α + b • β) →
      a • α + b • β ∈ hset h := by
  intro α hα β hβ a b ha hb hr
  obtain ⟨hr', hp, hle⟩ := nsmul_add_nsmul_mem_heightSet (k := h) (h := h)
    ⟨hα.2.1, hα.2.2⟩ ⟨hβ.2.1, hβ.2.2⟩ ha hb hr
  exact ⟨hr', hp, by linarith⟩

theorem wset_pos : ∀ α ∈ wset, IsRoot .G2 α ∧ 0 < height α := fun _ hα => ⟨hα.1, hα.2.1⟩

theorem height_r : height (τ := .G2) (![0, 1] : Fin Tag.G2.rank → ℤ) = 1 := by
  decide +kernel

theorem wset_closed :
    ∀ α ∈ wset, ∀ β ∈ wset, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot .G2 (a • α + b • β) →
      a • α + b • β ∈ wset := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hh : height (a • α + b • β) = a * height α + b * height β :=
    height_nsmul_add_nsmul a b α β
  have h1 := hα.2.1
  have h2 := hβ.2.1
  refine ⟨hr, by rw [hh]; nlinarith, fun heq => ?_⟩
  have h3 : height (a • α + b • β) = height (τ := .G2) (![0, 1] : Fin Tag.G2.rank → ℤ) := by
    rw [heq]
  rw [hh, height_r] at h3
  nlinarith

theorem ncard_hset_one : (hset 1).ncard = 6 := by
  have h : hset 1 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (1 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_hset_two : (hset 2).ncard = 4 := by
  have h : hset 2 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (2 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_hset_three : (hset 3).ncard = 3 := by
  have h : hset 3 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (3 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_hset_four : (hset 4).ncard = 2 := by
  have h : hset 4 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (4 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_hset_five : (hset 5).ncard = 1 := by
  have h : hset 5 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (5 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_hset_six : (hset 6).ncard = 0 := by
  have h : hset 6 = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ (6 : ℤ) ≤ height β) := by
    ext d
    simp [hset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_wset : wset.ncard = 5 := by
  have h : wset = ↑((rootFinset .G2).filter fun β => 0 < height β ∧ β ≠ ![0, 1]) := by
    ext d
    simp [wset, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem height_a : height (τ := .G2) (![1, 0] : Fin Tag.G2.rank → ℤ) = 1 := by decide +kernel

theorem height_u : height (τ := .G2) (![1, 1] : Fin Tag.G2.rank → ℤ) = 2 := by decide +kernel

theorem height_v : height (τ := .G2) (![1, 2] : Fin Tag.G2.rank → ℤ) = 3 := by decide +kernel

theorem height_b : height (τ := .G2) (![1, 3] : Fin Tag.G2.rank → ℤ) = 4 := by decide +kernel

theorem height_c : height (τ := .G2) (![2, 3] : Fin Tag.G2.rank → ℤ) = 5 := by decide +kernel

theorem r_mem_lA : (![0, 1] : Fin Tag.G2.rank → ℤ) ∈ lA := List.mem_cons_self

theorem a_mem_lA : (![1, 0] : Fin Tag.G2.rank → ℤ) ∈ lA :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem u_mem_lA : (![1, 1] : Fin Tag.G2.rank → ℤ) ∈ lA :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem v_mem_lA : (![1, 2] : Fin Tag.G2.rank → ℤ) ∈ lA :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem b_mem_lA : (![1, 3] : Fin Tag.G2.rank → ℤ) ∈ lA :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem c_mem_lA : (![2, 3] : Fin Tag.G2.rank → ℤ) ∈ lA :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))))

theorem a_mem_lW : (![1, 0] : Fin Tag.G2.rank → ℤ) ∈ lW := List.mem_cons_self

theorem mem_hset_of {α : Fin Tag.G2.rank → ℤ} {h : ℤ}
    (hα : α ∈ lA) (hh : h ≤ height α) : α ∈ hset h :=
  ⟨((mem_lA_iff α).1 hα).1, ((mem_lA_iff α).1 hα).2.1, hh⟩

theorem hset_two_sub_wset : ∀ α ∈ hset 2, α ∈ wset := by
  intro α hα
  refine ⟨hα.1, hα.2.1, fun h => ?_⟩
  have h2 := hα.2.2
  rw [h, height_r] at h2
  omega

theorem wset_sub_hset_one : ∀ α ∈ wset, α ∈ hset 1 := fun α hα => ⟨hα.1, hα.2.1, by
  have := hα.2.1
  omega⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47
open scoped commutatorElement

@[expose] def Wg (F : Type) [Field F] : Subgroup (ModGL .G2 F) := rootSpan .G2 F wset

variable {F : Type} [Field F]

theorem pinnedX_mem_hset {α : Fin Tag.G2.rank → ℤ} {h : ℤ} (hα : α ∈ hset h) (c : F) :
    pinnedX .G2 F α c ∈ heightSeries .G2 F h :=
  (le_iSup₂_of_le α hα le_rfl : rootSubgroup .G2 F α ≤ rootSpan .G2 F (hset h))
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem pinnedX_mem_Wg {α : Fin Tag.G2.rank → ℤ} (hα : α ∈ wset) (c : F) :
    pinnedX .G2 F α c ∈ Wg F :=
  (le_iSup₂_of_le α hα le_rfl : rootSubgroup .G2 F α ≤ rootSpan .G2 F wset)
    (Subgroup.subset_closure ⟨c, rfl⟩)

theorem Xr_mem_hs {h : ℤ} (hh : h ≤ 1) (x : F) : Xr x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![0, 1]) r_mem_lA (by rw [height_r]; exact hh)) x

theorem Xa_mem_hs {h : ℤ} (hh : h ≤ 1) (x : F) : Xa x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![1, 0]) a_mem_lA (by rw [height_a]; exact hh)) x

theorem Xu_mem_hs {h : ℤ} (hh : h ≤ 2) (x : F) : Xu x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![1, 1]) u_mem_lA (by rw [height_u]; exact hh)) x

theorem Xv_mem_hs {h : ℤ} (hh : h ≤ 3) (x : F) : Xv x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![1, 2]) v_mem_lA (by rw [height_v]; exact hh)) x

theorem Xb_mem_hs {h : ℤ} (hh : h ≤ 4) (x : F) : Xb x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![1, 3]) b_mem_lA (by rw [height_b]; exact hh)) x

theorem Xc_mem_hs {h : ℤ} (hh : h ≤ 5) (x : F) : Xc x ∈ heightSeries .G2 F h :=
  pinnedX_mem_hset (mem_hset_of (α := ![2, 3]) c_mem_lA (by rw [height_c]; exact hh)) x

theorem Xa_mem_Wg (x : F) : Xa x ∈ Wg F :=
  pinnedX_mem_Wg (α := ![1, 0]) ((mem_lW_iff _).1 a_mem_lW) x

theorem hs_two_le_Wg : heightSeries .G2 F 2 ≤ Wg F := biSup_mono hset_two_sub_wset

theorem Wg_le_hs_one : Wg F ≤ heightSeries .G2 F 1 := biSup_mono wset_sub_hset_one

theorem dec1 {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F 1) :
    ∃ t s : F, ∃ n ∈ heightSeries .G2 F 2, g = Xr t * Xa s * n := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := hset 1) hset_pos (hset_closed le_rfl)
    lA_nodup mem_lA_iff hg
  have h6 : (lA.map fun α => pinnedX .G2 F α (c α)).prod = Xr (c ![0, 1]) * (Xa (c ![1, 0]) *
      (Xu (c ![1, 1]) * (Xv (c ![1, 2]) * (Xb (c ![1, 3]) * (Xc (c ![2, 3]) * 1))))) := rfl
  refine ⟨c ![0, 1], c ![1, 0], Xu (c ![1, 1]) * (Xv (c ![1, 2]) * (Xb (c ![1, 3]) *
    Xc (c ![2, 3]))), mul_mem (Xu_mem_hs le_rfl _) (mul_mem (Xv_mem_hs (by norm_num) _)
    (mul_mem (Xb_mem_hs (by norm_num) _) (Xc_mem_hs (by norm_num) _))), ?_⟩
  rw [← hc, h6]
  simp only [mul_one, mul_assoc]

theorem decW {g : ModGL .G2 F} (hg : g ∈ Wg F) :
    ∃ s : F, ∃ n ∈ heightSeries .G2 F 2, g = Xa s * n := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := wset) wset_pos wset_closed
    lW_nodup mem_lW_iff hg
  have h6 : (lW.map fun α => pinnedX .G2 F α (c α)).prod = Xa (c ![1, 0]) *
      (Xu (c ![1, 1]) * (Xv (c ![1, 2]) * (Xb (c ![1, 3]) * (Xc (c ![2, 3]) * 1)))) := rfl
  refine ⟨c ![1, 0], Xu (c ![1, 1]) * (Xv (c ![1, 2]) * (Xb (c ![1, 3]) * Xc (c ![2, 3]))),
    mul_mem (Xu_mem_hs le_rfl _) (mul_mem (Xv_mem_hs (by norm_num) _)
    (mul_mem (Xb_mem_hs (by norm_num) _) (Xc_mem_hs (by norm_num) _))), ?_⟩
  rw [← hc, h6]
  simp only [mul_one]

theorem dec2 {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F 2) :
    ∃ w : F, ∃ n ∈ heightSeries .G2 F 3, g = Xu w * n := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := hset 2) hset_pos
    (hset_closed (by norm_num)) l2_nodup mem_l2_iff hg
  have h6 : (l2.map fun α => pinnedX .G2 F α (c α)).prod = Xu (c ![1, 1]) *
      (Xv (c ![1, 2]) * (Xb (c ![1, 3]) * (Xc (c ![2, 3]) * 1))) := rfl
  refine ⟨c ![1, 1], Xv (c ![1, 2]) * (Xb (c ![1, 3]) * Xc (c ![2, 3])),
    mul_mem (Xv_mem_hs le_rfl _) (mul_mem (Xb_mem_hs (by norm_num) _)
    (Xc_mem_hs (by norm_num) _)), ?_⟩
  rw [← hc, h6]
  simp only [mul_one]

theorem dec3 {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F 3) :
    ∃ x : F, ∃ n ∈ heightSeries .G2 F 4, g = Xv x * n := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := hset 3) hset_pos
    (hset_closed (by norm_num)) l3_nodup mem_l3_iff hg
  have h6 : (l3.map fun α => pinnedX .G2 F α (c α)).prod = Xv (c ![1, 2]) *
      (Xb (c ![1, 3]) * (Xc (c ![2, 3]) * 1)) := rfl
  refine ⟨c ![1, 2], Xb (c ![1, 3]) * Xc (c ![2, 3]),
    mul_mem (Xb_mem_hs le_rfl _) (Xc_mem_hs (by norm_num) _), ?_⟩
  rw [← hc, h6]
  simp only [mul_one]

theorem dec4 {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F 4) :
    ∃ y : F, ∃ n ∈ heightSeries .G2 F 5, g = Xb y * n := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := hset 4) hset_pos
    (hset_closed (by norm_num)) l4_nodup mem_l4_iff hg
  have h6 : (l4.map fun α => pinnedX .G2 F α (c α)).prod = Xb (c ![1, 3]) *
      (Xc (c ![2, 3]) * 1) := rfl
  refine ⟨c ![1, 3], Xc (c ![2, 3]), Xc_mem_hs le_rfl _, ?_⟩
  rw [← hc, h6]
  simp only [mul_one]

theorem dec5 {g : ModGL .G2 F} (hg : g ∈ heightSeries .G2 F 5) : ∃ z : F, g = Xc z := by
  obtain ⟨c, hc⟩ := exists_list_prod_pinnedX_eq F (S := hset 5) hset_pos
    (hset_closed (by norm_num)) l5_nodup mem_l5_iff hg
  have h6 : (l5.map fun α => pinnedX .G2 F α (c α)).prod = Xc (c ![2, 3]) * 1 := rfl
  refine ⟨c ![2, 3], ?_⟩
  rw [← hc, h6]
  simp only [mul_one]

theorem card_hs [Finite F] {h : ℤ} (hh : 1 ≤ h) :
    Nat.card (heightSeries .G2 F h) = Nat.card F ^ (hset h).ncard :=
  (positive_root_height_series .G2 F).2.2.2.2.2.2 h hh

theorem card_hs_one [Finite F] : Nat.card (heightSeries .G2 F 1) = Nat.card F ^ 6 := by
  rw [card_hs le_rfl, ncard_hset_one]

theorem card_Wg [Finite F] : Nat.card (Wg F) = Nat.card F ^ 5 := by
  rw [Wg, card_rootSpan wset_pos wset_closed, ncard_wset]

theorem card_hs_two [Finite F] : Nat.card (heightSeries .G2 F 2) = Nat.card F ^ 4 := by
  rw [card_hs (by norm_num), ncard_hset_two]

theorem card_hs_three [Finite F] : Nat.card (heightSeries .G2 F 3) = Nat.card F ^ 3 := by
  rw [card_hs (by norm_num), ncard_hset_three]

theorem card_hs_four [Finite F] : Nat.card (heightSeries .G2 F 4) = Nat.card F ^ 2 := by
  rw [card_hs (by norm_num), ncard_hset_four]

theorem card_hs_five [Finite F] : Nat.card (heightSeries .G2 F 5) = Nat.card F := by
  rw [card_hs (by norm_num), ncard_hset_five, pow_one]

theorem hs_six_eq_bot [Finite F] : heightSeries .G2 F 6 = ⊥ := by
  have h : Nat.card (heightSeries .G2 F 6) = 1 := by
    rw [card_hs (by norm_num), ncard_hset_six, pow_zero]
  exact Subgroup.card_eq_one.1 h

theorem eq_zero_of_Xu_mem {a : F} (h : Xu a ∈ heightSeries .G2 F 3) : a = 0 := by
  obtain ⟨x, n, hn, hxn⟩ := dec3 h
  obtain ⟨y, m, hm, hym⟩ := dec4 hn
  obtain ⟨z, hz⟩ := dec5 hm
  rw [hz] at hym
  rw [hym] at hxn
  have := inj4 (p₁ := a) (p₂ := 0) (p₃ := 0) (p₄ := 0) (q₁ := 0) (q₂ := x) (q₃ := y) (q₄ := z)
    (by simp only [Xu_zero, Xv_zero, Xb_zero, Xc_zero, one_mul, mul_one, mul_assoc]; exact hxn)
  exact this.1

theorem eq_zero_of_Xv_mem {a : F} (h : Xv a ∈ heightSeries .G2 F 4) : a = 0 := by
  obtain ⟨y, m, hm, hym⟩ := dec4 h
  obtain ⟨z, hz⟩ := dec5 hm
  rw [hz] at hym
  have := inj4 (p₁ := 0) (p₂ := a) (p₃ := 0) (p₄ := 0) (q₁ := 0) (q₂ := 0) (q₃ := y) (q₄ := z)
    (by simp only [Xu_zero, Xv_zero, Xb_zero, Xc_zero, one_mul, mul_one, mul_assoc]; exact hym)
  exact this.2.1

theorem eq_zero_of_Xb_mem {a : F} (h : Xb a ∈ heightSeries .G2 F 5) : a = 0 := by
  obtain ⟨z, hz⟩ := dec5 h
  have := inj4 (p₁ := 0) (p₂ := 0) (p₃ := a) (p₄ := 0) (q₁ := 0) (q₂ := 0) (q₃ := 0) (q₄ := z)
    (by simp only [Xu_zero, Xv_zero, Xb_zero, Xc_zero, one_mul, mul_one, mul_assoc]; exact hz)
  exact this.2.2.1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.G2Rank
