module

public import CFSG.Foundations.Basic
public import CFSG.Open.CurtisTitsPresentationMilestoneDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.LieType.Universal.SpecialLinear

open Matrix
open scoped commutatorElement

variable (m : ℕ) (F : Type) [Field F]

@[expose] noncomputable def rootSubgroup {i j : Fin (m + 1)} (hij : i ≠ j) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  (SpecialLinearGroup.transvectionHom hij).range

@[expose] noncomputable def fundamentalRootSubgroup (k : Fin m) :
    Bool → Subgroup (SpecialLinearGroup (Fin (m + 1)) F)
  | true => rootSubgroup m F (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  | false => rootSubgroup m F (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne'

@[expose] noncomputable def levi (J : Finset (Fin m)) :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  ⨆ k ∈ J, ⨆ s : Bool, fundamentalRootSubgroup m F k s

variable {m F}

theorem mem_rootSubgroup {i j : Fin (m + 1)} (hij : i ≠ j)
    (g : SpecialLinearGroup (Fin (m + 1)) F) :
    g ∈ rootSubgroup m F hij ↔ ∃ c : F, SpecialLinearGroup.transvection hij c = g := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.toAdd c, by simp⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, by simp⟩

theorem transvection_mem_rootSubgroup {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ∈ rootSubgroup m F hij :=
  (mem_rootSubgroup hij _).mpr ⟨c, rfl⟩

private noncomputable abbrev fundamentalSpan (m : ℕ) (F : Type) [Field F] :
    Subgroup (SpecialLinearGroup (Fin (m + 1)) F) :=
  ⨆ k : Fin m, ⨆ s : Bool, fundamentalRootSubgroup m F k s

private theorem fundamental_le_span (k : Fin m) (s : Bool) :
    fundamentalRootSubgroup m F k s ≤ fundamentalSpan m F :=
  le_iSup_of_le k (le_iSup (fun s => fundamentalRootSubgroup m F k s) s)

private theorem adjacent_up_mem (i j : Fin (m + 1)) (h : i ≠ j) (hij : j.val = i.val + 1)
    (c : F) : SpecialLinearGroup.transvection h c ∈ fundamentalSpan m F := by
  have hi : i.val < m := by omega
  obtain ⟨k, rfl⟩ : ∃ k : Fin m, k.castSucc = i := ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
  rw [Fin.val_castSucc] at hij
  obtain rfl : j = k.succ := Fin.ext (by rw [Fin.val_succ]; omega)
  exact fundamental_le_span k true (transvection_mem_rootSubgroup _ c)

private theorem adjacent_down_mem (i j : Fin (m + 1)) (h : i ≠ j) (hij : i.val = j.val + 1)
    (c : F) : SpecialLinearGroup.transvection h c ∈ fundamentalSpan m F := by
  have hj : j.val < m := by omega
  obtain ⟨k, rfl⟩ : ∃ k : Fin m, k.castSucc = j := ⟨⟨j.val, hj⟩, Fin.ext rfl⟩
  rw [Fin.val_castSucc] at hij
  obtain rfl : i = k.succ := Fin.ext (by rw [Fin.val_succ]; omega)
  exact fundamental_le_span k false (transvection_mem_rootSubgroup _ c)

private theorem commutatorElement_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem up_mem (d : ℕ) : ∀ (i j : Fin (m + 1)) (h : i ≠ j), j.val = i.val + d + 1 →
    ∀ c : F, SpecialLinearGroup.transvection h c ∈ fundamentalSpan m F := by
  induction d with
  | zero => exact fun i j h hij c => adjacent_up_mem i j h (by omega) c
  | succ d ih =>
    intro i j h hij c
    let l : Fin (m + 1) := ⟨i.val + 1, by omega⟩
    have hil : i ≠ l := fun e => by have := congrArg Fin.val e; simp [l] at this
    have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [l] at this; omega
    have key := SpecialLinearGroup.commutatorElement_transvection hil hlj h c (1 : F)
    rw [mul_one] at key
    rw [← key]
    exact commutatorElement_mem _ (adjacent_up_mem i l hil rfl c)
      (ih l j hlj (by simp [l]; omega) 1)

private theorem down_mem (d : ℕ) : ∀ (i j : Fin (m + 1)) (h : i ≠ j), i.val = j.val + d + 1 →
    ∀ c : F, SpecialLinearGroup.transvection h c ∈ fundamentalSpan m F := by
  induction d with
  | zero => exact fun i j h hij c => adjacent_down_mem i j h (by omega) c
  | succ d ih =>
    intro i j h hij c
    let l : Fin (m + 1) := ⟨i.val - 1, by omega⟩
    have hil : i ≠ l := fun e => by have := congrArg Fin.val e; simp [l] at this; omega
    have hlj : l ≠ j := fun e => by have := congrArg Fin.val e; simp [l] at this; omega
    have key := SpecialLinearGroup.commutatorElement_transvection hil hlj h c (1 : F)
    rw [mul_one] at key
    rw [← key]
    exact commutatorElement_mem _ (adjacent_down_mem i l hil (by simp [l]; omega) c)
      (ih l j hlj (by simp [l]; omega) 1)

theorem transvection_mem_iSup_fundamental {i j : Fin (m + 1)} (hij : i ≠ j) (c : F) :
    SpecialLinearGroup.transvection hij c ∈
      ⨆ k : Fin m, ⨆ s : Bool, fundamentalRootSubgroup m F k s := by
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact up_mem (j.val - i.val - 1) i j hij (by omega) c
  · exact down_mem (i.val - j.val - 1) i j hij (by omega) c

theorem iSup_fundamentalRootSubgroup_eq_top :
    ⨆ k : Fin m, ⨆ s : Bool, fundamentalRootSubgroup m F k s = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  exact transvection_mem_iSup_fundamental hij c

theorem iSup_levi_eq_top :
    ⨆ J : {J : Finset (Fin m) // J.card ≤ 2}, levi m F J.1 = ⊤ := by
  rw [eq_top_iff, ← iSup_fundamentalRootSubgroup_eq_top, iSup_le_iff]
  intro k
  have hk : ({k} : Finset (Fin m)).card ≤ 2 := by simp
  refine le_trans ?_ (le_iSup (fun J : {J : Finset (Fin m) // J.card ≤ 2} => levi m F J.1)
    ⟨{k}, hk⟩)
  simp only [levi, Finset.mem_singleton, iSup_iSup_eq_left, le_refl]

variable (m F) in
theorem levi_eq_curtisTitsLevi (J : Finset (Fin m)) :
    levi m F J = CFSG.Open.curtisTitsLevi m F J := by
  apply le_antisymm
  · simp only [levi, iSup_le_iff]
    intro k hk s x hx
    apply Subgroup.subset_closure
    cases s
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
      exact ⟨k, hk, c, .inr (by rw [SpecialLinearGroup.transvection_coe]; rfl)⟩
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ x).mp hx
      exact ⟨k, hk, c, .inl (by rw [SpecialLinearGroup.transvection_coe]; rfl)⟩
  · rw [CFSG.Open.curtisTitsLevi, Subgroup.closure_le]
    rintro A ⟨k, hk, c, hA | hA⟩
    · have hAeq : A = SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne c := by
        ext1
        rw [hA, SpecialLinearGroup.transvection_coe, Matrix.transvection]
      rw [hAeq]
      exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem hk
        (Subgroup.mem_iSup_of_mem true (transvection_mem_rootSubgroup _ c)))
    · have hAeq : A = SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne' c := by
        ext1
        rw [hA, SpecialLinearGroup.transvection_coe, Matrix.transvection]
      rw [hAeq]
      exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem hk
        (Subgroup.mem_iSup_of_mem false (transvection_mem_rootSubgroup _ c)))

variable (m F) in
theorem isQuasisimple (hm : 2 ≤ m) : IsQuasisimple (SpecialLinearGroup (Fin (m + 1)) F) := by
  have hperf : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  have hsimple : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin (m + 1)) F) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 (m + 1) (by omega) (.inl (by omega))
      (.inl (by omega))
  refine ⟨hperf, hsimple, ?_⟩
  by_contra hcomm
  simp only [not_exists, not_not] at hcomm
  have : IsMulCommutative (ProjectiveSpecialLinearGroup (Fin (m + 1)) F) := ⟨⟨hcomm⟩⟩
  exact Group.IsPerfect.not_isMulCommutative _ this

open CFSG.Assembly.LowTwoRank in
variable (m F) in
theorem statedClassicalModel_center_quotient [Finite F] {p f : ℕ}
    (hadm : StatedLieAdmissible .PSL (m + 1) p f) (hF : Nat.card F = p ^ f) :
    StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin (m + 1)) F) .PSL (m + 1) p f :=
  ⟨hadm, F, inferInstance, inferInstance, hF,
    ⟨projectiveSpecialLinearGroupEquivStatedProj (m + 1) F⟩⟩

end CFSG.LieType.Universal.SpecialLinear
