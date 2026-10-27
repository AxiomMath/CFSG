module

public import CFSG.LieType.TitsSimplicity.LeviDatum

public section

namespace CFSG.LieType.TitsSimplicity.Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem.Restrict

variable {G : Type*} [Group G] {D : UniversalRootDatum G} {m : ℕ} {e : Fin m → Fin D.rank}
  (he : Function.Injective e) {n : Fin D.rank → G} {H : Fin D.rank → Subgroup G}
  (hdiv : D.divisible = ∅)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType

namespace CT

theorem rankOne_le_leviC (i : Fin m) : rankOne D.rootGroup (e i) ≤ leviC D e :=
  rankOne_le_levi D.rootGroup (Finset.mem_image_of_mem e (Finset.mem_univ i))

theorem rootGroup_single_le_leviC (i : Fin m) :
    D.rootGroup (Pi.single (e i) 1) ≤ leviC D e :=
  le_sup_left.trans (rankOne_le_leviC i)

theorem rootGroup_neg_single_le_leviC (i : Fin m) :
    D.rootGroup (-Pi.single (e i) 1) ≤ leviC D e :=
  le_sup_right.trans (rankOne_le_leviC i)

include he in
theorem ext_neg_single (i : Fin m) : ext e (-Pi.single i 1) = -Pi.single (e i) 1 := by
  have h := ext_smul he (-1) (Pi.single i 1)
  rwa [neg_one_smul, neg_one_smul, ext_single he] at h

variable (X : (Fin m → ℤ) → Subgroup ↥(leviC D e))
  (hX : ∀ γ, X γ = (D.rootGroup (ext e γ)).subgroupOf (leviC D e))

include hX in
theorem mem_iff {γ : Fin m → ℤ} {x : ↥(leviC D e)} :
    x ∈ X γ ↔ (x : G) ∈ D.rootGroup (ext e γ) := by
  rw [hX γ]
  exact Subgroup.mem_subgroupOf

include he hX in
theorem rankOne_eq (i : Fin m) :
    rankOne X i = (rankOne D.rootGroup (e i)).subgroupOf (leviC D e) := by
  unfold rankOne
  rw [hX, hX, ext_single he, ext_neg_single he,
    Subgroup.subgroupOf_sup (rootGroup_single_le_leviC i) (rootGroup_neg_single_le_leviC i)]

include he hX in
theorem iSup_rankOne_eq_top : ⨆ i : Fin m, rankOne X i = ⊤ := by
  have hle : leviC D e ≤ (⨆ i : Fin m, rankOne X i).map (leviC D e).subtype := by
    refine iSup₂_le fun j hj => ?_
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hj
    calc rankOne D.rootGroup (e i)
        = ((rankOne D.rootGroup (e i)).subgroupOf (leviC D e)).map (leviC D e).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (rankOne_le_leviC i)).symm
      _ = (rankOne X i).map (leviC D e).subtype := by rw [rankOne_eq he X hX]
      _ ≤ (⨆ i : Fin m, rankOne X i).map (leviC D e).subtype :=
          Subgroup.map_mono (le_iSup (fun i => rankOne X i) i)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp (hle x.2)
  exact (Subtype.ext hxy : y = x) ▸ hy

theorem map_alternatingWord {α β : Type*} (f : α → β) (i j : α) (k : ℕ) :
    (CoxeterSystem.alternatingWord i j k).map f =
      CoxeterSystem.alternatingWord (f i) (f j) k := by
  induction k generalizing i j with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ k ih => simp [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, ih]

include he in
theorem map_braidWord (i j : Fin m) :
    (CoxeterSystem.braidWord (coxeterMatrix (D.isFiniteType.submatrix he)) i j).map e =
      CoxeterSystem.braidWord (coxeterMatrix D.isFiniteType) (e i) (e j) := by
  simp only [CoxeterSystem.braidWord]
  rw [map_alternatingWord, coxeterMatrix_submatrix_apply he]

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct in
theorem coe_list_prod_nC (l : List (Fin m)) :
    (((l.map (nC D n e)).prod : ↥(leviC D e)) : G) = ((l.map e).map n).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, coe_nC hct]

include he hdiv hct hX in
theorem isCTGroupDatum_aux :
    IsCTGroupDatum (coxeterMatrix (D.isFiniteType.submatrix he)).toCoxeterSystem
      (weylAction (D.isFiniteType.submatrix he)) (roots (D.isFiniteType.submatrix he) ∅) X
      (nC D n e) (HC D H e) := by
  have hroots : ∀ γ : Fin m → ℤ,
      γ ∈ roots (D.isFiniteType.submatrix he) ∅ → ext e γ ∈ D.roots := fun γ hγ =>
    (restrict_roots he hdiv γ).mp hγ
  have hΦ := isCTRootSystem (D.isFiniteType.submatrix he) ∅
  have hneg : ∀ i : Fin m, (-Pi.single i 1 : Fin m → ℤ) ∈ roots (D.isFiniteType.submatrix he) ∅ :=
    fun i => by
      have := hΦ.smul_mem ((coxeterMatrix (D.isFiniteType.submatrix he)).toCoxeterSystem.simple i)
        _ (hΦ.single_mem i)
      rwa [hΦ.simple_single] at this
  have hle : ∀ i : Fin m, H (e i) ≤ leviC D e := fun i =>
    (hct.H_le (e i)).trans (rankOne_le_leviC i)
  refine
    { n_mem := fun i => ?_, conj_mem := fun i γ hγ x hx => ?_, braid := fun i j => ?_,
      H_le := fun i => ?_, sq_mem := fun i => ?_, H_conj_mem := fun k γ hγ h hh x hx => ?_,
      conj_H_mem := fun j k h hh => ?_, le_rankOne := fun i γ hγ hsupp => ?_,
      iSup_eq_top := ?_ }
  · rw [rankOne_eq he X hX, Subgroup.mem_subgroupOf, coe_nC hct]
    exact hct.n_mem (e i)
  · rw [mem_iff X hX] at hx ⊢
    have h := hct.conj_mem (e i) (ext e γ) (hroots γ hγ) (x : G) hx
    rw [weylAction_simple, reflection_ext he i γ] at h
    rw [weylAction_simple, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_nC hct]
    exact h
  · apply Subtype.ext
    rw [coe_list_prod_nC hct, coe_list_prod_nC hct, map_braidWord he, map_braidWord he]
    exact hct.braid (e i) (e j)
  · rw [rankOne_eq he X hX]
    exact Subgroup.subgroupOf_mono _ (hct.H_le (e i))
  · change _ ∈ (H (e i)).subgroupOf (leviC D e)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, coe_nC hct]
    exact hct.sq_mem (e i)
  · rw [mem_iff X hX] at hx ⊢
    exact hct.H_conj_mem (e k) (ext e γ) (hroots γ hγ) h hh x hx
  · change _ ∈ (H (e j)).subgroupOf (leviC D e) ⊔ (H (e k)).subgroupOf (leviC D e)
    rw [← Subgroup.subgroupOf_sup (hle j) (hle k), Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_nC hct]
    exact hct.conj_H_mem (e j) (e k) h hh
  · have hsupp' : ∀ k, k ≠ e i → ext e γ k = 0 := by
      intro k hk
      by_cases hr : k ∈ Set.range e
      · obtain ⟨k', rfl⟩ := hr
        rw [ext_apply he]
        exact hsupp k' fun h => hk (by rw [h])
      · exact ext_apply_of_notMem_range (e := e) γ hr
    rw [hX γ, rankOne_eq he X hX]
    exact Subgroup.subgroupOf_mono _ (hct.le_rankOne (e i) (ext e γ) (hroots γ hγ) hsupp')
  · refine eq_top_iff.mpr ?_
    rw [← iSup_rankOne_eq_top he X hX]
    exact iSup_le fun i => sup_le (le_iSup₂_of_le _ (hΦ.single_mem i) le_rfl)
      (le_iSup₂_of_le _ (hneg i) le_rfl)

end CT

variable (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)

include hct hdiv in
theorem restrict_isCTGroupDatum :
    IsCTGroupDatum (coxeterMatrix (restrict D he).isFiniteType).toCoxeterSystem
      (weylAction (restrict D he).isFiniteType) (restrict D he).roots (restrict D he).rootGroup
      (nC D n e) (HC D H e) :=
  CT.isCTGroupDatum_aux he hdiv _ (fun _ => rfl) hct

end CFSG.LieType.TitsSimplicity.Levi
