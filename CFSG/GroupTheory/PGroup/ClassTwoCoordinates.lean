module

public import CFSG.Quasithin.Vol2.KGFactC31EBasis
import CFSG.GroupTheory.SuzukiTwoGroupsQuadratic

public section

namespace CFSG.GroupTheory

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement Matrix

open CFSG.Quasithin.KGC31 (eElt eElt_zero eElt_single eElt_add eElt_injective conj_eElt map_eElt
  commute_eElt eElt_pow_val EBasis eSub eSub_sq eSub_eq_closure)

variable {G : Type*} [Group G]

@[expose]
def quadMapOfCoeffs {n d : ℕ} (sq : Fin n → Fin d → ZMod 2)
    (cm : Fin n → Fin n → Fin d → ZMod 2) (v : Fin n → ZMod 2) : Fin d → ZMod 2 :=
  ∑ i, v i • sq i + ∑ i, ∑ j, if i < j then (v i * v j) • cm i j else 0

theorem quadMapOfCoeffs_add {n d : ℕ} (sq sq' : Fin n → Fin d → ZMod 2)
    (cm cm' : Fin n → Fin n → Fin d → ZMod 2) (v : Fin n → ZMod 2) :
    quadMapOfCoeffs (sq + sq') (cm + cm') v =
      quadMapOfCoeffs sq cm v + quadMapOfCoeffs sq' cm' v := by
  have hrow : ∀ i : Fin n, (∑ j : Fin n,
        (if i < j then (v i * v j) • ((cm + cm') i j) else 0)) =
      (∑ j : Fin n, (if i < j then (v i * v j) • cm i j else 0)) +
        ∑ j : Fin n, (if i < j then (v i * v j) • cm' i j else 0) := by
    intro i
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · exact smul_add _ _ _
    · exact (add_zero 0).symm
  have hA : (∑ i : Fin n, v i • (sq + sq') i) =
      (∑ i : Fin n, v i • sq i) + ∑ i : Fin n, v i • sq' i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => smul_add _ _ _
  have hB : (∑ i : Fin n, ∑ j : Fin n,
        (if i < j then (v i * v j) • ((cm + cm') i j) else 0)) =
      (∑ i : Fin n, ∑ j : Fin n, (if i < j then (v i * v j) • cm i j else 0)) +
        ∑ i : Fin n, ∑ j : Fin n, (if i < j then (v i * v j) • cm' i j else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hrow i
  simp only [quadMapOfCoeffs]
  rw [hA, hB]
  abel

theorem quadMapOfCoeffs_mulVec_coeffs {n d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2))
    (sq : Fin n → Fin d → ZMod 2) (cm : Fin n → Fin n → Fin d → ZMod 2)
    (v : Fin n → ZMod 2) :
    quadMapOfCoeffs (fun i => A *ᵥ sq i) (fun i j => A *ᵥ cm i j) v =
      A *ᵥ quadMapOfCoeffs sq cm v := by
  have hrow : ∀ i : Fin n, (∑ j : Fin n,
        (if i < j then (v i * v j) • (A *ᵥ cm i j) else 0)) =
      A *ᵥ (∑ j : Fin n, (if i < j then (v i * v j) • cm i j else 0)) := by
    intro i
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · rw [if_pos hij, if_pos hij, Matrix.mulVec_smul (R := ZMod 2) A (v i * v j) (cm i j)]
    · rw [if_neg hij, if_neg hij, Matrix.mulVec_zero]
  rw [quadMapOfCoeffs, quadMapOfCoeffs, Matrix.mulVec_add, Matrix.mulVec_sum,
    Matrix.mulVec_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact (Matrix.mulVec_smul (R := ZMod 2) A (v i) (sq i)).symm
  · exact Finset.sum_congr rfl fun i _ => hrow i

theorem quadMapOfCoeffs_zero {n d : ℕ} (v : Fin n → ZMod 2) :
    quadMapOfCoeffs (0 : Fin n → Fin d → ZMod 2) 0 v = 0 := by
  simp [quadMapOfCoeffs]

theorem quadMapOfCoeffs_smul {n d : ℕ} (a : ZMod 2) (sq : Fin n → Fin d → ZMod 2)
    (cm : Fin n → Fin n → Fin d → ZMod 2) (v : Fin n → ZMod 2) :
    quadMapOfCoeffs (a • sq) (a • cm) v = a • quadMapOfCoeffs sq cm v := by
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
  · simpa using quadMapOfCoeffs_zero (n := n) (d := d) v
  · simp only [one_smul]

theorem quadMapOfCoeffs_sum {n d : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ZMod 2)
    (sq : ι → Fin n → Fin d → ZMod 2) (cm : ι → Fin n → Fin n → Fin d → ZMod 2)
    (v : Fin n → ZMod 2) :
    quadMapOfCoeffs (∑ x ∈ s, c x • sq x) (∑ x ∈ s, c x • cm x) v =
      ∑ x ∈ s, c x • quadMapOfCoeffs (sq x) (cm x) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, quadMapOfCoeffs_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, quadMapOfCoeffs_add,
      quadMapOfCoeffs_smul, ih, Finset.sum_insert ha]

theorem quadMapOfCoeffs_congr {n d : ℕ} {sq : Fin n → Fin d → ZMod 2}
    {cm cm' : Fin n → Fin n → Fin d → ZMod 2} (h : ∀ i j, i < j → cm i j = cm' i j)
    (v : Fin n → ZMod 2) : quadMapOfCoeffs sq cm v = quadMapOfCoeffs sq cm' v := by
  simp only [quadMapOfCoeffs]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · rw [h i j hij]
  · rfl

theorem toAdd_eElt {n d : ℕ} (f : Fin n → Multiplicative (Fin d → ZMod 2))
    (u : Fin n → ZMod 2) :
    (eElt f u).toAdd = ∑ i, (u i).val • (f i).toAdd := by
  simp [eElt, List.prod_ofFn]

theorem eElt_mem_of_forall_mem {n : ℕ} {H : Subgroup G} {f : Fin n → G}
    (hf : ∀ i, f i ∈ H) (v : Fin n → ZMod 2) : eElt f v ∈ H := by
  rw [eElt]
  exact Subgroup.list_prod_mem (K := H) fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact H.pow_mem (hf i) _

theorem eElt_append {m k : ℕ} (v : Fin m → G) (w : Fin k → G) (c : Fin m → ZMod 2)
    (d : Fin k → ZMod 2) :
    eElt (Fin.append v w) (Fin.append c d) = eElt v c * eElt w d := by
  have h : (fun i => Fin.append v w i ^ (Fin.append c d i).val) =
      Fin.append (fun i => v i ^ (c i).val) (fun j => w j ^ (d j).val) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp [Fin.append_left]
    · intro j
      simp [Fin.append_right]
  rw [eElt, eElt, eElt, h, List.ofFn_fin_append, List.prod_append]

theorem eElt_eq_castAdd_mul_natAdd {m n : ℕ} (f : Fin (m + n) → G)
    (v : Fin (m + n) → ZMod 2) :
    eElt f v = eElt (fun i : Fin m => f (Fin.castAdd n i)) (fun i => v (Fin.castAdd n i)) *
      eElt (fun j : Fin n => f (Fin.natAdd m j)) (fun j => v (Fin.natAdd m j)) := by
  conv_lhs => rw [← Fin.append_castAdd_natAdd (m := m) (n := n) (f := f)]
  conv_lhs => rw [← Fin.append_castAdd_natAdd (m := m) (n := n) (f := v)]
  exact eElt_append _ _ _ _

theorem eElt_ofAdd_cols {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    eElt (fun i => Multiplicative.ofAdd (fun j => B j i)) v =
      Multiplicative.ofAdd (B *ᵥ v) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_eElt]
  funext j
  simp only [toAdd_ofAdd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
    dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact mul_comm (v i) (B j i)

private theorem eElt_sum_list {d : ℕ} {z : Fin d → G} (hz2 : ∀ t, z t * z t = 1)
    (hzz : ∀ t s, Commute (z t) (z s)) (u : Fin d → Fin d → ZMod 2) :
    ∀ l : List (Fin d), eElt z ((l.map u).sum) = (l.map (fun t => eElt z (u t))).prod := by
  intro l
  induction l with
  | nil => simp [eElt_zero]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, ← ih, ← eElt_add hz2 hzz]

theorem eElt_eElt_eq_eElt_mulVec {d : ℕ} {z : Fin d → G} (hz2 : ∀ t, z t * z t = 1)
    (hzz : ∀ t s, Commute (z t) (z s)) (S : Matrix (Fin d) (Fin d) (ZMod 2))
    (u : Fin d → ZMod 2) :
    eElt (fun t => eElt z fun s => S s t) u = eElt z (S *ᵥ u) := by
  have hmv : S *ᵥ u = ∑ t : Fin d, u t • (fun s => S s t) := by
    funext s
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [eElt, List.ofFn_eq_map, hmv, Fin.sum_univ_def, eElt_sum_list hz2 hzz]
  congr 1
  refine List.map_congr_left ?_
  intro t _
  exact eElt_pow_val (v := z) (u t) (fun s => S s t)

theorem conj_eElt_eq_mulVec {d : ℕ} {z : Fin d → G} {g : G} (hz2 : ∀ t, z t * z t = 1)
    (hzz : ∀ t s, Commute (z t) (z s)) (S : Matrix (Fin d) (Fin d) (ZMod 2))
    (hgz : ∀ t, g * z t * g⁻¹ = eElt z fun s => S s t) (u : Fin d → ZMod 2) :
    g * eElt z u * g⁻¹ = eElt z (S *ᵥ u) := by
  rw [conj_eElt,
    show (fun t => g * z t * g⁻¹) = fun t => eElt z fun s => S s t from funext hgz]
  exact eElt_eElt_eq_eElt_mulVec hz2 hzz S u

theorem eElt_add_mul_inv_mem {n : ℕ} {Z : Subgroup G} {f : Fin n → G}
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (v w : Fin n → ZMod 2) :
    eElt f (v + w) * (eElt f v * eElt f w)⁻¹ ∈ Z := by
  classical
  let F : Subgroup G := Subgroup.closure (Set.range f)
  have hfF : ∀ i, f i ∈ F := fun i => Subgroup.subset_closure (Set.mem_range_self i)
  have hpowF : ∀ u : Fin n → ZMod 2, eElt f u ∈ F := fun u => eElt_mem_of_forall_mem hfF u
  have hFZ : F ≤ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.closure_le _).mpr <| Set.range_subset_iff.mpr fun i =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => hZc y hy i
  let Z' : Subgroup ↥F := Z.subgroupOf F
  have hZ'normal : Z'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (hFZ.trans (Subgroup.centralizer_le_normalizer _))
  haveI : Z'.Normal := hZ'normal
  let Q := ↥F ⧸ Z'
  let p : ↥F →* Q := QuotientGroup.mk' Z'
  let z : Fin n → Q := fun i => p ⟨f i, hfF i⟩
  have hp_one : ∀ x : ↥F, p x = 1 ↔ x ∈ Z' := by
    intro x
    rw [show p x = (x : Q) from rfl, QuotientGroup.eq_one_iff]
  have hz2 : ∀ i, z i ^ 2 = 1 := by
    intro i
    rw [show z i ^ 2 = p ((⟨f i, hfF i⟩ : ↥F) ^ 2) from (map_pow p _ 2).symm]
    rw [hp_one, Subgroup.mem_subgroupOf]
    simpa using hsq i
  have hzz : ∀ i j, Commute (z i) (z j) := by
    intro i j
    have hcoe : (((⟨f i, hfF i⟩ : ↥F) * (⟨f j, hfF j⟩ : ↥F) *
        ((⟨f j, hfF j⟩ : ↥F) * (⟨f i, hfF i⟩ : ↥F))⁻¹ : ↥F) : G) = ⁅f i, f j⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    have hmem : (⟨f i, hfF i⟩ : ↥F) * (⟨f j, hfF j⟩ : ↥F) *
        ((⟨f j, hfF j⟩ : ↥F) * (⟨f i, hfF i⟩ : ↥F))⁻¹ ∈ Z' := by
      rw [Subgroup.mem_subgroupOf, hcoe]
      exact hcm i j
    have h1 : p ((⟨f i, hfF i⟩ : ↥F) * (⟨f j, hfF j⟩ : ↥F) *
        ((⟨f j, hfF j⟩ : ↥F) * (⟨f i, hfF i⟩ : ↥F))⁻¹) = 1 := (hp_one _).mpr hmem
    have h2 : p ((⟨f i, hfF i⟩ : ↥F) * (⟨f j, hfF j⟩ : ↥F) *
        ((⟨f j, hfF j⟩ : ↥F) * (⟨f i, hfF i⟩ : ↥F))⁻¹) = z i * z j * (z j * z i)⁻¹ := by
      rw [map_mul, map_mul, map_inv, map_mul]
    rw [h2] at h1
    exact mul_inv_eq_one.mp h1
  have hmap : ∀ u : Fin n → ZMod 2, eElt z u = p ⟨eElt f u, hpowF u⟩ := by
    intro u
    rw [← map_eElt p u]
    congr 1
    exact Subtype.ext (by simpa using map_eElt (Subgroup.subtype F) u)
  have hmain : eElt z (v + w) = eElt z v * eElt z w :=
    eElt_add (fun i => (sq (z i)).symm.trans (hz2 i)) hzz v w
  rw [hmap, hmap, hmap] at hmain
  have hmem : (⟨eElt f (v + w), hpowF (v + w)⟩ : ↥F) *
      (⟨eElt f v, hpowF v⟩ * ⟨eElt f w, hpowF w⟩)⁻¹ ∈ Z' := by
    have h1 : p ((⟨eElt f (v + w), hpowF (v + w)⟩ : ↥F) *
        (⟨eElt f v, hpowF v⟩ * ⟨eElt f w, hpowF w⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, ← hmain, mul_inv_cancel]
    exact (hp_one _).mp h1
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem eElt_sum_list_mod {n : ℕ} {Z : Subgroup G} {f : Fin n → G}
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (u : Fin n → Fin n → ZMod 2) (l : List (Fin n)) :
    eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹ ∈ Z := by
  induction l with
  | nil =>
    have h1 : (List.map (fun j => eElt f (u j)) ([] : List (Fin n))).prod = 1 := by simp
    rw [List.map_nil, List.sum_nil, h1, inv_one, mul_one, eElt_zero]
    exact Z.one_mem
  | cons a l ih =>
    have h1 := eElt_add_mul_inv_mem hZc hsq hcm (u a) ((l.map u).sum)
    have hz : eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹ ∈ Z := ih
    have hABU : eElt f (u a) * eElt f ((l.map u).sum) *
        ((l.map fun j => eElt f (u j)).prod)⁻¹ * (eElt f (u a))⁻¹ ∈ Z := by
      have hA : eElt f (u a) * (eElt f ((l.map u).sum) *
          ((l.map fun j => eElt f (u j)).prod)⁻¹) =
          (eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹) *
            eElt f (u a) :=
        (commute_eElt (fun i => hZc _ hz i) (u a)).symm
      have heq : eElt f (u a) * eElt f ((l.map u).sum) *
          ((l.map fun j => eElt f (u j)).prod)⁻¹ * (eElt f (u a))⁻¹
          = eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹ := by
        calc eElt f (u a) * eElt f ((l.map u).sum) *
              ((l.map fun j => eElt f (u j)).prod)⁻¹ * (eElt f (u a))⁻¹
            = eElt f (u a) * (eElt f ((l.map u).sum) *
                ((l.map fun j => eElt f (u j)).prod)⁻¹) * (eElt f (u a))⁻¹ := by group
          _ = (eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹) *
                eElt f (u a) * (eElt f (u a))⁻¹ := by rw [hA]
          _ = eElt f ((l.map u).sum) * ((l.map fun j => eElt f (u j)).prod)⁻¹ := by group
      rw [heq]
      exact hz
    rw [List.map_cons, List.sum_cons, List.map_cons, List.prod_cons]
    have heq : eElt f (u a + (l.map u).sum) * (eElt f (u a) *
          (l.map fun j => eElt f (u j)).prod)⁻¹
        = (eElt f (u a + (l.map u).sum) *
            (eElt f (u a) * eElt f ((l.map u).sum))⁻¹) *
          (eElt f (u a) * eElt f ((l.map u).sum) *
            ((l.map fun j => eElt f (u j)).prod)⁻¹ * (eElt f (u a))⁻¹) := by group
    rw [heq]
    exact Z.mul_mem h1 hABU

private theorem eElt_sum_mod {n : ℕ} {Z : Subgroup G} {f : Fin n → G}
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (u : Fin n → Fin n → ZMod 2) :
    eElt f (∑ j : Fin n, u j) * ((List.finRange n).map (fun j => eElt f (u j))).prod⁻¹ ∈ Z := by
  rw [Fin.sum_univ_def]
  exact eElt_sum_list_mod hZc hsq hcm u (List.finRange n)

private theorem list_prod_mul_split {ι : Type*} {Z : Subgroup G} (l : List ι) (zz ff : ι → G)
    (e : ι → ZMod 2) (hz : ∀ i ∈ l, zz i ∈ Z)
    (hc : ∀ i ∈ l, ∀ y ∈ Z, ff i * y = y * ff i) :
    (l.map (fun i => (zz i * ff i) ^ (e i).val)).prod =
      (l.map (fun i => zz i ^ (e i).val)).prod *
        (l.map (fun i => ff i ^ (e i).val)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hza : zz a ∈ Z := hz a (by simp)
    have hz' : ∀ i ∈ l, zz i ∈ Z := fun i hi => hz i (by simp [hi])
    have hc' : ∀ i ∈ l, ∀ y ∈ Z, ff i * y = y * ff i := fun i hi => hc i (by simp [hi])
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      ih hz' hc']
    have h1 : (zz a * ff a) ^ (e a).val = zz a ^ (e a).val * ff a ^ (e a).val :=
      (show Commute (zz a) (ff a) from (hc a (by simp) (zz a) hza).symm).mul_pow _
    have h2 : Commute (ff a ^ (e a).val) ((l.map fun i => zz i ^ (e i).val).prod) := by
      refine Commute.list_prod_right _ _ ?_
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      exact ((show Commute (ff a) (zz i) from hc a (by simp) (zz i) (hz' i hi)).pow_pow _ _)
    rw [h1]
    calc zz a ^ (e a).val * ff a ^ (e a).val *
          ((l.map fun i => zz i ^ (e i).val).prod * (l.map fun i => ff i ^ (e i).val).prod)
        = zz a ^ (e a).val *
            (ff a ^ (e a).val * (l.map fun i => zz i ^ (e i).val).prod) *
            (l.map fun i => ff i ^ (e i).val).prod := by group
      _ = zz a ^ (e a).val *
            ((l.map fun i => zz i ^ (e i).val).prod * ff a ^ (e a).val) *
            (l.map fun i => ff i ^ (e i).val).prod := by rw [h2.eq]
      _ = (zz a ^ (e a).val * (l.map fun i => zz i ^ (e i).val).prod) *
            (ff a ^ (e a).val * (l.map fun i => ff i ^ (e i).val).prod) := by group

theorem eElt_mul_inv_mem_of_cols {n : ℕ} {Z : Subgroup G} {f f' : Fin n → G}
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (hf' : ∀ j, f' j * (eElt f fun i => R i j)⁻¹ ∈ Z) (v : Fin n → ZMod 2) :
    eElt f' v * (eElt f (R *ᵥ v))⁻¹ ∈ Z := by
  classical
  set ff : Fin n → G := fun j => eElt f (fun i => R i j) with hff
  set zz : Fin n → G := fun j => f' j * (ff j)⁻¹ with hzz
  have hzZ : ∀ j, zz j ∈ Z := by
    intro j
    simpa [hzz, hff] using hf' j
  have hfun : f' = fun j => zz j * ff j := by
    funext j
    simp only [hzz]
    group
  have hcommff : ∀ j, ∀ y ∈ Z, ff j * y = y * ff j := by
    intro j y hy
    exact (commute_eElt (fun i => hZc y hy i) _).symm
  rw [hfun]
  have hprod : eElt (fun j => zz j * ff j) v =
      (List.map (fun j => zz j ^ (v j).val) (List.finRange n)).prod *
        (List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod := by
    rw [eElt, List.ofFn_eq_map]
    exact list_prod_mul_split (List.finRange n) zz ff v (fun j _ => hzZ j) (fun j _ => hcommff j)
  have hPz : (List.map (fun j => zz j ^ (v j).val) (List.finRange n)).prod ∈ Z :=
    Subgroup.list_prod_mem (K := Z) fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
      exact Z.pow_mem (hzZ j) _
  have hstep1 : eElt (fun j => zz j * ff j) v *
      ((List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod)⁻¹ ∈ Z := by
    rw [hprod]
    rw [show (List.map (fun j => zz j ^ (v j).val) (List.finRange n)).prod *
          (List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod *
          ((List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod)⁻¹
        = (List.map (fun j => zz j ^ (v j).val) (List.finRange n)).prod from by group]
    exact hPz
  have hmv : R *ᵥ v = ∑ j : Fin n, v j • (fun i => R i j) := by
    funext i
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hstep2 : ((List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod) *
      (eElt f (R *ᵥ v))⁻¹ ∈ Z := by
    have hmap : (List.map (fun j => ff j ^ (v j).val) (List.finRange n)) =
        (List.map (fun j => eElt f (v j • fun i => R i j)) (List.finRange n)) := by
      refine List.map_congr_left ?_
      intro j _
      rw [hff]
      exact eElt_pow_val (v := f) (v j) (fun i => R i j)
    rw [hmap]
    have hmap2 : (List.map (fun j => eElt f (v j • fun i => R i j)) (List.finRange n)) =
        (List.map (fun j => eElt f fun i => v j * R i j) (List.finRange n)) := by
      refine List.map_congr_left ?_
      intro j _
      congr 1
    rw [hmap2]
    have hmv' : R *ᵥ v = ∑ j : Fin n, (fun i => v j * R i j) := by
      rw [hmv]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [hmv']
    have h := eElt_sum_mod hZc hsq hcm (fun j i => v j * R i j)
    rw [show (List.map (fun j => eElt f fun i => v j * R i j) (List.finRange n)).prod *
        (eElt f (∑ j : Fin n, (fun i => v j * R i j)))⁻¹
        = (eElt f (∑ j : Fin n, (fun i => v j * R i j)) *
            (List.map (fun j => eElt f fun i => v j * R i j) (List.finRange n)).prod⁻¹)⁻¹
        from by group]
    exact Z.inv_mem h
  rw [show eElt (fun j => zz j * ff j) v * (eElt f (R *ᵥ v))⁻¹
      = (eElt (fun j => zz j * ff j) v *
          ((List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod)⁻¹) *
        (((List.map (fun j => ff j ^ (v j).val) (List.finRange n)).prod) *
          (eElt f (R *ᵥ v))⁻¹) from by group]
  exact Z.mul_mem hstep1 hstep2

theorem conj_eElt_mul_inv_mem {n : ℕ} {Z : Subgroup G} {f : Fin n → G} {g : G}
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (hg : ∀ j, g * f j * g⁻¹ * (eElt f fun i => R i j)⁻¹ ∈ Z) (v : Fin n → ZMod 2) :
    g * eElt f v * g⁻¹ * (eElt f (R *ᵥ v))⁻¹ ∈ Z := by
  rw [conj_eElt]
  exact eElt_mul_inv_mem_of_cols hZc hsq hcm R hg v

theorem exists_eElt_mul {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q] {f : Fin n → G}
    (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q) (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y)
    (hsq : ∀ i, f i ^ 2 ∈ Z) (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z)
    (hind : ∀ v, eElt f v ∈ Z → v = 0) (hcard : Nat.card Q = 2 ^ n * Nat.card Z) :
    ∀ x ∈ Q, ∃ v : Fin n → ZMod 2, ∃ y ∈ Z, x = eElt f v * y := by
  classical
  let F : (Fin n → ZMod 2) × ↥Z → ↥Q := fun p =>
    ⟨eElt f p.1 * (p.2 : G), Q.mul_mem (eElt_mem_of_forall_mem hfQ p.1) (hZQ p.2.2)⟩
  have hinj : Function.Injective F := by
    rintro ⟨v, y⟩ ⟨v', y'⟩ h
    have hval : eElt f v * (y : G) = eElt f v' * (y' : G) := congrArg Subtype.val h
    have hy : (y' : G) * (y : G)⁻¹ ∈ Z := Z.mul_mem y'.2 (Z.inv_mem y.2)
    have hmain : eElt f v * (eElt f v')⁻¹ ∈ Z := by
      have h1 : eElt f v = eElt f v' * ((y' : G) * (y : G)⁻¹) := by
        have h2 := congrArg (fun t => t * (y : G)⁻¹) hval
        rw [mul_assoc, mul_inv_cancel, mul_one] at h2
        rw [h2, mul_assoc]
      have hcomm : ((y' : G) * (y : G)⁻¹) * eElt f v' =
          eElt f v' * ((y' : G) * (y : G)⁻¹) :=
        commute_eElt (fun i => hZc ((y' : G) * (y : G)⁻¹) hy i) v'
      rw [h1, ← hcomm]
      rw [show ((y' : G) * (y : G)⁻¹) * eElt f v' * (eElt f v')⁻¹
        = (y' : G) * (y : G)⁻¹ from by group]
      exact hy
    have hneg : eElt f v' * eElt f (-v') ∈ Z := by
      have h := eElt_add_mul_inv_mem hZc hsq hcm v' (-v')
      rw [add_neg_cancel, eElt_zero, one_mul] at h
      simpa using Z.inv_mem h
    have hw : eElt f (v + -v') ∈ Z := by
      have h := eElt_add_mul_inv_mem hZc hsq hcm v (-v')
      have hA : eElt f v * eElt f (-v') ∈ Z := by
        have hm := Z.mul_mem hmain hneg
        rwa [show eElt f v * (eElt f v')⁻¹ * (eElt f v' * eElt f (-v'))
            = eElt f v * eElt f (-v') from by group] at hm
      have := Z.mul_mem h hA
      rwa [show eElt f (v + -v') * (eElt f v * eElt f (-v'))⁻¹ *
          (eElt f v * eElt f (-v')) = eElt f (v + -v') from by group] at this
    have hvv : v = v' := by
      have h1 : v + -v' = 0 := hind _ hw
      rwa [add_eq_zero_iff_eq_neg, neg_neg] at h1
    subst hvv
    have hyy : (y : G) = (y' : G) := by
      have h2 : eElt f v * (y : G) = eElt f v * (y' : G) := hval
      exact mul_left_cancel h2
    exact Prod.ext rfl (Subtype.ext hyy)
  have hcard2 : Nat.card ((Fin n → ZMod 2) × ↥Z) = Nat.card ↥Q := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod, hcard]
  have hbij : Function.Bijective F :=
    (Nat.bijective_iff_injective_and_card F).mpr ⟨hinj, hcard2⟩
  intro x hx
  obtain ⟨p, hp⟩ := hbij.2 ⟨x, hx⟩
  refine ⟨p.1, p.2, p.2.2, ?_⟩
  have hval : (F p).val = x := congrArg Subtype.val hp
  rw [← hval]

private theorem eElt_castSucc {n : ℕ} (f : Fin (n + 1) → G) (v : Fin (n + 1) → ZMod 2) :
    eElt f v = eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc) *
      f (Fin.last n) ^ (v (Fin.last n)).val := by
  rw [eElt, eElt, List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]

private theorem quadMapOfCoeffs_castSucc {n d : ℕ} (sq : Fin (n + 1) → Fin d → ZMod 2)
    (cm : Fin (n + 1) → Fin (n + 1) → Fin d → ZMod 2) (v : Fin (n + 1) → ZMod 2) :
    quadMapOfCoeffs sq cm v =
      quadMapOfCoeffs (fun i => sq i.castSucc) (fun i j => cm i.castSucc j.castSucc)
          (fun i => v i.castSucc) +
        v (Fin.last n) • sq (Fin.last n) +
        ∑ i : Fin n, (v i.castSucc * v (Fin.last n)) • cm i.castSucc (Fin.last n) := by
  simp only [quadMapOfCoeffs]
  have hA : (∑ i : Fin (n + 1), v i • sq i) =
      (∑ i : Fin n, v i.castSucc • sq i.castSucc) + v (Fin.last n) • sq (Fin.last n) :=
    Fin.sum_univ_castSucc _
  have hrow : ∀ i : Fin n,
      (∑ j : Fin (n + 1), (if i.castSucc < j then (v i.castSucc * v j) • cm i.castSucc j else 0))
        = (∑ j : Fin n,
              (if i < j then (v i.castSucc * v j.castSucc) • cm i.castSucc j.castSucc else 0)) +
          (v i.castSucc * v (Fin.last n)) • cm i.castSucc (Fin.last n) := by
    intro i
    rw [Fin.sum_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
    rfl
  have hlast : (∑ j : Fin (n + 1),
      (if Fin.last n < j then (v (Fin.last n) * v j) • cm (Fin.last n) j else 0)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (not_lt.mpr (Fin.le_last j))]
  have hB : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (if i < j then (v i * v j) • cm i j else 0))
      = (∑ i : Fin n, ∑ j : Fin n,
            (if i < j then (v i.castSucc * v j.castSucc) • cm i.castSucc j.castSucc else 0)) +
        ∑ i : Fin n, (v i.castSucc * v (Fin.last n)) • cm i.castSucc (Fin.last n) := by
    rw [Fin.sum_univ_castSucc, hlast, Finset.sum_congr rfl fun i _ => hrow i,
      Finset.sum_add_distrib, add_zero]
  rw [hA, hB]
  abel

private theorem commutator_eElt_list {n d : ℕ} {z : Fin d → G}
    (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s)) {f : Fin n → G}
    (hzf : ∀ t i, z t * f i = f i * z t) {x : G} (hxz : ∀ t, x * z t = z t * x)
    (u : Fin n → Fin d → ZMod 2) (hu : ∀ i : Fin n, ⁅x, f i⁆ = eElt z (u i)) :
    ∀ (l : List (Fin n)) (v : Fin n → ZMod 2),
      ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ =
        eElt z ((l.map (fun i => v i • u i)).sum) := by
  intro l
  induction l with
  | nil =>
    intro v
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    rw [eElt_zero]
    simp
  | cons a l ih =>
    intro v
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
    have hsingle : ⁅x, f a ^ (v a).val⁆ = eElt z (v a • u a) := by
      rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) (v a) with h0 | h1
      · rw [h0, ZMod.val_zero, pow_zero, zero_smul, eElt_zero]
        simp
      · rw [h1, ZMod.val_one, pow_one, one_smul, hu a]
    have hxcomm : ∀ t, (f a ^ (v a).val) * z t = z t * (f a ^ (v a).val) := fun t =>
      (show Commute (f a ^ (v a).val) (z t)
        from (show Commute (f a) (z t) from (hzf t a).symm).pow_left _).eq
    have htail : Commute (f a ^ (v a).val)
        ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ := by
      rw [ih v]
      exact commute_eElt hxcomm _
    have hstep : ⁅x, f a ^ (v a).val * (l.map (fun i => f i ^ (v i).val)).prod⁆ =
        ⁅x, f a ^ (v a).val⁆ * ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ := by
      have h1 : ⁅x, f a ^ (v a).val * (l.map (fun i => f i ^ (v i).val)).prod⁆ =
          ⁅x, f a ^ (v a).val⁆ *
            (f a ^ (v a).val * ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ *
              (f a ^ (v a).val)⁻¹) := by
        simp only [commutatorElement_def]
        group
      have h2 : f a ^ (v a).val * ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ *
          (f a ^ (v a).val)⁻¹ = ⁅x, (l.map (fun i => f i ^ (v i).val)).prod⁆ := by
        rw [htail.eq]
        group
      rw [h1, h2]
    rw [hstep, hsingle, ih v, ← eElt_add hz2 hzz]

theorem eElt_sq {n d : ℕ} {f : Fin n → G} {z : Fin d → G}
    (hz2 : ∀ t, z t * z t = 1) (hzz : ∀ t s, Commute (z t) (z s))
    (hzf : ∀ t i, z t * f i = f i * z t)
    {sq : Fin n → Fin d → ZMod 2} {cm : Fin n → Fin n → Fin d → ZMod 2}
    (hsq : ∀ i, f i ^ 2 = eElt z (sq i))
    (hcm : ∀ i j, i < j → ⁅f j, f i⁆ = eElt z (cm i j)) (v : Fin n → ZMod 2) :
    eElt f v ^ 2 = eElt z (quadMapOfCoeffs sq cm v) := by
  induction n with
  | zero =>
    have h1 : eElt f v = 1 := by
      rw [eElt]
      simp
    have h2 : quadMapOfCoeffs sq cm v = 0 := by
      simp only [quadMapOfCoeffs]
      simp
    rw [h1, h2, one_pow, eElt_zero]
  | succ n ih =>
    rw [eElt_castSucc f v, quadMapOfCoeffs_castSucc sq cm v]
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) (v (Fin.last n)) with h0 | h1
    · rw [h0, ZMod.val_zero, pow_zero, mul_one, zero_smul]
      simp only [mul_zero, zero_smul, Finset.sum_const_zero, add_zero, zero_add]
      exact ih (f := fun i : Fin n => f i.castSucc)
        (sq := fun i : Fin n => sq i.castSucc)
        (cm := fun i j : Fin n => cm i.castSucc j.castSucc)
        (hzf := fun t i => hzf t i.castSucc)
        (hsq := fun i => hsq i.castSucc)
        (hcm := fun i j hij => hcm i.castSucc j.castSucc (by simpa using hij))
        (v := fun i => v i.castSucc)
    · rw [h1, ZMod.val_one, pow_one, one_smul]
      have hA : (eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc)) ^ 2 =
          eElt z (quadMapOfCoeffs (fun i => sq i.castSucc)
            (fun i j => cm i.castSucc j.castSucc) (fun i => v i.castSucc)) :=
        ih (f := fun i : Fin n => f i.castSucc)
          (sq := fun i : Fin n => sq i.castSucc)
          (cm := fun i j : Fin n => cm i.castSucc j.castSucc)
          (hzf := fun t i => hzf t i.castSucc)
          (hsq := fun i => hsq i.castSucc)
          (hcm := fun i j hij => hcm i.castSucc j.castSucc (by simpa using hij))
          (v := fun i => v i.castSucc)
      have hcommA' : ⁅f (Fin.last n),
          eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc)⁆ =
          eElt z (∑ i : Fin n, v i.castSucc • cm i.castSucc (Fin.last n)) := by
        have h := commutator_eElt_list hz2 hzz (f := fun i : Fin n => f i.castSucc)
          (fun t i => hzf t i.castSucc) (x := f (Fin.last n))
          (fun t => (hzf t (Fin.last n)).symm)
          (fun i => cm i.castSucc (Fin.last n))
          (fun i => hcm i.castSucc (Fin.last n) (Fin.castSucc_lt_last i))
          (List.finRange n) (fun i => v i.castSucc)
        have hA' : eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc) =
            (List.map (fun i => f i.castSucc ^ (v i.castSucc).val) (List.finRange n)).prod := by
          rw [eElt, List.ofFn_eq_map]
        rw [Fin.sum_univ_def, hA', h]
      rw [CFSG.GroupTheory.SuzukiTwoGroup.mul_sq_of_commute]
      · rw [hcommA', hA, hsq (Fin.last n)]
        have harg : quadMapOfCoeffs (fun i => sq i.castSucc)
            (fun i j => cm i.castSucc j.castSucc) (fun i => v i.castSucc) +
              sq (Fin.last n) +
              ∑ i : Fin n, (v i.castSucc * 1) • cm i.castSucc (Fin.last n)
            = (∑ i : Fin n, v i.castSucc • cm i.castSucc (Fin.last n)) +
              quadMapOfCoeffs (fun i => sq i.castSucc)
                (fun i j => cm i.castSucc j.castSucc) (fun i => v i.castSucc) +
                sq (Fin.last n) := by
          simp only [mul_one]
          abel
        rw [harg, ← eElt_add hz2 hzz, ← eElt_add hz2 hzz]
      · have hxcomm : ∀ t, (eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc)) * z t =
            z t * (eElt (fun i : Fin n => f i.castSucc) (fun i => v i.castSucc)) := by
          intro t
          exact (commute_eElt (v := fun i : Fin n => f i.castSucc)
            (fun i => hzf t i.castSucc) _).symm
        rw [hcommA']
        exact commute_eElt hxcomm _

theorem quadMapOfCoeffs_conj {n d : ℕ} {f : Fin n → G} {z : Fin d → G} {g : G}
    (hz : EBasis z) (hzf : ∀ t i, z t * f i = f i * z t)
    {sq : Fin n → Fin d → ZMod 2} {cm : Fin n → Fin n → Fin d → ZMod 2}
    (hsq : ∀ i, f i ^ 2 = eElt z (sq i))
    (hcm : ∀ i j, i < j → ⁅f j, f i⁆ = eElt z (cm i j))
    (R : Matrix (Fin n) (Fin n) (ZMod 2)) (S : Matrix (Fin d) (Fin d) (ZMod 2))
    (hg : ∀ j, ∃ u, g * f j * g⁻¹ = eElt f (fun i => R i j) * eElt z u)
    (hgz : ∀ t, g * z t * g⁻¹ = eElt z fun s => S s t) (v : Fin n → ZMod 2) :
    quadMapOfCoeffs sq cm (R *ᵥ v) = S *ᵥ quadMapOfCoeffs sq cm v := by
  classical
  let Z : Subgroup G := Subgroup.closure (Set.range z)
  have hzZ : ∀ t, z t ∈ Z := fun t => Subgroup.subset_closure (Set.mem_range_self t)
  have hZpow : ∀ u, eElt z u ∈ Z := fun u => eElt_mem_of_forall_mem hzZ u
  have hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y := by
    intro y hy i
    have hle : Z ≤ Subgroup.centralizer ({f i} : Set G) := by
      change Subgroup.closure (Set.range z) ≤ Subgroup.centralizer ({f i} : Set G)
      rw [Subgroup.closure_le]
      rintro w ⟨t, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzf t i)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hZexp : ∀ y ∈ Z, y ^ 2 = 1 := by
    intro y hy
    have hy' : y ∈ eSub hz := by rwa [eSub_eq_closure hz]
    exact (pow_two y).trans (eSub_sq hz y hy')
  have hsqZ : ∀ i, f i ^ 2 ∈ Z := fun i => by rw [hsq i]; exact hZpow _
  have hcmZ : ∀ i j, ⁅f i, f j⁆ ∈ Z := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [← commutatorElement_inv (g₁ := f j) (g₂ := f i), hcm i j h]
      exact Z.inv_mem (hZpow _)
    · subst h; simp
    · rw [hcm j i h]; exact hZpow _
  have hgz' : ∀ j, g * f j * g⁻¹ * (eElt f fun i => R i j)⁻¹ ∈ Z := by
    intro j
    obtain ⟨u, hu⟩ := hg j
    have hcomm : eElt z u * eElt f (fun i => R i j) =
        eElt f (fun i => R i j) * eElt z u :=
      commute_eElt (v := f) (x := eElt z u) (fun i => hZc (eElt z u) (hZpow u) i) _
    rw [hu]
    have he : eElt f (fun i => R i j) * eElt z u * (eElt f fun i => R i j)⁻¹ = eElt z u := by
      rw [← hcomm]
      group
    rw [he]
    exact hZpow _
  have hmod : g * eElt f v * g⁻¹ * (eElt f (R *ᵥ v))⁻¹ ∈ Z :=
    conj_eElt_mul_inv_mem hZc hsqZ hcmZ R hgz' v
  obtain ⟨y, hyZ, hy⟩ : ∃ y ∈ Z, g * eElt f v * g⁻¹ = y * eElt f (R *ᵥ v) := by
    refine ⟨g * eElt f v * g⁻¹ * (eElt f (R *ᵥ v))⁻¹, hmod, ?_⟩
    group
  have hycomm : y * eElt f (R *ᵥ v) = eElt f (R *ᵥ v) * y :=
    commute_eElt (v := f) (x := y) (fun i => hZc y hyZ i) _
  have hsq1 : (g * eElt f v * g⁻¹) ^ 2 = eElt z (quadMapOfCoeffs sq cm (R *ᵥ v)) := by
    rw [hy]
    rw [Commute.mul_pow (show Commute y (eElt f (R *ᵥ v)) from hycomm) 2,
      hZexp y hyZ, one_mul, eElt_sq hz.sq hz.comm hzf hsq hcm]
  have hsq2 : (g * eElt f v * g⁻¹) ^ 2 = eElt z (S *ᵥ quadMapOfCoeffs sq cm v) := by
    rw [show (g * eElt f v * g⁻¹) ^ 2 = g * (eElt f v ^ 2) * g⁻¹ from by
      rw [pow_two (g * eElt f v * g⁻¹), pow_two (eElt f v)]
      group]
    rw [eElt_sq hz.sq hz.comm hzf hsq hcm]
    exact conj_eElt_eq_mulVec hz.sq hz.comm S hgz (quadMapOfCoeffs sq cm v)
  exact eElt_injective hz (hsq1.symm.trans hsq2)

@[expose]
noncomputable def eEltQuotEquiv {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q]
    [(Z.subgroupOf Q).Normal] (f : Fin n → G) (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q)
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (hind : ∀ v, eElt f v ∈ Z → v = 0)
    (hcard : Nat.card Q = 2 ^ n * Nat.card Z) :
    Multiplicative (Fin n → ZMod 2) ≃* ↥Q ⧸ Z.subgroupOf Q :=
  let φ : Multiplicative (Fin n → ZMod 2) →* ↥Q ⧸ Z.subgroupOf Q :=
    { toFun := fun v => QuotientGroup.mk ⟨eElt f v.toAdd, eElt_mem_of_forall_mem hfQ v.toAdd⟩
      map_one' := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        show eElt f 0 ∈ Z
        rw [eElt_zero]
        exact Z.one_mem
      map_mul' := fun v w => by
        have h := eElt_add_mul_inv_mem hZc hsq hcm v.toAdd w.toAdd
        rw [← QuotientGroup.mk_mul]
        refine QuotientGroup.eq_iff_div_mem.mpr ?_
        rw [Subgroup.mem_subgroupOf]
        simpa [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h }
  have hinj : Function.Injective φ := by
    intro v w h
    have h1 : φ (v * w⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : eElt f ((v * w⁻¹).toAdd) ∈ Z := by
      have h3 : (⟨eElt f ((v * w⁻¹).toAdd), eElt_mem_of_forall_mem hfQ _⟩ : ↥Q) ∈
          Z.subgroupOf Q := by
        apply (QuotientGroup.eq_one_iff _).mp
        simpa [φ] using h1
      rwa [Subgroup.mem_subgroupOf] at h3
    have hmem : eElt f (v.toAdd + -w.toAdd) ∈ Z := by
      simpa using h2
    have hzero : v.toAdd + -w.toAdd = 0 := hind _ hmem
    have hv : v.toAdd = w.toAdd := by
      have := add_eq_zero_iff_eq_neg.mp hzero
      rwa [neg_neg] at this
    exact Multiplicative.ext hv
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, y, hyZ, hxy⟩ :=
      exists_eElt_mul hZQ hfQ hZc hsq hcm hind hcard (x : G) x.2
    refine ⟨Multiplicative.ofAdd v, ?_⟩
    have hxval : x = (⟨eElt f v * y,
        Q.mul_mem (eElt_mem_of_forall_mem hfQ v) (hZQ hyZ)⟩ : ↥Q) := Subtype.ext hxy
    have hphi : φ (Multiplicative.ofAdd v) =
        QuotientGroup.mk (⟨eElt f v, eElt_mem_of_forall_mem hfQ v⟩ : ↥Q) := rfl
    rw [hphi, hxval]
    rw [show (⟨eElt f v * y, Q.mul_mem (eElt_mem_of_forall_mem hfQ v) (hZQ hyZ)⟩ : ↥Q) =
        (⟨eElt f v, eElt_mem_of_forall_mem hfQ v⟩ : ↥Q) * ⟨y, hZQ hyZ⟩ from rfl,
      QuotientGroup.mk_mul]
    have hy1 : (QuotientGroup.mk ⟨y, hZQ hyZ⟩ : ↥Q ⧸ Z.subgroupOf Q) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hyZ)
    rw [hy1, mul_one]
  MulEquiv.ofBijective φ ⟨hinj, hsurj⟩

theorem eEltQuotEquiv_ofAdd {n : ℕ} {Q Z : Subgroup G} [Finite ↥Q]
    [(Z.subgroupOf Q).Normal] (f : Fin n → G) (hZQ : Z ≤ Q) (hfQ : ∀ i, f i ∈ Q)
    (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y) (hsq : ∀ i, f i ^ 2 ∈ Z)
    (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z) (hind : ∀ v, eElt f v ∈ Z → v = 0)
    (hcard : Nat.card Q = 2 ^ n * Nat.card Z) (v : Fin n → ZMod 2) :
    eEltQuotEquiv f hZQ hfQ hZc hsq hcm hind hcard (Multiplicative.ofAdd v) =
      (QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hfQ v⟩ : ↥Q ⧸ Z.subgroupOf Q) := rfl

theorem mk_conj_eq_mk_mulVec {n : ℕ} {Q Z : Subgroup G} [(Z.subgroupOf Q).Normal]
    {f : Fin n → G} {g : G} (hfQ : ∀ i, f i ∈ Q) (hZc : ∀ y ∈ Z, ∀ i, y * f i = f i * y)
    (hsq : ∀ i, f i ^ 2 ∈ Z) (hcm : ∀ i j, ⁅f i, f j⁆ ∈ Z)
    (hgZ : ∀ y ∈ Z, g * y * g⁻¹ ∈ Z) (R : Matrix (Fin n) (Fin n) (ZMod 2))
    (hg : ∀ j, g * f j * g⁻¹ * (eElt f fun i => R i j)⁻¹ ∈ Z) {x w : ↥Q}
    {v : Fin n → ZMod 2}
    (hx : (QuotientGroup.mk x : ↥Q ⧸ Z.subgroupOf Q) =
      QuotientGroup.mk ⟨eElt f v, eElt_mem_of_forall_mem hfQ v⟩)
    (hw : (w : G) = g * x * g⁻¹) :
    (QuotientGroup.mk w : ↥Q ⧸ Z.subgroupOf Q) =
      QuotientGroup.mk ⟨eElt f (R *ᵥ v), eElt_mem_of_forall_mem hfQ _⟩ := by
  have hmem : (x : G) * (eElt f v)⁻¹ ∈ Z := by
    have h := QuotientGroup.eq_iff_div_mem.mp hx
    rw [Subgroup.mem_subgroupOf] at h
    simpa [div_eq_mul_inv] using h
  obtain ⟨y, hyZ, hyx⟩ : ∃ y ∈ Z, (x : G) = y * eElt f v := by
    refine ⟨(x : G) * (eElt f v)⁻¹, hmem, ?_⟩
    group
  have h1 : g * y * g⁻¹ ∈ Z := hgZ y hyZ
  have h2 : g * eElt f v * g⁻¹ * (eElt f (R *ᵥ v))⁻¹ ∈ Z :=
    conj_eElt_mul_inv_mem hZc hsq hcm R hg v
  have hwq : (w : G) * (eElt f (R *ᵥ v))⁻¹ ∈ Z := by
    have heq : (w : G) * (eElt f (R *ᵥ v))⁻¹ =
        (g * y * g⁻¹) * (g * eElt f v * g⁻¹ * (eElt f (R *ᵥ v))⁻¹) := by
      rw [hw, hyx]
      group
    rw [heq]
    exact Z.mul_mem h1 h2
  rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
  simpa [div_eq_mul_inv] using hwq

end CFSG.GroupTheory
