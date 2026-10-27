module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.ClassBound
public import Mathlib.Data.List.GetD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

@[expose] def compTab (a b : List ℕ) : List ℕ := b.map fun i => a.getD i 0

@[expose] def invTab (n : ℕ) (a : List ℕ) : List ℕ := (List.range n).map fun j => a.idxOf j

private theorem finRange_map_val_getD {n : ℕ} (σ : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < n) :
    ((List.finRange n).map fun i => (σ i).val).getD j 0 = (σ ⟨j, hj⟩).val := by
  rw [List.getD_eq_getElem (hn := by simpa using hj), List.getElem_map, List.getElem_finRange]
  exact congrArg Fin.val (congrArg σ (Fin.ext rfl))

theorem permTab_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permTab (σ * τ) = compTab (permTab σ) (permTab τ) := by
  unfold compTab permTab
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  show ((σ * τ) i).val = ((List.finRange n).map fun x => (σ x).val).getD ((τ i).val) 0
  rw [finRange_map_val_getD σ (τ i).isLt, Equiv.Perm.mul_apply]

theorem permTab_one {n : ℕ} : permTab (1 : Equiv.Perm (Fin n)) = List.range n := by
  rw [permTab]
  have h : (fun i : Fin n => ((1 : Equiv.Perm (Fin n)) i).val) = (↑·) := by
    funext i; rfl
  rw [h, List.map_coe_finRange_eq_range]

theorem permTab_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) : permTab σ⁻¹ = invTab n (permTab σ) := by
  unfold permTab invTab
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  apply List.map_congr_left
  intro i _
  have hnd : ((List.finRange n).map fun x => (σ x).val).Nodup :=
    List.Nodup.map (f := fun x => (σ x).val)
      (fun a b h => σ.injective (Fin.ext h)) (List.nodup_finRange n)
  have hlen : (σ⁻¹ i).val < ((List.finRange n).map fun x => (σ x).val).length := by
    simpa using (σ⁻¹ i).isLt
  have hval : ((List.finRange n).map fun x => (σ x).val)[(σ⁻¹ i).val] =
      (σ (σ⁻¹ i)).val := by
    rw [List.getElem_map, List.getElem_finRange]
    exact congrArg Fin.val (congrArg σ (Fin.ext rfl))
  have hsym : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
  have hk := hnd.idxOf_getElem (σ⁻¹ i).val hlen
  rw [hval, hsym] at hk
  exact hk.symm

theorem permTab_list_prod {n : ℕ} (l : List (Equiv.Perm (Fin n))) :
    permTab l.prod = (l.map permTab).foldr compTab (List.range n) := by
  induction l with
  | nil => simpa using (permTab_one (n := n))
  | cons a t ih =>
    rw [List.prod_cons, permTab_mul, ih, List.map_cons, List.foldr_cons]

end CFSG.OddStandard.SmallF3.HarrisU33
