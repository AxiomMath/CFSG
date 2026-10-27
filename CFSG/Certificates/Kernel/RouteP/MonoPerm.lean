module

public import CFSG.Certificates.Kernel.RouteP.MonoSet

public section

namespace CFSG.KS.RouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

abbrev Pt : Type := Fin 920808

open Classical in
@[expose] noncomputable def gT (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (j : Nat) : Perm Pt :=
  if h : LOK NW KA KB (Int.ofNat (j + 1)) then
    { toFun := fun x => ⟨eL NW KA KB (Int.negSucc j) x.val, (eL_pos_neg (n := j) h.1 h.2 x.isLt).1⟩
      invFun := fun x => ⟨eL NW KA KB (Int.ofNat (j + 1)) x.val, (eL_pos_neg (n := j) h.1 h.2 x.isLt).2.2.1⟩
      left_inv := fun x => Fin.ext (eL_pos_neg (n := j) h.1 h.2 x.isLt).2.1
      right_inv := fun x => Fin.ext (eL_pos_neg (n := j) h.1 h.2 x.isLt).2.2.2 }
  else 1

theorem gT_apply {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {j : Nat} (h : LOK NW KA KB (Int.ofNat (j + 1)))
    (x : Pt) : (gT NW KA KB j x).val = eL NW KA KB (Int.negSucc j) x.val := by
  unfold gT
  rw [dif_pos h]
  rfl

theorem gT_inv_apply {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {j : Nat}
    (h : LOK NW KA KB (Int.ofNat (j + 1))) (x : Pt) :
    ((gT NW KA KB j)⁻¹ x).val = eL NW KA KB (Int.ofNat (j + 1)) x.val := by
  unfold gT
  rw [dif_pos h]
  rfl

theorem wordG_apply {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} (ρ : ℤ → Perm Pt) (c : ℤ → ℤ) :
    ∀ (u : List ℤ), (∀ l ∈ u, ∀ y : Pt, (ρ l y).val = eL NW KA KB (c l) y.val) →
      ∀ y : Pt, (wordG ρ u y).val = eW NW KA KB (u.map c) y.val
  | [], _, _ => rfl
  | l :: u, h, y => by
    have e : wordG ρ (l :: u) = ρ l * wordG ρ u := by simp [wordG]
    rw [e, Perm.mul_apply, h l List.mem_cons_self, wordG_apply ρ c u
      (fun l' hl' => h l' (List.mem_cons_of_mem l hl')) y, List.map_cons, eW_cons]

theorem wordG_eq_one {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} (ρ : ℤ → Perm Pt) (c : ℤ → ℤ) {u : List ℤ}
    (hρ : ∀ l ∈ u, ∀ y : Pt, (ρ l y).val = eL NW KA KB (c l) y.val) (hw : WOK NW KA KB (u.map c))
    (h : ∀ k < 19, idOK NW (u.map c) k = true) (hk : idKOK NW KA KB (u.map c) = true) : wordG ρ u = 1 := by
  apply Equiv.ext
  intro y
  apply Fin.ext
  rw [wordG_apply ρ c u hρ y, id_spec hw h hk _ y.isLt]
  rfl

theorem wordG_invW {G : Type*} [Group G] (ρ : ℤ → G) (hρ : ∀ l, ρ (-l) = (ρ l)⁻¹) :
    ∀ u : List ℤ, wordG ρ (u.reverse.map fun l => -l) = (wordG ρ u)⁻¹
  | [] => by simp [wordG]
  | l :: u => by
    have e1 : wordG ρ ((l :: u).reverse.map fun l => -l) =
        wordG ρ (u.reverse.map fun l => -l) * ρ (-l) := by
      simp [wordG, List.map_append, List.prod_append]
    have e2 : wordG ρ (l :: u) = ρ l * wordG ρ u := by simp [wordG]
    rw [e1, e2, wordG_invW ρ hρ u, hρ, mul_inv_rev]

theorem wordG_eq_of {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} (ρ : ℤ → Perm Pt) (c : ℤ → ℤ)
    (hinv : ∀ l, ρ (-l) = (ρ l)⁻¹) {u v : List ℤ}
    (hρ : ∀ l ∈ u ++ (v.reverse.map fun l => -l), ∀ y : Pt, (ρ l y).val = eL NW KA KB (c l) y.val)
    (hw : WOK NW KA KB ((u ++ (v.reverse.map fun l => -l)).map c))
    (h : ∀ k < 19, idOK NW ((u ++ (v.reverse.map fun l => -l)).map c) k = true)
    (hk : idKOK NW KA KB ((u ++ (v.reverse.map fun l => -l)).map c) = true) : wordG ρ u = wordG ρ v := by
  have h1 := wordG_eq_one ρ c hρ hw h hk
  have e : wordG ρ (u ++ (v.reverse.map fun l => -l)) = wordG ρ u * (wordG ρ v)⁻¹ := by
    rw [← wordG_invW ρ hinv v]
    simp [wordG, List.map_append, List.prod_append]
  rw [e] at h1
  exact mul_inv_eq_one.1 h1

end CFSG.KS.RouteP

end
