module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Q

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {K : Fin 4 → Subgroup G} {z : G}

@[expose] def Sec5B517Prod (k : Fin 4 → G) : G := k 0 * k 1 * k 2 * k 3

theorem sec5b517_prod_one : Sec5B517Prod (fun _ : Fin 4 => (1 : G)) = 1 := by
  simp [Sec5B517Prod]

private lemma sec5b517_move2 {p q r x : G} (h : Commute x (q * r)) :
    p * q * r * x = p * x * (q * r) := by
  rw [show p * q * r * x = p * (q * r) * x by group]
  exact (h.right_comm p).symm

private lemma sec5b517_move3 {p q r s x : G} (h : Commute x (q * r * s)) :
    p * q * r * s * x = p * x * (q * r * s) := by
  rw [show p * q * r * s * x = p * (q * r * s) * x by group]
  exact (h.right_comm p).symm

theorem sec5b517_prod_mul (hq : Sec5B517Quad K z) {k l : Fin 4 → G} (hk : ∀ i, k i ∈ K i)
    (hl : ∀ i, l i ∈ K i) :
    Sec5B517Prod k * Sec5B517Prod l = Sec5B517Prod (fun i => k i * l i) := by
  have h01 : Commute (l 0) (k 1) := hq.comm 0 1 (by decide) (l 0) (hl 0) (k 1) (hk 1)
  have h02 : Commute (l 0) (k 2) := hq.comm 0 2 (by decide) (l 0) (hl 0) (k 2) (hk 2)
  have h03 : Commute (l 0) (k 3) := hq.comm 0 3 (by decide) (l 0) (hl 0) (k 3) (hk 3)
  have h12 : Commute (l 1) (k 2) := hq.comm 1 2 (by decide) (l 1) (hl 1) (k 2) (hk 2)
  have h13 : Commute (l 1) (k 3) := hq.comm 1 3 (by decide) (l 1) (hl 1) (k 3) (hk 3)
  have h23 : Commute (l 2) (k 3) := hq.comm 2 3 (by decide) (l 2) (hl 2) (k 3) (hk 3)
  have hA : Commute (l 0) (k 1 * k 2 * k 3) := (h01.mul_right h02).mul_right h03
  have hB : Commute (l 1) (k 2 * k 3) := h12.mul_right h13
  simp only [Sec5B517Prod]
  calc
    k 0 * k 1 * k 2 * k 3 * (l 0 * l 1 * l 2 * l 3)
        = k 0 * l 0 * (k 1 * k 2 * k 3) * (l 1 * l 2 * l 3) := by
          rw [show k 0 * k 1 * k 2 * k 3 * (l 0 * l 1 * l 2 * l 3)
                = k 0 * k 1 * k 2 * k 3 * l 0 * (l 1 * l 2 * l 3) by group,
              sec5b517_move3 hA]
    _ = k 0 * l 0 * (k 1 * l 1 * (k 2 * k 3)) * (l 2 * l 3) := by
          rw [show k 0 * l 0 * (k 1 * k 2 * k 3) * (l 1 * l 2 * l 3)
                = k 0 * l 0 * (k 1 * k 2 * k 3 * l 1) * (l 2 * l 3) by group,
              sec5b517_move2 hB]
    _ = k 0 * l 0 * (k 1 * l 1 * (k 2 * l 2 * k 3)) * l 3 := by
          rw [show k 0 * l 0 * (k 1 * l 1 * (k 2 * k 3)) * (l 2 * l 3)
                = k 0 * l 0 * (k 1 * l 1 * (k 2 * k 3 * l 2)) * l 3 by group,
              (h23.right_comm (k 2)).symm]
    _ = (k 0 * l 0) * (k 1 * l 1) * (k 2 * l 2) * (k 3 * l 3) := by group

theorem sec5b517_prod_inv (hq : Sec5B517Quad K z) {k : Fin 4 → G} (hk : ∀ i, k i ∈ K i) :
    (Sec5B517Prod k)⁻¹ = Sec5B517Prod (fun i => (k i)⁻¹) := by
  have hl : ∀ i, (k i)⁻¹ ∈ K i := fun i => (K i).inv_mem (hk i)
  have hmul := sec5b517_prod_mul hq hk hl
  have hone : Sec5B517Prod (fun i => k i * (k i)⁻¹) = 1 := by
    simp only [Sec5B517Prod, mul_inv_cancel, one_mul]
  exact inv_eq_of_mul_eq_one_right (by rw [hmul, hone])

theorem sec5b517_prod_pow (hq : Sec5B517Quad K z) {k : Fin 4 → G} (hk : ∀ i, k i ∈ K i)
    (n : ℕ) : Sec5B517Prod k ^ n = Sec5B517Prod (fun i => k i ^ n) := by
  induction n with
  | zero => simp [Sec5B517Prod]
  | succ n ih =>
      rw [pow_succ, ih,
        sec5b517_prod_mul hq (fun i => (K i).pow_mem (hk i) n) hk]
      congr 1
      funext i
      rw [pow_succ]

theorem sec5b517_prod_conj (hq : Sec5B517Quad K z) {u k : Fin 4 → G} (hu : ∀ i, u i ∈ K i)
    (hk : ∀ i, k i ∈ K i) :
    (Sec5B517Prod u)⁻¹ * Sec5B517Prod k * Sec5B517Prod u =
      Sec5B517Prod (fun i => (u i)⁻¹ * k i * u i) := by
  rw [sec5b517_prod_inv hq hu,
    sec5b517_prod_mul hq (fun i => (K i).inv_mem (hu i)) hk,
    sec5b517_prod_mul hq (fun i => (K i).mul_mem ((K i).inv_mem (hu i)) (hk i)) hu]

theorem sec5b517_commute_prod {v : G} {k : Fin 4 → G} (h : ∀ i, Commute v (k i)) :
    Commute v (Sec5B517Prod k) := by
  simpa [Sec5B517Prod] using (((h 0).mul_right (h 1)).mul_right (h 2)).mul_right (h 3)

theorem sec5b517_prod_mem {k : Fin 4 → G} (hk : ∀ i, k i ∈ K i) :
    Sec5B517Prod k ∈ Sec5B517All K := by
  have h0 : k 0 ∈ K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hk 0)))
  have h1 : k 1 ∈ K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hk 1)))
  have h2 : k 2 ∈ K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (hk 2))
  have h3 : k 3 ∈ K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3 :=
    Subgroup.mem_sup_right (hk 3)
  rw [Sec5B517Prod]
  change k 0 * k 1 * k 2 * k 3 ∈ K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3
  exact (K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3).mul_mem
    ((K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3).mul_mem
      ((K 0 ⊔ K 1 ⊔ K 2 ⊔ K 3).mul_mem h0 h1) h2) h3

theorem sec5b517_decomp (hq : Sec5B517Quad K z) {x : G} (hx : x ∈ Sec5B517All K) :
    ∃ k : Fin 4 → G, (∀ i, k i ∈ K i) ∧ x = Sec5B517Prod k :=
  hq.decomp hx

theorem sec5b517_prod_single (i : Fin 4) (u : G) :
    Sec5B517Prod (fun j => if j = i then u else 1) = u := by
  fin_cases i <;> simp [Sec5B517Prod]

end CFSG.OddStandard.SmallF3.Omega
