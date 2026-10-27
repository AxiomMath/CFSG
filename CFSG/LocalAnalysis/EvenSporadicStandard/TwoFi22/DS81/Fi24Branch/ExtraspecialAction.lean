module

public import CFSG.Certificates.ExtraspecialNormalForm

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ExtraspecialAction

open CFSG.Certificates.ExtraspecialNF

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G] {n : ℕ} {z : G} {q : Fin n → G} {c : Fin n → Fin n → ZMod 2}

@[expose] def HasVec (z : G) (q : Fin n → G) (x : G) (w : Fin n → ZMod 2) : Prop :=
  ∃ s, x = nf z q s w

theorem hasVec_one : HasVec z q 1 0 := ⟨0, (nf_zero_zero z q).symm⟩

theorem hasVec_mul (h : Rel z q c) {x y : G} {v w : Fin n → ZMod 2} (hx : HasVec z q x v)
    (hy : HasVec z q y w) : HasVec z q (x * y) (v + w) := by
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨t, rfl⟩ := hy
  exact ⟨_, nf_mul_nf h s t v w⟩

theorem hasVec_list_prod (h : Rel z q c) :
    ∀ l : List (G × (Fin n → ZMod 2)), (∀ p ∈ l, HasVec z q p.1 p.2) →
      HasVec z q (l.map Prod.fst).prod (l.map Prod.snd).sum
  | [], _ => by simpa using hasVec_one
  | p :: l, hl => by
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact hasVec_mul h (hl p (List.mem_cons_self ..))
      (hasVec_list_prod h l fun p' hp' => hl p' (List.mem_cons_of_mem _ hp'))

theorem hasVec_pow_val (h : Rel z q c) {x : G} {w : Fin n → ZMod 2} (hx : HasVec z q x w)
    (b : ZMod 2) : HasVec z q (x ^ b.val) (b • w) := by
  rcases zmod_two_cases b with rfl | rfl
  · simpa using hasVec_one
  · simpa [val_one_two] using hx

theorem conj_mon_hasVec (h : Rel z q c) {g : G} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hq : ∀ j, HasVec z q (g * q j * g⁻¹) fun i => M i j) (v : Fin n → ZMod 2) :
    HasVec z q (g * mon q v * g⁻¹) (M.mulVec v) := by
  have e1 : g * mon q v * g⁻¹ =
      (List.ofFn fun i => (g * q i * g⁻¹) ^ (v i).val).prod := by
    have := map_list_prod (MulAut.conj g) (List.ofFn fun i => q i ^ (v i).val)
    simpa [mon, List.map_ofFn, MulAut.conj_apply, Function.comp_def, map_pow] using this
  have e2 : (List.ofFn fun i => (g * q i * g⁻¹) ^ (v i).val).prod =
      ((List.ofFn fun i => ((g * q i * g⁻¹) ^ (v i).val, v i • fun r => M r i)).map
        Prod.fst).prod := by
    simp [List.map_ofFn, Function.comp_def]
  have e3 : M.mulVec v = ((List.ofFn fun i =>
      ((g * q i * g⁻¹) ^ (v i).val, v i • fun r => M r i)).map Prod.snd).sum := by
    funext r
    simp [List.map_ofFn, Function.comp_def, List.sum_ofFn, Matrix.mulVec, dotProduct,
      mul_comm, Finset.sum_apply]
  rw [e1, e2, e3]
  refine hasVec_list_prod h _ fun p hp => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
  exact hasVec_pow_val h (hq i) (v i)

theorem conj_nf_hasVec (h : Rel z q c) {g : G} (hz : g * z * g⁻¹ = z)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hq : ∀ j, HasVec z q (g * q j * g⁻¹) fun i => M i j) (s : ZMod 2) (v : Fin n → ZMod 2) :
    HasVec z q (g * nf z q s v * g⁻¹) (M.mulVec v) := by
  obtain ⟨t, ht⟩ := conj_mon_hasVec h M hq v
  refine ⟨s + t, ?_⟩
  have e : g * nf z q s v * g⁻¹ = z ^ s.val * (g * mon q v * g⁻¹) := by
    have hzp : g * z ^ s.val * g⁻¹ = z ^ s.val := by rw [← conj_pow, hz]
    calc g * nf z q s v * g⁻¹ = g * z ^ s.val * g⁻¹ * (g * mon q v * g⁻¹) := by
          simp only [nf, mul_assoc, inv_mul_cancel_left]
      _ = z ^ s.val * (g * mon q v * g⁻¹) := by rw [hzp]
  rw [e, ht]
  simp only [nf]
  rw [← mul_assoc, ← pow_val_add h.z_sq]

theorem bil_sub_left (c : Fin n → Fin n → ZMod 2) (v w u : Fin n → ZMod 2) :
    bil c (v - w) u = bil c v u - bil c w u := by
  simp only [bil, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem zpow_val_inj (hz : z ≠ 1) {a b : ZMod 2} (h : z ^ a.val = z ^ b.val) : a = b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · exact absurd (by simpa [val_one_two] using h.symm) hz
  · exact absurd (by simpa [val_one_two] using h) hz
  · rfl

theorem injective_nf_of_nondeg (h : Rel z q c) (hz : z ≠ 1) (hnd : Nondegenerate c) :
    Function.Injective (Function.uncurry (nf z q)) := by
  have hsymm := h.symm_of_ne_one hz
  have hdiag := h.diag_eq_zero hz
  rintro ⟨s, v⟩ ⟨s', w⟩ hst
  change nf z q s v = nf z q s' w at hst
  have hbil : ∀ u, bil c v u = bil c w u := by
    intro u
    have h1 := nf_mul_comm h hsymm hdiag s 0 v u
    have h2 := nf_mul_comm h hsymm hdiag s' 0 w u
    rw [← hst] at h2
    rw [h1] at h2
    exact zpow_val_inj hz (mul_left_cancel h2)
  have hvw : v = w := by
    by_contra hne
    obtain ⟨u, hu⟩ := hnd (v - w) (sub_ne_zero.2 hne)
    rw [bil_sub_left, hbil u, sub_self] at hu
    exact hu rfl
  subst hvw
  have hs : z ^ s.val = z ^ s'.val := mul_right_cancel hst
  rw [zpow_val_inj hz hs]

theorem card_sq_le_of_isotropic {c : Fin n → Fin n → ZMod 2} (hc : (Matrix.of c).det ≠ 0)
    (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (hW : ∀ v ∈ W, ∀ w ∈ W, bil c v w = 0) :
    Nat.card W ^ 2 ≤ 2 ^ n := by
  set B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) := Matrix.toBilin' (Matrix.of c) with hB
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' _ hc
  have hBc : ∀ v w, B v w = bil c v w := fun v w => by
    rw [hB, Matrix.toBilin'_apply', bil_eq_dotProduct]
  have hle : W ≤ B.orthogonal W := fun w hw n hn => by
    rw [hBc]
    exact hW n hn w hw
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal (K := ZMod 2) (V := Fin n → ZMod 2) hnd W
  rw [h2, Module.finrank_fin_fun] at h1
  have h3 : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h3, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.ExtraspecialAction
