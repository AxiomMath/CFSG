module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHsyl
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LieType.Steinberg.Sp (blockMat)
open scoped MatrixGroups

variable {K : Type} [Field K] {n m : ℕ}

section Element

@[expose] def zThreeMat : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, -1]

theorem det_zThreeMat : (zThreeMat (K := K)).det = 1 := by
  simp [zThreeMat, Matrix.det_fin_two]

@[expose] def zThreeSL : SL(2, K) := mkSL zThreeMat det_zThreeMat

theorem coe_zThreeSL : (zThreeSL : SL(2, K)) = (zThreeMat : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem coe_zThreeSL_sq :
    ((zThreeSL ^ 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![-1, -1; 1, 0] := by
  rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, coe_zThreeSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zThreeMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem zThreeSL_pow_three : (zThreeSL : SL(2, K)) ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_zThreeSL_sq, coe_zThreeSL,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zThreeMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem zThreeSL_ne_one : (zThreeSL : SL(2, K)) ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp [coe_zThreeSL, zThreeMat] at this

theorem orderOf_zThreeSL : orderOf (zThreeSL : SL(2, K)) = 3 :=
  orderOf_eq_prime zThreeSL_pow_three zThreeSL_ne_one

omit [Field K] in
theorem eq_zero_or_eq_one_of_natCard_two [Field K] (hK : Nat.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  rcases eq_or_ne c 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (mul_left_cancel₀ h0 (h.trans (mul_one c).symm))

theorem mem_zpowers_zThreeSL_of_entries [CharP K 2] (hK : Nat.card K = 2) {B : SL(2, K)}
    (h10 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = -(B : Matrix (Fin 2) (Fin 2) K) 0 1)
    (h11 : (B : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (B : Matrix (Fin 2) (Fin 2) K) 0 0 - (B : Matrix (Fin 2) (Fin 2) K) 0 1) :
    B ∈ zpowers (zThreeSL (K := K)) := by
  have hdet := B.2
  rw [Matrix.det_fin_two, h10, h11] at hdet
  set p := (B : Matrix (Fin 2) (Fin 2) K) 0 0 with hp
  set q := (B : Matrix (Fin 2) (Fin 2) K) 0 1 with hq
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  have hB : ∀ (M : Matrix (Fin 2) (Fin 2) K), M 0 0 = p → M 0 1 = q → M 1 0 = -q →
      M 1 1 = p - q → (B : Matrix (Fin 2) (Fin 2) K) = M := by
    intro M h00 h01 h10' h11'
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00.symm
    · exact h01.symm
    · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue]
      rw [h10, h10']
    · simp only [Fin.mk_one, Fin.isValue]
      rw [h11, h11']
  rcases eq_zero_or_eq_one_of_natCard_two hK p with h0 | h0 <;>
    rcases eq_zero_or_eq_one_of_natCard_two hK q with h1 | h1
  · rw [h0, h1] at hdet
    simp at hdet
  ·
    have e : B = zThreeSL := Subtype.ext (by
      rw [hB zThreeMat (by simp [zThreeMat, h0]) (by simp [zThreeMat, h1])
        (by simp [zThreeMat, h1]) (by simp [zThreeMat, h0, h1])]
      rfl)
    rw [e]
    exact mem_zpowers _
  ·
    have e : B = 1 := Subtype.ext (by
      rw [hB 1 (by simp [h0]) (by simp [h1]) (by simp [h1]) (by simp [h0, h1])]
      rfl)
    rw [e]
    exact one_mem _
  ·
    have e : B = zThreeSL ^ 2 := Subtype.ext (by
      rw [coe_zThreeSL_sq]
      refine hB _ ?_ ?_ ?_ ?_
      · simp [h0, hneg]
      · simp [h1, hneg]
      · simp [h1, hneg]
      · simp [h0, h1])
    rw [e]
    exact pow_mem (mem_zpowers _) 2

end Element

section Torus

@[expose] noncomputable def nsElt (k : Fin n) : StatedSp n K := longBlock K n k zThreeSL

variable (K) in
@[expose] noncomputable def nsTorusSp (k : Fin n) : Subgroup (StatedSp n K) := zpowers (nsElt k)

theorem mat_nsElt (k : Fin n) :
    mat n K (nsElt k) = blockMat (Sum.inl k) (Sum.inr k) (zThreeMat (K := K)) :=
  rfl

theorem nsElt_mem_nsTorusSp (k : Fin n) : nsElt (K := K) k ∈ nsTorusSp K k := mem_zpowers _

theorem nsElt_pow_three (k : Fin n) : nsElt (K := K) k ^ 3 = 1 := by
  rw [nsElt, ← map_pow, zThreeSL_pow_three, map_one]

theorem nsElt_ne_one (k : Fin n) : nsElt (K := K) k ≠ 1 := fun h =>
  zThreeSL_ne_one ((longBlock_injective k) (h.trans (map_one _).symm))

theorem orderOf_nsElt (k : Fin n) : orderOf (nsElt (K := K) k) = 3 :=
  orderOf_eq_prime (nsElt_pow_three k) (nsElt_ne_one k)

theorem card_nsTorusSp (k : Fin n) : Nat.card (nsTorusSp K k) = 3 := by
  rw [nsTorusSp, Nat.card_zpowers, orderOf_nsElt]

theorem odd_card_nsTorusSp (k : Fin n) : Odd (Nat.card (nsTorusSp K k)) := by
  rw [card_nsTorusSp]
  decide

theorem isCyclic_nsTorusSp (k : Fin n) : IsCyclic (nsTorusSp K k) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  isCyclic_of_prime_card (card_nsTorusSp k)

theorem nsTorusSp_le_longRootSp2 (k : Fin n) : nsTorusSp K k ≤ longRootSp2 K n k := by
  rw [nsTorusSp, zpowers_le]
  exact ⟨zThreeSL, rfl⟩

theorem nsTorusSp_le_centralizer_self (k : Fin n) :
    nsTorusSp K k ≤ centralizer (nsTorusSp K k : Set (StatedSp n K)) := by
  rintro _ ⟨i, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨j, rfl⟩
  exact zpow_mul_comm _ _ _

theorem complSp_le_centralizer_nsTorusSp (k : Fin n) :
    complSp K k ≤ centralizer (nsTorusSp K k : Set (StatedSp n K)) :=
  (complSp_le_centralizer_longRootSp2 k).trans (centralizer_le (nsTorusSp_le_longRootSp2 k))

theorem disjoint_nsTorusSp_complSp (k : Fin n) : Disjoint (nsTorusSp K k) (complSp K k) :=
  (disjoint_longRootSp2_complSp k).mono_left (nsTorusSp_le_longRootSp2 k)

theorem map_conj_permSp_nsTorusSp (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (nsTorusSp K k).map (MulAut.conj (permSp K π)).toMonoidHom = nsTorusSp K (π k) := by
  rw [nsTorusSp, nsTorusSp, MonoidHom.map_zpowers]
  congr 1
  exact conj_permSp_longBlock π k zThreeSL

end Torus

section Centralizer

variable {k : Fin n}

theorem mat_apply_eq_zero_of_commute_nsElt [CharP K 2] {x : StatedSp n K}
    (hx : x * nsElt k = nsElt k * x) {r : Fin n ⊕ Fin n} (hr : r ∉ coords k) :
    mat n K x r (Sum.inl k) = 0 ∧ mat n K x r (Sum.inr k) = 0 := by
  have hM := congrArg (mat n K) hx
  rw [map_mul, map_mul] at hM
  have hrow : ∀ u, mat n K (nsElt k) r u = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r u :=
    fun u => by
      rw [mat_nsElt]
      exact blockMat_apply_of_not_mem k _ (fun h => hr h.1)
  have hR : ∀ t, (mat n K (nsElt k) * mat n K x) r t = mat n K x r t := fun t => by
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [hrow u]), ← Matrix.mul_apply,
      Matrix.one_mul]
  have hL : ∀ t ∈ coords k, (mat n K x * mat n K (nsElt k)) r t =
      mat n K x r (Sum.inl k) * mat n K (nsElt k) (Sum.inl k) t +
        mat n K x r (Sum.inr k) * mat n K (nsElt k) (Sum.inr k) t := by
    intro t ht
    rw [Matrix.mul_apply, Finset.sum_eq_add (Sum.inl k) (Sum.inr k) Sum.inl_ne_inr]
    · intro u _ hu
      have hu' : u ∉ coords k := by
        rw [mem_coords]
        tauto
      have hut : u ≠ t := fun e => hu' (by rw [e]; exact ht)
      rw [mat_nsElt, blockMat_apply_of_not_mem k _ (fun h => hu' h.1),
        Matrix.one_apply_ne hut, mul_zero]
    · simp
    · simp
  have h00 : mat n K (nsElt k) (Sum.inl k) (Sum.inl k) = 0 := by
    simp [mat_nsElt, blockMat, zThreeMat]
  have h01 : mat n K (nsElt k) (Sum.inl k) (Sum.inr k) = 1 := by
    simp [mat_nsElt, blockMat, zThreeMat]
  have h10 : mat n K (nsElt k) (Sum.inr k) (Sum.inl k) = -1 := by
    simp [mat_nsElt, blockMat, zThreeMat]
  have h11 : mat n K (nsElt k) (Sum.inr k) (Sum.inr k) = -1 := by
    simp [mat_nsElt, blockMat, zThreeMat]
  have e1 := hL _ (inl_mem_coords k)
  have e2 := hL _ (inr_mem_coords k)
  rw [hM, hR, h00, h10] at e1
  rw [hM, hR, h01, h11] at e2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hb : mat n K x r (Sum.inr k) = 0 := by
    linear_combination e1 + e2 - mat n K x r (Sum.inr k) * h2
  refine ⟨?_, hb⟩
  linear_combination e1 - hb

theorem mat_nsElt_inl_inl (k : Fin n) : mat n K (nsElt k) (Sum.inl k) (Sum.inl k) = 0 := by
  simp [mat_nsElt, blockMat, zThreeMat]

theorem mat_nsElt_inl_inr (k : Fin n) : mat n K (nsElt k) (Sum.inl k) (Sum.inr k) = 1 := by
  simp [mat_nsElt, blockMat, zThreeMat]

theorem mat_nsElt_inr_inl (k : Fin n) : mat n K (nsElt k) (Sum.inr k) (Sum.inl k) = -1 := by
  simp [mat_nsElt, blockMat, zThreeMat]

theorem mat_nsElt_inr_inr (k : Fin n) : mat n K (nsElt k) (Sum.inr k) (Sum.inr k) = -1 := by
  simp [mat_nsElt, blockMat, zThreeMat]

theorem mul_mat_nsElt_apply (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (r : Fin n ⊕ Fin n)
    {t : Fin n ⊕ Fin n} (ht : t ∈ coords k) :
    (M * mat n K (nsElt k)) r t = M r (Sum.inl k) * mat n K (nsElt k) (Sum.inl k) t +
      M r (Sum.inr k) * mat n K (nsElt k) (Sum.inr k) t := by
  rw [Matrix.mul_apply, Finset.sum_eq_add (Sum.inl k) (Sum.inr k) Sum.inl_ne_inr]
  · intro u _ hu
    have hu' : u ∉ coords k := by
      rw [mem_coords]
      tauto
    have hut : u ≠ t := fun e => hu' (by rw [e]; exact ht)
    rw [mat_nsElt, blockMat_apply_of_not_mem k _ (fun h => hu' h.1), Matrix.one_apply_ne hut,
      mul_zero]
  · simp
  · simp

theorem mat_nsElt_mul_apply (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    {r : Fin n ⊕ Fin n} (hr : r ∈ coords k) (t : Fin n ⊕ Fin n) :
    (mat n K (nsElt k) * M) r t = mat n K (nsElt k) r (Sum.inl k) * M (Sum.inl k) t +
      mat n K (nsElt k) r (Sum.inr k) * M (Sum.inr k) t := by
  rw [Matrix.mul_apply, Finset.sum_eq_add (Sum.inl k) (Sum.inr k) Sum.inl_ne_inr]
  · intro u _ hu
    have hu' : u ∉ coords k := by
      rw [mem_coords]
      tauto
    have hru : r ≠ u := fun e => hu' (by rw [← e]; exact hr)
    rw [mat_nsElt, blockMat_apply_of_not_mem k _ (fun h => hu' h.2), Matrix.one_apply_ne hru,
      zero_mul]
  · simp
  · simp

theorem exists_eq_mul_of_commute_nsElt [CharP K 2] (hK : Nat.card K = 2) {x : StatedSp n K}
    (hx : x * nsElt k = nsElt k * x) :
    ∃ a ∈ nsTorusSp K k, ∃ y ∈ complSp K k, x = a * y := by
  have hpq : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  have hoff : ∀ r t, r ∉ coords k → t ∈ coords k → mat n K x r t = 0 := by
    intro r t hr ht
    rcases mem_coords.1 ht with rfl | rfl
    · exact (mat_apply_eq_zero_of_commute_nsElt hx hr).1
    · exact (mat_apply_eq_zero_of_commute_nsElt hx hr).2
  have hdet : (stdBlock k (mat n K x)).det = 1 :=
    det_stdBlock_eq_one x k fun r hr => hoff r _ hr (inl_mem_coords k)
  have hM := congrArg (mat n K) hx
  rw [map_mul, map_mul] at hM
  have e1 := mul_mat_nsElt_apply (mat n K x) (Sum.inl k) (inl_mem_coords k)
  have e2 := mul_mat_nsElt_apply (mat n K x) (Sum.inl k) (inr_mem_coords k)
  rw [hM, mat_nsElt_mul_apply _ (inl_mem_coords k)] at e1 e2
  rw [mat_nsElt_inl_inl, mat_nsElt_inl_inr, mat_nsElt_inr_inl] at e1
  rw [mat_nsElt_inl_inl, mat_nsElt_inl_inr, mat_nsElt_inr_inr] at e2
  set B : SL(2, K) := mkSL (stdBlock k (mat n K x)) hdet with hB
  have hBC : B ∈ zpowers (zThreeSL (K := K)) := by
    apply mem_zpowers_zThreeSL_of_entries hK
    · simp only [hB, coe_mkSL, stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      linear_combination e1
    · simp only [hB, coe_mkSL, stdBlock, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one]
      linear_combination e2
  set a : StatedSp n K := longBlock K n k B with ha
  have haX : a ∈ nsTorusSp K k := by
    obtain ⟨j, hj⟩ := hBC
    refine ⟨j, ?_⟩
    simp only [ha, nsElt] at hj ⊢
    rw [← map_zpow, hj]
  have hcol : ∀ u t, t ∈ coords k → mat n K x u t = mat n K a u t := by
    intro u t ht
    by_cases hu : u ∈ coords k
    · rw [ha, mat_longBlock, hB, coe_mkSL]
      rcases mem_coords.1 hu with rfl | rfl <;> rcases mem_coords.1 ht with rfl | rfl <;>
        simp [stdBlock, blockMat, hpq.symm]
    · rw [hoff u t hu ht, ha, mat_longBlock, blockMat_apply_of_not_mem k _ (fun h => hu h.1)]
      exact (Matrix.one_apply_ne (fun e => hu (by rw [e]; exact ht))).symm
  refine ⟨a, haX, a⁻¹ * x, ?_, by group⟩
  rw [complSp, mem_suppGroup_iff (parClosed_coords k).compl]
  intro t ht r
  have ht' : t ∈ coords k := by simpa using ht
  rw [map_mul, Matrix.mul_apply, Finset.sum_congr rfl (fun u _ => by rw [hcol u t ht']),
    ← Matrix.mul_apply, ← map_mul, inv_mul_cancel, map_one]

theorem centralizer_nsTorusSp [CharP K 2] (hK : Nat.card K = 2) (k : Fin n) :
    centralizer (nsTorusSp K k : Set (StatedSp n K)) = nsTorusSp K k ⊔ complSp K k ∧
      Disjoint (nsTorusSp K k) (complSp K k) := by
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (nsTorusSp_le_centralizer_self k)
    (complSp_le_centralizer_nsTorusSp k)), disjoint_nsTorusSp_complSp k⟩
  obtain ⟨a, ha, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
    (mem_centralizer_iff.1 hx _ (nsElt_mem_nsTorusSp k)).symm
  exact mul_mem (mem_sup_left ha) (mem_sup_right hy)

theorem commutator_mem_complSp_of_mem_centralizer_nsTorusSp [CharP K 2] (hK : Nat.card K = 2)
    (k : Fin n) {g g' : StatedSp n K} (hg : g ∈ centralizer (nsTorusSp K k : Set (StatedSp n K)))
    (hg' : g' ∈ centralizer (nsTorusSp K k : Set (StatedSp n K))) :
    g * g' * g⁻¹ * g'⁻¹ ∈ complSp K k := by
  refine commutator_mem_of_eq_mul (A := nsTorusSp K k)
    (fun a ha a' ha' => mem_centralizer_iff.1 (nsTorusSp_le_centralizer_self k ha') a ha)
    (fun a ha d hd => (mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hd) a ha))
    ?_ ?_
  · obtain ⟨a, ha, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
      (mem_centralizer_iff.1 hg _ (nsElt_mem_nsTorusSp k)).symm
    exact ⟨a, ha, y, hy, rfl⟩
  · obtain ⟨a, ha, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
      (mem_centralizer_iff.1 hg' _ (nsElt_mem_nsTorusSp k)).symm
    exact ⟨a, ha, y, hy, rfl⟩

theorem centralizer_nsTorusSp_inf_centralizer_complSp [CharP K 2] (hK : Nat.card K = 2)
    (k : Fin (m + 1)) :
    centralizer (nsTorusSp K k : Set (StatedSp (m + 1) K)) ⊓
        centralizer (complSp K k : Set (StatedSp (m + 1) K)) = nsTorusSp K k := by
  refine le_antisymm (fun x hx => ?_) (le_inf (nsTorusSp_le_centralizer_self k) ?_)
  · obtain ⟨a, ha, y, hy, rfl⟩ := exists_eq_mul_of_commute_nsElt hK
      (mem_centralizer_iff.1 hx.1 _ (nsElt_mem_nsTorusSp k)).symm
    have hac : a ∈ centralizer (complSp K k : Set (StatedSp (m + 1) K)) :=
      mem_centralizer_iff.2 fun d hd =>
        (mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hd) a ha).symm
    have hyc : y ∈ centralizer (complSp K k : Set (StatedSp (m + 1) K)) := by
      have := mul_mem (inv_mem hac) hx.2
      rwa [inv_mul_cancel_left] at this
    rw [eq_one_of_mem_complSp_of_mem_centralizer hy hyc, mul_one]
    exact ha
  · intro x hx
    exact mem_centralizer_iff.2 fun d hd =>
      (mem_centralizer_iff.1 (complSp_le_centralizer_nsTorusSp k hd) x hx).symm

end Centralizer

section Layer

theorem isQuasisimple_complSp_two (hK : Nat.card K = 2) (hm : 3 ≤ m) (k : Fin (m + 1)) :
    CFSG.IsQuasisimple (complSp K k) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (complSpEquiv k)
    (CFSG.LieType.Universal.Symplectic.isQuasisimple m K (by omega) (Or.inr (Or.inr ⟨hK, hm⟩)))

theorem isQuasisimple_map_complSp_two {G : Type*} [Group G] {L : Subgroup G}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    CFSG.IsQuasisimple (((complSp K k).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((complSp K k).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((complSp K k).map e.symm.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective))
    (isQuasisimple_complSp_two hK hm k)

theorem isQuasisimple_open_map_complSp_two {G : Type*} [Group G] {L : Subgroup G}
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    CFSG.Open.IsQuasisimple (((complSp K k).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_complSp_two hK hm e k).1.commutator_eq_top,
    (isQuasisimple_map_complSp_two hK hm e k).2.1⟩

theorem layer_inf_centralizer_nsTorusSp {G : Type*} [Group G] {L : Subgroup G} [CharP K 2]
    (hK : Nat.card K = 2) (hm : 3 ≤ m) (e : L ≃* StatedSp (m + 1) K) (k : Fin (m + 1)) :
    inSubgroup layer
        (L ⊓ centralizer ((((nsTorusSp K k).map e.symm.toMonoidHom).map L.subtype :
          Subgroup G) : Set G)) =
      ((complSp K k).map e.symm.toMonoidHom).map L.subtype :=
  LinearPilot.inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (complSp_le_centralizer_nsTorusSp k)
    (fun _ hg _ hg' => commutator_mem_complSp_of_mem_centralizer_nsTorusSp hK k hg hg')
    (isQuasisimple_complSp_two hK hm k)

end Layer

section Aut

variable [Finite K] [CharP K 2]

theorem exists_mem_nsTorusSp_eq_conj_of_fix (hK : Nat.card K = 2) (hn : 2 ≤ n)
    (k : Fin (n + 1)) {β : MulAut (StatedSp (n + 1) K)}
    (hX : ∀ x ∈ nsTorusSp K k, β x = x) (hD : ∀ d ∈ complSp K k, β d = d) :
    ∃ x ∈ nsTorusSp K k, β = MulAut.conj x := by
  have : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨i, hik⟩ := exists_ne k
  obtain ⟨s, rfl⟩ := exists_eq_conj_of_forall_elt_fix (ρ := .positiveLong i) (by omega)
    fun c => hD _ (elt_positiveLong_mem_complSp hik c)
  have hs : s ∈ centralizer (nsTorusSp K k : Set (StatedSp (n + 1) K)) ⊓
      centralizer (complSp K k : Set (StatedSp (n + 1) K)) :=
    ⟨mem_centralizer_iff.2 fun x hx => mul_comm_of_conj_apply_eq (hX x hx),
      mem_centralizer_iff.2 fun d hd => mul_comm_of_conj_apply_eq (hD d hd)⟩
  rw [centralizer_nsTorusSp_inf_centralizer_complSp hK k] at hs
  exact ⟨s, hs, rfl⟩

theorem eq_one_of_two_pow_fix_nsTorusSp (hK : Nat.card K = 2) (hn : 2 ≤ n) (k : Fin (n + 1))
    {β : MulAut (StatedSp (n + 1) K)} (hX : ∀ x ∈ nsTorusSp K k, β x = x)
    (hD : ∀ d ∈ complSp K k, β d = d) {m : ℕ} (hβm : β ^ 2 ^ m = 1) : β = 1 := by
  obtain ⟨x, hx, rfl⟩ := exists_mem_nsTorusSp_eq_conj_of_fix hK hn k hX hD
  rw [eq_one_of_conj_pow_eq_one hβm (odd_card_nsTorusSp k)
    ((nsTorusSp K k).orderOf_dvd_natCard hx), map_one]

end Aut

end CFSG.SeitzReduction.SymplecticPilot
