module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SF

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

theorem ae6Word_append (a b : List (Fin 8)) : ae6Word (a ++ b) = ae6Word a * ae6Word b := by
  simp [ae6Word]

theorem ae6Word_nil : ae6Word [] = 1 := by
  simp [ae6Word]

@[expose] def ae6CycIdx (i : Fin 4) (s : Fin 3) : Fin 12 := ⟨3 * i.val + s.val, by omega⟩

theorem ae6Blk_cycIdx (i : Fin 4) (s : Fin 3) : ae6Blk (ae6CycIdx i s) = i := by
  ext
  simp only [ae6Blk, ae6CycIdx]
  omega

theorem ae6KWord_mem (s : Fin 3) : ae6Word (ae6KWord s) ∈ ae6ModelK := by
  fin_cases s
  · exact Subgroup.subset_closure (by simp [ae6KWord])
  · exact Subgroup.subset_closure (by simp [ae6KWord])
  · have h : ae6KWord 2 = ae6KWord 0 ++ ae6KWord 1 := rfl
    change ae6Word (ae6KWord 2) ∈ ae6ModelK
    rw [h, ae6Word_append]
    exact mul_mem (Subgroup.subset_closure (by simp [ae6KWord]))
      (Subgroup.subset_closure (by simp [ae6KWord]))

theorem mem_range_ae6CLetter {j : Fin 8} : j ∈ Set.range ae6CLetter ↔ j ≠ 3 := by
  constructor
  · rintro ⟨x, rfl⟩
    revert x
    decide
  · intro h
    fin_cases j
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, absurd rfl h, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩]

section Basic

variable (hinv : ∀ i : Fin 8, A6.curtisGen i * A6.curtisGen i = 1)
include hinv

theorem ae6Word_reverse (w : List (Fin 8)) : ae6Word w.reverse = (ae6Word w)⁻¹ := by
  induction w with
  | nil => simp [ae6Word]
  | cons a w ih =>
    rw [List.reverse_cons, ae6Word_append, ih]
    simp only [ae6Word, List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one, mul_inv_rev]
    rw [inv_eq_of_mul_eq_one_right (hinv a)]

theorem ae6Cyc_eq (n : Fin 12) :
    ae6Cyc n = ae6Word (ae6TwinWord (ae6Blk n)) * ae6Word (ae6KWord ⟨n.val % 3, by omega⟩) *
      (ae6Word (ae6TwinWord (ae6Blk n)))⁻¹ := by
  rw [ae6Cyc, ae6CycWord, ae6Word_append, ae6Word_append, ae6Word_reverse hinv]

theorem ae6Cyc_cycIdx (i : Fin 4) (s : Fin 3) :
    ae6Cyc (ae6CycIdx i s) = ae6Word (ae6TwinWord i) * ae6Word (ae6KWord s) * (ae6Word (ae6TwinWord i))⁻¹ := by
  have e : (⟨(ae6CycIdx i s).val % 3, by omega⟩ : Fin 3) = s := by
    ext
    simp only [ae6CycIdx]
    omega
  rw [ae6Cyc_eq hinv, ae6Blk_cycIdx, e]

theorem ae6Cyc_mem_twin (n : Fin 12) : ae6Cyc n ∈ ae6Twin (ae6Blk n) := by
  rw [ae6Cyc_eq hinv]
  exact conj_mem_conjSub (ae6KWord_mem _)

end Basic

section Twins

variable (hC : Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) = ae6LetterSub (Set.range ae6CLetter))
  (hinv : ∀ i : Fin 8, A6.curtisGen i * A6.curtisGen i = 1)
  (hK : ∀ y ∈ ae6ModelK, y = 1 ∨ y = ae6ModelZ ∨
      ∃ s : Fin 3, y = ae6Word (ae6KWord s) ∨ y = (ae6Word (ae6KWord s))⁻¹)
  (hk2 : ∀ s : Fin 3, ae6Word (ae6KWord s) ^ 2 = ae6ModelZ) (hz : ae6ModelZ ≠ 1)
  (hzz : ae6ModelZ * ae6ModelZ = 1)
  (htw : ∀ (x : Fin 7) (i : Fin 4), ∃ j : Fin 4, conjSub (A6.curtisGen (ae6CLetter x)) (ae6Twin i) = ae6Twin j)
  (hdist : ∀ m n : Fin 12, m ≠ n → ae6Cyc m ≠ ae6Cyc n ∧ ae6Cyc m ≠ (ae6Cyc n)⁻¹)

theorem conj_ae6ModelZ {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    c * ae6ModelZ * c⁻¹ = ae6ModelZ := by
  have h := Subgroup.mem_centralizer_iff.mp hc ae6ModelZ rfl
  rw [← h]
  group

include hC in
theorem ae6TwinWord_mem_C (i : Fin 4) :
    ae6Word (ae6TwinWord i) ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := by
  rw [hC]
  apply ae6Word_mem
  intro j hj
  rw [mem_range_ae6CLetter]
  revert j
  fin_cases i <;> decide

include hC hinv hk2 in
theorem ae6Cyc_sq (n : Fin 12) : ae6Cyc n ^ 2 = ae6ModelZ := by
  rw [ae6Cyc_eq hinv]
  have e : ∀ c k : AE6Om, (c * k * c⁻¹) ^ 2 = c * k ^ 2 * c⁻¹ := fun c k => by simp [sq, mul_assoc]
  rw [e, hk2]
  exact conj_ae6ModelZ (ae6TwinWord_mem_C hC _)

include hC hinv hk2 hz in
theorem ae6Cyc_ne_one (n : Fin 12) : ae6Cyc n ≠ 1 := fun h =>
  hz (by rw [← ae6Cyc_sq hC hinv hk2 n, h, one_pow])

include hC hinv hk2 hz in
theorem ae6Cyc_ne_inv (n : Fin 12) : ae6Cyc n ≠ (ae6Cyc n)⁻¹ := fun h => by
  have e := ae6Cyc_sq hC hinv hk2 n
  rw [sq, mul_eq_one_iff_eq_inv.mpr h] at e
  exact hz e.symm

include hC hinv hK in
theorem mem_ae6Twin {i : Fin 4} {y : AE6Om} (hy : y ∈ ae6Twin i) :
    y = 1 ∨ y = ae6ModelZ ∨ ∃ n, ae6Blk n = i ∧ (y = ae6Cyc n ∨ y = (ae6Cyc n)⁻¹) := by
  rw [ae6Twin, mem_conjSub_iff] at hy
  have hyc : y = ae6Word (ae6TwinWord i) * ((ae6Word (ae6TwinWord i))⁻¹ * y * ae6Word (ae6TwinWord i)) *
      (ae6Word (ae6TwinWord i))⁻¹ := by group
  rcases hK _ hy with h | h | ⟨s, h | h⟩
  · left
    rw [hyc, h]
    group
  · right; left
    rw [hyc, h]
    exact conj_ae6ModelZ (ae6TwinWord_mem_C hC i)
  · right; right
    refine ⟨ae6CycIdx i s, ae6Blk_cycIdx i s, Or.inl ?_⟩
    rw [hyc, h, ae6Cyc_cycIdx hinv]
  · right; right
    refine ⟨ae6CycIdx i s, ae6Blk_cycIdx i s, Or.inr ?_⟩
    rw [hyc, h, ae6Cyc_cycIdx hinv]
    group

include hC hinv htw in
theorem conjSub_ae6Twin {g : AE6Om} (hg : g ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) (i : Fin 4) :
    ∃ j, conjSub g (ae6Twin i) = ae6Twin j := by
  rw [hC, ae6LetterSub] at hg
  induction hg using Subgroup.closure_induction'' generalizing i with
  | mem x hx =>
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
    exact htw a i
  | inv_mem x hx =>
    obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
    rw [inv_eq_of_mul_eq_one_right (hinv _)]
    exact htw a i
  | one => exact ⟨i, conjSub_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨k, hk⟩ := hx j
    exact ⟨k, by rw [conjSub_mul, hj, hk]⟩

theorem ae6Twin_zero : ae6Twin 0 = ae6ModelK := by
  rw [ae6Twin, show ae6TwinWord 0 = [] from rfl, ae6Word_nil, conjSub_one]

include hC hinv htw in
theorem ae6ModelTwins_eq : ae6ModelTwins = Set.range ae6Twin := by
  ext J
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨j, hj⟩ := conjSub_ae6Twin hC hinv htw hg 0
    exact ⟨j, by rw [← hj, ae6Twin_zero]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ae6TwinWord_mem_C hC i, rfl⟩

include hC hinv htw in
theorem ae6Twin_le_P (i : Fin 4) : ae6Twin i ≤ ae6ModelP :=
  le_sSup (by rw [ae6ModelTwins_eq hC hinv htw]; exact ⟨i, rfl⟩)

include hC hinv hK hk2 htw in
theorem ae6ModelP_eq : ae6ModelP = Subgroup.closure (Set.range ae6Cyc) := by
  apply le_antisymm
  · apply sSup_le
    rw [ae6ModelTwins_eq hC hinv htw]
    rintro _ ⟨i, rfl⟩ y hy
    rcases mem_ae6Twin hC hinv hK hy with rfl | rfl | ⟨n, -, rfl | rfl⟩
    · exact one_mem _
    · rw [← ae6Cyc_sq hC hinv hk2 0]
      exact pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) 2
    · exact Subgroup.subset_closure (Set.mem_range_self n)
    · exact inv_mem (Subgroup.subset_closure (Set.mem_range_self n))
  · rw [Subgroup.closure_le]
    rintro _ ⟨n, rfl⟩
    exact ae6Twin_le_P hC hinv htw _ (ae6Cyc_mem_twin hinv n)

include hC hinv hK hk2 htw in
theorem ae6ModelP_le_C : ae6ModelP ≤ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := by
  rw [ae6ModelP_eq hC hinv hK hk2 htw, Subgroup.closure_le]
  rintro _ ⟨n, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ rfl
  rw [← ae6Cyc_sq hC hinv hk2 n, sq, mul_assoc]

include hC hinv hK hk2 htw in
theorem ae6Cyc_mem_P (n : Fin 12) : ae6Cyc n ∈ ae6ModelP := by
  rw [ae6ModelP_eq hC hinv hK hk2 htw]
  exact Subgroup.subset_closure (Set.mem_range_self n)

end Twins

namespace AE6FFin

variable (h : AE6FFin)
include h

theorem hC : Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) = ae6LetterSub (Set.range ae6CLetter) := h.1
theorem hK : ∀ y ∈ ae6ModelK, y = 1 ∨ y = ae6ModelZ ∨
    ∃ s : Fin 3, y = ae6Word (ae6KWord s) ∨ y = (ae6Word (ae6KWord s))⁻¹ := h.2.1
theorem hk2 : ∀ s : Fin 3, ae6Word (ae6KWord s) ^ 2 = ae6ModelZ := h.2.2.1
theorem hz : ae6ModelZ ≠ 1 := h.2.2.2.1
theorem hzz : ae6ModelZ * ae6ModelZ = 1 := h.2.2.2.2.1
theorem hinv : ∀ i : Fin 8, A6.curtisGen i * A6.curtisGen i = 1 := h.2.2.2.2.2.1
theorem htw : ∀ (x : Fin 7) (i : Fin 4), ∃ j : Fin 4,
    conjSub (A6.curtisGen (ae6CLetter x)) (ae6Twin i) = ae6Twin j := h.2.2.2.2.2.2.1
theorem hdist : ∀ m n : Fin 12, m ≠ n → ae6Cyc m ≠ ae6Cyc n ∧ ae6Cyc m ≠ (ae6Cyc n)⁻¹ :=
  h.2.2.2.2.2.2.2.1
theorem hcomm : ∀ m n : Fin 12, ae6Blk m ≠ ae6Blk n → ae6Cyc m * ae6Cyc n = ae6Cyc n * ae6Cyc m :=
  h.2.2.2.2.2.2.2.2.1
theorem hq8 : ∀ m n : Fin 12, ae6Blk m = ae6Blk n → m ≠ n →
    ae6Cyc m * ae6Cyc n * (ae6Cyc m)⁻¹ = (ae6Cyc n)⁻¹ := h.2.2.2.2.2.2.2.2.2.1
theorem hF3 : ∀ (x : Fin 7) (n : Fin 12),
    A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) = ae6Cyc (ae6LetterHat x n) ∨
      A6.curtisGen (ae6CLetter x) * ae6Cyc n * A6.curtisGen (ae6CLetter x) = (ae6Cyc (ae6LetterHat x n))⁻¹ :=
  h.2.2.2.2.2.2.2.2.2.2.1
theorem hF4 : ∀ c : Fin 2,
    (∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1) ∧
      ae6Word (ae6ZWord.map (ae6Diag c)) = ae6ModelZ ∧
      (∀ n : Fin 12, ae6Word ((ae6CycWord n).map (ae6Diag c)) = ae6Cyc (ae6GammaHat c n) ∨
        ae6Word ((ae6CycWord n).map (ae6Diag c)) = (ae6Cyc (ae6GammaHat c n))⁻¹) ∧
      ∀ w ∈ ae6WWords, ae6Word (w.map (ae6Diag c)) ∈ ae6ModelW := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem hF5 : ∀ σ : Equiv.Perm (Fin 12), (∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) →
    σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) →
    ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
      (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 := h.2.2.2.2.2.2.2.2.2.2.2.2

theorem twins_eq : ae6ModelTwins = Set.range ae6Twin := ae6ModelTwins_eq h.hC h.hinv h.htw
theorem P_eq : ae6ModelP = Subgroup.closure (Set.range ae6Cyc) := ae6ModelP_eq h.hC h.hinv h.hK h.hk2 h.htw
theorem P_le_C : ae6ModelP ≤ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) :=
  ae6ModelP_le_C h.hC h.hinv h.hK h.hk2 h.htw
theorem cyc_mem_P (n : Fin 12) : ae6Cyc n ∈ ae6ModelP := ae6Cyc_mem_P h.hC h.hinv h.hK h.hk2 h.htw n
theorem cyc_sq (n : Fin 12) : ae6Cyc n ^ 2 = ae6ModelZ := ae6Cyc_sq h.hC h.hinv h.hk2 n
theorem cyc_ne_one (n : Fin 12) : ae6Cyc n ≠ 1 := ae6Cyc_ne_one h.hC h.hinv h.hk2 h.hz n
theorem cyc_ne_inv (n : Fin 12) : ae6Cyc n ≠ (ae6Cyc n)⁻¹ := ae6Cyc_ne_inv h.hC h.hinv h.hk2 h.hz n
theorem mem_twin {i : Fin 4} {y : AE6Om} (hy : y ∈ ae6Twin i) :
    y = 1 ∨ y = ae6ModelZ ∨ ∃ n, ae6Blk n = i ∧ (y = ae6Cyc n ∨ y = (ae6Cyc n)⁻¹) :=
  mem_ae6Twin h.hC h.hinv h.hK hy
theorem twin_le_P (i : Fin 4) : ae6Twin i ≤ ae6ModelP := ae6Twin_le_P h.hC h.hinv h.htw i
theorem z_mem_twin (i : Fin 4) : ae6ModelZ ∈ ae6Twin i := by
  rw [← h.cyc_sq (ae6CycIdx i 0)]
  have := ae6Cyc_mem_twin h.hinv (ae6CycIdx i 0)
  rw [ae6Blk_cycIdx] at this
  exact pow_mem this 2
theorem z_mem_P : ae6ModelZ ∈ ae6ModelP := h.twin_le_P 0 (h.z_mem_twin 0)

theorem cyc_idx_unique {y : AE6Om} {m m' : Fin 12} (hm : y = ae6Cyc m ∨ y = (ae6Cyc m)⁻¹)
    (hm' : y = ae6Cyc m' ∨ y = (ae6Cyc m')⁻¹) : m = m' := by
  by_contra hne
  rcases hm with rfl | rfl <;> rcases hm' with e | e
  · exact (h.hdist m m' hne).1 e
  · exact (h.hdist m m' hne).2 e
  · exact (h.hdist m' m (Ne.symm hne)).2 e.symm
  · exact (h.hdist m m' hne).1 (inv_injective e)

theorem cyc_comm_twin {j : Fin 4} {q : AE6Om} (hq : q ∈ ae6Twin j) {n : Fin 12} (hn : ae6Blk n ≠ j) :
    Commute q (ae6Cyc n) := by
  rcases h.mem_twin hq with rfl | rfl | ⟨m, hm, rfl | rfl⟩
  · exact Commute.one_left _
  · rw [← h.cyc_sq n]
    exact (Commute.refl _).pow_left 2
  · exact h.hcomm m n (by rw [hm]; exact Ne.symm hn)
  · exact Commute.inv_left (h.hcomm m n (by rw [hm]; exact Ne.symm hn))

end AE6FFin

@[expose] noncomputable def ae6CycP (h : AE6FFin) (n : Fin 12) : ↥ae6ModelP := ⟨ae6Cyc n, h.cyc_mem_P n⟩

theorem AE6FFin.aut_ext (h : AE6FFin) {x y : MulAut ↥ae6ModelP} (hxy : ∀ n, x (ae6CycP h n) = y (ae6CycP h n)) :
    x = y := by
  have hcl : Subgroup.closure (Set.range ae6Cyc) ≤ ae6ModelP := h.P_eq.symm.le
  have key : ∀ q (hq : q ∈ Subgroup.closure (Set.range ae6Cyc)), x ⟨q, hcl hq⟩ = y ⟨q, hcl hq⟩ := by
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem q hq =>
      obtain ⟨n, rfl⟩ := hq
      exact hxy n
    | one => exact (map_one x).trans (map_one y).symm
    | mul a b ha hb iha ihb =>
      have e : (⟨a * b, hcl (mul_mem ha hb)⟩ : ↥ae6ModelP) = ⟨a, hcl ha⟩ * ⟨b, hcl hb⟩ := rfl
      rw [e, map_mul, map_mul, iha, ihb]
    | inv a ha iha =>
      have e : (⟨a⁻¹, hcl (inv_mem ha)⟩ : ↥ae6ModelP) = (⟨a, hcl ha⟩ : ↥ae6ModelP)⁻¹ := rfl
      rw [e, map_inv, map_inv, iha]
  exact MulEquiv.ext fun p => key p (h.P_eq ▸ p.2)

@[expose] def ae6RestrictAut {G : Type*} [Group G] (H : Subgroup G) (φ : MulAut G)
    (hφ : ∀ x, x ∈ H ↔ φ x ∈ H) : MulAut ↥H where
  toFun x := ⟨φ x, (hφ x).1 x.2⟩
  invFun x := ⟨φ.symm x, (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact x.2)⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply (x : G))
  right_inv x := Subtype.ext (φ.apply_symm_apply (x : G))
  map_mul' x y := Subtype.ext (map_mul φ (x : G) y)

@[simp] theorem coe_ae6RestrictAut {G : Type*} [Group G] (H : Subgroup G) (φ : MulAut G)
    (hφ : ∀ x, x ∈ H ↔ φ x ∈ H) (x : ↥H) : (ae6RestrictAut H φ hφ x : G) = φ x := rfl

@[simp] theorem coe_ae6RestrictAut_inv {G : Type*} [Group G] (H : Subgroup G) (φ : MulAut G)
    (hφ : ∀ x, x ∈ H ↔ φ x ∈ H) (x : ↥H) : ((ae6RestrictAut H φ hφ)⁻¹ x : G) = φ.symm x := rfl

theorem AE6FFin.conj_mem_P (h : AE6FFin) {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))
    {q : AE6Om} (hq : q ∈ ae6ModelP) : c * q * c⁻¹ ∈ ae6ModelP := by
  rw [h.P_eq] at hq
  induction hq using Subgroup.closure_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    obtain ⟨j, hj⟩ := conjSub_ae6Twin h.hC h.hinv h.htw hc (ae6Blk n)
    exact h.twin_le_P j (hj ▸ conj_mem_conjSub (ae6Cyc_mem_twin h.hinv n))
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ iha =>
    have e : c * a⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem iha

theorem AE6FFin.conj_mem_P_iff (h : AE6FFin) {c : AE6Om}
    (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) (q : AE6Om) :
    q ∈ ae6ModelP ↔ MulAut.conj c q ∈ ae6ModelP := by
  rw [MulAut.conj_apply]
  refine ⟨h.conj_mem_P hc, fun hq => ?_⟩
  have := h.conj_mem_P (inv_mem hc) hq
  simpa [mul_assoc] using this

@[expose] noncomputable def ae6ConjP (h : AE6FFin) (c : AE6Om)
    (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) : MulAut ↥ae6ModelP :=
  ae6RestrictAut ae6ModelP (MulAut.conj c) (h.conj_mem_P_iff hc)

@[simp] theorem coe_ae6ConjP (h : AE6FFin) {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))
    (p : ↥ae6ModelP) : (ae6ConjP h c hc p : AE6Om) = c * p * c⁻¹ := rfl

theorem ae6ConjP_mem (h : AE6FFin) {c : AE6Om} (hc : c ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    ae6ConjP h c hc ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :=
  ⟨c, hc, fun _ => rfl⟩

@[expose] def ae6PM (h : AE6FFin) (p : ↥ae6ModelP) (m : Fin 12) : Prop := p = ae6CycP h m ∨ p = (ae6CycP h m)⁻¹

theorem ae6PM_coe {h : AE6FFin} {p : ↥ae6ModelP} {m : Fin 12} (hp : ae6PM h p m) :
    (p : AE6Om) = ae6Cyc m ∨ (p : AE6Om) = (ae6Cyc m)⁻¹ := by
  rcases hp with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem ae6PM_unique {h : AE6FFin} {p : ↥ae6ModelP} {m m' : Fin 12} (hm : ae6PM h p m) (hm' : ae6PM h p m') :
    m = m' := h.cyc_idx_unique (ae6PM_coe hm) (ae6PM_coe hm')

theorem ae6PM_inv {h : AE6FFin} {p : ↥ae6ModelP} {m : Fin 12} (hp : ae6PM h p m) : ae6PM h p⁻¹ m := by
  rcases hp with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (inv_inv _)

theorem ae6PM_self (h : AE6FFin) (m : Fin 12) : ae6PM h (ae6CycP h m) m := Or.inl rfl

theorem ae6PM_map {h : AE6FFin} {x : MulAut ↥ae6ModelP} {p : ↥ae6ModelP} {m m' : Fin 12} (hp : ae6PM h p m)
    (hx : ae6PM h (x (ae6CycP h m)) m') : ae6PM h (x p) m' := by
  rcases hp with rfl | rfl
  · exact hx
  · rw [map_inv]
    exact ae6PM_inv hx

@[expose] def ae6Good (h : AE6FFin) (x : MulAut ↥ae6ModelP) : Prop := ∀ n, ∃ m, ae6PM h (x (ae6CycP h n)) m

open Classical in
@[expose] noncomputable def ae6HatFun (h : AE6FFin) (x : MulAut ↥ae6ModelP) (n : Fin 12) : Fin 12 :=
  if hn : ∃ m, ae6PM h (x (ae6CycP h n)) m then hn.choose else n

theorem ae6HatFun_spec {h : AE6FFin} {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) (n : Fin 12) :
    ae6PM h (x (ae6CycP h n)) (ae6HatFun h x n) := by
  rw [ae6HatFun, dif_pos (hx n)]
  exact (hx n).choose_spec

theorem ae6HatFun_eq {h : AE6FFin} {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) {n m : Fin 12}
    (hm : ae6PM h (x (ae6CycP h n)) m) : ae6HatFun h x n = m :=
  ae6PM_unique (ae6HatFun_spec hx n) hm

theorem ae6HatFun_injective {h : AE6FFin} {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) :
    Function.Injective (ae6HatFun h x) := by
  intro n n' e
  have h1 := ae6HatFun_spec hx n
  have h2 := ae6HatFun_spec hx n'
  rw [e] at h1
  have key : ae6CycP h n = ae6CycP h n' ∨ ae6CycP h n = (ae6CycP h n')⁻¹ := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (x.injective (h1.trans h2.symm))
    · exact Or.inr (x.injective (by rw [map_inv, h1, h2, inv_inv]))
    · exact Or.inr (x.injective (by rw [map_inv, h1, h2]))
    · exact Or.inl (x.injective (h1.trans h2.symm))
  exact (ae6PM_unique (ae6PM_self h n) key).symm.symm ▸ rfl

theorem ae6HatFun_bijective {h : AE6FFin} {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) :
    Function.Bijective (ae6HatFun h x) :=
  ⟨ae6HatFun_injective hx, Finite.injective_iff_surjective.mp (ae6HatFun_injective hx)⟩

theorem ae6Good_mul {h : AE6FFin} {x y : MulAut ↥ae6ModelP} (hx : ae6Good h x) (hy : ae6Good h y) (n : Fin 12) :
    ae6PM h ((x * y) (ae6CycP h n)) (ae6HatFun h x (ae6HatFun h y n)) :=
  show ae6PM h (x (y (ae6CycP h n))) _ from ae6PM_map (ae6HatFun_spec hy n) (ae6HatFun_spec hx _)

theorem ae6Good_inv {h : AE6FFin} {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) : ae6Good h x⁻¹ := by
  intro n
  obtain ⟨n', hn'⟩ := (ae6HatFun_bijective hx).2 n
  have hs := ae6HatFun_spec hx n'
  rw [hn'] at hs
  refine ⟨n', ?_⟩
  rcases hs with hs | hs
  · left
    rw [← hs, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  · right
    rw [← inv_inv (ae6CycP h n), ← hs, ← map_inv, MulAut.inv_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def ae6GoodSub (h : AE6FFin) : Subgroup (MulAut ↥ae6ModelP) where
  carrier := {x | ae6Good h x}
  one_mem' n := ⟨n, ae6PM_self h n⟩
  mul_mem' hx hy n := ⟨_, ae6Good_mul hx hy n⟩
  inv_mem' hx := ae6Good_inv hx

@[expose] noncomputable def ae6Hat (h : AE6FFin) : ↥(ae6GoodSub h) →* Equiv.Perm (Fin 12) where
  toFun x := Equiv.ofBijective _ (ae6HatFun_bijective x.2)
  map_one' := Equiv.ext fun n => ae6HatFun_eq (ae6GoodSub h).one_mem (ae6PM_self h n)
  map_mul' x y := Equiv.ext fun n => ae6HatFun_eq (mul_mem x.2 y.2) (ae6Good_mul x.2 y.2 n)

theorem ae6Hat_spec (h : AE6FFin) (x : ↥(ae6GoodSub h)) (n : Fin 12) :
    ae6PM h ((x : MulAut ↥ae6ModelP) (ae6CycP h n)) (ae6Hat h x n) := ae6HatFun_spec x.2 n

theorem ae6Hat_eq (h : AE6FFin) (x : ↥(ae6GoodSub h)) {n m : Fin 12}
    (hm : ae6PM h ((x : MulAut ↥ae6ModelP) (ae6CycP h n)) m) : ae6Hat h x n = m := ae6HatFun_eq x.2 hm

@[expose] noncomputable def ae6ZP (h : AE6FFin) : ↥ae6ModelP := ⟨ae6ModelZ, h.z_mem_P⟩

theorem ae6Commute_coe {p p' : ↥ae6ModelP} : Commute p p' ↔ Commute (p : AE6Om) p' :=
  ⟨fun e => congrArg Subtype.val e, fun e => Subtype.ext e⟩

theorem ae6Commute_aut (x : MulAut ↥ae6ModelP) {p p' : ↥ae6ModelP} : Commute (x p) (x p') ↔ Commute p p' :=
  ⟨fun e => x.injective (by rw [map_mul, map_mul]; exact e), fun e => e.map x⟩

theorem ae6PM_commute {h : AE6FFin} {p p' : ↥ae6ModelP} {m m' : Fin 12} (hp : ae6PM h p m) (hp' : ae6PM h p' m') :
    Commute p p' ↔ Commute (ae6CycP h m) (ae6CycP h m') := by
  rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl <;>
    simp only [Commute.inv_left_iff, Commute.inv_right_iff]

theorem AE6FFin.commute_iff (h : AE6FFin) {m n : Fin 12} (hmn : m ≠ n) :
    Commute (ae6CycP h m) (ae6CycP h n) ↔ ae6Blk m ≠ ae6Blk n := by
  rw [ae6Commute_coe]
  refine ⟨fun hc hb => ?_, fun hb => h.hcomm m n hb⟩
  have hc' : Commute (ae6Cyc m) (ae6Cyc n) := hc
  have e := h.hq8 m n hb hmn
  rw [hc'.eq, mul_inv_cancel_right] at e
  exact h.cyc_ne_inv n e

theorem ae6Hat_blk (h : AE6FFin) (x : ↥(ae6GoodSub h)) (m n : Fin 12) :
    ae6Blk m = ae6Blk n ↔ ae6Blk (ae6Hat h x m) = ae6Blk (ae6Hat h x n) := by
  by_cases hmn : m = n
  · subst hmn
    simp
  have hmn' : ae6Hat h x m ≠ ae6Hat h x n := fun e => hmn ((ae6Hat h x).injective e)
  rw [← not_iff_not, ← Ne, ← Ne, ← h.commute_iff hmn, ← h.commute_iff hmn',
    ← ae6PM_commute (ae6Hat_spec h x m) (ae6Hat_spec h x n), ae6Commute_aut]

theorem AE6FFin.zP_eq (h : AE6FFin) (m : Fin 12) : ae6ZP h = ae6CycP h m ^ 2 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact (h.cyc_sq m).symm)

theorem ae6Good_z (h : AE6FFin) {x : MulAut ↥ae6ModelP} (hx : ae6Good h x) : x (ae6ZP h) = ae6ZP h := by
  have hzP : ae6ZP h * ae6ZP h = 1 := Subtype.ext h.hzz
  obtain ⟨m, hm⟩ := hx 0
  have e0 : x (ae6ZP h) = x (ae6CycP h 0) ^ 2 := by rw [← map_pow, ← h.zP_eq 0]
  rcases hm with hm | hm
  · rw [e0, hm, ← h.zP_eq m]
  · rw [e0, hm, inv_pow, ← h.zP_eq m]
    exact inv_eq_of_mul_eq_one_right hzP

theorem AE6FFin.mem_twin_P (h : AE6FFin) {i : Fin 4} {p : ↥ae6ModelP} (hp : (p : AE6Om) ∈ ae6Twin i) :
    p = 1 ∨ p = ae6ZP h ∨ ∃ n, ae6Blk n = i ∧ ae6PM h p n := by
  rcases h.mem_twin hp with e | e | ⟨n, hn, e | e⟩
  · exact Or.inl (Subtype.ext e)
  · exact Or.inr (Or.inl (Subtype.ext e))
  · exact Or.inr (Or.inr ⟨n, hn, Or.inl (Subtype.ext e)⟩)
  · exact Or.inr (Or.inr ⟨n, hn, Or.inr (Subtype.ext e)⟩)

theorem AE6FFin.PM_mem_twin (h : AE6FFin) {p : ↥ae6ModelP} {n : Fin 12} (hp : ae6PM h p n) :
    (p : AE6Om) ∈ ae6Twin (ae6Blk n) := by
  rcases ae6PM_coe hp with e | e <;> rw [e]
  · exact ae6Cyc_mem_twin h.hinv n
  · exact inv_mem (ae6Cyc_mem_twin h.hinv n)

theorem ae6Good_twin (h : AE6FFin) (x : ↥(ae6GoodSub h)) (hb : ∀ n, ae6Blk (ae6Hat h x n) = ae6Blk n)
    {i : Fin 4} {p : ↥ae6ModelP} (hp : (p : AE6Om) ∈ ae6Twin i) :
    ((x : MulAut ↥ae6ModelP) p : AE6Om) ∈ ae6Twin i := by
  rcases h.mem_twin_P hp with rfl | rfl | ⟨n, rfl, hn⟩
  · rw [map_one]
    exact one_mem _
  · rw [ae6Good_z h x.2]
    exact h.z_mem_twin i
  · rw [← hb n]
    exact h.PM_mem_twin (ae6PM_map hn (ae6Hat_spec h x n))

theorem ae6Hat_ker_sq (h : AE6FFin) (x : ↥(ae6GoodSub h)) (hx : ae6Hat h x = 1) :
    (x : MulAut ↥ae6ModelP) * x = 1 := by
  apply h.aut_ext
  intro n
  have hs := ae6Hat_spec h x n
  rw [hx, Equiv.Perm.one_apply] at hs
  rw [MulAut.mul_apply, MulAut.one_apply]
  rcases hs with hs | hs
  · rw [hs, hs]
  · rw [hs, map_inv, hs, inv_inv]

theorem ae6_q8_choice {G : Type*} [Group G] {a b u v : G} (hab : a * b * a⁻¹ = b⁻¹) (hba : b * a * b⁻¹ = a⁻¹)
    (hu : u = a ∨ u = a⁻¹) (hv : v = b ∨ v = b⁻¹) :
    ∃ q ∈ ({1, a, b, a * b} : Set G), q * a * q⁻¹ = u ∧ q * b * q⁻¹ = v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact ⟨1, by simp, by group, by group⟩
  · exact ⟨u, by simp, by group, hab⟩
  · exact ⟨v, by simp, hba, by group⟩
  · refine ⟨a * b, by simp, ?_, ?_⟩
    · calc a * b * a * (a * b)⁻¹ = a * (b * a * b⁻¹) * a⁻¹ := by group
        _ = a⁻¹ := by rw [hba]; group
    · calc a * b * b * (a * b)⁻¹ = a * b * a⁻¹ := by group
        _ = b⁻¹ := hab

theorem ae6_conj_prod4 {G : Type*} [Group G] (q : Fin 4 → G) (i : Fin 4) {y y' : G}
    (hy : ∀ j, j ≠ i → Commute (q j) y) (hy' : ∀ j, j ≠ i → Commute (q j) y') (hi : q i * y * (q i)⁻¹ = y') :
    q 0 * q 1 * q 2 * q 3 * y * (q 0 * q 1 * q 2 * q 3)⁻¹ = y' := by
  have f : ∀ j, j ≠ i → q j * y * (q j)⁻¹ = y := fun j hj => by rw [(hy j hj).eq, mul_inv_cancel_right]
  have f' : ∀ j, j ≠ i → q j * y' * (q j)⁻¹ = y' := fun j hj => by rw [(hy' j hj).eq, mul_inv_cancel_right]
  have e : q 0 * q 1 * q 2 * q 3 * y * (q 0 * q 1 * q 2 * q 3)⁻¹ =
      q 0 * (q 1 * (q 2 * (q 3 * y * (q 3)⁻¹) * (q 2)⁻¹) * (q 1)⁻¹) * (q 0)⁻¹ := by group
  rw [e]
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> simp
  rcases hi4 with rfl | rfl | rfl | rfl
  · rw [f 3 (by decide), f 2 (by decide), f 1 (by decide)]; exact hi
  · rw [f 3 (by decide), f 2 (by decide), hi, f' 0 (by decide)]
  · rw [f 3 (by decide), hi, f' 1 (by decide), f' 0 (by decide)]
  · rw [hi, f' 2 (by decide), f' 1 (by decide), f' 0 (by decide)]

theorem ae6CycIdx_blk (n : Fin 12) : n = ae6CycIdx (ae6Blk n) ⟨n.val % 3, by omega⟩ := by
  ext
  simp only [ae6CycIdx, ae6Blk]
  omega

theorem AE6FFin.cyc_idx2 (h : AE6FFin) (i : Fin 4) :
    ae6Cyc (ae6CycIdx i 2) = ae6Cyc (ae6CycIdx i 0) * ae6Cyc (ae6CycIdx i 1) := by
  rw [ae6Cyc_cycIdx h.hinv, ae6Cyc_cycIdx h.hinv, ae6Cyc_cycIdx h.hinv,
    show ae6KWord 2 = ae6KWord 0 ++ ae6KWord 1 from rfl, ae6Word_append]
  group

theorem ae6Hat_ker (h : AE6FFin) (x : ↥(ae6GoodSub h)) (hx : ae6Hat h x = 1) :
    ∃ q ∈ ae6ModelP, ∀ n, ((x : MulAut ↥ae6ModelP) (ae6CycP h n) : AE6Om) = q * ae6Cyc n * q⁻¹ := by
  have hfix : ∀ n, ae6PM h ((x : MulAut ↥ae6ModelP) (ae6CycP h n)) n := fun n => by
    have := ae6Hat_spec h x n
    rwa [hx, Equiv.Perm.one_apply] at this
  have hblock : ∀ i : Fin 4, ∃ q ∈ ae6Twin i, ∀ n, ae6Blk n = i →
      ((x : MulAut ↥ae6ModelP) (ae6CycP h n) : AE6Om) = q * ae6Cyc n * q⁻¹ := by
    intro i
    have hne : ae6CycIdx i 0 ≠ ae6CycIdx i 1 := by simp [ae6CycIdx, Fin.ext_iff]
    have hb : ae6Blk (ae6CycIdx i 0) = ae6Blk (ae6CycIdx i 1) := by rw [ae6Blk_cycIdx, ae6Blk_cycIdx]
    obtain ⟨q, hq, h0, h1⟩ := ae6_q8_choice (h.hq8 _ _ hb hne) (h.hq8 _ _ hb.symm hne.symm)
      (ae6PM_coe (hfix (ae6CycIdx i 0))) (ae6PM_coe (hfix (ae6CycIdx i 1)))
    have hmem : ∀ s, ae6Cyc (ae6CycIdx i s) ∈ ae6Twin i := fun s => by
      have := ae6Cyc_mem_twin h.hinv (ae6CycIdx i s)
      rwa [ae6Blk_cycIdx] at this
    refine ⟨q, ?_, ?_⟩
    · rcases hq with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hmem 0
      · exact hmem 1
      · exact mul_mem (hmem 0) (hmem 1)
    intro n hn
    rw [ae6CycIdx_blk n, hn]
    generalize (⟨n.val % 3, _⟩ : Fin 3) = s
    have h2 : ae6CycP h (ae6CycIdx i 2) = ae6CycP h (ae6CycIdx i 0) * ae6CycP h (ae6CycIdx i 1) :=
      Subtype.ext (h.cyc_idx2 i)
    fin_cases s
    · exact h0.symm
    · exact h1.symm
    · change ((x : MulAut ↥ae6ModelP) (ae6CycP h (ae6CycIdx i 2)) : AE6Om) = q * ae6Cyc (ae6CycIdx i 2) * q⁻¹
      rw [h2, map_mul, Subgroup.coe_mul, h0.symm, h1.symm, h.cyc_idx2 i]
      group
  choose qf hqf using hblock
  refine ⟨qf 0 * qf 1 * qf 2 * qf 3, ?_, fun n => ?_⟩
  · exact mul_mem (mul_mem (mul_mem (h.twin_le_P 0 (hqf 0).1) (h.twin_le_P 1 (hqf 1).1))
      (h.twin_le_P 2 (hqf 2).1)) (h.twin_le_P 3 (hqf 3).1)
  symm
  apply ae6_conj_prod4 qf (ae6Blk n)
  · intro j hj
    exact h.cyc_comm_twin (hqf j).1 (Ne.symm hj)
  · intro j hj
    rcases ae6PM_coe (hfix n) with e | e <;> rw [e]
    · exact h.cyc_comm_twin (hqf j).1 (Ne.symm hj)
    · exact (h.cyc_comm_twin (hqf j).1 (Ne.symm hj)).inv_right
  · exact ((hqf (ae6Blk n)).2 n rfl).symm

theorem AE6FFin.letter_mem_C (h : AE6FFin) (x : Fin 7) :
    A6.curtisGen (ae6CLetter x) ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := by
  rw [h.hC]
  exact Subgroup.subset_closure ⟨_, ⟨x, rfl⟩, rfl⟩

theorem ae6ConjP_letter_PM (h : AE6FFin) (x : Fin 7) (n : Fin 12) :
    ae6PM h (ae6ConjP h _ (h.letter_mem_C x) (ae6CycP h n)) (ae6LetterHat x n) := by
  have e : (A6.curtisGen (ae6CLetter x))⁻¹ = A6.curtisGen (ae6CLetter x) :=
    inv_eq_of_mul_eq_one_right (h.hinv _)
  rcases h.hF3 x n with h3 | h3
  · left
    apply Subtype.ext
    rw [coe_ae6ConjP, e]
    exact h3
  · right
    apply Subtype.ext
    rw [coe_ae6ConjP, e]
    exact h3

@[expose] noncomputable def ae6LetterP (h : AE6FFin) (x : Fin 7) : ↥(ae6GoodSub h) :=
  ⟨ae6ConjP h _ (h.letter_mem_C x), fun n => ⟨_, ae6ConjP_letter_PM h x n⟩⟩

theorem ae6Hat_letterP (h : AE6FFin) (x : Fin 7) : ae6Hat h (ae6LetterP h x) = ae6LetterHatPerm x :=
  Equiv.ext fun n => ae6Hat_eq h _ (ae6ConjP_letter_PM h x n)

theorem ae6LetterP_mem (h : AE6FFin) (x : Fin 7) :
    ((ae6LetterP h x : ↥(ae6GoodSub h)) : MulAut ↥ae6ModelP) ∈
      ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) := ae6ConjP_mem h (h.letter_mem_C x)

theorem ae6Good_of_twin (h : AE6FFin) {x : MulAut ↥ae6ModelP}
    (hx : ∀ J ∈ ae6ModelTwins, ∃ J' ∈ ae6ModelTwins, ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ (x p : AE6Om) ∈ J') :
    ae6Good h x := by
  intro n
  obtain ⟨J', hJ', hJ⟩ := hx _ (h.twins_eq ▸ ⟨ae6Blk n, rfl⟩ : ae6Twin (ae6Blk n) ∈ ae6ModelTwins)
  rw [h.twins_eq] at hJ'
  obtain ⟨j, rfl⟩ := hJ'
  have hmem := (hJ (ae6CycP h n)).1 (ae6Cyc_mem_twin h.hinv n)
  have hzP1 : ae6ZP h ≠ 1 := fun e => h.hz (congrArg Subtype.val e)
  rcases h.mem_twin_P hmem with e | e | ⟨m, -, hm⟩
  · exact absurd (x.injective (e.trans (map_one x).symm)) fun e' => h.cyc_ne_one n (congrArg Subtype.val e')
  · exfalso
    have e2 : x (ae6ZP h) = 1 := by
      rw [h.zP_eq n, map_pow, e]
      exact Subtype.ext h.hzz
    exact hzP1 (x.injective (e2.trans (map_one x).symm))
  · exact ⟨m, hm⟩

section Gamma

theorem ae6Diag_involutive (c : Fin 2) : Function.Involutive (ae6Diag c) := by
  have : ∀ c : Fin 2, ∀ i, ae6Diag c (ae6Diag c i) = i := by decide
  exact this c

theorem AE6FFin.exists_gamma (h : AE6FFin) (c : Fin 2) :
    ∃ e : MulAut AE6Om, ∀ i, e (A6.curtisGen i) = A6.curtisGen (ae6Diag c i) :=
  ae6_aut_of_perm _ (ae6Diag_involutive c).surjective (h.hF4 c).1

@[expose] noncomputable def ae6GammaE (h : AE6FFin) (c : Fin 2) : MulAut AE6Om := (h.exists_gamma c).choose

theorem ae6GammaE_gen (h : AE6FFin) (c : Fin 2) (i : Fin 8) :
    ae6GammaE h c (A6.curtisGen i) = A6.curtisGen (ae6Diag c i) := (h.exists_gamma c).choose_spec i

theorem ae6GammaE_word (h : AE6FFin) (c : Fin 2) (w : List (Fin 8)) :
    ae6GammaE h c (ae6Word w) = ae6Word (w.map (ae6Diag c)) := by
  induction w with
  | nil => simp [ae6Word]
  | cons a w ih =>
    simp only [ae6Word] at ih ⊢
    rw [List.map_cons, List.prod_cons, map_mul, ih, ae6GammaE_gen]
    rfl

theorem ae6GammaE_gammaE (h : AE6FFin) (c : Fin 2) (y : AE6Om) : ae6GammaE h c (ae6GammaE h c y) = y := by
  have key : ∀ y ∈ Subgroup.closure (Set.range A6.curtisGen), ae6GammaE h c (ae6GammaE h c y) = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [ae6GammaE_gen, ae6GammaE_gen, ae6Diag_involutive c i]
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  exact key y (by rw [A6.closure_curtisGen]; exact Subgroup.mem_top y)

theorem ae6GammaE_z (h : AE6FFin) (c : Fin 2) : ae6GammaE h c ae6ModelZ = ae6ModelZ := by
  rw [show ae6ModelZ = ae6Word ae6ZWord from rfl, ae6GammaE_word]
  exact (h.hF4 c).2.1

theorem ae6GammaE_C (h : AE6FFin) (c : Fin 2) {y : AE6Om}
    (hy : y ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)) :
    ae6GammaE h c y ∈ Subgroup.centralizer ({ae6ModelZ} : Set AE6Om) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  rintro _ rfl
  rw [← ae6GammaE_z h c, ← map_mul, ← map_mul, hy _ rfl]

theorem ae6GammaE_cyc (h : AE6FFin) (c : Fin 2) (n : Fin 12) :
    ae6GammaE h c (ae6Cyc n) = ae6Cyc (ae6GammaHat c n) ∨
      ae6GammaE h c (ae6Cyc n) = (ae6Cyc (ae6GammaHat c n))⁻¹ := by
  rw [show ae6Cyc n = ae6Word (ae6CycWord n) from rfl, ae6GammaE_word]
  exact (h.hF4 c).2.2.1 n

theorem ae6GammaE_P_mem (h : AE6FFin) (c : Fin 2) {y : AE6Om} (hy : y ∈ ae6ModelP) :
    ae6GammaE h c y ∈ ae6ModelP := by
  rw [h.P_eq] at hy ⊢
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    rcases ae6GammaE_cyc h c n with e | e <;> rw [e]
    · exact Subgroup.subset_closure (Set.mem_range_self _)
    · exact inv_mem (Subgroup.subset_closure (Set.mem_range_self _))
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

theorem ae6GammaE_P (h : AE6FFin) (c : Fin 2) (y : AE6Om) : y ∈ ae6ModelP ↔ ae6GammaE h c y ∈ ae6ModelP :=
  ⟨ae6GammaE_P_mem h c, fun hy => ae6GammaE_gammaE h c y ▸ ae6GammaE_P_mem h c hy⟩

theorem ae6GammaE_W (h : AE6FFin) (c : Fin 2) {y : AE6Om} (hy : y ∈ ae6ModelW) : ae6GammaE h c y ∈ ae6ModelW := by
  have hle : ae6ModelW ≤ ae6ModelW.comap (ae6GammaE h c).toMonoidHom := by
    rw [ae6ModelW, Subgroup.closure_le]
    have hw : ∀ w ∈ ae6WWords, ae6Word w ∈ (ae6ModelW.comap (ae6GammaE h c).toMonoidHom : Set AE6Om) := by
      intro w hw
      change ae6GammaE h c (ae6Word w) ∈ ae6ModelW
      rw [ae6GammaE_word]
      exact (h.hF4 c).2.2.2 w hw
    rintro _ (rfl | rfl | rfl | rfl | rfl) <;> exact hw _ (by simp [ae6WWords])
  exact hle hy

@[expose] noncomputable def ae6GammaPAut (h : AE6FFin) (c : Fin 2) : MulAut ↥ae6ModelP :=
  ae6RestrictAut ae6ModelP (ae6GammaE h c) (ae6GammaE_P h c)

theorem ae6GammaP_PM (h : AE6FFin) (c : Fin 2) (n : Fin 12) :
    ae6PM h (ae6GammaPAut h c (ae6CycP h n)) (ae6GammaHat c n) := by
  rcases ae6GammaE_cyc h c n with e | e
  · exact Or.inl (Subtype.ext e)
  · exact Or.inr (Subtype.ext e)

@[expose] noncomputable def ae6GammaP (h : AE6FFin) (c : Fin 2) : ↥(ae6GoodSub h) :=
  ⟨ae6GammaPAut h c, fun n => ⟨_, ae6GammaP_PM h c n⟩⟩

theorem ae6Hat_gammaP (h : AE6FFin) (c : Fin 2) : ae6Hat h (ae6GammaP h c) = ae6GammaHatPerm c :=
  Equiv.ext fun n => ae6Hat_eq h _ (ae6GammaP_PM h c n)

end Gamma

theorem ae6ConjAut_mul {X : Subgroup AE6Om} {α β : MulAut ↥ae6ModelP} (hα : α ∈ ae6ConjAut X)
    (hβ : β ∈ ae6ConjAut X) : α * β ∈ ae6ConjAut X := by
  obtain ⟨c, hc, hα⟩ := hα
  obtain ⟨d, hd, hβ⟩ := hβ
  exact ⟨c * d, mul_mem hc hd, fun p => by rw [MulAut.mul_apply, hα, hβ]; group⟩

theorem ae6ConjAut_inv {X : Subgroup AE6Om} {α : MulAut ↥ae6ModelP} (hα : α ∈ ae6ConjAut X) :
    α⁻¹ ∈ ae6ConjAut X := by
  obtain ⟨c, hc, hα⟩ := hα
  refine ⟨c⁻¹, inv_mem hc, fun p => ?_⟩
  have e : α (α⁻¹ p) = p := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have := hα (α⁻¹ p)
  rw [e] at this
  rw [this]
  group

theorem ae6ConjAut_one (X : Subgroup AE6Om) : (1 : MulAut ↥ae6ModelP) ∈ ae6ConjAut X :=
  ⟨1, one_mem _, fun p => by simp⟩

theorem ae6ConjAut_transport (Φ : MulAut ↥ae6ModelP) (e : MulAut AE6Om) (f : AE6Om → AE6Om)
    (hΦ : ∀ p, (Φ p : AE6Om) = e p) (hΦi : ∀ p, (Φ⁻¹ p : AE6Om) = f p) (hef : ∀ y, e (f y) = y)
    {X : Subgroup AE6Om} (hX : ∀ x ∈ X, e x ∈ X) {α : MulAut ↥ae6ModelP} (hα : α ∈ ae6ConjAut X) :
    Φ * α * Φ⁻¹ ∈ ae6ConjAut X := by
  obtain ⟨c, hc, hα⟩ := hα
  refine ⟨e c, hX c hc, fun p => ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hΦ, hα, hΦi, map_mul, map_mul, map_inv, hef]

theorem ae6_image_conj_mul {G : Type*} [Group G] (a b : G) (S : Set G) :
    (fun α => a * b * α * (a * b)⁻¹) '' S = (fun α => a * α * a⁻¹) '' ((fun α => b * α * b⁻¹) '' S) := by
  rw [Set.image_image]
  congr 1
  funext α
  group

@[expose] def ae6Nice (φ : MulAut ↥ae6ModelP) : Prop :=
  (∀ α ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)),
      φ * α * φ⁻¹ ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))) ∧
    ∃ β ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om)),
      (fun α => φ * α * φ⁻¹) '' ae6ConjAut ae6ModelW = (fun α => β * α * β⁻¹) '' ae6ConjAut ae6ModelW

theorem ae6Nice_mul {φ ψ : MulAut ↥ae6ModelP} (hφ : ae6Nice φ) (hψ : ae6Nice ψ) : ae6Nice (φ * ψ) := by
  obtain ⟨hφ1, β₁, hβ₁, hφ2⟩ := hφ
  obtain ⟨hψ1, β₂, hβ₂, hψ2⟩ := hψ
  refine ⟨fun α hα => ?_, φ * β₂ * φ⁻¹ * β₁, ae6ConjAut_mul (hφ1 _ hβ₂) hβ₁, ?_⟩
  · have e : φ * ψ * α * (φ * ψ)⁻¹ = φ * (ψ * α * ψ⁻¹) * φ⁻¹ := by group
    rw [e]
    exact hφ1 _ (hψ1 α hα)
  · rw [ae6_image_conj_mul φ ψ, hψ2, ← ae6_image_conj_mul, show φ * β₂ = φ * β₂ * φ⁻¹ * φ by group,
      ae6_image_conj_mul _ φ, hφ2, ← ae6_image_conj_mul]
    congr 1
    funext α
    group

theorem ae6Nice_of_mem {φ : MulAut ↥ae6ModelP}
    (hφ : φ ∈ ae6ConjAut (Subgroup.centralizer ({ae6ModelZ} : Set AE6Om))) : ae6Nice φ :=
  ⟨fun _ hα => ae6ConjAut_mul (ae6ConjAut_mul hφ hα) (ae6ConjAut_inv hφ), φ, hφ, rfl⟩

theorem ae6Nice_one : ae6Nice 1 := ae6Nice_of_mem (ae6ConjAut_one _)

section GammaNice

theorem ae6GammaPAut_inv_apply (h : AE6FFin) (c : Fin 2) (p : ↥ae6ModelP) :
    ((ae6GammaPAut h c)⁻¹ p : AE6Om) = ae6GammaE h c p := by
  rw [ae6GammaPAut, coe_ae6RestrictAut_inv, MulEquiv.symm_apply_eq, ae6GammaE_gammaE]

theorem ae6Nice_gammaP (h : AE6FFin) (c : Fin 2) : ae6Nice (ae6GammaPAut h c) := by
  have hΦ : ∀ p, (ae6GammaPAut h c p : AE6Om) = ae6GammaE h c p := fun _ => rfl
  have hΦi := ae6GammaPAut_inv_apply h c
  have hef := ae6GammaE_gammaE h c
  have hW : ∀ x ∈ ae6ModelW, ae6GammaE h c x ∈ ae6ModelW := fun _ hx => ae6GammaE_W h c hx
  refine ⟨fun α hα => ae6ConjAut_transport _ _ _ hΦ hΦi hef (fun _ hx => ae6GammaE_C h c hx) hα,
    1, ae6ConjAut_one _, ?_⟩
  ext α
  constructor
  · rintro ⟨α', hα', rfl⟩
    exact ⟨_, ae6ConjAut_transport _ _ _ hΦ hΦi hef hW hα', by group⟩
  · rintro ⟨α', hα', rfl⟩
    refine ⟨(ae6GammaPAut h c)⁻¹ * α' * (ae6GammaPAut h c)⁻¹⁻¹, ?_, by group⟩
    exact ae6ConjAut_transport _ _ _ hΦi (fun p => by rw [inv_inv]; rfl) hef hW hα'

end GammaNice

theorem ae6_toPerm_inv {f : Fin 12 → Fin 12} (hf : Function.Involutive f) : (hf.toPerm f)⁻¹ = hf.toPerm f :=
  Equiv.ext fun n => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hf n).symm

section DCase

theorem ae6_D_lift (h : AE6FFin) {σ : Equiv.Perm (Fin 12)}
    (hσ : σ ∈ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm)) :
    ∃ φ : ↥(ae6GoodSub h), ae6Hat h φ = σ ∧ ae6Nice (φ : MulAut ↥ae6ModelP) := by
  have gen : ∀ σ ∈ Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm,
      σ⁻¹ = σ ∧ ∃ φ : ↥(ae6GoodSub h), ae6Hat h φ = σ ∧ ae6Nice (φ : MulAut ↥ae6ModelP) := by
    rintro _ (⟨x, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨ae6_toPerm_inv _, ae6LetterP h x, ae6Hat_letterP h x, ae6Nice_of_mem (ae6LetterP_mem h x)⟩
    · exact ⟨ae6_toPerm_inv _, ae6GammaP h c, ae6Hat_gammaP h c, ae6Nice_gammaP h c⟩
  induction hσ using Subgroup.closure_induction'' with
  | mem σ hσ => exact (gen σ hσ).2
  | inv_mem σ hσ => rw [(gen σ hσ).1]; exact (gen σ hσ).2
  | one => exact ⟨1, map_one _, ae6Nice_one⟩
  | mul σ τ _ _ hσ hτ =>
    obtain ⟨φ, hφ, hφn⟩ := hσ
    obtain ⟨ψ, hψ, hψn⟩ := hτ
    exact ⟨φ * ψ, by rw [map_mul, hφ, hψ], ae6Nice_mul hφn hψn⟩

end DCase

theorem ae6PM_sq_fix {h : AE6FFin} {x : MulAut ↥ae6ModelP} {n : Fin 12} (hs : ae6PM h (x (ae6CycP h n)) n) :
    x (x (ae6CycP h n)) = ae6CycP h n := by
  rcases hs with hs | hs
  · rw [hs, hs]
  · rw [hs, map_inv, hs, inv_inv]

theorem ae6_fix_twin (h : AE6FFin) (y : ↥(ae6GoodSub h)) (h3 : (y : MulAut ↥ae6ModelP) ^ 3 = 1) {i : Fin 4}
    (hi : ∀ n, ae6Blk n = i → ae6Hat h y n = n) {p : ↥ae6ModelP} (hp : (p : AE6Om) ∈ ae6Twin i) :
    (y : MulAut ↥ae6ModelP) p = p := by
  have hfix : ∀ n, ae6Blk n = i → (y : MulAut ↥ae6ModelP) (ae6CycP h n) = ae6CycP h n := by
    intro n hn
    have hs := ae6Hat_spec h y n
    rw [hi n hn] at hs
    have e2 := ae6PM_sq_fix hs
    calc (y : MulAut ↥ae6ModelP) (ae6CycP h n)
        = (y : MulAut ↥ae6ModelP) ((y : MulAut ↥ae6ModelP) ((y : MulAut ↥ae6ModelP) (ae6CycP h n))) := by rw [e2]
      _ = ((y : MulAut ↥ae6ModelP) ^ 3) (ae6CycP h n) := by
          rw [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply]
      _ = ae6CycP h n := by rw [h3, MulAut.one_apply]
  rcases h.mem_twin_P hp with rfl | rfl | ⟨n, hn, hpn⟩
  · exact map_one _
  · exact ae6Good_z h y.2
  · rcases hpn with rfl | rfl
    · exact hfix n hn
    · rw [map_inv, hfix n hn]

theorem ae6_weight_one (h : AE6FFin) (y : ↥(ae6GoodSub h)) {τ : Equiv.Perm (Fin 12)} (hy : ae6Hat h y = τ)
    (h3 : (y : MulAut ↥ae6ModelP) ^ 3 = 1) (hτb : ∀ n, ae6Blk (τ n) = ae6Blk n)
    (hτc : (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1) :
    (∀ J ∈ ae6ModelTwins, ∀ p : ↥ae6ModelP, (p : AE6Om) ∈ J ↔ ((y : MulAut ↥ae6ModelP) p : AE6Om) ∈ J) ∧
      Set.ncard {J | J ∈ ae6ModelTwins ∧ ∃ p : ↥ae6ModelP, (p : AE6Om) ∈ J ∧ (y : MulAut ↥ae6ModelP) p ≠ p} = 1 := by
  have hb1 : ∀ n, ae6Blk (ae6Hat h y n) = ae6Blk n := by rw [hy]; exact hτb
  have hb2 : ∀ n, ae6Blk (ae6Hat h (y ^ 2) n) = ae6Blk n := by
    intro n
    rw [map_pow, pow_two, Equiv.Perm.mul_apply, hb1, hb1]
  constructor
  · intro J hJ p
    rw [h.twins_eq] at hJ
    obtain ⟨i, rfl⟩ := hJ
    refine ⟨ae6Good_twin h y hb1, fun hp => ?_⟩
    have hm := ae6Good_twin h (y ^ 2) hb2 hp
    have e : ((y ^ 2 : ↥(ae6GoodSub h)) : MulAut ↥ae6ModelP) ((y : MulAut ↥ae6ModelP) p) = p := by
      rw [SubgroupClass.coe_pow, ← MulAut.mul_apply, ← pow_succ, h3, MulAut.one_apply]
    rwa [e] at hm
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hτc
    have hmem : ∀ i, (∃ n, ae6Blk n = i ∧ τ n ≠ n) ↔ i = b := fun i => by
      have := Finset.ext_iff.mp hb i
      simpa using this
    have hset : {J | J ∈ ae6ModelTwins ∧ ∃ p : ↥ae6ModelP, (p : AE6Om) ∈ J ∧ (y : MulAut ↥ae6ModelP) p ≠ p} =
        {ae6Twin b} := by
      ext J
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hJ, p, hp, hne⟩
        rw [h.twins_eq] at hJ
        obtain ⟨i, rfl⟩ := hJ
        congr 1
        by_contra hib
        apply hne
        refine ae6_fix_twin h y h3 (fun n hn => ?_) hp
        rw [hy]
        by_contra hτn
        exact hib ((hmem i).1 ⟨n, hn, hτn⟩)
      · rintro rfl
        obtain ⟨n, hn, hτn⟩ := (hmem b).2 rfl
        refine ⟨by rw [h.twins_eq]; exact ⟨b, rfl⟩, ae6CycP h n, ?_, fun e => hτn ?_⟩
        · rw [← hn]
          exact ae6Cyc_mem_twin h.hinv n
        · have hs := ae6Hat_spec h y n
          rw [e, hy] at hs
          exact (ae6PM_unique (ae6PM_self h n) hs).symm
    rw [hset, Set.ncard_singleton]

section Main

theorem ae6ModelF_of_fin (h : AE6FFin) : AE6ModelF := by
  intro X hCX hTw h3 x hx
  have hXG : ∀ y ∈ X, y ∈ ae6GoodSub h := fun y hy => ae6Good_of_twin h (hTw y hy)
  set xg : ↥(ae6GoodSub h) := ⟨x, hXG x hx⟩ with hxg
  by_cases hD : ae6Hat h xg ∈ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm)
  · obtain ⟨φ, hφ, hn⟩ := ae6_D_lift h hD
    have hk : ae6Hat h (φ⁻¹ * xg) = 1 := by rw [map_mul, map_inv, hφ, inv_mul_cancel]
    obtain ⟨q, hq, hkq⟩ := ae6Hat_ker h _ hk
    have hk' : ((φ⁻¹ * xg : ↥(ae6GoodSub h)) : MulAut ↥ae6ModelP) = ae6ConjP h q (h.P_le_C hq) :=
      h.aut_ext fun n => Subtype.ext (by rw [coe_ae6ConjP]; exact hkq n)
    have hx' : x = (φ : MulAut ↥ae6ModelP) * ae6ConjP h q (h.P_le_C hq) := by
      rw [← hk', ← Subgroup.coe_mul, mul_inv_cancel_left]
    obtain ⟨-, β, hβ, hβe⟩ := ae6Nice_mul hn (ae6Nice_of_mem (ae6ConjP_mem h (h.P_le_C hq)))
    exact ⟨β, hβ, by rw [hx']; exact hβe⟩
  · exfalso
    obtain ⟨τ, hτ, hτ3, hτb, hτc⟩ := h.hF5 _ (ae6Hat_blk h xg) hD
    have hsub : Subgroup.closure (insert (ae6Hat h xg) (Set.range ae6LetterHatPerm)) ≤
        (X.comap (ae6GoodSub h).subtype).map (ae6Hat h) := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | ⟨y, rfl⟩)
      · exact ⟨xg, hx, rfl⟩
      · exact ⟨ae6LetterP h y, hCX (ae6LetterP_mem h y), ae6Hat_letterP h y⟩
    obtain ⟨y, hyX, hyτ⟩ := hsub hτ
    have hyX' : (y : MulAut ↥ae6ModelP) ∈ X := hyX
    have hτ3' : τ ^ 3 = 1 := by rw [← hτ3]; exact pow_orderOf_eq_one τ
    have hk : ae6Hat h (y ^ 3) = 1 := by rw [map_pow, hyτ, hτ3']
    have h6 := ae6Hat_ker_sq h _ hk
    rw [SubgroupClass.coe_pow, ← pow_add] at h6
    have hy'τ : ae6Hat h (y ^ 4) = τ := by rw [map_pow, hyτ, pow_succ, hτ3', one_mul]
    have hy'3 : ((y ^ 4 : ↥(ae6GoodSub h)) : MulAut ↥ae6ModelP) ^ 3 = 1 := by
      rw [SubgroupClass.coe_pow, ← pow_mul, show 4 * 3 = (3 + 3) * 2 from rfl, pow_mul, h6, one_pow]
    have hy'1 : ((y ^ 4 : ↥(ae6GoodSub h)) : MulAut ↥ae6ModelP) ≠ 1 := fun e => by
      have e' : y ^ 4 = 1 := Subtype.ext e
      rw [e', map_one] at hy'τ
      rw [← hy'τ, orderOf_one] at hτ3
      norm_num at hτ3
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨htw, hnc⟩ := ae6_weight_one h (y ^ 4) hy'τ hy'3 hτb hτc
    exact h3 _ (by rw [SubgroupClass.coe_pow]; exact pow_mem hyX' 4) (orderOf_eq_prime hy'3 hy'1) htw hnc

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
