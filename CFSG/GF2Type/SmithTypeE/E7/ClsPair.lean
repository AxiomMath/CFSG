module

public import CFSG.GF2Type.SmithTypeE.E7.ClsBlocks
public import CFSG.GF2Type.SmithTypeE.E7.ClsLemmaA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

theorem sA_mul (A B : GL6) : sA A * sA B = sA (A * B) := by
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, sA_apply, Units.val_mul, mul_inv_rev, Matrix.transpose_mul,
    Matrix.mulVec_mulVec]

theorem sA_one : sA 1 = 1 := by
  refine LinearEquiv.ext fun v => ?_
  simp only [sA_apply, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec]
  rfl

theorem kN_mul_sA (B : GL6) (N : M6) :
    kN N * sA B = sA B * kN (((B⁻¹ : GL6) : M6) * N * ((B⁻¹ : GL6) : M6)ᵀ) := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, y⟩ := v
  simp only [LinearEquiv.mul_apply, kN_apply, sA_apply]
  refine Prod.ext rfl ?_
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Units.mul_inv,
    Matrix.one_mul]

theorem sk_mul (A B : GL6) (N N' : M6) :
    (sA A * kN N) * (sA B * kN N') =
      sA (A * B) * kN (((B⁻¹ : GL6) : M6) * N * ((B⁻¹ : GL6) : M6)ᵀ + N') := by
  calc (sA A * kN N) * (sA B * kN N') = sA A * (kN N * sA B) * kN N' := by
        simp only [mul_assoc]
    _ = sA A * (sA B * kN (((B⁻¹ : GL6) : M6) * N * ((B⁻¹ : GL6) : M6)ᵀ)) * kN N' := by
        rw [kN_mul_sA]
    _ = (sA A * sA B) * (kN (((B⁻¹ : GL6) : M6) * N * ((B⁻¹ : GL6) : M6)ᵀ) * kN N') := by
        simp only [mul_assoc]
    _ = _ := by rw [sA_mul, kN_add]

theorem sk_inj {A A' : GL6} {N N' : M6} (h : sA A * kN N = sA A' * kN N') : A = A' ∧ N = N' := by
  have hA : A = A' := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h1 := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => (f (0, Pi.single j 1)).2 i) h
    simpa [LinearEquiv.mul_apply, kN_apply, sA_apply, Matrix.mulVec_single_one] using h1
  subst hA
  refine ⟨rfl, ?_⟩
  have h2 : kN N = kN N' := mul_left_cancel h
  refine Matrix.ext fun i j => ?_
  have h1 := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => (f (Pi.single j 1, 0)).2 i) h2
  simpa [kN_apply, Matrix.mulVec_single_one] using h1

theorem isAlt_add {N N' : M6} (h : IsAlt N) (h' : IsAlt N') : IsAlt (N + N') :=
  ⟨by rw [Matrix.transpose_add, h.1, h'.1], fun i => by
    rw [Matrix.add_apply, h.2, h'.2, add_zero]⟩

theorem isAlt_zero : IsAlt (0 : M6) := ⟨Matrix.transpose_zero, fun _ => rfl⟩

theorem neg_eq_self_M6 (N : M6) : -N = N := by
  ext i j
  simp only [Matrix.neg_apply]
  generalize N i j = a
  revert a
  decide

theorem add_self_M6 (N : M6) : N + N = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize N i j = a
  revert a
  decide

theorem isAlt_neg {N : M6} (h : IsAlt N) : IsAlt (-N) := by
  rw [neg_eq_self_M6]
  exact h

theorem isAlt_conj {N : M6} (h : IsAlt N) (A : M6) : IsAlt (A * N * Aᵀ) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, h.1,
      Matrix.mul_assoc]
  · have h1 := dotProduct_mulVec_self_of_isAlt h (fun k => A i k)
    have e : (A * N * Aᵀ) i i = (fun k => A i k) ⬝ᵥ (N *ᵥ (fun k => A i k)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    exact h1

@[expose] def Tmat (v : Fin 6 → ZMod 2) : M6 := 1 + Matrix.of fun i j => if j = 5 then v i else 0

theorem InT_iff {A : M6} : InT A ↔ ∃ v : Fin 6 → ZMod 2, v 5 = 0 ∧ A = Tmat v := Iff.rfl

theorem Tmat_apply (v : Fin 6 → ZMod 2) (i j : Fin 6) :
    Tmat v i j = (if i = j then 1 else 0) + (if j = 5 then v i else 0) := by
  simp only [Tmat, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]

theorem Tmat_zero : Tmat 0 = 1 := by
  ext i j
  simp [Tmat_apply, Matrix.one_apply]

theorem Tmat_mul {v w : Fin 6 → ZMod 2} (hv : v 5 = 0) (hw : w 5 = 0) :
    Tmat v * Tmat w = Tmat (v + w) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_six, Tmat_apply, Pi.add_apply]
  fin_cases i <;> fin_cases j <;> simp [hv, hw] <;> ring

theorem Tmat_mul_self {v : Fin 6 → ZMod 2} (hv : v 5 = 0) : Tmat v * Tmat v = 1 := by
  have h2 : v + v = 0 := funext fun i => by
    simp only [Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_self_eq_zero (v i)
  rw [Tmat_mul hv hv, h2, Tmat_zero]

theorem Tmat_conj {N : M6} (hN : IsAlt N) {v : Fin 6 → ZMod 2} (hv : v 5 = 0) :
    Tmat v * N * (Tmat v)ᵀ = N + Matrix.of fun i j => v i * N j 5 + N i 5 * v j := by
  have hsym : ∀ i j, N i j = N j i := fun i j => congrFun (congrFun hN.1 j) i
  have h55 : N 5 5 = 0 := hN.2 5
  have e0 : N 5 0 = N 0 5 := hsym 5 0
  have e1 : N 5 1 = N 1 5 := hsym 5 1
  have e2 : N 5 2 = N 2 5 := hsym 5 2
  have e3 : N 5 3 = N 3 5 := hsym 5 3
  have e4 : N 5 4 = N 4 5 := hsym 5 4
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_six, Tmat_apply,
    Matrix.add_apply, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, e3, e4, h55] <;> ring

theorem wedge_cases {v h : Fin 6 → ZMod 2} (H : ∀ i j, v i * h j + h i * v j = 0) :
    v = 0 ∨ h = 0 ∨ h = v := by
  have hone : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hsw : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  by_cases hv : v = 0
  · exact Or.inl hv
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv (funext fun k => hne k)
  have hvi : v i = 1 := hone _ hi
  have key : ∀ j, h j = h i * v j := fun j => by
    have h1 := H i j
    rw [hvi, one_mul] at h1
    exact hsw _ _ h1
  by_cases hhi : h i = 0
  · exact Or.inr (Or.inl (funext fun j => by simp [key j, hhi]))
  · have hhi1 : h i = 1 := hone _ hhi
    exact Or.inr (Or.inr (funext fun j => by simp [key j, hhi1]))

theorem t2_comm {A : M6} (hc : ∀ B : M6, IsUT B → A * B = B * A) {k l : Fin 6} (hkl : k < l)
    (r c : Fin 6) : A r k * (if c = l then 1 else 0) = if r = k then A l c else 0 := by
  have hB : IsUT (1 + Matrix.of fun i j : Fin 6 => if i = k ∧ j = l then (1 : ZMod 2) else 0) := by
    intro i j hji
    have hne : ¬ (i = k ∧ j = l) := by
      rintro ⟨h1, h2⟩
      rw [h1, h2] at hji
      exact lt_irrefl _ (lt_of_lt_of_le hkl hji)
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, if_neg hne, add_zero]
  have e0 := hc _ hB
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at e0
  have e1 := add_left_cancel e0
  have e := congrFun (congrFun e1 r) c
  simp only [Matrix.mul_apply, Matrix.of_apply] at e
  have s1 : ∑ m : Fin 6, A r m * (if m = k ∧ c = l then (1 : ZMod 2) else 0)
      = A r k * (if c = l then 1 else 0) := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm
      simp [hm]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have s2 : ∑ m : Fin 6, (if r = k ∧ m = l then (1 : ZMod 2) else 0) * A m c
      = if r = k then A l c else 0 := by
    rw [Finset.sum_eq_single l]
    · by_cases hr : r = k <;> simp [hr]
    · intro m _ hm
      simp [hm]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [s1, s2] at e
  exact e

theorem t2_col {A : M6} (hc : ∀ B : M6, IsUT B → A * B = B * A)
    (hdiag : ∀ l : Fin 6, A l l = 1) {k l : Fin 6} (hkl : k < l) (r : Fin 6) :
    A r k = if r = k then 1 else 0 := by
  have e := t2_comm hc hkl r l
  rw [if_pos (rfl : l = l), mul_one, hdiag l] at e
  exact e

theorem t2_row {A : M6} (hc : ∀ B : M6, IsUT B → A * B = B * A) {k l c : Fin 6}
    (hkl : k < l) (hcl : c ≠ l) : A l c = 0 := by
  have e := t2_comm hc hkl k c
  rw [if_neg hcl, mul_zero, if_pos (rfl : k = k)] at e
  exact e.symm

theorem center_UT {A : M6} (hA : IsUT A) (hc : ∀ B : M6, IsUT B → A * B = B * A) :
    A = 1 ∨ A = tau0M := by
  have hdiag : ∀ l : Fin 6, A l l = 1 := fun l => by
    rw [hA l l le_rfl, if_pos rfl]
  have c0 : ∀ r : Fin 6, A r 0 = if r = 0 then 1 else 0 :=
    t2_col (k := 0) (l := 1) hc hdiag (by decide)
  have c1 : ∀ r : Fin 6, A r 1 = if r = 1 then 1 else 0 :=
    t2_col (k := 1) (l := 2) hc hdiag (by decide)
  have c2 : ∀ r : Fin 6, A r 2 = if r = 2 then 1 else 0 :=
    t2_col (k := 2) (l := 3) hc hdiag (by decide)
  have c3 : ∀ r : Fin 6, A r 3 = if r = 3 then 1 else 0 :=
    t2_col (k := 3) (l := 4) hc hdiag (by decide)
  have c4 : ∀ r : Fin 6, A r 4 = if r = 4 then 1 else 0 :=
    t2_col (k := 4) (l := 5) hc hdiag (by decide)
  have r1 : A 1 5 = 0 := t2_row (k := 0) (l := 1) (c := 5) hc (by decide) (by decide)
  have r2 : A 2 5 = 0 := t2_row (k := 1) (l := 2) (c := 5) hc (by decide) (by decide)
  have r3 : A 3 5 = 0 := t2_row (k := 2) (l := 3) (c := 5) hc (by decide) (by decide)
  have r4 : A 4 5 = 0 := t2_row (k := 3) (l := 4) (c := 5) hc (by decide) (by decide)
  have hcol : ∀ c : Fin 6, c ≠ 5 → ∀ r : Fin 6, A r c = if r = c then 1 else 0 := by
    intro c hc5 r
    fin_cases c
    · exact c0 r
    · exact c1 r
    · exact c2 r
    · exact c3 r
    · exact c4 r
    · exact absurd rfl hc5
  have hfin : ∀ r : Fin 6, r ≠ 0 → A r 5 = if r = 5 then 1 else 0 := by
    intro r hr0
    fin_cases r
    · exact absurd rfl hr0
    · exact r1.trans (by decide)
    · exact r2.trans (by decide)
    · exact r3.trans (by decide)
    · exact r4.trans (by decide)
    · exact (hdiag 5).trans (by decide)
  have hall : ∀ r c : Fin 6, ¬ (r = 0 ∧ c = 5) → A r c = (1 : M6) r c := by
    intro r c hrc
    rw [Matrix.one_apply]
    by_cases hc5 : c = 5
    · subst hc5
      exact hfin r (fun h => hrc ⟨h, rfl⟩)
    · exact hcol c hc5 r
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (A 0 5) with h | h
  · left
    ext r c
    by_cases hrc : r = 0 ∧ c = 5
    · obtain ⟨rfl, rfl⟩ := hrc
      rw [h, Matrix.one_apply_ne (show (0 : Fin 6) ≠ 5 by decide)]
    · exact hall r c hrc
  · right
    ext r c
    by_cases hrc : r = 0 ∧ c = 5
    · obtain ⟨rfl, rfl⟩ := hrc
      rw [h]
      simp [tau0M, Matrix.one_apply]
    · rw [hall r c hrc]
      simp only [tau0M, Matrix.add_apply, Matrix.of_apply, if_neg hrc, add_zero]

theorem exists_GL_of_isUT {B : M6} (hB : IsUT B) : ∃ g : GL6, g ∈ UTsub ∧ (g : M6) = B := by
  refine ⟨UTunit (fun p => B p.1.1 p.1.2), mem_UTsub.mpr ?_, ?_⟩
  · rw [UTunit_val]
    exact isUT_UTofEntries _
  · rw [UTunit_val]
    refine isUT_ext_of_upper (isUT_UTofEntries _) hB fun i j hij => ?_
    exact UTofEntries_up (fun p : UTpos => B p.1.1 p.1.2) ⟨(i, j), hij⟩

theorem card_range_mul_card_ker {G G' : Type*} [Group G] [Group G'] (f : G →* G') :
    Nat.card G = Nat.card f.range * Nat.card f.ker := by
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1, mul_comm]

theorem map_conj_mul_gen {G : Type*} [Group G] (A : Subgroup G) (a b : G) :
    A.map (MulAut.conj (a * b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  show (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹
  group

section Stab

@[expose] noncomputable def alphaS : Stab0 →* GL6 := MonoidHom.toHomUnits (aM Stab0 le_rfl)

theorem alphaS_coe (x : Stab0) : ((alphaS x : GL6) : M6) = Ablk (sig x.1) := rfl

@[expose] noncomputable def nS (x : Stab0) : M6 :=
  (((alphaS x)⁻¹ : GL6) : M6) * Sblk (sig x.1)

theorem nS_isAlt (x : Stab0) : IsAlt (nS x) :=
  (eq_sA_kN (iso_sig x.1) (stab_F x.2) (alphaS_coe x).symm).1

theorem sig_eq_sA_kN (x : Stab0) : sig x.1 = sA (alphaS x) * kN (nS x) :=
  (eq_sA_kN (iso_sig x.1) (stab_F x.2) (alphaS_coe x).symm).2

theorem nS_mul (x y : Stab0) :
    nS (x * y) = (((alphaS y)⁻¹ : GL6) : M6) * nS x * (((alphaS y)⁻¹ : GL6) : M6)ᵀ + nS y := by
  have h : sA (alphaS (x * y)) * kN (nS (x * y)) =
      sA (alphaS x * alphaS y) *
        kN ((((alphaS y)⁻¹ : GL6) : M6) * nS x * (((alphaS y)⁻¹ : GL6) : M6)ᵀ + nS y) := by
    rw [← sig_eq_sA_kN (x * y), ← sk_mul, ← sig_eq_sA_kN x, ← sig_eq_sA_kN y]
    exact sig_mul x.1 y.1
  exact (sk_inj h).2

theorem mem_K0_iff_alphaS (x : Stab0) : x.1 ∈ K0 ↔ alphaS x = 1 := by
  constructor
  · intro hx
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h1 : sig x.1 (0, Pi.single j 1) = (0, Pi.single j 1) :=
      mem_K0.mp hx (0, Pi.single j 1) (mem_F_iff.mpr rfl)
    rw [alphaS_coe, Ablk_apply, h1, Units.val_one]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · intro hx y hy
    have hA : Ablk (sig x.1) = 1 := by
      rw [← alphaS_coe, hx]
      rfl
    have hy0 : y = (0, y.2) := Prod.ext (mem_F_iff.mp hy) rfl
    show sig x.1 y = y
    rw [hy0, apply_F (sig x.1) (stab_F x.2), hA, Matrix.one_mulVec]

theorem exists_K0_sig_kN {M : M6} (hM : IsAlt M) : ∃ g ∈ K0, sig g = kN M := by
  obtain ⟨g, hg, hent⟩ := exists_K0_ent (fun p => M p.1.1 p.1.2)
  refine ⟨g, hg, fix_ext (iso_sig g) (fixesF_of_mem_K0 hg) (kN_iso hM) ?_ ?_⟩
  · intro b
    rw [kN_apply]
    simp
  · intro i j hij
    rw [ent_kN]
    exact hent ⟨(i, j), hij⟩

theorem nS_one : nS (1 : Stab0) = 0 := by
  have h1 := sig_eq_sA_kN (1 : Stab0)
  have h2 : sig ((1 : Stab0) : TD6) = 1 := sig_one
  rw [h2, map_one, sA_one, one_mul] at h1
  have h3 : sA 1 * kN (nS 1) = sA 1 * kN 0 := by rw [sA_one, one_mul, one_mul, ← h1, kN_zero]
  exact (sk_inj h3).2

theorem sig_eq_kN (x : Stab0) (h : alphaS x = 1) : sig x.1 = kN (nS x) := by
  rw [sig_eq_sA_kN x, h, sA_one, one_mul]

theorem inv_eq_Tmat {A : GL6} {v : Fin 6 → ZMod 2} (hv : v 5 = 0) (hA : (A : M6) = Tmat v) :
    ((A⁻¹ : GL6) : M6) = Tmat v := by
  have h : A * A = 1 := Units.ext (by rw [Units.val_mul, hA, Tmat_mul_self hv]; rfl)
  rw [inv_eq_of_mul_eq_one_right h]
  exact hA

theorem exists_tau0_mem {Xs Ps : Subgroup ↥Stab0} (hXP : Xs ≤ Ps)
    (hPN : ∀ g ∈ Ps, ∀ x ∈ Xs, g * x * g⁻¹ ∈ Xs)
    (hUT : ∀ g ∈ Ps, IsUT ((alphaS g : GL6) : M6))
    (hUTall : ∀ A : GL6, A ∈ UTsub → ∃ g ∈ Ps, alphaS g = A)
    (hne : ∃ x ∈ Xs, alphaS x ≠ 1) : ∃ x ∈ Xs, ((alphaS x : GL6) : M6) = tau0M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥UTsub := IsPGroup.of_card card_UTsub
  haveI : Group.IsNilpotent ↥UTsub := hp.isNilpotent
  let H : Subgroup ↥UTsub := (Xs.map alphaS).subgroupOf UTsub
  haveI : H.Normal := by
    refine ⟨fun a ha u => ?_⟩
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp ha)
    obtain ⟨g, hg, hgu⟩ := hUTall u.1 u.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hPN g hg x hx, ?_⟩)
    rw [map_mul, map_mul, map_inv, hgu, hxa]
    rfl
  have hH : H ≠ ⊥ := by
    obtain ⟨x, hx, hx1⟩ := hne
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro h
    have hmem : alphaS x ∈ UTsub := mem_UTsub.mpr (hUT x (hXP hx))
    have := h ⟨alphaS x, hmem⟩ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
    exact hx1 (congrArg Subtype.val this)
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hH)
  have hzH : (z : ↥UTsub) ∈ H := z.2.1
  have hzc : (z : ↥UTsub) ∈ Subgroup.center ↥UTsub := z.2.2
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hzH)
  have hcomm : ∀ B : M6, IsUT B → ((z : ↥UTsub).1 : M6) * B = B * ((z : ↥UTsub).1 : M6) := by
    intro B hB
    obtain ⟨u, hu, rfl⟩ := exists_GL_of_isUT hB
    have h1 := Subgroup.mem_center_iff.mp hzc ⟨u, hu⟩
    have h2 := congrArg (fun w : ↥UTsub => ((w.1 : GL6) : M6)) h1
    exact h2.symm
  rcases center_UT (mem_UTsub.mp (z : ↥UTsub).2) hcomm with h1 | h1
  · exfalso
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact Units.ext h1
  · exact ⟨x, hx, by rw [hxz]; exact h1⟩

end Stab

end CFSG.GF2Type.SmithTypeE.E7
