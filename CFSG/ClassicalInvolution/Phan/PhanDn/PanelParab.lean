module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParabLe
public import CFSG.ClassicalInvolution.Phan.PhanDn.KLinearIsometry
import all CFSG.ClassicalInvolution.Phan.PhanDn.PanelStab

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.Monster.B.Geometry
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ}

variable {M : CoxeterMatrix (Fin (m + 1))}
  {S : PhanFamilyE K 2 f M ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}

private theorem suEndN_diagSU {n : ℕ} (d : Fin n → normOne (unitaryInvolution K 2 f))
    (hd : d ∈ detKer (unitaryInvolution K 2 f) n) :
    suEndN (F := F) (unitaryInvolution K 2 f) n
        (diagSU (unitaryInvolution K 2 f) d hd) =
      diagHom F (unitaryInvolution K 2 f) n d := by
  refine LinearEquiv.ext fun v => ?_
  funext i
  rw [suEndN_apply, diagHom_apply]
  exact congrFun (diagSU_smul d hd v) i

theorem map_torus_suEndNΩ_le (hn : 4 ≤ m + 1) :
    (torus (unitaryInvolution K 2 f) (m + 1)).map (suEndNΩ E hn) ≤
      (diagTorusV F (unitaryInvolution K 2 f) (m + 1)).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) := by
  rintro x ⟨s, hs, rfl⟩
  obtain ⟨d, rfl⟩ := hs
  rw [Subgroup.mem_subgroupOf, diagSUHom_apply]
  have hcoe : ((suEndNΩ E hn (diagSU (unitaryInvolution K 2 f) d.1 d.2) :
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      suEndN (F := F) (unitaryInvolution K 2 f) (m + 1)
        (diagSU (unitaryInvolution K 2 f) d.1 d.2) := rfl
  rw [hcoe, suEndN_diagSU]
  exact ⟨d.1, rfl⟩

theorem suEndNΩ_comp_blockEmb2 (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (k : Fin m) :
    (suEndNΩ E (by omega)).comp (blockEmb2 K 2 f m k) = S.ι k.castSucc := by
  refine MonoidHom.ext fun A => Subtype.ext ?_
  show suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) (blockEmb2 K 2 f m k A) =
    (((S.ι k.castSucc A :
      ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
      (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))
  rw [hS.ι_castSucc k A]
  rfl

private noncomputable def firstHalf (n : ℕ) : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v i := v (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Finite K] [CharP K 2] in
private theorem firstHalf_apply (n : ℕ) (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    firstHalf (K := K) n v i = v (Sum.inl i) := rfl

omit [Finite K] [CharP K 2] in
private theorem firstHalf_stdE {n : ℕ} (i : Fin n) :
    firstHalf (K := K) n (stdE (K := K) (n := n) i) = (Pi.single i 1 : Fin n → K) := by
  funext j
  rw [firstHalf_apply, stdE_inl, Pi.single_apply]

omit [Finite K] [CharP K 2] in
private theorem firstHalf_coordSpan {n : ℕ} (I : Set (Fin n)) :
    (coordSpan (K := K) n I ∅).map (firstHalf (K := K) n) =
      Submodule.span K ((fun i : Fin n => (Pi.single i 1 : Fin n → K)) '' I) := by
  rw [coordSpan, Submodule.map_span, Set.image_empty, Set.union_empty]
  congr 1
  ext v
  constructor
  · rintro ⟨u, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (firstHalf_stdE i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨stdE i, ⟨i, hi, rfl⟩, firstHalf_stdE i⟩

omit [Finite K] [CharP K 2] in
private noncomputable def stdSpan (n l : ℕ) : Submodule K (Fin n → K) :=
  Submodule.span K
    ((fun i : Fin n => (Pi.single i (1 : K) : Fin n → K)) '' {i : Fin n | (i : ℕ) < l})

omit [Finite K] [CharP K 2] in
private theorem stdSpan_le_ker {n l : ℕ} (i : Fin n) (hi : l ≤ (i : ℕ)) :
    stdSpan (K := K) n l ≤ LinearMap.ker (LinearMap.proj i : (Fin n → K) →ₗ[K] K) := by
  rw [stdSpan, Submodule.span_le]
  rintro _ ⟨u, hu, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
  refine Pi.single_eq_of_ne (M := fun _ : Fin n => K) (show i ≠ u from fun h => ?_) 1
  simp only [Set.mem_setOf_eq] at hu
  have hvu : (i : ℕ) = (u : ℕ) := congrArg Fin.val h
  omega

omit [Finite K] [CharP K 2] in
private theorem stdSpan_apply_eq_zero {n l : ℕ} {i : Fin n} (hi : l ≤ (i : ℕ))
    {x : Fin n → K} (hx : x ∈ stdSpan (K := K) n l) : x i = 0 := by
  have h := stdSpan_le_ker (K := K) (l := l) i hi hx
  rwa [LinearMap.mem_ker, LinearMap.proj_apply] at h

omit [Finite K] [CharP K 2] in
private theorem mem_stdSpan_of_support {n l : ℕ} {x : Fin n → K}
    (hx : ∀ i : Fin n, ¬ (i : ℕ) < l → x i = 0) : x ∈ stdSpan (K := K) n l := by
  have hdecomp : x = ∑ i : Fin n, x i • (Pi.single i 1 : Fin n → K) := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro b _ hb
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hdecomp, stdSpan]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < l
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [hx i hi, zero_smul]
    exact Submodule.zero_mem _

private noncomputable def suAct {n : ℕ} (s : SUid (unitaryInvolution K 2 f) n) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  Matrix.mulVecLin ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

private theorem suAct_apply {n : ℕ} (s : SUid (unitaryInvolution K 2 f) n) (v : Fin n → K) :
    suAct (K := K) s v = s • v := by
  rw [suAct, Matrix.mulVecLin_apply, CFSG.ClassicalGroups.Unitary.smul_def]

private theorem firstHalf_bcLin {n : ℕ} (s : SUid (unitaryInvolution K 2 f) n)
    (v : Fin n ⊕ Fin n → K) :
    firstHalf (K := K) n (bcLin E n (suEndN (F := F) (unitaryInvolution K 2 f) n s) v) =
      suAct (K := K) s (firstHalf (K := K) n v) := by
  funext i
  rw [firstHalf_apply, bcLin_suEndN, blockDiag_inl, suAct, Matrix.mulVecLin_apply]
  rfl

private theorem stdSpan_map_suAct_eq {n l : ℕ} (s : SUid (unitaryInvolution K 2 f) n)
    (h : (coordSpan (K := K) n {i : Fin n | (i : ℕ) < l} ∅).map
        (bcLin E n (suEndN (F := F) (unitaryInvolution K 2 f) n s)) =
      coordSpan (K := K) n {i : Fin n | (i : ℕ) < l} ∅) :
    (stdSpan (K := K) n l).map (suAct (K := K) s) = stdSpan (K := K) n l := by
  have h2 : (coordSpan (K := K) n {i : Fin n | (i : ℕ) < l} ∅).map
      (firstHalf (K := K) n) = stdSpan (K := K) n l :=
    firstHalf_coordSpan (K := K) {i : Fin n | (i : ℕ) < l}
  rw [← h2, ← Submodule.map_comp]
  rw [show (suAct (K := K) s).comp (firstHalf (K := K) n) =
      (firstHalf (K := K) n).comp
        (bcLin E n (suEndN (F := F) (unitaryInvolution K 2 f) n s)) from
    LinearMap.ext fun v => (firstHalf_bcLin E s v).symm]
  rw [Submodule.map_comp, h]

private def hermPerp {n : ℕ} (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ v ∈ W, herm (unitaryInvolution K 2 f) x v = 0}
  zero_mem' := by
    intro v _
    simp
  add_mem' := by
    intro x y hx hy v hv
    rw [herm_add_left, hx v hv, hy v hv, add_zero]
  smul_mem' := by
    intro c x hx v hv
    rw [herm_smul_left, hx v hv, mul_zero]

private theorem mem_hermPerp {n : ℕ} {W : Submodule K (Fin n → K)} {x : Fin n → K} :
    x ∈ hermPerp (K := K) (f := f) W ↔
      ∀ v ∈ W, herm (unitaryInvolution K 2 f) x v = 0 :=
  Iff.rfl

private theorem map_hermPerp_map_suAct {n : ℕ} (s : SUid (unitaryInvolution K 2 f) n)
    {W : Submodule K (Fin n → K)} (hW : W.map (suAct (K := K) s) = W) :
    (hermPerp (K := K) (f := f) W).map (suAct (K := K) s) =
      hermPerp (K := K) (f := f) W := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩ v hv
    have hv' : v ∈ W.map (suAct (K := K) s) := by rw [hW]; exact hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv'
    rw [suAct_apply, suAct_apply, herm_smul_smul]
    exact hy u hu
  · intro x hx
    refine Submodule.mem_map.mpr ⟨s⁻¹ • x, ?_, ?_⟩
    · intro v hv
      have hmem : suAct (K := K) s v ∈ W := by
        rw [← hW]
        exact Submodule.mem_map_of_mem (f := suAct (K := K) s) hv
      have hsv : s • v ∈ W := by rwa [suAct_apply] at hmem
      have h := hx (s • v) hsv
      have h1 : herm (unitaryInvolution K 2 f) (s⁻¹ • x) v =
          herm (unitaryInvolution K 2 f) x (s • v) := by
        rw [← herm_smul_smul (unitaryInvolution K 2 f) s (s⁻¹ • x) v, smul_inv_smul]
      rw [h1, h]
    · rw [suAct_apply, smul_inv_smul]

private theorem stdSpan_succ_inf_hermPerp {n : ℕ} (j : Fin n) :
    stdSpan (K := K) n ((j : ℕ) + 1) ⊓
        hermPerp (K := K) (f := f) (stdSpan (K := K) n (j : ℕ)) =
      K ∙ (Pi.single j (1 : K) : Fin n → K) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    have hlt : ∀ i : Fin n, (i : ℕ) < (j : ℕ) → x i = 0 := by
      intro i hi
      have h := (mem_hermPerp (K := K) (f := f)).mp hx2 (Pi.single i (1 : K))
        (Submodule.subset_span ⟨i, hi, rfl⟩)
      rw [herm_single_right] at h
      have h' : (unitaryInvolution K 2 f) (x i) = 0 := by simpa using h
      exact (map_eq_zero_iff _ (unitaryInvolution K 2 f).injective).mp h'
    have hgt : ∀ i : Fin n, (j : ℕ) < (i : ℕ) → x i = 0 :=
      fun i hi => stdSpan_apply_eq_zero (K := K) (l := (j : ℕ) + 1) (by omega) hx1
    refine Submodule.mem_span_singleton.mpr ⟨x j, ?_⟩
    funext i
    by_cases hij : i = j
    · subst hij
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have h0 : x i = 0 := by
        rcases lt_or_gt_of_ne (fun h : (i : ℕ) = (j : ℕ) => hij (Fin.ext h)) with h | h
        · exact hlt i h
        · exact hgt i h
      rw [h0, Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero]
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · refine mem_stdSpan_of_support (K := K) (l := (j : ℕ) + 1) fun i hi => ?_
      have hij : i ≠ j := by
        rintro rfl
        exact hi (by omega)
      rw [Pi.smul_apply, Pi.single_eq_of_ne hij, smul_zero]
    · intro v hv
      rw [herm_smul_left]
      have hvj : v j = 0 := stdSpan_apply_eq_zero (K := K) (l := (j : ℕ)) le_rfl hv
      rw [herm_single_left, hvj, mul_zero, mul_zero]

private theorem flipSpan_map_eq_of_mem_panelStab (hm : 4 ≤ m + 1)
    (s : SUid (unitaryInvolution K 2 f) (m + 1)) {k : Fin m}
    (hsu : suEndNΩ E hm s ∈ panelStab E k.castSucc)
    {l : ℕ} (hl : l ≤ m + 1) (hlk : l ≠ (k : ℕ) + 1) :
    (coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < l} ∅).map
        (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s)) =
      coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < l} ∅ := by
  have hg : ∀ j : Fin (m + 1), j ≠ k.castSucc →
      ((stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j).map
        (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s)) =
      (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt j := by
    intro j hj
    exact (mem_panelStab (E := E)).mp hsu j hj
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · subst hl0
    simp [coordSpan]
  rcases eq_or_ne l (m + 1) with hlm1 | hlm1
  · rw [hlm1]
    have hI : {i : Fin (m + 1) | (i : ℕ) < m + 1} = Set.univ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact i.isLt
    rw [hI, ← stdDChamber_elt_last_eq_coordSpan]
    refine hg (Fin.last m) fun h => ?_
    have hv := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  rcases eq_or_ne l m with hlm | hlm
  · rw [hlm]
    have hkm : (k : ℕ) ≠ m - 1 := by omega
    have ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last] at hv
      have h2 : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) = m - 1 := rfl
      omega
    have ha' : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) + 1 = m := by
      have h2 : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) = m - 1 := rfl
      omega
    have hane : (⟨m - 1, by omega⟩ : Fin (m + 1)) ≠ k.castSucc := by
      intro h
      apply hkm
      have h1 := congrArg Fin.val h
      simp only [Fin.val_castSucc] at h1
      have h2 : ((⟨m - 1, by omega⟩ : Fin (m + 1)) : ℕ) = m - 1 := rfl
      omega
    have hlastne' : Fin.last m ≠ k.castSucc := by
      intro h
      have h1 := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at h1
      omega
    have h1 := hg _ hane
    have h2 := hg (Fin.last m) hlastne'
    have hsub : coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < m} ∅ =
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) ⊓
          (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt ⟨m - 1, by omega⟩ := by
      have h2 : (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt (Fin.last m) ⊓
          (stdDChamber (unitaryInvolution K 2 f) (m + 1)).elt ⟨m - 1, by omega⟩ =
          coordSpan (K := K) (m + 1) {i : Fin (m + 1) | (i : ℕ) < m} ∅ := by
        rw [stdDChamber_elt_eq_alt ha ha', FlipFrame.elt_last_inf_alt E.isUnitary.invol,
          stdDChamber_sub_eq_span]
        simp only [coordSpan, Set.image_empty, Set.union_empty]
      exact h2.symm
    have hinj : Function.Injective
        (bcLin E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s)) := by
      intro a b hab
      rw [bcLin_eq_coe_bc] at hab
      exact (bc E (m + 1) (suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s)).injective hab
    conv_lhs => rw [hsub]
    rw [Submodule.map_inf _ hinj, h1, h2]
    exact hsub.symm
  · have hlm' : l ≤ m - 1 := by omega
    have hj : (⟨l - 1, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last] at hv
      have h2 : ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) = l - 1 := rfl
      omega
    have hj' : ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) + 1 ≠ m := by
      have h2 : ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) = l - 1 := rfl
      omega
    have hjne : (⟨l - 1, by omega⟩ : Fin (m + 1)) ≠ k.castSucc := by
      intro h
      apply hlk
      have h1 := congrArg Fin.val h
      simp only [Fin.val_castSucc] at h1
      have h2 : ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) = l - 1 := rfl
      omega
    have h := hg _ hjne
    rw [stdDChamber_elt_eq_sub_coordSpan hj hj'] at h
    have hset : {i : Fin (m + 1) | (i : ℕ) < l} =
        {i : Fin (m + 1) | (i : ℕ) < ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) + 1} := by
      ext i
      simp only [Set.mem_setOf_eq]
      have h2 : ((⟨l - 1, by omega⟩ : Fin (m + 1)) : ℕ) = l - 1 := rfl
      omega
    rw [hset]
    exact h

private theorem suAct_single_mem_span_singleton (hm : 4 ≤ m + 1)
    (s : SUid (unitaryInvolution K 2 f) (m + 1)) {k : Fin m}
    (hsu : suEndNΩ E hm s ∈ panelStab E k.castSucc)
    (j : Fin (m + 1)) (hj1 : j ≠ k.castSucc) (hj2 : j ≠ k.succ) :
    suAct (K := K) s (Pi.single j 1) ∈ K ∙ (Pi.single j 1 : Fin (m + 1) → K) := by
  have hV1 : (stdSpan (K := K) (m + 1) ((j : ℕ) + 1)).map (suAct (K := K) s) =
      stdSpan (K := K) (m + 1) ((j : ℕ) + 1) := by
    refine stdSpan_map_suAct_eq E s
      (flipSpan_map_eq_of_mem_panelStab E hm s hsu (l := (j : ℕ) + 1) (by omega) ?_)
    intro h
    apply hj1
    apply Fin.ext
    simp only [Fin.val_castSucc]
    omega
  have hV0 : (stdSpan (K := K) (m + 1) (j : ℕ)).map (suAct (K := K) s) =
      stdSpan (K := K) (m + 1) (j : ℕ) := by
    refine stdSpan_map_suAct_eq E s
      (flipSpan_map_eq_of_mem_panelStab E hm s hsu (l := (j : ℕ)) (by omega) ?_)
    intro h
    apply hj2
    apply Fin.ext
    simp only [Fin.val_succ]
    omega
  have hperp : (hermPerp (K := K) (f := f) (stdSpan (K := K) (m + 1) (j : ℕ))).map
      (suAct (K := K) s) = hermPerp (K := K) (f := f) (stdSpan (K := K) (m + 1) (j : ℕ)) :=
    map_hermPerp_map_suAct (f := f) s hV0
  have hmem1 : suAct (K := K) s (Pi.single j 1) ∈
      stdSpan (K := K) (m + 1) ((j : ℕ) + 1) := by
    have h1 : Pi.single j (1 : K) ∈ stdSpan (K := K) (m + 1) ((j : ℕ) + 1) := by
      refine mem_stdSpan_of_support (K := K) (l := (j : ℕ) + 1) fun i hi => ?_
      exact Pi.single_eq_of_ne (M := fun _ : Fin (m + 1) => K)
        (show i ≠ j from fun h => hi (by rw [h]; exact Nat.lt_succ_self _)) 1
    have h2 := Submodule.mem_map_of_mem (f := suAct (K := K) s) h1
    rwa [hV1] at h2
  have hmem2 : suAct (K := K) s (Pi.single j 1) ∈
      hermPerp (K := K) (f := f) (stdSpan (K := K) (m + 1) (j : ℕ)) := by
    have h1 : Pi.single j (1 : K) ∈
        hermPerp (K := K) (f := f) (stdSpan (K := K) (m + 1) (j : ℕ)) := by
      intro v hv
      rw [herm_single_left]
      have hvj : v j = 0 := stdSpan_apply_eq_zero (K := K) (l := (j : ℕ)) le_rfl hv
      rw [hvj, mul_zero]
    have h2 := Submodule.mem_map_of_mem (f := suAct (K := K) s) h1
    rwa [hperp] at h2
  rw [← stdSpan_succ_inf_hermPerp (K := K) (f := f) j]
  exact Submodule.mem_inf.mpr ⟨hmem1, hmem2⟩

theorem panelStab_castSucc_le_parab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (k : Fin m) :
    panelStab E k.castSucc ≤ S.parab {k.castSucc} := by
  intro g hg
  have hn : 4 ≤ m + 1 := by omega
  have hKlin : ∀ (a : K) x,
      (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (a • x) =
        a • (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) x :=
    isKLinear_of_mem_panelStab E k.castSucc (by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega) g hg
  have horth : (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) :=
    mem_orthogonalGroup_of_mem_orthDerived E (m + 1) g.2
  obtain ⟨t, s, hts⟩ := exists_diagHom_mul_suEndN_eq E (by omega : 1 ≤ m + 1) horth hKlin
  let tΩ : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
    ⟨diagHom F (unitaryInvolution K 2 f) (m + 1) t,
      diagTorusV_le_orthDerived E hn ⟨t, rfl⟩⟩
  have htorus : tΩ ∈ S.torus := by
    rw [hS.torus_eq, Subgroup.mem_subgroupOf]
    exact ⟨t, rfl⟩
  have htpanel : tΩ ∈ panelStab E k.castSucc := torus_le_panelStab E hm hS _ htorus
  have heq : suEndNΩ E hn s = tΩ⁻¹ * g := by
    refine Subtype.ext ?_
    show suEndN (F := F) (unitaryInvolution K 2 f) (m + 1) s =
      (diagHom F (unitaryInvolution K 2 f) (m + 1) t)⁻¹ *
        (g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
    rw [← hts]
    group
  have hsu : suEndNΩ E hn s ∈ panelStab E k.castSucc := by
    rw [heq]
    exact Subgroup.mul_mem _ ((panelStab E k.castSucc).inv_mem htpanel) hg
  obtain ⟨t', ht', hst'⟩ := exists_mem_torus_smul_eq
    (σ := unitaryInvolution K 2 f) s k.castSucc
    ({k.castSucc, k.succ} : Set (Fin (m + 1))) (Or.inl rfl) fun l hl => by
      have hl1 : l ≠ k.castSucc := fun h => hl (Or.inl h)
      have hl2 : l ≠ k.succ := fun h => hl (Or.inr h)
      have h := suAct_single_mem_span_singleton E hn s hsu l hl1 hl2
      rwa [suAct_apply] at h
  have hblock : t'⁻¹ * s ∈ (blockEmb2 K 2 f m k).range := by
    have hmem : t'⁻¹ * s ∈ (blockEmb K 2 f (m + 1) 2 (k : ℕ) (by omega)).range := by
      refine (mem_range_blockEmb_iff (p := 2) (f := f) (m := m + 1) (k := 2)
        (i := (k : ℕ)) (by omega) (t'⁻¹ * s)).mpr fun l hl => ?_
      have hnot : l ∉ ({k.castSucc, k.succ} : Set (Fin (m + 1))) := by
        intro hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h
        · apply hl
          rw [h]
          exact ⟨le_rfl, by simp only [Fin.val_castSucc]; omega⟩
        · apply hl
          rw [h]
          exact ⟨by simp only [Fin.val_succ]; omega, by simp only [Fin.val_succ]; omega⟩
      rw [mul_smul, hst' l hnot, inv_smul_smul]
    simpa [blockEmb2] using hmem
  have hs : s ∈ torus (unitaryInvolution K 2 f) (m + 1) ⊔ (blockEmb2 K 2 f m k).range := by
    have hmul := Subgroup.mul_mem_sup ht' hblock
    rwa [mul_inv_cancel_left] at hmul
  have hle : (torus (unitaryInvolution K 2 f) (m + 1)).map (suEndNΩ E hn) ≤ S.torus := by
    rw [hS.torus_eq]
    exact map_torus_suEndNΩ_le E hn
  have hmap : suEndNΩ E hn s ∈
      (torus (unitaryInvolution K 2 f) (m + 1) ⊔ (blockEmb2 K 2 f m k).range).map
        (suEndNΩ E hn) := Subgroup.mem_map_of_mem (f := suEndNΩ E hn) hs
  rw [Subgroup.map_sup, MonoidHom.map_range, suEndNΩ_comp_blockEmb2 E hm hS k] at hmap
  have hsup : suEndNΩ E hn s ∈ S.torus ⊔ (S.ι k.castSucc).range :=
    sup_le_sup hle le_rfl hmap
  have hgeq : g = tΩ * suEndNΩ E hn s := by
    rw [heq]
    exact (mul_inv_cancel_left tΩ g).symm
  rw [parab_singleton (E := E) (i := k.castSucc), hgeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htorus) hsup

theorem panelStab_eq_parab (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (i : Fin (m + 1)) :
    panelStab E i = S.parab {i} := by
  refine le_antisymm ?_ (parab_le_panelStab E hm hS i)
  by_cases hi : i = Fin.last m
  · subst hi
    have hchain : panelStab E (⟨m - 1, by omega⟩ : Fin (m + 1)) ≤
        S.parab {(⟨m - 1, by omega⟩ : Fin (m + 1))} := by
      have hidx : ((⟨m - 1, by omega⟩ : Fin m).castSucc : Fin (m + 1)) =
          (⟨m - 1, by omega⟩ : Fin (m + 1)) := Fin.ext rfl
      rw [← hidx]
      exact panelStab_castSucc_le_parab E hm hS ⟨m - 1, by omega⟩
    rw [← map_conjTau_panelStab E hm, ← map_conjTau_parab E hm hS]
    exact Subgroup.map_mono hchain
  · have hival : (i : ℕ) < m := by
      have h1 := i.isLt
      have hne : (i : ℕ) ≠ m := fun h' => hi (Fin.ext (by simpa using h'))
      omega
    have hidx : i = ((⟨i.val, hival⟩ : Fin m).castSucc : Fin (m + 1)) := Fin.ext rfl
    rw [hidx]
    exact panelStab_castSucc_le_parab E hm hS ⟨i.val, hival⟩

theorem adj_smul_stdDChamber_iff (hm : 3 ≤ m) (hS : IsStdDFamily E hm S) (i : Fin (m + 1))
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))) :
    (dChamberSystem (unitaryInvolution K 2 f) m).adj i
        (g • stdDChamber (unitaryInvolution K 2 f) (m + 1))
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)) ↔ g ∈ S.parab {i} := by
  rw [adj_smul_stdDChamber_iff_mem_panelStab (E := E), panelStab_eq_parab E hm hS i]

end CFSG.ClassicalInvolution.PhanDn

end
