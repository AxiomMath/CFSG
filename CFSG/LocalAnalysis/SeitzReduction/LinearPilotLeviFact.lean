module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresTori
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresAbstract
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootSL2Aut

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)

section LeviFact

variable {n : ℕ} {F : Type*} [Field F]

@[expose] def BlockDiagOn (I : Finset (Fin n)) (x : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, i ≠ j → (i ∉ I ∨ j ∉ I) → x i j = 0

theorem BlockDiagOn.mul {I : Finset (Fin n)} {x y : Matrix (Fin n) (Fin n) F}
    (hx : BlockDiagOn I x) (hy : BlockDiagOn I y) :
    BlockDiagOn I (x * y) ∧ ∀ j, j ∉ I → (x * y) j j = x j j * y j j := by
  refine ⟨fun i j hij hIJ => ?_, fun j hj => ?_⟩
  · rw [mul_apply]
    rcases hIJ with hi | hj
    · rw [Finset.sum_eq_single i (fun k _ hki => by rw [hx i k (Ne.symm hki) (Or.inl hi), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), hy i j hij (Or.inl hi), mul_zero]
    · rw [Finset.sum_eq_single j (fun k _ hkj => by rw [hy k j hkj (Or.inr hj), mul_zero])
        (fun h => absurd (Finset.mem_univ j) h), hx i j hij (Or.inr hj), zero_mul]
  · rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by rw [hy k j hkj (Or.inr hj), mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]

private theorem mul_apply_of_diag {d x : Matrix (Fin n) (Fin n) F} (hd : ∀ i j, i ≠ j → d i j = 0)
    (i j : Fin n) : (d * x) i j = d i i * x i j ∧ (x * d) i j = x i j * d j j := by
  refine ⟨?_, ?_⟩
  · rw [mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hd i k (Ne.symm hki), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]
  · rw [mul_apply, Finset.sum_eq_single j (fun k _ hkj => by rw [hd k j hkj, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)]

theorem blockDiagOn_of_mem {N I : Finset (Fin n)} {D : Set (SpecialLinearGroup (Fin n) F)}
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ d ∈ D, (d : Matrix (Fin n) (Fin n) F) i i ≠ (d : Matrix (Fin n) (Fin n) F) j j)
    {x : SpecialLinearGroup (Fin n) F} (hxN : x ∈ blockSpecialLinear (K := F) N)
    (hxD : x ∈ centralizer D) : BlockDiagOn I (x : Matrix (Fin n) (Fin n) F) := by
  intro i j hij hIJ
  by_cases hN : i ∈ N ∧ j ∈ N
  · obtain ⟨d, hd, hne⟩ := hsep i hN.1 j hN.2 hij hIJ
    have hc := mem_centralizer_iff.mp hxD d hd
    have e := congrFun (congrFun (congrArg
      (fun A : SpecialLinearGroup (Fin n) F => (A : Matrix (Fin n) (Fin n) F)) hc) i) j
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e
    rw [(mul_apply_of_diag (hdiag d hd) i j).1, (mul_apply_of_diag (hdiag d hd) i j).2] at e
    have h0 : ((d : Matrix (Fin n) (Fin n) F) i i - (d : Matrix (Fin n) (Fin n) F) j j) *
        (x : Matrix (Fin n) (Fin n) F) i j = 0 := by linear_combination e
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  · have h1 := (mem_blockSpecialLinear.mp hxN) i j (by tauto)
    rw [h1, one_apply_ne hij]

theorem perfectCore_inf_centralizer_eq_blockSpecialLinear [Finite F] {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (D : Set (SpecialLinearGroup (Fin n) F))
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    (hconst : ∀ d ∈ D, ∀ i ∈ I, ∀ j ∈ I,
      (d : Matrix (Fin n) (Fin n) F) i i = (d : Matrix (Fin n) (Fin n) F) j j)
    (hsep : ∀ i ∈ N, ∀ j ∈ N, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ d ∈ D, (d : Matrix (Fin n) (Fin n) F) i i ≠ (d : Matrix (Fin n) (Fin n) F) j j)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I) :
    perfectCore (blockSpecialLinear (K := F) N ⊓ centralizer D) = blockSpecialLinear I := by
  set P := blockSpecialLinear (K := F) N ⊓ centralizer D
  have hbd : ∀ x ∈ P, BlockDiagOn I (x : Matrix (Fin n) (Fin n) F) := fun x hx =>
    blockDiagOn_of_mem hdiag hsep (mem_inf.mp hx).1 (mem_inf.mp hx).2
  have hPC : ⁅P, P⁆ ≤ blockSpecialLinear (K := F) I := by
    rw [commutator_le]
    intro x hx y hy
    have bx := hbd x hx
    have by' := hbd y hy
    have bxi := hbd x⁻¹ (P.inv_mem hx)
    have byi := hbd y⁻¹ (P.inv_mem hy)
    have hxx : ∀ j, j ∉ I → (x : Matrix (Fin n) (Fin n) F) j j *
        ((x⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = 1 := fun j hj => by
      rw [← (bx.mul bxi).2 j hj, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    have hyy : ∀ j, j ∉ I → (y : Matrix (Fin n) (Fin n) F) j j *
        ((y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) j j = 1 := fun j hj => by
      rw [← (by'.mul byi).2 j hj, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    have h1 := bx.mul by'
    have h2 := h1.1.mul bxi
    have h3 := h2.1.mul byi
    rw [commutatorElement_def, mem_blockSpecialLinear]
    intro i j hij
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    by_cases h : i = j
    · subst h
      have hi : i ∉ I := by tauto
      rw [h3.2 i hi, h2.2 i hi, h1.2 i hi, one_apply_eq]
      linear_combination (y : Matrix (Fin n) (Fin n) F) i i *
          ((y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i * hxx i hi +
        hyy i hi
    · rw [h3.1 i j h hij, one_apply_ne h]
  refine le_antisymm ?_ (le_perfectCore_of_perfect (le_inf (blockSpecialLinear_mono hIN) ?_) hperf)
  · calc perfectCore P = ⁅perfectCore P, perfectCore P⁆ := (perfectCore_perfect P).symm
      _ ≤ ⁅P, P⁆ := commutator_mono (perfectCore_le P) (perfectCore_le P)
      _ ≤ _ := hPC
  · intro x hx
    rw [mem_centralizer_iff]
    intro d hd
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    rw [(mul_apply_of_diag (hdiag d hd) i j).1, (mul_apply_of_diag (hdiag d hd) i j).2]
    by_cases hij : i ∈ I ∧ j ∈ I
    · rw [hconst d hd i hij.1 j hij.2, mul_comm]
    · rw [(mem_blockSpecialLinear.mp hx) i j (by tauto)]
      by_cases h : i = j
      · subst h
        rw [one_apply_eq, mul_one, one_mul]
      · rw [one_apply_ne h, mul_zero, zero_mul]

theorem inv_apply_of_diag {g : SpecialLinearGroup (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    ∀ i j, i ≠ j → ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  intro i j hij
  have h1 : ((g * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_apply_ne hij]
  have h2 : ((g * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
  rw [Matrix.SpecialLinearGroup.coe_mul, (mul_apply_of_diag hg i j).1] at h1
  rw [Matrix.SpecialLinearGroup.coe_mul, (mul_apply_of_diag hg i i).1] at h2
  exact (mul_eq_zero.mp h1).resolve_left (left_ne_zero_of_mul_eq_one h2)

theorem conj_mem_blockSpecialLinear_of_diag {N : Finset (Fin n)}
    {g : SpecialLinearGroup (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0)
    {x : SpecialLinearGroup (Fin n) F} (hx : x ∈ blockSpecialLinear N) :
    g * x * g⁻¹ ∈ blockSpecialLinear N := by
  rw [mem_blockSpecialLinear]
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    (mul_apply_of_diag (inv_apply_of_diag hg) i j).2, (mul_apply_of_diag hg i j).1,
    (mem_blockSpecialLinear.mp hx) i j hij]
  by_cases h : i = j
  · subst h
    have h2 : ((g * g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
      rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
    rw [Matrix.SpecialLinearGroup.coe_mul, (mul_apply_of_diag hg i i).1] at h2
    rw [one_apply_eq, mul_one, h2]
  · rw [one_apply_ne h, mul_zero, zero_mul]

theorem mem_normalizer_blockSpecialLinear_of_diag {N : Finset (Fin n)}
    {g : SpecialLinearGroup (Fin n) F}
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    g ∈ normalizer (blockSpecialLinear (K := F) N : Set (SpecialLinearGroup (Fin n) F)) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_blockSpecialLinear_of_diag hg, fun h => ?_⟩
  have := conj_mem_blockSpecialLinear_of_diag (inv_apply_of_diag hg) h
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

@[expose] noncomputable def conjDiagonal (N : Finset (Fin n)) (g : SpecialLinearGroup (Fin n) F)
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    MulAut (blockSpecialLinear (K := F) N) :=
  (blockSpecialLinear (K := F) N).normalizerMonoidHom
    ⟨g, mem_normalizer_blockSpecialLinear_of_diag hg⟩

theorem coe_conjDiagonal_apply (N : Finset (Fin n)) (g : SpecialLinearGroup (Fin n) F)
    (hg : ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) F) i j = 0)
    (x : blockSpecialLinear (K := F) N) :
    ((conjDiagonal N g hg x : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) =
      g * x * g⁻¹ :=
  rfl

theorem perfectCore_fixAll_eq [Finite F] {N I : Finset (Fin n)} (hIN : I ⊆ N) {ι' : Type*}
    (α : ι' → MulAut (blockSpecialLinear (K := F) N)) (d : ι' → SpecialLinearGroup (Fin n) F)
    (hα : ∀ j x, ((α j x : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) =
      d j * x * (d j)⁻¹)
    (hdiag : ∀ j, ∀ i k, i ≠ k → (d j : Matrix (Fin n) (Fin n) F) i k = 0)
    (hconst : ∀ j, ∀ i ∈ I, ∀ k ∈ I,
      (d j : Matrix (Fin n) (Fin n) F) i i = (d j : Matrix (Fin n) (Fin n) F) k k)
    (hsep : ∀ i ∈ N, ∀ k ∈ N, i ≠ k → (i ∉ I ∨ k ∉ I) →
      ∃ j, (d j : Matrix (Fin n) (Fin n) F) i i ≠ (d j : Matrix (Fin n) (Fin n) F) k k)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I) :
    perfectCore (fixAll α) = (blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N) := by
  have hmap : (fixAll α).map (blockSpecialLinear (K := F) N).subtype =
      blockSpecialLinear (K := F) N ⊓ centralizer (Set.range d) := by
    ext x
    simp only [mem_map, mem_inf, coe_subtype, mem_centralizer_iff, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun j => ?_⟩
      have h := congrArg Subtype.val (mem_fixAll.1 hy j)
      rw [hα] at h
      calc d j * (y : SpecialLinearGroup (Fin n) F) =
            d j * (y : SpecialLinearGroup (Fin n) F) * (d j)⁻¹ * d j := by group
        _ = (y : SpecialLinearGroup (Fin n) F) * d j := by rw [h]
    · rintro ⟨hxN, hx⟩
      refine ⟨⟨x, hxN⟩, mem_fixAll.2 fun j => Subtype.ext ?_, rfl⟩
      rw [hα]
      change d j * x * (d j)⁻¹ = x
      rw [hx j, mul_inv_cancel_right]
  apply Subgroup.map_injective (blockSpecialLinear (K := F) N).subtype_injective
  rw [CFSG.Quasithin.map_perfectCore, hmap, subgroupOf_map_subtype,
    inf_of_le_left (blockSpecialLinear_mono hIN)]
  refine perfectCore_inf_centralizer_eq_blockSpecialLinear hIN (Set.range d)
    (by rintro _ ⟨j, rfl⟩; exact hdiag j) (by rintro _ ⟨j, rfl⟩; exact hconst j)
    (fun i hi k hk hik hIk => ?_) hperf
  obtain ⟨j, hj⟩ := hsep i hi k hk hik hIk
  exact ⟨d j, ⟨j, rfl⟩, hj⟩

theorem eq_one_of_mem_center_of_mem_blockSpecialLinear {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {j : Fin n} (hjN : j ∈ N) (hjI : j ∉ I) {z : blockSpecialLinear (K := F) N}
    (hz : z ∈ center (blockSpecialLinear (K := F) N))
    (hzI : (z : SpecialLinearGroup (Fin n) F) ∈ blockSpecialLinear I) : z = 1 := by
  set Z : Matrix (Fin n) (Fin n) F :=
    ((z : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hcomm : ∀ {a b : Fin n} (hab : a ≠ b), a ∈ N → b ∈ N →
      Matrix.transvection a b (1 : F) * Z = Z * Matrix.transvection a b 1 := by
    intro a b hab ha hb
    have h := mem_center_iff.mp hz ⟨_, transvection_mem_blockSpecialLinear (K := F) hab ha hb 1⟩
    exact congrArg (fun x : blockSpecialLinear (K := F) N =>
      ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  have hZjj : Z j j = 1 := by
    have := (mem_blockSpecialLinear.mp hzI) j j (Or.inl hjI)
    rwa [one_apply_eq] at this
  have hdiag : ∀ k, Z k k = 1 := by
    intro k
    by_cases hkN : k ∈ N
    · by_cases hkj : k = j
      · rw [hkj]
        exact hZjj
      · have h := congrFun (congrFun (hcomm (Ne.symm hkj) hjN hkN) j) k
        rw [transvection_mul_apply_same, mul_transvection_apply_same] at h
        linear_combination h + hZjj
    · have := (mem_blockSpecialLinear.mp hzI) k k (Or.inl fun hk => hkN (hIN hk))
      rwa [one_apply_eq] at this
  have hoff : ∀ a b, a ≠ b → Z a b = 0 := by
    intro a b hab
    by_cases hI : a ∈ I ∧ b ∈ I
    · have hbj : b ≠ j := fun h => hjI (h ▸ hI.2)
      have h := congrFun (congrFun (hcomm hbj (hIN hI.2) hjN) a) j
      rw [transvection_mul_apply_of_ne (ha := hab), mul_transvection_apply_same] at h
      linear_combination -h
    · have := (mem_blockSpecialLinear.mp hzI) a b (not_and_or.mp hI)
      rwa [one_apply_ne hab] at this
  have hZ1 : Z = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [hdiag a, one_apply_eq]
    · rw [hoff a b hab, one_apply_ne hab]
  exact Subtype.ext (Subtype.ext hZ1)

theorem injective_comp_subtype_of_ker_le_center {G : Type*} [Group G] {N I : Finset (Fin n)}
    (hIN : I ⊆ N) (hne : I ≠ N) (Φ : blockSpecialLinear (K := F) N →* G)
    (hker : Φ.ker ≤ center (blockSpecialLinear (K := F) N)) :
    Function.Injective
      (Φ.comp ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).subtype) := by
  obtain ⟨j, hjN, hjI⟩ : ∃ j ∈ N, j ∉ I :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hIN, hne⟩)
  rw [injective_iff_map_eq_one]
  intro x hx
  exact Subtype.ext (eq_one_of_mem_center_of_mem_blockSpecialLinear hIN hjN hjI
    (hker ((MonoidHom.mem_ker).2 hx)) (mem_subgroupOf.mp x.2))

theorem map_subgroupOf_le_centralizer_of_disjoint {G : Type*} [Group G] {N I J : Finset (Fin n)}
    (hIJ : Disjoint I J) (Φ : blockSpecialLinear (K := F) N →* G) :
    ((blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N)).map Φ ≤
      centralizer ((((blockSpecialLinear (K := F) J).subgroupOf (blockSpecialLinear N)).map Φ :
        Subgroup G) : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h : x * y = y * x := Subtype.ext
    (commute_blockSpecialLinear_of_disjoint hIJ (mem_subgroupOf.mp hx) (mem_subgroupOf.mp hy)).eq
  rw [← map_mul, ← map_mul, h]

end LeviFact

section Glue

variable {n : ℕ} {K : Type*} [Field K] {F : Type*} [Field F]

theorem map_ringHom_mem_blockSpecialLinear (ι : K →+* F) {I : Finset (Fin n)}
    {A : SpecialLinearGroup (Fin n) K} (hA : A ∈ blockSpecialLinear I) :
    Matrix.SpecialLinearGroup.map ι A ∈ blockSpecialLinear (K := F) I := by
  intro i j hij
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    hA i j hij, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem map_torusDiagSL_apply_of_ne (ι : K →+* F)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) {i j : Fin n} (hij : i ≠ j) :
    ((Matrix.SpecialLinearGroup.map ι (torusDiagSL c) : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = 0 := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    torusDiagSL_apply_of_ne c hij, map_zero]

theorem map_torusDiagSL_apply_self (ι : K →+* F)
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (i : Fin n) :
    ((Matrix.SpecialLinearGroup.map ι (torusDiagSL c) : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i i = ι ((c.1 i : Kˣ) : K) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    torusDiagSL_apply_self]

@[expose] noncomputable def conjDiag (ι : K →+* F) (N : Finset (Fin n))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) : MulAut (blockSpecialLinear (K := F) N) :=
  conjDiagonal N (Matrix.SpecialLinearGroup.map ι (torusDiagSL c))
    fun _ _ hij => map_torusDiagSL_apply_of_ne ι c hij

theorem coe_conjDiag_apply (ι : K →+* F) (N : Finset (Fin n))
    (c : blockTorusParam (K := K) (∅ : Finset (Fin n))) (x : blockSpecialLinear (K := F) N) :
    ((conjDiag ι N c x : blockSpecialLinear (K := F) N) : SpecialLinearGroup (Fin n) F) =
      Matrix.SpecialLinearGroup.map ι (torusDiagSL c) * x *
        (Matrix.SpecialLinearGroup.map ι (torusDiagSL c))⁻¹ :=
  rfl

theorem commutator_blockSpecialLinear_eq_of_two_le [Finite F] {I : Finset (Fin n)}
    (hI : 2 ≤ I.card) (hF : 4 ≤ Nat.card F) :
    ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ = blockSpecialLinear I := by
  rcases hI.lt_or_eq with h | h
  · exact commutator_blockSpecialLinear_eq_of_three_le h
  · exact commutator_blockSpecialLinear_eq_of_card_two h.symm hF

theorem perfectCore_fixAll_conjDiag [Finite F] (ι : K →+* F) {N I : Finset (Fin n)} (hIN : I ⊆ N)
    {ι' : Type*} (c : ι' → blockTorusParam (K := K) (∅ : Finset (Fin n)))
    (hc : ∀ j, (c j).1 ∈ blockTorusParam I)
    (hsep : ∀ i ∈ N, ∀ k ∈ N, i ≠ k → (i ∉ I ∨ k ∉ I) → ∃ j, (c j).1 i ≠ (c j).1 k)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I) :
    perfectCore (fixAll fun j => conjDiag ι N (c j)) =
      (blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N) := by
  refine perfectCore_fixAll_eq hIN _ (fun j => Matrix.SpecialLinearGroup.map ι (torusDiagSL (c j)))
    (fun j x => rfl) (fun j i k hik => map_torusDiagSL_apply_of_ne ι (c j) hik)
    (fun j i hi k hk => by
      rw [map_torusDiagSL_apply_self, map_torusDiagSL_apply_self, (hc j).2 i hi k hk])
    (fun i hi k hk hik hIk => ?_) hperf
  obtain ⟨j, hj⟩ := hsep i hi k hk hik hIk
  refine ⟨j, ?_⟩
  rw [map_torusDiagSL_apply_self, map_torusDiagSL_apply_self]
  exact fun h => hj (Units.ext (ι.injective h))

theorem perfectCore_fixAll_conjDiag_blockTorusLift [Finite F] (ι : K →+* F)
    {N I : Finset (Fin n)} (hIN : I ⊆ N) {k : Fin n} (hk : k ∉ N) {κ : Kˣ} (hκ : κ ≠ 1)
    (hperf : ⁅blockSpecialLinear (K := F) I, blockSpecialLinear (K := F) I⁆ =
      blockSpecialLinear I) :
    perfectCore (fixAll fun d : blockTorus (K := K) I => conjDiag ι N (blockTorusLift d)) =
      (blockSpecialLinear (K := F) I).subgroupOf (blockSpecialLinear N) := by
  refine perfectCore_fixAll_conjDiag ι hIN _ blockTorusLift_mem
    (fun i hi j hj hij hIJ => ?_) hperf
  obtain ⟨c, hc, hcij⟩ := exists_mem_blockTorusParam_ne_of_notMem hIN hk hκ hi hj hij hIJ
  exact exists_blockTorusLift_ne hc hcij

theorem perfectCore_fixAll_conjDiag_blockTorusLift_self [Finite F] (ι : K →+* F)
    (N : Finset (Fin n))
    (hperf : ⁅blockSpecialLinear (K := F) N, blockSpecialLinear (K := F) N⁆ =
      blockSpecialLinear N) :
    perfectCore (fixAll fun d : blockTorus (K := K) N => conjDiag ι N (blockTorusLift d)) = ⊤ := by
  rw [perfectCore_fixAll_conjDiag ι subset_rfl _ blockTorusLift_mem
    (fun i _ j _ _ hIJ => absurd hIJ (by tauto)) hperf, subgroupOf_self]

end Glue

end CFSG.SeitzReduction.LinearPilot
