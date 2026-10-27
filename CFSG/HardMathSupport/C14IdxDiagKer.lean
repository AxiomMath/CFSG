module

public import CFSG.HardMathSupport.C14IdxDet
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameLemmas

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Exc

namespace CFSG.HardMathSupport.C14Idx

private lemma smith_a_ne_zero {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (Submodule.span ℤ Ψ) (Fin τ.rank) n) (i : Fin n) :
    snf.a i ≠ 0 := by
  intro h
  have h1 : (snf.bN i : Fin τ.rank → ℤ) = 0 := by rw [snf.snf, h, zero_smul]
  have h2 : snf.bN i = 0 := Subtype.ext h1
  have h3 := snf.bN.repr_self i
  rw [h2, map_zero] at h3
  exact Finsupp.single_ne_zero.2 one_ne_zero h3.symm

private lemma rootChar_pow_bM_eq_one {τ : Tag} {L : Type} [Field L]
    {Ψ : Set (Fin τ.rank → ℤ)} {t : Fin τ.rank → Lˣ}
    (ht : ∀ α ∈ Ψ, rootChar t α = 1) {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (Submodule.span ℤ Ψ) (Fin τ.rank) n) (i : Fin n) :
    rootChar t (snf.bM (snf.f i)) ^ (∏ j : Fin n, (snf.a j).natAbs) = 1 := by
  have hbN : rootChar t (snf.bN i : Fin τ.rank → ℤ) = 1 :=
    CFSG.RankThree.PartOne.KE.CTTorus.rootChar_eq_one_of_mem_span ht (snf.bN i).2
  rw [snf.snf, rootChar_zsmul] at hbN
  have hk : rootChar t (snf.bM (snf.f i)) ^ (snf.a i).natAbs = 1 :=
    (pow_natAbs_eq_one (a := rootChar t (snf.bM (snf.f i))) (n := snf.a i)).2 hbN
  obtain ⟨m, hm⟩ :=
    Finset.dvd_prod_of_mem (fun j : Fin n => (snf.a j).natAbs) (Finset.mem_univ i)
  rw [hm, pow_mul, hk, one_pow]

private lemma perp_coord_of_notMem_range {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (Submodule.span ℤ Ψ) (Fin τ.rank) n) {j : Fin τ.rank}
    (hj : j ∉ Set.range snf.f) :
    ∀ α ∈ Ψ, ∑ k, α k * (snf.bM.coord j) (Pi.single k 1) = 0 := by
  intro α hα
  have h1 : (snf.bM.coord j) α = 0 := by
    have h2 := snf.repr_eq_zero_of_notMem_range ⟨α, Submodule.subset_span hα⟩ hj
    rw [← Module.Basis.coord_apply] at h2
    exact h2
  have hα' : α = ∑ k, α k • (Pi.single k 1 : Fin τ.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc ∑ k, α k * (snf.bM.coord j) (Pi.single k 1)
      = ∑ k, (snf.bM.coord j) (α k • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, smul_eq_mul]
    _ = (snf.bM.coord j) (∑ k, α k • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
        rw [map_sum]
    _ = (snf.bM.coord j) α := by rw [← hα']
    _ = 0 := h1

private lemma pow_eq_prod_cochar_coord {τ : Tag} {L : Type} [Field L]
    {Ψ : Set (Fin τ.rank → ℤ)} {t : Fin τ.rank → Lˣ} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (Submodule.span ℤ Ψ) (Fin τ.rank) n)
    (k : Fin τ.rank) :
    t k ^ (∏ j : Fin n, (snf.a j).natAbs) =
      ∏ j, (rootChar t (snf.bM j) ^ (∏ i : Fin n, (snf.a i).natAbs)) ^
        ((snf.bM.coord j) (Pi.single k 1)) := by
  have hsingle : rootChar t (Pi.single k 1 : Fin τ.rank → ℤ) = t k := by
    simpa using rootChar_nsmul_single t k 1
  have hrecon : (Pi.single k 1 : Fin τ.rank → ℤ) =
      ∑ j, ((snf.bM.coord j) (Pi.single k 1)) • snf.bM j := by
    simpa [Module.Basis.coord_apply] using
      (Module.Basis.sum_repr snf.bM (Pi.single k 1)).symm
  calc t k ^ (∏ j : Fin n, (snf.a j).natAbs)
      = rootChar t (Pi.single k 1) ^ (∏ j : Fin n, (snf.a j).natAbs) := by rw [hsingle]
    _ = rootChar t (((∏ j : Fin n, (snf.a j).natAbs : ℕ) : ℤ) • Pi.single k 1) := by
        rw [rootChar_zsmul, zpow_natCast]
    _ = rootChar t (((∏ j : Fin n, (snf.a j).natAbs : ℕ) : ℤ) •
          ∑ j, ((snf.bM.coord j) (Pi.single k 1)) • snf.bM j) := by
        conv_lhs => rw [hrecon]
    _ = rootChar t (∑ j, (((∏ i : Fin n, (snf.a i).natAbs : ℕ) : ℤ) *
          (snf.bM.coord j) (Pi.single k 1)) • snf.bM j) := by
        congr 1
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    _ = ∏ j, rootChar t ((((∏ i : Fin n, (snf.a i).natAbs : ℕ) : ℤ) *
          (snf.bM.coord j) (Pi.single k 1)) • snf.bM j) := by
        rw [rootChar_sum]
    _ = ∏ j, (rootChar t (snf.bM j) ^ (∏ i : Fin n, (snf.a i).natAbs)) ^
          ((snf.bM.coord j) (Pi.single k 1)) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [rootChar_zsmul, zpow_mul, zpow_natCast]

private lemma pow_eq_prod_cochar {τ : Tag} {L : Type} [Field L]
    {Ψ : Set (Fin τ.rank → ℤ)} {t : Fin τ.rank → Lˣ}
    (ht : ∀ α ∈ Ψ, rootChar t α = 1) {n : ℕ}
    (snf : Module.Basis.SmithNormalForm (Submodule.span ℤ Ψ) (Fin τ.rank) n) :
    t ^ (∏ j : Fin n, (snf.a j).natAbs) =
      ∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range snf.f),
        cochar (fun k => (snf.bM.coord j) (Pi.single k 1))
          (rootChar t (snf.bM j) ^ (∏ i : Fin n, (snf.a i).natAbs)) := by
  funext k
  rw [Pi.pow_apply, pow_eq_prod_cochar_coord snf k, Finset.prod_apply]
  simp only [cochar]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ Set.range snf.f
  · obtain ⟨i, rfl⟩ := hj
    have hzero : (rootChar t (snf.bM (snf.f i)) ^
        (∏ i : Fin n, (snf.a i).natAbs)) ^
          ((snf.bM.repr (Pi.single k 1)) (snf.f i)) = 1 := by
      rw [rootChar_pow_bM_eq_one ht snf i, one_zpow]
    simp [hzero, Set.mem_range_self i]
  · simp [hj]

private lemma rootDiagUnit_prod_mem_famZ {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {κ : Type} (s : Finset κ) (f : κ → Fin τ.rank → Lˣ)
    (hf : ∀ j ∈ s, rootDiagUnit τ (f j) ∈ famZ a) :
    rootDiagUnit τ (∏ j ∈ s, f j) ∈ famZ a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, rootDiagUnit_one]
    exact (famZ a).one_mem
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, rootDiagUnit_mul]
    exact (famZ a).mul_mem (hf j (Finset.mem_insert_self j s))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

private lemma famZ_mul_comm {τ : Tag} {L : Type} [Field L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {x y : ModGL τ L}
    (hx : x ∈ famZ a) (hy : y ∈ famZ a) : x * y = y * x := by
  obtain ⟨s, -, rfl⟩ := C14IdxDet.exists_of_mem_famZ hx
  obtain ⟨s', -, rfl⟩ := C14IdxDet.exists_of_mem_famZ hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm s s']

private lemma exists_pow_eq_of_zGen {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} {N : ℕ} (hN : 0 < N) {lam : Fin τ.rank → ℤ} {c : Lˣ}
    (hlam : ∀ α ∈ familyKernel a, ∑ i, α i * lam i = 0) :
    ∃ y ∈ famZ a, y ^ N = rootDiagUnit τ (cochar lam c) := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (c : L) hN
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.ne_of_gt hN)] at hx
    exact c.ne_zero hx.symm
  refine ⟨rootDiagUnit τ (cochar lam (Units.mk0 x hx0)), ?_, ?_⟩
  · rw [famZ]
    exact Subgroup.subset_closure ⟨lam, Units.mk0 x hx0, hlam, rfl⟩
  rw [rootDiagUnit_pow]
  congr 1
  funext i
  have hcx : (Units.mk0 x hx0 : Lˣ) ^ N = c :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hx)
  simp only [Pi.pow_apply, cochar]
  calc ((Units.mk0 x hx0 : Lˣ) ^ (lam i)) ^ N
      = (Units.mk0 x hx0 : Lˣ) ^ ((lam i : ℤ) * (N : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul]
    _ = (Units.mk0 x hx0 : Lˣ) ^ ((N : ℤ) * (lam i : ℤ)) := by rw [mul_comm]
    _ = ((Units.mk0 x hx0 : Lˣ) ^ (N : ℤ)) ^ (lam i : ℤ) := by rw [zpow_mul]
    _ = ((Units.mk0 x hx0 : Lˣ) ^ N) ^ (lam i : ℤ) := by rw [zpow_natCast]
    _ = c ^ (lam i : ℤ) := by rw [hcx]

theorem exists_pow_mem_famZ_of_mem_diagKer {τ : Tag} {L : Type} [Field L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ diagKer τ L (familyKernel a), g ^ N ∈ famZ a := by
  classical
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun ℤ (Fin τ.rank))
    (Submodule.span ℤ (familyKernel a))
  set N : ℕ := ∏ j : Fin n, (snf.a j).natAbs with hNdef
  have hN : 0 < N := by
    rw [hNdef]
    exact Finset.prod_pos fun i _ => Int.natAbs_pos.mpr (smith_a_ne_zero snf i)
  refine ⟨N, hN, ?_⟩
  intro g hg
  obtain ⟨t, rfl, ht⟩ := hg
  rw [hNdef, rootDiagUnit_pow, pow_eq_prod_cochar ht snf]
  refine rootDiagUnit_prod_mem_famZ (Finset.univ.filter (fun j => j ∉ Set.range snf.f))
    (fun j => cochar (fun k => (snf.bM.coord j) (Pi.single k 1))
      (rootChar t (snf.bM j) ^ (∏ i : Fin n, (snf.a i).natAbs))) fun j hj => ?_
  have hjr : j ∉ Set.range snf.f := (Finset.mem_filter.1 hj).2
  rw [famZ]
  exact Subgroup.subset_closure
    ⟨fun k => (snf.bM.coord j) (Pi.single k 1), _,
      perp_coord_of_notMem_range snf hjr, rfl⟩

theorem exists_pow_eq_of_mem_famZ {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {ι : Type}
    (a : ι → Fin τ.rank → Lˣ) {N : ℕ} (hN : 0 < N) {z : ModGL τ L} (hz : z ∈ famZ a) :
    ∃ y ∈ famZ a, y ^ N = z := by
  classical
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨lam, c, hlam, rfl⟩ := hz
    exact exists_pow_eq_of_zGen hN hlam
  | one =>
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_pow]
  | mul x y hx hy ihx ihy =>
    obtain ⟨x', hx'mem, hx'⟩ := ihx
    obtain ⟨y', hy'mem, hy'⟩ := ihy
    refine ⟨x' * y', Subgroup.mul_mem _ hx'mem hy'mem, ?_⟩
    have hcomm : Commute x' y' := famZ_mul_comm hx'mem hy'mem
    rw [hcomm.mul_pow, hx', hy']
  | inv x hx ih =>
    obtain ⟨y, hymem, hy⟩ := ih
    refine ⟨y⁻¹, Subgroup.inv_mem _ hymem, ?_⟩
    rw [inv_pow, hy]

end CFSG.HardMathSupport.C14Idx
