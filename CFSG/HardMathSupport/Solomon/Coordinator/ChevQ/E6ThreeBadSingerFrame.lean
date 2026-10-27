module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerMat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerFrame

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4
open CFSG.RankThree.E6 (chain13 chainRoot e6Index support13 mem_support13 a2Equiv₁ a2Rep₁ a2Mat₁
  coe_a2Rep₁ a2Equiv₁_apply a2Mat₁_mul a2Mat₁_x1 a2Mat₁_y1 a2Mat₁_x3 a2Mat₁_y3)

open CFSG.RankThree.PartOne.TCX.E (e6rhoA2₁ a2Std₁)

open CFSG.ComponentClassification.CatLeafProof (weylWordElt)

open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Char

variable {K : Type} [Field K]

theorem rootChar_e6D0Char (ω : Kˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (e6D0Char ω) v = ω ^ (v 1 + v 4 + v 5) := by
  show ∏ i : Fin 6, (![1, ω, 1, 1, ω, ω] : Fin 6 → Kˣ) i ^ v i = _
  rw [Fin.prod_univ_six]
  show 1 ^ v 0 * ω ^ v 1 * 1 ^ v 2 * 1 ^ v 3 * ω ^ v 4 * ω ^ v 5 = _
  simp only [_root_.one_zpow, one_mul, mul_one, _root_.zpow_add]

theorem zpow_eq_zpow_of_three_dvd {G : Type*} [Group G] {g : G} (hg : g ^ 3 = 1) {n m : ℤ}
    (h : (3 : ℤ) ∣ n - m) : g ^ n = g ^ m := by
  obtain ⟨k, hk⟩ := h
  have hg' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  rw [show n = m + 3 * k by omega, _root_.zpow_add, _root_.zpow_mul, hg', _root_.one_zpow,
    mul_one]

theorem e6LineRoots_zero_subset_rootCharKernel (ω : Kˣ) :
    (e6LineRoots 0 : Set (Fin Tag.E6.rank → ℤ)) ⊆ rootCharKernel (e6D0Char ω) := by
  intro α hα
  have hα' : α ∈ e6LineRoots 0 := hα
  have key : ∀ β ∈ e6LineRoots 0, β 1 + β 4 + β 5 = 0 := by decide +kernel
  exact ⟨isRoot_of_mem_e6LineRoots hα', by rw [rootChar_e6D0Char, key α hα', zpow_zero]⟩

end Char

section Std

variable
  {K : Type} [Field K]

theorem e6WeylElt_mem_subsystemGroup13 {i : Fin Tag.E6.rank} (hi : i ∈ support13) :
    weylElt Tag.E6 K i 1 ∈ subsystemGroup Tag.E6 K support13 := by
  have hx : ∀ c : K, xUnit Tag.E6 K i c ∈ subsystemGroup Tag.E6 K support13 := fun c =>
    Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩
  have hy : ∀ c : K, yUnit Tag.E6 K i c ∈ subsystemGroup Tag.E6 K support13 := fun c =>
    Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩
  rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (hx _) (hy _)) (hx _)

theorem a2Mat₁_weylElt_zero :
    a2Mat₁ (weylElt Tag.E6 K (e6Index 0) 1) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  have hi : e6Index 0 ∈ support13 := (mem_support13 _).2 (Or.inl rfl)
  have hx : xUnit Tag.E6 K (e6Index 0) 1 ∈ subsystemGroup Tag.E6 K support13 :=
    Subgroup.subset_closure ⟨e6Index 0, hi, 1, Or.inl rfl⟩
  have hy : yUnit Tag.E6 K (e6Index 0) (-1) ∈ subsystemGroup Tag.E6 K support13 :=
    Subgroup.subset_closure ⟨e6Index 0, hi, -1, Or.inr rfl⟩
  rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, inv_one, Units.val_one,
    a2Mat₁_mul (mul_mem hx hy) hx, a2Mat₁_mul hx hy, a2Mat₁_x1, a2Mat₁_y1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem a2Mat₁_weylElt_two :
    a2Mat₁ (weylElt Tag.E6 K (e6Index 2) 1) = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  have hi : e6Index 2 ∈ support13 := (mem_support13 _).2 (Or.inr rfl)
  have hx : xUnit Tag.E6 K (e6Index 2) 1 ∈ subsystemGroup Tag.E6 K support13 :=
    Subgroup.subset_closure ⟨e6Index 2, hi, 1, Or.inl rfl⟩
  have hy : yUnit Tag.E6 K (e6Index 2) (-1) ∈ subsystemGroup Tag.E6 K support13 :=
    Subgroup.subset_closure ⟨e6Index 2, hi, -1, Or.inr rfl⟩
  rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, inv_one, Units.val_one,
    a2Mat₁_mul (mul_mem hx hy) hx, a2Mat₁_mul hx hy, a2Mat₁_x3, a2Mat₁_y3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply]

theorem e6rhoA2₁_signedCycSL :
    e6rhoA2₁ K signedCycSL = weylElt Tag.E6 K (e6Index 0) 1 * weylElt Tag.E6 K (e6Index 2) 1 := by
  have h0 := e6WeylElt_mem_subsystemGroup13 (K := K) ((mem_support13 (e6Index 0)).2 (Or.inl rfl))
  have h2 := e6WeylElt_mem_subsystemGroup13 (K := K) ((mem_support13 (e6Index 2)).2 (Or.inr rfl))
  have h : (a2Equiv₁ K).symm signedCycSL = ⟨_, mul_mem h0 h2⟩ := by
    rw [MulEquiv.symm_apply_eq, a2Equiv₁_apply]
    apply Subtype.ext
    rw [coe_a2Rep₁]
    show signedCycMat = a2Mat₁ (weylElt Tag.E6 K (e6Index 0) 1 * weylElt Tag.E6 K (e6Index 2) 1)
    rw [a2Mat₁_mul h0 h2, a2Mat₁_weylElt_zero, a2Mat₁_weylElt_two, signedCycMat]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h]

theorem exists_frame_e6Line_mono (K : Type) [Field K] (i : Fin 3) :
    ∃ (ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K)
      (σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ),
      IsA2Frame ρ σ ∧ ρ.range = e6LineFactor K i ∧ σ 0 1 = (e6LinePair i).1 ∧
        σ 1 2 = (e6LinePair i).2 ∧ ρ signedCycSL ∈ monomialSubgroup Tag.E6 K := by
  obtain ⟨v, h1, h2⟩ := exists_weyl_a2Pair_E6 (isA2Pair_e6LinePair i)
  have hfr := (e6Std_frame K).transport v
  have h01 : v • chainRoot chain13 0 1 = (e6LinePair i).1 := by
    rw [chainRoot13_zero_one]
    exact h1
  have h12 : v • chainRoot chain13 1 2 = (e6LinePair i).2 := by
    rw [chainRoot13_one_two]
    exact h2
  refine ⟨_, _, hfr, ?_, h01, h12, ?_⟩
  · rw [hfr.range, e6LineFactor, e6LineRoots_eq_pair]
    congr 1
    exact frame_roots_eq (hneg := hfr.neg) (hadd := hfr.add) h01 h12
  · show canonicalRep (coxeterSystem Tag.E6) K v * e6rhoA2₁ K signedCycSL *
      (canonicalRep (coxeterSystem Tag.E6) K v)⁻¹ ∈ monomialSubgroup Tag.E6 K
    rw [e6rhoA2₁_signedCycSL]
    exact mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K v)
      (mul_mem (weylElt_mem_monomialSubgroup _) (weylElt_mem_monomialSubgroup _)))
      (inv_mem (canonicalRep_mem_monomialSubgroup K v))

theorem rootChar_e6D0Char_frame {ω : Kˣ} (hw3 : ω ^ 3 = 1)
    {ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ) {i : Fin 3} (hi : i ≠ 0)
    (h01 : σ 0 1 = (e6LinePair i).1) (h12 : σ 1 2 = (e6LinePair i).2) :
    (fun j => ((rootChar (e6D0Char ω) (σ j 0) : Kˣ) : K)) = ![1, (ω : K) ^ 2, (ω : K)] := by
  have h00 : σ 0 0 = 0 := by rw [hfr.eq_sub 0 0, sub_self]
  have h10 : σ 1 0 = -(e6LinePair i).1 := by rw [hfr.neg 0 1, h01]
  have h20 : σ 2 0 = -((e6LinePair i).1 + (e6LinePair i).2) := by
    rw [hfr.neg 0 2, ← hfr.add 0 1 2, h01, h12]
  have e1 : rootChar (e6D0Char ω) (σ 1 0) = ω ^ ((2 : ℕ) : ℤ) := by
    rw [h10, rootChar_e6D0Char]
    apply zpow_eq_zpow_of_three_dvd hw3
    fin_cases i
    · exact absurd rfl hi
    · decide
    · decide
  have e2 : rootChar (e6D0Char ω) (σ 2 0) = ω ^ (1 : ℤ) := by
    rw [h20, rootChar_e6D0Char]
    apply zpow_eq_zpow_of_three_dvd hw3
    fin_cases i
    · exact absurd rfl hi
    · decide
    · decide
  funext j
  fin_cases j
  · show ((rootChar (e6D0Char ω) (σ 0 0) : Kˣ) : K) = 1
    rw [h00, rootChar_zero, Units.val_one]
  · show ((rootChar (e6D0Char ω) (σ 1 0) : Kˣ) : K) = (ω : K) ^ 2
    rw [e1, zpow_natCast, Units.val_pow_eq_pow_val]
  · show ((rootChar (e6D0Char ω) (σ 2 0) : Kˣ) : K) = (ω : K)
    rw [e2, zpow_one]

theorem frame_mem_monomialSubgroup {ρ : SpecialLinearGroup (Fin 3) K →* ModGL Tag.E6 K}
    {σ : Fin 3 → Fin 3 → Fin Tag.E6.rank → ℤ} (hfr : IsA2Frame ρ σ)
    (hC : ρ signedCycSL ∈ monomialSubgroup Tag.E6 K) {s : SpecialLinearGroup (Fin 3) K}
    {d : Fin 3 → K} {k : ℕ}
    (hs : (s : Matrix (Fin 3) (Fin 3) K) = diagonal d * signedCycMat ^ k) :
    ρ s ∈ monomialSubgroup Tag.E6 K := by
  have e1 : ((signedCycSL ^ k : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      signedCycMat ^ k :=
    (Matrix.SpecialLinearGroup.coe_pow (signedCycSL : SpecialLinearGroup (Fin 3) K) k).trans
      (congrArg (· ^ k) coe_signedCycSL)
  have e2 : ((signedCycSL ^ k : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((signedCycSL ^ k)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 :=
    (Matrix.SpecialLinearGroup.coe_mul (signedCycSL ^ k : SpecialLinearGroup (Fin 3) K)
      (signedCycSL ^ k)⁻¹).symm.trans
      ((congrArg Subtype.val
        (mul_inv_cancel (signedCycSL ^ k : SpecialLinearGroup (Fin 3) K))).trans
        Matrix.SpecialLinearGroup.coe_one)
  have hy : ((s * (signedCycSL ^ k)⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    have h1 : ((s * (signedCycSL ^ k)⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (s : Matrix (Fin 3) (Fin 3) K) *
          (((signedCycSL ^ k)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      Matrix.SpecialLinearGroup.coe_mul s (signedCycSL ^ k)⁻¹
    rw [h1, hs, ← e1, Matrix.mul_assoc, e2, Matrix.mul_one]
  have hyd : ∀ i j, i ≠ j →
      ((s * (signedCycSL ^ k)⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
        0 := by
    intro i j hij
    rw [hy, diagonal_apply_ne _ hij]
  have hs' : s = s * (signedCycSL ^ k)⁻¹ * signedCycSL ^ k := by rw [inv_mul_cancel_right]
  rw [hs', map_mul, map_pow]
  exact mul_mem (Subgroup.mem_sup_left (hfr.diag _ hyd)) (pow_mem hC k)

end Std

section Word

variable
  {K : Type} [Field K]

theorem coe_weylWordElt_of_isReduced {ν : List (Fin Tag.E6.rank)}
    (hν : (coxeterSystem Tag.E6).IsReduced ν) :
    ((weylWordElt .E6 K ν : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      canonicalRep (coxeterSystem Tag.E6) K ((coxeterSystem Tag.E6).wordProd ν) := by
  rw [canonicalRep_wordProd hν, weylWordElt, SubmonoidClass.coe_list_prod, List.map_map]
  rfl

theorem exists_weylWordElt_of_mem_monomialSubgroup {g : ModGL Tag.E6 K}
    (hg : g ∈ monomialSubgroup Tag.E6 K) (e : Fin Tag.E6.rank → Kˣ) :
    ∃ (ν : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ), ∀ h : adjointGroup Tag.E6 K,
      (((MulAut.conj (weylWordElt .E6 K ν) * rootDiagAutHom .E6 K a) h :
        adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 e * g * h * (rootDiagUnit Tag.E6 e * g)⁻¹ := by
  obtain ⟨w, t, ht, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  obtain ⟨c, rfl⟩ := torusGroup_le_range_rootDiagUnitHom_E6 ht
  obtain ⟨ν, hν, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  have hn := coe_weylWordElt_of_isReduced (K := K) hν
  refine ⟨ν, weylTuple ((coxeterSystem Tag.E6).wordProd ν)⁻¹ (e * c), fun h => ?_⟩
  have h1 := canonicalRep_conj_rootDiagUnit (K := K) ((coxeterSystem Tag.E6).wordProd ν)
    (weylTuple ((coxeterSystem Tag.E6).wordProd ν)⁻¹ (e * c))
  rw [weylTuple_weylTuple, mul_inv_cancel, weylTuple_one, ← hn] at h1
  rw [← hn]
  have key : rootDiagUnit Tag.E6 e * (rootDiagUnitHom Tag.E6 K c *
      (weylWordElt .E6 K ν : ModGL Tag.E6 K)) = (weylWordElt .E6 K ν : ModGL Tag.E6 K) *
        rootDiagUnit Tag.E6 (weylTuple ((coxeterSystem Tag.E6).wordProd ν)⁻¹ (e * c)) := by
    calc rootDiagUnit Tag.E6 e * (rootDiagUnitHom Tag.E6 K c *
          (weylWordElt .E6 K ν : ModGL Tag.E6 K))
        = rootDiagUnit Tag.E6 (e * c) * (weylWordElt .E6 K ν : ModGL Tag.E6 K) := by
          rw [rootDiagUnit_mul, mul_assoc]
          rfl
      _ = _ := by
          rw [← h1]
          group
  rw [key]
  show (weylWordElt .E6 K ν : ModGL Tag.E6 K) *
      (rootDiagUnit Tag.E6 (weylTuple ((coxeterSystem Tag.E6).wordProd ν)⁻¹ (e * c)) * h *
        (rootDiagUnit Tag.E6 (weylTuple ((coxeterSystem Tag.E6).wordProd ν)⁻¹ (e * c)))⁻¹) *
      (weylWordElt .E6 K ν : ModGL Tag.E6 K)⁻¹ = _
  group

end Word

section Shift

variable
  {K : Type} [Field K]

theorem rootDiagUnit_e6D0Char_conj_of_mem {ω : Kˣ} {g : ModGL Tag.E6 K}
    (hg : g ∈ e6LineFactor K 0) :
    rootDiagUnit Tag.E6 (e6D0Char ω) * g * (rootDiagUnit Tag.E6 (e6D0Char ω))⁻¹ = g :=
  conj_eq_iff_mem_centralizer.2
    (rootSpan_le_centralizer _ (e6LineRoots_zero_subset_rootCharKernel ω) hg)

theorem shift_eq_zero_of_commute_e6D0Char {ω : Kˣ} (hw1 : ω ≠ 1)
    {f : MulAut (adjointGroup Tag.E6 K)}
    (hfδ : f * rootDiagAutHom .E6 K (e6D0Char ω) = rootDiagAutHom .E6 K (e6D0Char ω) * f)
    {k : Fin 3}
    (hk : ((e6LineFactor K 0).subgroupOf (adjointGroup Tag.E6 K)).map f.toMonoidHom =
      (e6LineFactor K k).subgroupOf (adjointGroup Tag.E6 K)) : k = 0 := by
  by_contra hk0
  have hFC : e6LineFactor K k ≤ adjointGroup Tag.E6 K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hβk : (e6LinePair k).1 ∈ e6LineRoots k := by
    rw [e6LineRoots_eq_pair]
    exact Finset.mem_insert_self _ _
  have hβr : IsRoot .E6 (e6LinePair k).1 := isRoot_of_mem_e6LineRoots hβk
  have hsum : (e6LinePair k).1 1 + (e6LinePair k).1 4 + (e6LinePair k).1 5 = 1 := by
    fin_cases k
    · exact absurd rfl hk0
    · decide
    · decide
  have hχ : rootChar (e6D0Char ω) (e6LinePair k).1 = ω := by
    rw [rootChar_e6D0Char, hsum, zpow_one]
  have hmem : pinnedX .E6 K (e6LinePair k).1 1 ∈ e6LineFactor K k :=
    pinnedX_mem_rootSpan (Finset.mem_coe.2 hβk) 1
  have hy : (⟨pinnedX .E6 K (e6LinePair k).1 1, hFC hmem⟩ : adjointGroup Tag.E6 K) ∈
      (e6LineFactor K k).subgroupOf (adjointGroup Tag.E6 K) := hmem
  rw [← hk] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hδx : rootDiagAutHom .E6 K (e6D0Char ω) x = x :=
    Subtype.ext (rootDiagUnit_e6D0Char_conj_of_mem (Subgroup.mem_subgroupOf.1 hx))
  have hfx : rootDiagAutHom .E6 K (e6D0Char ω) (f x) = f x := by
    rw [← MulAut.mul_apply, ← hfδ, MulAut.mul_apply, hδx]
  have hxy' : f x = ⟨pinnedX .E6 K (e6LinePair k).1 1, hFC hmem⟩ := hxy
  rw [hxy'] at hfx
  have hval := congrArg Subtype.val hfx
  change rootDiagUnit Tag.E6 (e6D0Char ω) * pinnedX .E6 K (e6LinePair k).1 1 *
    (rootDiagUnit Tag.E6 (e6D0Char ω))⁻¹ = pinnedX .E6 K (e6LinePair k).1 1 at hval
  rw [rootDiagUnit_conj_pinnedX _ hβr, hχ, mul_one] at hval
  exact hw1 (Units.val_eq_one.1 (pinnedX_injective Tag.E6 K _ hval))

end Shift

section Conj

variable {G : Type*} [Group G] {C : Subgroup G}

theorem coe_conj_mul_mul_inv_apply (u : C) {ε : MulAut C} {F : G}
    (hε : ∀ k : C, ((ε k : C) : G) = F * k * F⁻¹) (h : C) :
    (((MulAut.conj u * ε * (MulAut.conj u)⁻¹) h : C) : G) =
      ((u : G) * F * (u : G)⁻¹) * h * ((u : G) * F * (u : G)⁻¹)⁻¹ := by
  simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, hε]
  group

theorem conj_mul_mul_inv_eq_self (u : C) {ε : MulAut C} {F : G}
    (hε : ∀ k : C, ((ε k : C) : G) = F * k * F⁻¹) (hu : (u : G) * F = F * u) :
    MulAut.conj u * ε * (MulAut.conj u)⁻¹ = ε := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_conj_mul_mul_inv_apply u hε, hε, hu]
  group

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
