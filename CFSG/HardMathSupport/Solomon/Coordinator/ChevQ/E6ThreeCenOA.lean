module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenTorus
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenGroup
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenInner
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOACheck
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenCoroot
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenO3
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralMat
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadMonoWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps
public import CFSG.RankThree.PartOne.TCX.E.E6A2Sigma

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.RankThree.PartOne.KF4 (IsA2Frame)

open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3 conjDiag3_transvection toGL_conjDiag3)

open CFSG.RankThree.E6 (chain13 chainRoot)

open CFSG.RankThree.PartOne.TCX.E (e6rhoA2₁)

open CFSG.ComponentClassification.CatLeafProof (weylWordElt)

open CFSG.RankThree.Chevalley (wordSign wordRep_conj_pinnedX wordSign_eq_one_or wordAct_eq_smul)

open CFSG.LieType.Steinberg.Adjoint (iform)

open CFSG.StandardType.TableBExc.E6Three (gE6 wordE6G0 wordE6G1 wordE6G2 gE6_comm gE6_pow_three)

open scoped MatrixGroups

set_option linter.unusedSectionVars false

private local instance e6CenOAMain_neZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Group

variable {G : Type*} [Group G]

private theorem e6CenOA_pow_inj {u w : G} (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (huw : u ∉ Subgroup.zpowers w) {i i' j j' : ℕ} (hi : i < 3) (hi' : i' < 3) (hj : j < 3)
    (hj' : j' < 3) (h : u ^ i * w ^ j = u ^ i' * w ^ j') : i = i' ∧ j = j' := by
  have key : ∀ {a b c d : ℕ}, a < b → b < 3 → u ^ a * w ^ c = u ^ b * w ^ d → False := by
    intro a b c d hab hb h
    have e : w ^ c = u ^ (b - a) * w ^ d := by
      apply mul_left_cancel (a := u ^ a)
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab.le]
    have hmem : u ^ (b - a) ∈ Subgroup.zpowers w := by
      rw [show u ^ (b - a) = w ^ c * (w ^ d)⁻¹ by rw [e, mul_inv_cancel_right]]
      exact mul_mem (pow_mem (Subgroup.mem_zpowers w) c)
        (inv_mem (pow_mem (Subgroup.mem_zpowers w) d))
    apply huw
    rcases (by omega : b - a = 1 ∨ b - a = 2) with h1 | h2
    · rwa [h1, pow_one] at hmem
    · have e2 : u = (u ^ (b - a)) ^ 2 := by
        rw [h2, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hu3, one_mul]
      rw [e2]
      exact pow_mem hmem 2
  rcases lt_trichotomy i i' with hlt | rfl | hgt
  · exact (key hlt hi' h).elim
  · refine ⟨rfl, ?_⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have ho : orderOf w = 3 := orderOf_eq_prime hw3 hw1
    exact pow_injOn_Iio_orderOf (x := w) (Set.mem_Iio.2 (by rw [ho]; exact hj))
      (Set.mem_Iio.2 (by rw [ho]; exact hj')) (mul_left_cancel h)
  · exact (key hgt hi h.symm).elim

private theorem e6CenOA_eq_pow_mul_pow {P : Subgroup G} (hP : Nat.card P = 3 ^ 2) {u w : G}
    (hu : u ∈ P) (hw : w ∈ P) (hu3 : u ^ 3 = 1) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (huw : u ∉ Subgroup.zpowers w) {s : G} (hs : s ∈ P) :
    ∃ i j : ZMod 3, s = u ^ i.val * w ^ j.val := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  obtain ⟨f, hf⟩ : ∃ f : ZMod 3 × ZMod 3 → P, ∀ p, (f p : G) = u ^ p.1.val * w ^ p.2.val :=
    ⟨fun p => ⟨_, mul_mem (pow_mem hu p.1.val) (pow_mem hw p.2.val)⟩, fun _ => rfl⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' := congrArg Subtype.val h
    rw [hf, hf] at h'
    obtain ⟨e1, e2⟩ := e6CenOA_pow_inj hu3 hw3 hw1 huw (ZMod.val_lt i) (ZMod.val_lt i')
      (ZMod.val_lt j) (ZMod.val_lt j') h'
    exact Prod.ext (ZMod.val_injective 3 e1) (ZMod.val_injective 3 e2)
  obtain ⟨⟨i, j⟩, hij⟩ :=
    (hinj.bijective_of_nat_card_le (by simp [hP, Nat.card_prod, Nat.card_zmod])).2 ⟨s, hs⟩
  refine ⟨i, j, ?_⟩
  have h' := congrArg Subtype.val hij
  rw [hf] at h'
  exact h'.symm

end Group

private theorem e6CenOA_kerCount_comb {x y : Fin Tag.E6.rank → ZMod 3} {n : ℕ}
    (ha : e6KerCount x = n) (hb : e6KerCount y = n) (hc : e6KerCount (x + y) = n)
    (hd : e6KerCount (x + y + y) = n) {i j : ZMod 3} (hij : i ≠ 0 ∨ j ≠ 0) :
    e6KerCount (i • y + j • x) = n := by
  have key : ∀ i j : ZMod 3, (i ≠ 0 ∨ j ≠ 0) →
      (∀ a b : ZMod 3, i * b + j * a = a) ∨ (∀ a b : ZMod 3, i * b + j * a = -a) ∨
      (∀ a b : ZMod 3, i * b + j * a = b) ∨ (∀ a b : ZMod 3, i * b + j * a = -b) ∨
      (∀ a b : ZMod 3, i * b + j * a = a + b) ∨ (∀ a b : ZMod 3, i * b + j * a = -(a + b)) ∨
      (∀ a b : ZMod 3, i * b + j * a = a + b + b) ∨
      (∀ a b : ZMod 3, i * b + j * a = -(a + b + b)) := by
    decide +kernel
  have ev : ∀ v : Fin Tag.E6.rank → ZMod 3, (∀ k, i * y k + j * x k = v k) →
      i • y + j • x = v := fun v hv => funext fun k => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact hv k
  rcases key i j hij with h | h | h | h | h | h | h | h
  · rw [ev x fun k => h (x k) (y k)]
    exact ha
  · rw [ev (-x) fun k => h (x k) (y k), e6Cen_kerCount_neg]
    exact ha
  · rw [ev y fun k => h (x k) (y k)]
    exact hb
  · rw [ev (-y) fun k => h (x k) (y k), e6Cen_kerCount_neg]
    exact hb
  · rw [ev (x + y) fun k => h (x k) (y k)]
    exact hc
  · rw [ev (-(x + y)) fun k => h (x k) (y k), e6Cen_kerCount_neg]
    exact hc
  · rw [ev (x + y + y) fun k => h (x k) (y k)]
    exact hd
  · rw [ev (-(x + y + y)) fun k => h (x k) (y k), e6Cen_kerCount_neg]
    exact hd

private theorem e6CenOA_trace_cases {K : Type} [Field K] {ω : Kˣ} (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) {m n : ℕ} (hm : m < 3) (hn : n < 3)
    (h : (1 : K) + (ω : K) ^ m + (ω : K) ^ n * (ω : K) ^ m = 0) : n = m ∧ n ≠ 0 := by
  have s := e6Cen_one_add_add_sq h3 h1
  have c3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h30 : (3 : K) ≠ 0 := e6Cen_three_ne_zero h3 h1
  interval_cases m <;> interval_cases n
  · exact (h30 (by linear_combination h)).elim
  · exact (h30 (by linear_combination s - ((ω : K) - 1) * h)).elim
  · exact (h30 (by linear_combination (2 + (ω : K)) * h - (1 + (ω : K)) * s)).elim
  · exact (h30 (by linear_combination 4 * s - (1 + 2 * (ω : K)) * h)).elim
  · exact ⟨rfl, by decide⟩
  · exact (h30 (by linear_combination s - ((ω : K) - 1) * h + ((ω : K) - 1) * c3)).elim
  · exact (h30 (by
      linear_combination 4 * s + 4 * (ω : K) * c3 - (1 + 2 * (ω : K) ^ 2) * h)).elim
  · exact (h30 (by
      linear_combination (2 + (ω : K)) * h - (2 + (ω : K)) * c3 - (1 + (ω : K)) * s)).elim
  · exact ⟨rfl, by decide⟩

private theorem e6CenOA_rootChar_single {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (k : Fin Tag.E6.rank) : rootChar a (Pi.single k 1) = a k := by
  simpa using rootChar_nsmul_single a k 1

private theorem e6CenOA_rootChar_neg {K : Type} [Field K] (a : Fin Tag.E6.rank → Kˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

private theorem e6CenOA_chainRoot_col :
    chainRoot chain13 0 0 = 0 ∧ chainRoot chain13 1 0 = -(Pi.single 0 1 : Fin Tag.E6.rank → ℤ) ∧
      chainRoot chain13 2 0 = -((Pi.single 0 1 : Fin Tag.E6.rank → ℤ) + Pi.single 2 1) := by
  decide +kernel

private theorem e6CenOA_iform_chainRoot : ∀ i j : Fin 3,
    iform (chainRoot chain13 i j) (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) = 0 ∧
      iform (chainRoot chain13 i j) (Pi.single 5 1 : Fin Tag.E6.rank → ℤ) = 0 := by
  decide +kernel

private theorem e6CenOA_chainRoot_supp : ∀ (i j : Fin 3) (m n : ZMod 3),
    ∑ l, e6CenTz 0 m n l * ((chainRoot chain13 i j l : ℤ) : ZMod 3) = 0 := by
  decide +kernel

private theorem e6CenOA_cenTg12_five : cenTg12 5 = (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) := by
  decide +kernel

private theorem e6CenOA_signedCycMat_mul_diagonal {K : Type} [Field K] (d : Fin 3 → K) :
    (signedCycMat * diagonal d : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![d 2, d 0, d 1] * signedCycMat := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [signedCycMat]

private theorem e6CenOA_signedCycMat_mul_diagonal_pow_three {K : Type} [Field K] (d : Fin 3 → K) :
    (signedCycMat * diagonal d : Matrix (Fin 3) (Fin 3) K) ^ 3 = (d 0 * d 1 * d 2) • 1 := by
  rw [e6CenOA_signedCycMat_mul_diagonal, diagonal_mul_signedCycMat_pow_three]
  congr 1
  show d 2 * d 0 * d 1 = d 0 * d 1 * d 2
  ring

private theorem e6CenOA_trace_signedCycMat_mul_diagonal {K : Type} [Field K] (d : Fin 3 → K) :
    Matrix.trace (signedCycMat * diagonal d : Matrix (Fin 3) (Fin 3) K) = 0 := by
  rw [Matrix.trace_fin_three]
  simp [signedCycMat, Matrix.mul_diagonal]

private theorem e6CenOA_eq_diagGL3 {K : Type} [Field K] {Γ : GL (Fin 3) K}
    (h : ∀ i j, i ≠ j → (Γ : Matrix (Fin 3) (Fin 3) K) i j = 0) : ∃ e, Γ = diagGL3 e := by
  have hd : (Γ : Matrix (Fin 3) (Fin 3) K) =
      diagonal fun i => (Γ : Matrix (Fin 3) (Fin 3) K) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, h i j hij]
  have hne : ∀ i, (Γ : Matrix (Fin 3) (Fin 3) K) i i ≠ 0 := by
    intro i hi
    have hdet : (Γ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    rw [hd, det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  exact ⟨fun i => Units.mk0 _ (hne i), Units.ext hd⟩

section Frame

variable {K : Type} [Field K]
  {ω : Kˣ}

private theorem e6CenOA_coe_weylWordElt :
    (weylWordElt .E6 K wordE6G0 : ModGL Tag.E6 K) = e6rhoA2₁ K signedCycSL := by
  rw [e6rhoA2₁_signedCycSL, coe_weylWordElt]
  show (([0, 2] : List (Fin Tag.E6.rank)).map fun i => weylElt Tag.E6 K i 1).prod = _
  rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

private theorem e6CenOA_rho_mem (A : SpecialLinearGroup (Fin 3) K) :
    e6rhoA2₁ K A ∈ adjointGroup Tag.E6 K := by
  have hfr : IsA2Frame (e6rhoA2₁ K) (chainRoot chain13) := e6Std_frame K
  have h : e6rhoA2₁ K A ∈ (e6rhoA2₁ K).range := ⟨A, rfl⟩
  rw [hfr.range] at h
  exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α) h

private theorem e6CenOA_rho_commute (A : SpecialLinearGroup (Fin 3) K) {k : Fin Tag.E6.rank}
    (hk : k = 4 ∨ k = 5) (t : K) :
    e6rhoA2₁ K A * pinnedX Tag.E6 K (Pi.single k 1) t =
      pinnedX Tag.E6 K (Pi.single k 1) t * e6rhoA2₁ K A := by
  have hfr : IsA2Frame (e6rhoA2₁ K) (chainRoot chain13) := e6Std_frame K
  have h : e6rhoA2₁ K A ∈ (e6rhoA2₁ K).range := ⟨A, rfl⟩
  rw [hfr.range] at h
  refine cen_rootSpan_commute (isRoot_single _ k) ?_ h t
  rintro α ⟨i, j, hij, rfl⟩
  refine ⟨hfr.isRoot i j hij, ?_⟩
  rcases hk with rfl | rfl
  · exact (e6CenOA_iform_chainRoot i j).1
  · exact (e6CenOA_iform_chainRoot i j).2

private theorem e6CenOA_rho_commute_torV (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (A : SpecialLinearGroup (Fin 3) K) (m n : ZMod 3) :
    e6rhoA2₁ K A * rootDiagUnit Tag.E6 (torV ω (e6CenTz 0 m n)) =
      rootDiagUnit Tag.E6 (torV ω (e6CenTz 0 m n)) * e6rhoA2₁ K A := by
  have hfr : IsA2Frame (e6rhoA2₁ K) (chainRoot chain13) := e6Std_frame K
  have h : e6rhoA2₁ K A ∈ (e6rhoA2₁ K).range := ⟨A, rfl⟩
  rw [hfr.range] at h
  have hle := rootSpan_le_centralizer (torV ω (e6CenTz 0 m n))
    (S := {r | ∃ i j : Fin 3, i ≠ j ∧ r = chainRoot chain13 i j}) (by
      rintro α ⟨i, j, hij, rfl⟩
      exact ⟨hfr.isRoot i j hij,
        (rootChar_torV_eq_one_iff h3 h1 _ _).2 (e6CenOA_chainRoot_supp i j m n)⟩)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle h)

private theorem e6CenOA_frame_step (hζ : ∃ ζ : K, IsPrimitiveRoot ζ 3)
    (b : Fin Tag.E6.rank → Kˣ) {μ : Kˣ} (hμ : μ ^ 3 = (b 0)⁻¹ ^ 2 * (b 2)⁻¹) :
    ∃ (z : SpecialLinearGroup (Fin 3) K) (c : Fin Tag.E6.rank → Kˣ),
      e6rhoA2₁ K z * (e6rhoA2₁ K signedCycSL * rootDiagUnit Tag.E6 b) * (e6rhoA2₁ K z)⁻¹ =
        rootDiagUnit Tag.E6 c ∧ (1 : K) + (c 2 : K) + (c 0 : K) * (c 2 : K) = 0 ∧
          c 4 = b 4 ∧ c 5 = b 5 := by
  have hfr : IsA2Frame (e6rhoA2₁ K) (chainRoot chain13) := e6Std_frame K
  obtain ⟨χ, hχ⟩ : ∃ χ : Fin 3 → Kˣ, χ = fun i => rootChar b (chainRoot chain13 i 0) :=
    ⟨_, rfl⟩
  have htor : ∀ s, rootDiagUnit Tag.E6 b * e6rhoA2₁ K s * (rootDiagUnit Tag.E6 b)⁻¹ =
      e6rhoA2₁ K (conjDiag3 χ s) := fun s => by rw [hfr.torus b s, hχ]
  have htoGL : ∀ (d : Fin 3 → Kˣ) (w : SpecialLinearGroup (Fin 3) K),
      SpecialLinearGroup.toGL (conjDiag3 d w) =
        diagGL3 d * SpecialLinearGroup.toGL w * (diagGL3 d)⁻¹ := toGL_conjDiag3
  have hγ3 : ((SpecialLinearGroup.toGL signedCycSL * diagGL3 χ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = ((χ 0 : K) * χ 1 * χ 2) • 1 :=
    e6CenOA_signedCycMat_mul_diagonal_pow_three fun i => (χ i : K)
  obtain ⟨hc0, hc1, hc2⟩ := e6CenOA_chainRoot_col
  have hμK : (μ : K) ^ 3 = (χ 0 : K) * χ 1 * χ 2 := by
    rw [← Units.val_pow_eq_pow_val, hμ, hχ]
    simp only [hc0, hc1, hc2, rootChar_zero, e6CenOA_rootChar_neg, rootChar_add,
      e6CenOA_rootChar_single]
    push_cast
    ring
  obtain ⟨z, hz⟩ := exists_SL_conj_offDiag_eq_zero_of_cube hζ hγ3 hμK
  obtain ⟨e, he⟩ := e6CenOA_eq_diagGL3 hz
  obtain ⟨A', hA'⟩ : ∃ A' : SpecialLinearGroup (Fin 3) K,
      A' = z * signedCycSL * conjDiag3 χ z⁻¹ := ⟨_, rfl⟩
  have hA'D : SpecialLinearGroup.toGL A' * diagGL3 χ = diagGL3 e := by
    rw [hA', ← he, map_mul, map_mul, htoGL, map_inv]
    group
  have hA'off : ∀ i j, i ≠ j → (A' : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
    intro i j hij
    have e1 : SpecialLinearGroup.toGL A' = diagGL3 e * (diagGL3 χ)⁻¹ := by
      rw [← hA'D, mul_inv_cancel_right]
    have e2 : (A' : Matrix (Fin 3) (Fin 3) K) =
        (diagGL3 e : Matrix (Fin 3) (Fin 3) K) * ((diagGL3 χ)⁻¹ : GL (Fin 3) K) :=
      congrArg Units.val e1
    rw [e2]
    change (diagonal (fun k => (e k : K)) * diagonal (fun k => (((χ k)⁻¹ : Kˣ) : K))) i j = 0
    rw [diagonal_mul_diagonal, diagonal_apply_ne _ hij]
  obtain ⟨e', he'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hfr.diag A' hA'off)
  have hconj : e6rhoA2₁ K z * (e6rhoA2₁ K signedCycSL * rootDiagUnit Tag.E6 b) *
      (e6rhoA2₁ K z)⁻¹ = rootDiagUnit Tag.E6 (e' * b) := by
    rw [rootDiagUnit_mul, ← he']
    calc e6rhoA2₁ K z * (e6rhoA2₁ K signedCycSL * rootDiagUnit Tag.E6 b) * (e6rhoA2₁ K z)⁻¹
        = e6rhoA2₁ K z * e6rhoA2₁ K signedCycSL *
            (rootDiagUnit Tag.E6 b * e6rhoA2₁ K z⁻¹ * (rootDiagUnit Tag.E6 b)⁻¹) *
              rootDiagUnit Tag.E6 b := by
          rw [map_inv]
          group
      _ = e6rhoA2₁ K A' * rootDiagUnit Tag.E6 b := by
          rw [htor, hA', map_mul, map_mul]
  have hAconj : ∀ s, A' * conjDiag3 χ s * A'⁻¹ = conjDiag3 e s := by
    intro s
    apply SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, map_inv, htoGL, htoGL, ← hA'D]
    group
  have hdc : ∀ s, rootDiagUnit Tag.E6 (e' * b) * e6rhoA2₁ K s *
      (rootDiagUnit Tag.E6 (e' * b))⁻¹ = e6rhoA2₁ K (conjDiag3 e s) := by
    intro s
    rw [rootDiagUnit_mul, ← hAconj s, map_mul, map_mul, map_inv, ← htor s, he']
    group
  have htr : ∀ {i j : Fin 3} (hij : i ≠ j) {k : Fin Tag.E6.rank},
      chainRoot chain13 i j = Pi.single k 1 →
        (((e' * b) k : Kˣ) : K) = (e i : K) * (((e j)⁻¹ : Kˣ) : K) := by
    intro i j hij k hk
    obtain ⟨ε, hε⟩ := hfr.transv i j hij
    have h := hdc (SpecialLinearGroup.transvection hij 1)
    rw [hε, conjDiag3_transvection, hε, hk, rootDiagUnit_conj_pinnedX _ (isRoot_single _ k),
      e6CenOA_rootChar_single] at h
    have h' := pinnedX_injective Tag.E6 K _ h
    apply mul_left_cancel₀ ε.ne_zero
    linear_combination h'
  have h0 := htr (i := 0) (j := 1) (by decide) chainRoot13_zero_one
  have h2 := htr (i := 1) (j := 2) (by decide) chainRoot13_one_two
  have htr0 : (e 0 : K) + e 1 + e 2 = 0 := by
    have h := congrArg (fun g : GL (Fin 3) K => Matrix.trace (g : Matrix (Fin 3) (Fin 3) K)) he
    simp only [Units.val_mul, Matrix.trace_units_conj] at h
    change Matrix.trace (signedCycMat * diagonal fun i => (χ i : K)) =
      Matrix.trace (diagonal fun i => (e i : K)) at h
    rw [e6CenOA_trace_signedCycMat_mul_diagonal, Matrix.trace_diagonal, Fin.sum_univ_three] at h
    exact h.symm
  have h45 : ∀ k : Fin Tag.E6.rank, (k = 4 ∨ k = 5) → e' k = 1 := by
    intro k hk
    have h := e6CenOA_rho_commute A' hk 1
    rw [he'] at h
    have h3 := mul_inv_eq_of_eq_mul h
    rw [rootDiagUnit_conj_pinnedX _ (isRoot_single _ k), e6CenOA_rootChar_single, mul_one] at h3
    exact Units.val_eq_one.1 (pinnedX_injective Tag.E6 K _ h3)
  refine ⟨z, e' * b, hconj, ?_, ?_, ?_⟩
  · have u1 : ((e 1 : K))⁻¹ * e 1 = 1 := inv_mul_cancel₀ (e 1).ne_zero
    have u2 : (e 2 : K) * ((e 2 : K))⁻¹ = 1 := mul_inv_cancel₀ (e 2).ne_zero
    rw [h0, h2, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    linear_combination ((e 2 : K))⁻¹ * htr0 - u2 + (e 0 : K) * ((e 2 : K))⁻¹ * u1
  · rw [Pi.mul_apply, h45 4 (Or.inl rfl), one_mul]
  · rw [Pi.mul_apply, h45 5 (Or.inr rfl), one_mul]

private theorem e6CenOA_b4_eq_b5 {X Y : MulAut (adjointGroup Tag.E6 K)}
    {b b' : Fin Tag.E6.rank → Kˣ}
    (hXb : X = MulAut.conj (weylWordElt .E6 K wordE6G0) * rootDiagAutHom Tag.E6 K b)
    (hYb : Y = MulAut.conj (weylWordElt .E6 K (wordE6G1 ++ wordE6G2)) *
      rootDiagAutHom Tag.E6 K b')
    (h : X * Y = Y * X) : b 4 = b 5 := by
  have hX : ∀ {k : Fin Tag.E6.rank}, (k = 4 ∨ k = 5) → ∀ (a : adjointGroup Tag.E6 K) (t : K),
      (a : ModGL Tag.E6 K) = pinnedX Tag.E6 K (Pi.single k 1) t →
        ((X a : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          pinnedX Tag.E6 K (Pi.single k 1) ((b k : K) * t) := by
    intro k hk a t ha
    rw [hXb]
    change (weylWordElt .E6 K wordE6G0 : ModGL Tag.E6 K) *
      (rootDiagUnit Tag.E6 b * (a : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b)⁻¹) *
        (weylWordElt .E6 K wordE6G0 : ModGL Tag.E6 K)⁻¹ = _
    rw [ha, rootDiagUnit_conj_pinnedX _ (isRoot_single _ k), e6CenOA_rootChar_single,
      e6CenOA_coe_weylWordElt]
    exact mul_inv_eq_of_eq_mul (e6CenOA_rho_commute signedCycSL hk _)
  have hY : ∀ (a : adjointGroup Tag.E6 K) (t : K),
      (a : ModGL Tag.E6 K) = pinnedX Tag.E6 K (Pi.single 5 1) t →
        ((Y a : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
          pinnedX Tag.E6 K (Pi.single 4 1)
            ((wordSign Tag.E6 (wordE6G1 ++ wordE6G2) (Pi.single 5 1) : K) * ((b' 5 : K) * t)) := by
    intro a t ha
    rw [hYb]
    change (weylWordElt .E6 K (wordE6G1 ++ wordE6G2) : ModGL Tag.E6 K) *
      (rootDiagUnit Tag.E6 b' * (a : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 b')⁻¹) *
        (weylWordElt .E6 K (wordE6G1 ++ wordE6G2) : ModGL Tag.E6 K)⁻¹ = _
    rw [ha, rootDiagUnit_conj_pinnedX _ (isRoot_single _ 5), e6CenOA_rootChar_single,
      coe_weylWordElt, wordRep_conj_pinnedX K _ (isRoot_single _ 5), wordAct_eq_smul,
      cen_smul_g12 5, e6CenOA_cenTg12_five]
  have hs : (wordSign Tag.E6 (wordE6G1 ++ wordE6G2) (Pi.single 5 1) : K) ≠ 0 := by
    rcases wordSign_eq_one_or (wordE6G1 ++ wordE6G2) (isRoot_single Tag.E6 5) with e | e <;>
      simp [e]
  obtain ⟨a, ha⟩ : ∃ a : adjointGroup Tag.E6 K,
      (a : ModGL Tag.E6 K) = pinnedX Tag.E6 K (Pi.single 5 1) 1 :=
    ⟨⟨_, pinnedX_mem_adjointGroup _ _⟩, rfl⟩
  have e : X (Y a) = Y (X a) := by
    simpa only [MulAut.mul_apply] using DFunLike.congr_fun h a
  have e2 := (hX (k := 4) (Or.inl rfl) _ _ (hY a 1 ha)).symm.trans
    ((congrArg Subtype.val e).trans (hY _ _ (hX (k := 5) (Or.inr rfl) a 1 ha)))
  have e3 := pinnedX_injective Tag.E6 K _ e2
  apply Units.ext
  have e4 : ((wordSign Tag.E6 (wordE6G1 ++ wordE6G2) (Pi.single 5 1) : K) * b' 5) *
      ((b 4 : K) - b 5) = 0 := by
    linear_combination e3
  rcases mul_eq_zero.1 e4 with e5 | e5
  · exact absurd e5 (mul_ne_zero hs (b' 5).ne_zero)
  · exact sub_eq_zero.1 e5

end Frame

section Census

variable
  {K : Type} [Field K] {ω : Kˣ}

private theorem e6CenOA_concl_of_planePat [Finite K] (hK4 : 4 ≤ Nat.card K) (h3 : ω ^ 3 = 1)
    (h1 : ω ≠ 1) {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    {x y : Fin Tag.E6.rank → ZMod 3} (hx : rootDiagAutHom Tag.E6 K (torV ω x) ∈ E)
    (hy : rootDiagAutHom Tag.E6 K (torV ω y) ∈ E) (hxl : e6CenLam x = 0) (hyl : e6CenLam y = 0)
    (hx0 : x ≠ 0) (hyx : ∀ k : ZMod 3, y ≠ k • x) (hpat : E6CenPlanePat x y) :
    E6CenConcl K E := by
  obtain ⟨hE, hEc, hED, hEi, hER, hA⟩ := hcube
  have hxy : rootDiagAutHom Tag.E6 K (torV ω (x + y)) ∈ E := by
    rw [e6PW_torV_add h3, map_mul]
    exact mul_mem hx hy
  have hxyy : rootDiagAutHom Tag.E6 K (torV ω (x + y + y)) ∈ E := by
    rw [e6PW_torV_add h3, map_mul]
    exact mul_mem hxy hy
  have h30 : ∀ v : Fin Tag.E6.rank → ZMod 3, rootDiagAutHom Tag.E6 K (torV ω v) ∈ E →
      e6KerCount v = 30 → False := by
    intro v hv hv30
    obtain ⟨ρ, hρ, hρv⟩ := e6Cen_coroot_of_kerCount v hv30
    have e : torV ω v = fun j => ω ^ iform ρ (Pi.single j 1) := by
      funext j
      show ω ^ (v j).val = ω ^ iform ρ (Pi.single j 1)
      rw [← zpow_natCast]
      refine zpow_eq_zpow_of_three_dvd h3 ?_
      have h0 : ((((v j).val : ℤ) - iform ρ (Pi.single j 1) : ℤ) : ZMod 3) = 0 := by
        rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, ← hρv j, sub_self]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h0
    refine hER (e6NormalizesR_of_commute_coroot h3 h1 hρ hED fun ε hε => ?_)
    rw [← e]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨ε, hε⟩ ⟨_, hv⟩)
  rcases hpat with ⟨ha, hb, hc, hd⟩ | h | hcen
  · refine (hA fun s hs hs1 => ?_).elim
    have h9 : Nat.card ↥(E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) = 3 ^ 2 :=
      card_inf_innerAut_of_le_e6Inndiag K hEc hED hEi
    have hxi : rootDiagAutHom Tag.E6 K (torV ω x) ∈
        E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
      Subgroup.mem_inf.2 ⟨hx, e6Cen_rootDiagAutHom_torV_mem hxl⟩
    have hyi : rootDiagAutHom Tag.E6 K (torV ω y) ∈
        E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
      Subgroup.mem_inf.2 ⟨hy, e6Cen_rootDiagAutHom_torV_mem hyl⟩
    have hsi : MulAut.conj s ∈ E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
      Subgroup.mem_inf.2 ⟨hs, ⟨s, rfl⟩⟩
    have hw1 : rootDiagAutHom Tag.E6 K (torV ω x) ≠ 1 := by
      intro h
      rw [← map_one (rootDiagAutHom Tag.E6 K), ← e6Cen_torV_zero (ω := ω)] at h
      exact hx0 (e6Cen_torV_injective h3 h1 (rootDiagAutHom_injective h))
    have huw : rootDiagAutHom Tag.E6 K (torV ω y) ∉
        Subgroup.zpowers (rootDiagAutHom Tag.E6 K (torV ω x)) := by
      intro hm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
      rw [← map_zpow] at hk
      have e := rootDiagAutHom_injective (τ := Tag.E6) (K := K) hk
      rcases e6Cen_torV_zpow h3 x k with h | h | h
      · exact hyx 0 (by rw [zero_smul]; exact e6Cen_torV_injective h3 h1 (e.symm.trans h))
      · exact hyx 1 (by rw [one_smul]; exact e6Cen_torV_injective h3 h1 (e.symm.trans h))
      · exact hyx 2 (by rw [two_smul]; exact e6Cen_torV_injective h3 h1 (e.symm.trans h))
    obtain ⟨i, j, hij⟩ := e6CenOA_eq_pow_mul_pow h9 hyi hxi (hE.2 _ hy) (hE.2 _ hx) hw1 huw hsi
    rw [← map_pow, ← map_pow, ← map_mul, ← e6PW_torV_smul h3, ← e6PW_torV_smul h3,
      ← e6PW_torV_add h3] at hij
    have hij' : i ≠ 0 ∨ j ≠ 0 := by
      by_contra hc'
      push Not at hc'
      obtain ⟨rfl, rfl⟩ := hc'
      refine hs1 (e6Cen_conj_injective hK4 ?_)
      rw [hij, zero_smul, zero_smul, add_zero, e6Cen_torV_zero, map_one, map_one]
    rw [e6Cen_coe_eq_of_conj_eq_rootDiag hK4 hij, e6PW_finrank_torV h3 h1,
      e6CenOA_kerCount_comb ha hb hc hd hij']
  · rcases h with h | h | h | h
    · exact (h30 x hx h).elim
    · exact (h30 y hy h).elim
    · exact (h30 _ hxy h).elim
    · exact (h30 _ hxyy h).elim
  · exact e6CenConcl_of_censusPat h3 h1 hx hy hxl hyl hcen

theorem e6Cen_OA [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    (hF : E6CenFrame e6CenOA E) : E6CenConcl K E := by
  have hK4 := e6Cen_four_le_card hK
  obtain ⟨hE, hEc, hED, hEi, -, -⟩ := id hcube
  obtain ⟨X, hXE, hX⟩ := hF.2 (gE6 0) (Subgroup.subset_closure (Set.mem_insert _ _))
  obtain ⟨Y, hYE, hY⟩ := hF.2 (gE6 1 * gE6 2)
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hc : ∀ V ∈ E, X * V = V * X := fun V hVE =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨X, hXE⟩ : E) ⟨V, hVE⟩)
  have hXi := e6Cen_inner_OA hK hX hY (hE.2 _ hXE) (hE.2 _ hYE) (hc Y hYE)
  have hZE : X * Y ∈ E := mul_mem hXE hYE
  have hZ : BmMono (X * Y) e6CenZ := by
    have h := hX.mul hY
    rw [← mul_assoc] at h
    exact h
  have hXI : gE6 0 ∈ e6CenImage E := mem_e6CenImage.2 ⟨X, hXE, hX⟩
  have hYI : gE6 1 * gE6 2 ∈ e6CenImage E := mem_e6CenImage.2 ⟨Y, hYE, hY⟩
  have hXI' : gE6 0 ∈ e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) :=
    mem_e6CenImage.2 ⟨X, Subgroup.mem_inf.2 ⟨hXE, hXi⟩, hX⟩
  obtain ⟨p, hp, hpX⟩ := e6Cen_exists_inner_notMem hE hEc hED hEi hXE
  obtain ⟨hpE, hpi⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨v, hv, hpv⟩ := hF.1 p hpE
  obtain ⟨k, l, -, hl, rfl⟩ := e6Cen_mem_closure_pair (e6CenImage_mul_comm hK4 hE hXI hYI)
    (e6CenImage_pow_three hK4 hE hXI) (e6CenImage_pow_three hK4 hE hYI) hv
  have hWE : p * (X ^ k)⁻¹ ∈ E := mul_mem hpE (inv_mem (pow_mem hXE k))
  have hWi : p * (X ^ k)⁻¹ ∈ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) :=
    mul_mem hpi (inv_mem (pow_mem hXi k))
  have hW : BmMono (p * (X ^ k)⁻¹) ((gE6 1 * gE6 2) ^ l) := by
    have h := hpv.mul (hX.pow k).inv
    rw [e6CenImage_mul_comm hK4 hE (pow_mem hXI k) (pow_mem hYI l), mul_inv_cancel_right] at h
    exact h
  have hl0 : l = 0 := by
    by_contra hl0
    have hYI' : gE6 1 * gE6 2 ∈
        e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) := by
      rcases (by omega : l = 1 ∨ l = 2) with rfl | rfl
      · rw [pow_one] at hW
        exact mem_e6CenImage.2 ⟨_, Subgroup.mem_inf.2 ⟨hWE, hWi⟩, hW⟩
      · have e : ((gE6 1 * gE6 2) ^ 2) ^ 2 = gE6 1 * gE6 2 := by
          rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ,
            e6CenImage_pow_three hK4 hE hYI, one_mul]
        have h2 := hW.pow 2
        rw [e] at h2
        exact mem_e6CenImage.2 ⟨_, Subgroup.mem_inf.2 ⟨pow_mem hWE 2, pow_mem hWi 2⟩, h2⟩
    refine hEi (e6Cen_le_innerAut_of_frame h3 h1 hE hF hZE hZ ?_)
    rintro _ (rfl | rfl)
    exacts [hXI', hYI']
  subst hl0
  rw [pow_zero] at hW
  obtain ⟨a, m, n, hD⟩ := e6Cen_diag_mem_frame h3 h1 hE hZE hZ hWE hW
  have hcD : X * rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a m n)) =
      rootDiagAutHom Tag.E6 K (torV ω (e6CenTz a m n)) * X := by
    rw [← hD]
    exact hc _ hWE
  obtain rfl : a = 0 := e6Cen_Tz_fix_g0 h3 h1 hX hcD
  have hmn : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hmn
    push Not at hmn
    obtain ⟨rfl, rfl⟩ := hmn
    rw [e6CenTz_zero, e6Cen_torV_zero, map_one, mul_inv_eq_one] at hD
    rw [hD] at hpX
    exact hpX (Subgroup.npow_mem_zpowers X k)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨y, hXy⟩ := cen_exists_exp (μ := wordE6G0) hX hg
  have hY' : BmMono Y ((coxeterSystem Tag.E6).wordProd (wordE6G1 ++ wordE6G2)) := by
    rw [CoxeterSystem.wordProd_append]
    exact hY
  obtain ⟨b', hYb⟩ := hY'.exists_eq_word
  have hX3 : (MulAut.conj (weylWordElt .E6 K wordE6G0) *
      rootDiagAutHom Tag.E6 K (fun j => g ^ y j)) ^ 3 = 1 := by
    rw [← hXy]
    exact hE.2 _ hXE
  have hcX := cen_cube_exp hK hg cen_smul_g0 (gE6_pow_three 0) hX3 3
  simp [bm_sum_six, cenTg0] at hcX
  obtain ⟨q, hq⟩ : ∃ q : ℤ, 3 * q = -2 * y 0 - y 2 := ⟨(-2 * y 0 - y 2) / 3, by omega⟩
  have hμ : (g ^ q) ^ 3 = (g ^ y 0)⁻¹ ^ 2 * (g ^ y 2)⁻¹ := by
    have e : (g ^ q) ^ 3 = g ^ (-2 * y 0 - y 2) := by
      rw [← hq, _root_.zpow_mul', zpow_ofNat]
    rw [e]
    group
  have hb45 : g ^ y 4 = g ^ y 5 := e6CenOA_b4_eq_b5 hXy hYb (hc Y hYE)
  obtain ⟨z, c, hzc, hrel, hc4, hc5⟩ :=
    e6CenOA_frame_step (exists_isPrimitiveRoot_three hK) (fun j => g ^ y j) hμ
  obtain ⟨u, hu⟩ : ∃ u : adjointGroup Tag.E6 K, (u : ModGL Tag.E6 K) = e6rhoA2₁ K z :=
    ⟨⟨_, e6CenOA_rho_mem z⟩, rfl⟩
  have hφ : MulAut.conj u ∈ e6Inndiag K := innerAut_le_e6Inndiag K ⟨u, rfl⟩
  have hεX : ∀ s : adjointGroup Tag.E6 K, ((X s : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (e6rhoA2₁ K signedCycSL * rootDiagUnit Tag.E6 (fun j => g ^ y j)) * s *
        (e6rhoA2₁ K signedCycSL * rootDiagUnit Tag.E6 (fun j => g ^ y j))⁻¹ := by
    intro s
    rw [hXy]
    change (weylWordElt .E6 K wordE6G0 : ModGL Tag.E6 K) *
      (rootDiagUnit Tag.E6 (fun j => g ^ y j) * s * (rootDiagUnit Tag.E6 (fun j => g ^ y j))⁻¹) *
        (weylWordElt .E6 K wordE6G0 : ModGL Tag.E6 K)⁻¹ = _
    rw [e6CenOA_coe_weylWordElt]
    group
  have hXc : MulAut.conj u * X * (MulAut.conj u)⁻¹ = rootDiagAutHom Tag.E6 K c := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    change _ = rootDiagUnit Tag.E6 c * (s : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 c)⁻¹
    rw [coe_conj_mul_mul_inv_apply u hεX, hu, hzc]
  have hD0 : MulAut.conj u * rootDiagAutHom Tag.E6 K (torV ω (e6CenTz 0 m n)) *
      (MulAut.conj u)⁻¹ = rootDiagAutHom Tag.E6 K (torV ω (e6CenTz 0 m n)) :=
    conj_mul_mul_inv_eq_self (ε := rootDiagAutHom Tag.E6 K (torV ω (e6CenTz 0 m n)))
      (F := rootDiagUnit Tag.E6 (torV ω (e6CenTz 0 m n))) u (fun _ => rfl)
      (by rw [hu]; exact e6CenOA_rho_commute_torV h3 h1 z m n)
  have hcube' := hcube.map hφ
  have hX'E : rootDiagAutHom Tag.E6 K c ∈ E.map (MulAut.congr (MulAut.conj u)).toMonoidHom :=
    ⟨X, hXE, by rw [congr_toMonoidHom_apply, hXc]⟩
  have hD0'E : rootDiagAutHom Tag.E6 K (torV ω (e6CenTz 0 m n)) ∈
      E.map (MulAut.congr (MulAut.conj u)).toMonoidHom :=
    ⟨_, hWE, by rw [congr_toMonoidHom_apply, hD, hD0]⟩
  obtain ⟨hE', -, -, -, -, -⟩ := id hcube'
  have hc3 : c ^ 3 = 1 := rootDiagAutHom_injective (τ := Tag.E6) (K := K)
    (show rootDiagAutHom Tag.E6 K (c ^ 3) = rootDiagAutHom Tag.E6 K 1 by
      rw [map_pow, hE'.2 _ hX'E, map_one])
  obtain ⟨f, rfl⟩ := e6PW_exists_torV h3 h1 fun i => congrFun hc3 i
  simp only [torV, Units.val_pow_eq_pow_val] at hrel
  obtain ⟨hf02, hf0⟩ := e6CenOA_trace_cases h3 h1 (ZMod.val_lt (f 2)) (ZMod.val_lt (f 0)) hrel
  have hprim : IsPrimitiveRoot ω 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact IsPrimitiveRoot.iff_orderOf.2 (orderOf_eq_prime h3 h1)
  have hf45 : f 4 = f 5 := ZMod.val_injective 3
    (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hc4.trans (hb45.trans hc5.symm)))
  have hf02' : f 0 = f 2 := ZMod.val_injective 3 hf02
  have hf0' : f 0 ≠ 0 := fun h => hf0 (by rw [h, ZMod.val_zero])
  have hyl : e6CenLam f = 0 := by
    have key : ∀ a b : ZMod 3, a + 2 * a + b + 2 * b = 0 := by decide
    show f 0 + 2 * f 2 + f 4 + 2 * f 5 = 0
    rw [← hf02', ← hf45]
    exact key (f 0) (f 4)
  have hx0 : e6CenTz 0 m n ≠ 0 := by
    have key : ∀ m n : ZMod 3, (m ≠ 0 ∨ n ≠ 0) → e6CenTz 0 m n ≠ 0 := by decide +kernel
    exact key m n hmn
  have hyx : ∀ k : ZMod 3, f ≠ k • e6CenTz 0 m n := by
    have key : ∀ k m n : ZMod 3, (k • e6CenTz 0 m n) 0 = 0 := by decide +kernel
    intro k h
    exact hf0' ((congrFun h 0).trans (key k m n))
  have hfv : f = e6ConjVec (f 0) (f 1) (f 0) (f 3) (f 4) (f 4) := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · exact hf02'.symm
    · rfl
    · rfl
    · exact hf45.symm
  have hx0v : e6CenTz 0 m n = e6ConjVec 0 m 0 n (2 * m) (2 * m) := by
    have key : ∀ m n : ZMod 3, e6CenTz 0 m n = e6ConjVec 0 m 0 n (2 * m) (2 * m) := by
      decide +kernel
    exact key m n
  have hpat : E6CenPlanePat (e6CenTz 0 m n) f := by
    rw [hfv, hx0v]
    exact e6Cen_OA_planePat (f 0) (f 1) (f 3) (f 4) m n hf0' hmn
  exact E6CenConcl.of_map hφ (e6CenOA_concl_of_planePat hK4 h3 h1 hcube' hD0'E hX'E
    (e6CenLam_Tz 0 m n) hyl hx0 hyx hpat)

end Census

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
