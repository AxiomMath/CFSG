module

public import CFSG.LargeExtraspecial.S4TwoPSL
public import CFSG.CGT.Timmesfeld75.StdPair
public import CFSG.Open.StatedAPI
public import CFSG.Open.StatedDefs
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S4FiveApp
public import CFSG.LargeExtraspecial.S4FiveRad
public import CFSG.LargeExtraspecial.S4OmegaTau
public import CFSG.LargeExtraspecial.S4SevenInput
public import CFSG.LargeExtraspecial.S4Three
public import CFSG.LargeExtraspecial.S4TwoA
public import CFSG.LargeExtraspecial.S4TwoInput
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.ClassicalGroups.Linear.Model

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

@[expose] def cg (n : ℕ) (K : Type) [Field K] (c : Fin n → K) :
    Subgroup (StatedProj (StatedSL n K)) :=
  transvImage n K (transvCenter n K c)

theorem apply_eq_dotProduct {n : ℕ} {K : Type} [Field K] (f : Module.Dual K (Fin n → K))
    (y : Fin n → K) : f y = (fun i => f (Pi.single i 1)) ⬝ᵥ y := by
  conv_lhs => rw [pi_eq_sum_univ y]
  rw [map_sum]
  simp only [dotProduct, map_smul, smul_eq_mul, mul_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem exists_vec_of_notMem {n : ℕ} {K : Type} [Field K] {p : Submodule K (Fin n → K)}
    {x : Fin n → K} (hx : x ∉ p) : ∃ a : Fin n → K, a ⬝ᵥ x = 1 ∧ ∀ y ∈ p, a ⬝ᵥ y = 0 := by
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hfp' : ∀ y ∈ p, f y = 0 := fun y hy => by
    have h : f y ∈ p.map f := Submodule.mem_map_of_mem hy
    rw [hfp, Submodule.mem_bot] at h
    exact h
  refine ⟨(f x)⁻¹ • (fun i => f (Pi.single i 1)), ?_, fun y hy => ?_⟩
  · rw [smul_dotProduct, ← apply_eq_dotProduct, smul_eq_mul, inv_mul_cancel₀ hfx]
  · rw [smul_dotProduct, ← apply_eq_dotProduct, hfp' y hy, smul_zero]

theorem conjSubgroup_cg (n : ℕ) (K : Type) [Field K] (c : Fin n → K) (g : StatedSL n K) :
    conjSubgroup (psl n K g) (cg n K c) =
      cg n K ((((g : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ c) := by
  unfold cg
  apply le_antisymm
  · intro x hx
    obtain ⟨Y, rfl⟩ : ∃ Y : StatedSL n K, psl n K Y = x := QuotientGroup.mk'_surjective _ x
    rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have hzx' : psl n K z = (psl n K g)⁻¹ * psl n K Y * psl n K g := hzx
    have hgz : psl n K (g * z * g⁻¹) = psl n K Y := by
      simp only [map_mul, map_inv, hzx']
      group
    rw [← hgz]
    obtain ⟨a, ha, hza⟩ := Subgroup.mem_subgroupOf.mp hz
    refine Subgroup.mem_map.mpr ⟨g * z * g⁻¹, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    refine ⟨a ᵥ* ((((g : GL (Fin n) K))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ?_, ?_⟩
    · rw [dotProduct_mulVec, vecMul_inv_vecMul]
      exact ha
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hza]
      exact conj_one_add_vecMulVec (g : GL (Fin n) K) c a
  · intro x hx
    obtain ⟨Y, hY, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, hYb⟩ := Subgroup.mem_subgroupOf.mp hY
    refine mem_conjSubgroup_transvImage (A := g) (Y := Y) (U := transvCenter n K c) ?_
    refine ⟨b ᵥ* ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ?_, ?_⟩
    · rw [← dotProduct_mulVec]
      exact hb
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hYb]
      exact inv_mul_one_add_vecMulVec_mul (g : GL (Fin n) K) c b

theorem mem_transvCenter_iff' {n : ℕ} {K : Type} [Field K] {c : Fin n → K}
    {g : GL (Fin n) K} :
    g ∈ transvCenter n K c ↔
      ∃ a : Fin n → K, a ⬝ᵥ c = 0 ∧ (g : Matrix (Fin n) (Fin n) K) = 1 + vecMulVec c a :=
  Iff.rfl

theorem psl_transvSL_mem_cg {n : ℕ} {K : Type} [Field K] {c a : Fin n → K}
    (ha : a ⬝ᵥ c = 0) :
    psl n K (transvSL ha) ∈ cg n K c := by
  unfold cg transvImage
  exact Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr (mem_transvCenter_iff'.mpr ⟨a, ha, coe_transvSL ha⟩))

theorem eq_smul_of_cg_eq (n : ℕ) (K : Type) [Field K] (hn : 3 ≤ n) (c c' : Fin n → K)
    (hc : c ≠ 0) (h : cg n K c = cg n K c') : ∃ μ : K, c' = μ • c := by
  obtain ⟨a, ha, hac, -⟩ := exists_ne_zero_dotProduct_eq_zero hn c c
  have hmem : psl n K (transvSL hac) ∈ cg n K c' := by
    rw [← h]
    exact psl_transvSL_mem_cg hac
  obtain ⟨Y, hY, hYX⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨b, -, hYb⟩ := mem_transvCenter_iff'.mp (Subgroup.mem_subgroupOf.mp hY)
  obtain ⟨u, hu⟩ :=
    (StatedAPI.statedProj_mk_eq_iff (StatedSL n K) Y (transvSL hac)).mp hYX
  have hscal : (1 + vecMulVec c a : Matrix (Fin n) (Fin n) K) =
      (u : K) • (1 + vecMulVec c' b) := by
    rw [← coe_transvSL hac, hu, Matrix.mul_smul, Matrix.mul_one, hYb]
  obtain ⟨w, hw0, hwa, hwb⟩ := exists_ne_zero_dotProduct_eq_zero hn a b
  have hw : (1 + vecMulVec c a : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
    rw [one_add_vecMulVec_mulVec, dotProduct_comm, hwa, zero_smul, add_zero]
  have hw' : (1 + vecMulVec c' b : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
    rw [one_add_vecMulVec_mulVec, dotProduct_comm, hwb, zero_smul, add_zero]
  have hsmul : (u : K) • w = w := by
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ w) hscal
    simp only [hw, Matrix.smul_mulVec, hw'] at h2
    exact h2.symm
  have hu1 : (u : K) = 1 := by
    have h3 : ((u : K) - 1) • w = 0 := by
      rw [sub_smul, one_smul, hsmul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hw0
  have hvv : vecMulVec c a = vecMulVec c' b := by
    rw [hu1, one_smul] at hscal
    exact add_left_cancel hscal
  have hentry : ∀ i j, c i * a j = c' i * b j := fun i j => by
    have h5 := congrFun (congrFun hvv i) j
    rwa [vecMulVec_apply, vecMulVec_apply] at h5
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hi' : c i ≠ 0 := hi
  have hj' : a j ≠ 0 := hj
  have hbj : b j ≠ 0 := by
    intro hb0
    apply mul_ne_zero hi' hj'
    rw [hentry i j, hb0, mul_zero]
  refine ⟨a j * (b j)⁻¹, funext fun k => ?_⟩
  have hk := hentry k j
  simp only [Pi.smul_apply, smul_eq_mul]
  calc c' k = c' k * b j * (b j)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hbj, mul_one]
    _ = c k * a j * (b j)⁻¹ := by rw [hk]
    _ = a j * (b j)⁻¹ * c k := by ring

@[expose] def planeStab (n : ℕ) (K : Type) [Field K] (Pl : Submodule K (Fin n → K)) :
    Subgroup (StatedProj (StatedSL n K)) where
  carrier := {x | ∃ g : StatedSL n K, psl n K g = x ∧
    ∀ v ∈ Pl, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Pl ∧
      (((g⁻¹ : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Pl}
  one_mem' := ⟨1, map_one (psl n K), fun v hv => by simp [hv]⟩
  mul_mem' := by
    rintro _ _ ⟨g, rfl, hg⟩ ⟨h, rfl, hh⟩
    refine ⟨g * h, map_mul (psl n K) g h, fun v hv => ⟨?_, ?_⟩⟩
    · rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
      exact (hg _ (hh v hv).1).1
    · rw [_root_.mul_inv_rev, Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
      exact (hh _ (hg v hv).2).2
  inv_mem' := by
    rintro _ ⟨g, rfl, hg⟩
    refine ⟨g⁻¹, map_inv (psl n K) g, fun v hv => ⟨(hg v hv).2, ?_⟩⟩
    rw [inv_inv]
    exact (hg v hv).1

theorem mulVec_mem_of_transvCenter {n : ℕ} {K : Type} [Field K] {c : Fin n → K}
    {Pl : Submodule K (Fin n → K)} (hc : c ∈ Pl) {h : GL (Fin n) K}
    (hh : h ∈ transvCenter n K c) {v : Fin n → K} (hv : v ∈ Pl) :
    (h : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ Pl := by
  obtain ⟨a, _, ha⟩ := hh
  rw [ha, one_add_vecMulVec_mulVec]
  exact Submodule.add_mem _ hv (Submodule.smul_mem _ _ hc)

theorem scalar_mulVec_aux {n : ℕ} {K : Type} [Field K] (u : Units K) (c : Fin n → K) :
    ((GeneralLinearGroup.scalar (Fin n) u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c =
      (u : K) • c := by
  rw [GeneralLinearGroup.coe_scalar]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem cg_le_planeStab (n : ℕ) (K : Type) [Field K] (Pl : Submodule K (Fin n → K))
    {c : Fin n → K} (hc : c ∈ Pl) : cg n K c ≤ planeStab n K Pl := by
  intro x hx
  unfold cg transvImage at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hy' : ((y : StatedSL n K) : GL (Fin n) K) ∈ transvCenter n K c :=
    Subgroup.mem_subgroupOf.mp hy
  refine ⟨y, rfl, fun v hv => ⟨mulVec_mem_of_transvCenter hc hy' hv, ?_⟩⟩
  have hi : ((y⁻¹ : StatedSL n K) : GL (Fin n) K) ∈ transvCenter n K c := by
    rw [Subgroup.coe_inv]
    exact (transvCenter n K c).inv_mem hy'
  exact mulVec_mem_of_transvCenter hc hi hv

theorem planeStab_ne_top (n : ℕ) (K : Type) [Field K] (Pl : Submodule K (Fin n → K))
    (h1 : Pl ≠ ⊥) (h2 : Pl ≠ ⊤) : planeStab n K Pl ≠ ⊤ := by
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
  obtain ⟨e, he⟩ : ∃ e : Fin n → K, e ∉ Pl := by
    by_contra h
    exact h2 (Submodule.eq_top_iff'.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  have hce : c ∉ Submodule.span K {e} := by
    intro hmem
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    have hr0 : r ≠ 0 := fun h0 => hc0 (by rw [← hr, h0, zero_smul])
    apply he
    have hee : e = r⁻¹ • c := by rw [← hr, smul_smul, inv_mul_cancel₀ hr0, one_smul]
    rw [hee]
    exact Submodule.smul_mem Pl r⁻¹ hc
  obtain ⟨a, hac, hae⟩ := exists_vec_of_notMem hce
  have hae' : a ⬝ᵥ e = 0 := hae e (Submodule.mem_span_singleton_self e)
  obtain ⟨T, hT⟩ : ∃ T : StatedSL n K, T = transvSL hae' := ⟨_, rfl⟩
  have hTc : (((T : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c + e := by
    rw [hT, coe_transvSL, one_add_vecMulVec_mulVec, hac, one_smul]
  intro htop
  have hmem : psl n K T ∈ planeStab n K Pl := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg, hgP⟩ := hmem
  have h3 : g⁻¹ * T ∈ (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
    QuotientGroup.eq.mp hg
  have h4 := Subgroup.mem_subgroupOf.mp h3
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at h4
  obtain ⟨u, hu⟩ := h4
  have hT' : ((T : StatedSL n K) : GL (Fin n) K) =
      ((g : StatedSL n K) : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) u := by
    rw [hu, mul_inv_cancel_left]
  have hTm : (((T : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c =
      (((g : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((u : K) • c) := by
    rw [hT', Units.val_mul, ← mulVec_mulVec, scalar_mulVec_aux]
  have hcePl : c + e ∈ Pl := by
    rw [← hTc, hTm]
    exact (hgP _ (Submodule.smul_mem Pl (u : K) hc)).1
  exact he (by simpa using Submodule.sub_mem Pl hcePl hc)

end CFSG.ClassicalGroups.Linear.Model
