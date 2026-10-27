module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Blocks7
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin7
public import CFSG.Quasithin.Background.F918Z4c2TI
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Lin
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

open CFSG.LieType.SeitzGeneration HyperBlocks CFSG.Open
open CFSG.RankThree.PartOne.KCOrthogonal (glue glue_apply glue_mul glue_one restrictEquiv
  coe_restrictEquiv exists_coe_add_of_isCompl)
open Polynomial CFSG.LocalAnalysis.ComponentInitial
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n p : ℕ} {h : UnitaryFieldData 2 n K}
variable {B : V →ₛₗ[h.bar] V →ₗ[K] K}
variable (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]

section NormDet

variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem bar_det_mul_det_eq_one {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hBsym : B.IsSymm)
    (hBsep : B.SeparatingLeft) {g : W ≃ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y) :
    h.bar (LinearMap.det (g : W →ₗ[K] W)) * LinearMap.det (g : W →ₗ[K] W) = 1 := by
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBsym hBsep
  have hgram : ((LinearMap.toMatrix e e (g : W →ₗ[K] W)).map h.bar).transpose *
      LinearMap.toMatrix e e (g : W →ₗ[K] W) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.map_apply]
    have hsum : (∑ k, h.bar ((LinearMap.toMatrix e e (g : W →ₗ[K] W)) k i) *
        (LinearMap.toMatrix e e (g : W →ₗ[K] W)) k j) = B (g (e i)) (g (e j)) := by
      rw [sesq_eq_sum_repr (b := e) (B := B) he (g (e i)) (g (e j))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
      rfl
    rw [hsum, hg, he i j]
  have hmapdet : ((LinearMap.toMatrix e e (g : W →ₗ[K] W)).map h.bar).det =
      h.bar (LinearMap.toMatrix e e (g : W →ₗ[K] W)).det := by
    rw [show ((LinearMap.toMatrix e e (g : W →ₗ[K] W)).map h.bar) =
      h.bar.mapMatrix (LinearMap.toMatrix e e (g : W →ₗ[K] W)) from rfl, ← RingHom.map_det]
  have hdet := congrArg Matrix.det hgram
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, hmapdet] at hdet
  rw [← LinearMap.det_toMatrix e (g : W →ₗ[K] W)]
  exact hdet

theorem det_eq_one_of_pow_eq_one {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hBsym : B.IsSymm)
    (hBsep : B.SeparatingLeft) {g : W ≃ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y)
    (hp : p.Prime) (hgp : g ^ p = 1) (hpQ : ¬ p ∣ 2 ^ n + 1) :
    LinearMap.det (g : W →ₗ[K] W) = 1 := by
  set d : K := LinearMap.det (g : W →ₗ[K] W) with hd
  have hnorm := bar_det_mul_det_eq_one hBsym hBsep hg
  rw [UnitaryFieldData.bar_apply] at hnorm
  have hnorm' : d ^ (2 ^ n + 1) = 1 := by
    rw [pow_add, pow_one]
    exact hnorm
  have hdp : d ^ p = 1 := by
    have h1 : LinearMap.det ((↑g : W →ₗ[K] W) ^ p) = 1 := by
      rw [← LinearEquiv.toLinearMap_pow, hgp]
      simp
    rw [hd, ← MonoidHom.map_pow LinearMap.det]
    exact h1
  have hdvd : orderOf d ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hdp
  have hdvd2 : orderOf d ∣ 2 ^ n + 1 := orderOf_dvd_iff_pow_eq_one.mpr hnorm'
  have hgcd : orderOf d ∣ Nat.gcd p (2 ^ n + 1) := Nat.dvd_gcd hdvd hdvd2
  have hcop : Nat.Coprime p (2 ^ n + 1) := hp.coprime_iff_not_dvd.mpr hpQ
  rw [hcop] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)

end NormDet

private theorem det_glue {U W : Submodule K V} (hc : IsCompl U W) (a : U ≃ₗ[K] U)
    (b : W ≃ₗ[K] W) :
    LinearMap.det (glue hc a b : V →ₗ[K] V) =
      LinearMap.det (a : U →ₗ[K] U) * LinearMap.det (b : W →ₗ[K] W) := by
  simp only [← LinearEquiv.coe_det, LinEngine.det_glue hc a b, Units.val_mul]

theorem blockEnd_mem_sesqSpecialUnitaryGroupLE (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : InvariantSesq A B)
    (hBsym : B.IsSymm) (hBn : B.SeparatingLeft) (hpQ : ¬ p ∣ 2 ^ n + 1)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p) :
    blockEnd A hp hpF hA t ht D ∈ sesqSpecialUnitaryGroupLE B := by
  refine mem_sesqSpecialUnitaryGroupLE.mpr
    ⟨fun x y => blockEnd_sesq A hp hpF hA B hB t ht D x y, ?_⟩
  have h1 : ∀ u ∈ blockSpace A D.1, (t D : V ≃ₗ[K] V) u ∈ blockSpace A D.1 :=
    fun u hu => blockSpace_invariant A hp hpF hA hu
  have h2 : ∀ u ∈ blockSpace A D.1, (t D : V ≃ₗ[K] V).symm u ∈ blockSpace A D.1 :=
    fun u hu => blockSpace_invariant A hp hpF hA (a := (t D)⁻¹) hu
  have hrestr : ∀ u v : ↥(blockSpace A D.1),
      (B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1))
        (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2 u)
        (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2 v) =
      (B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1)) u v := by
    intro u v
    simp only [LinearMap.domRestrict₁₂_apply, coe_restrictEquiv]
    exact hB (t D) u.1 v.1
  have htDp : ((t D : V ≃ₗ[K] V) ^ p) = 1 := by
    rw [hA.2 (t D) (t D).2]
  have hpow : (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) ^ p = 1 := by
    ext u
    have hcoe : ∀ (m : ℕ) (x : ↥(blockSpace A D.1)),
        (((restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) ^ m) x : V) =
          ((t D : V ≃ₗ[K] V) ^ m) x := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
          intro x
          calc (((restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) ^ (m + 1)) x : V)
              = (((restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) ^ m)
                  (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2 x) : V) := by
                rw [pow_succ, LinearEquiv.mul_apply]
            _ = (((t D : V ≃ₗ[K] V) ^ m) ((t D : V ≃ₗ[K] V) x) : V) := by
                rw [ih, coe_restrictEquiv]
            _ = (((t D : V ≃ₗ[K] V) ^ (m + 1)) x : V) := by
                rw [pow_succ, LinearEquiv.mul_apply]
    rw [hcoe p u, htDp]
    rfl
  have hdetrestr := det_eq_one_of_pow_eq_one (h := h)
    (B := B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1))
    (hBsym.domRestrict _) (blockSpace_sesq_nondegenerate A hp hpF hA hB hBn D)
    (g := restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) hrestr hp hpow hpQ
  have hglue : ((blockEnd A hp hpF hA t ht D : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (glue (isCompl_blockSpace_ker A hp hpF hA D)
        (restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2) 1 : V ≃ₗ[K] V) := rfl
  rw [hglue, det_glue, hdetrestr]
  simp

theorem pointwiseStab_le_centralizer_blockEnd_sesq (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : InvariantSesq A B)
    (hrefl : B.IsRefl) (hBn : B.SeparatingLeft) {H : Subgroup (V ≃ₗ[K] V)}
    (hbH : ∀ g ∈ H, ∀ u v : V, B ((g : V ≃ₗ[K] V) u) ((g : V ≃ₗ[K] V) v) = B u v)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) (D : Hyperplane A p)
    (htH : blockEnd A hp hpF hA t ht D ∈ H) :
    pointwiseStab H (blockSpace A D.1) ≤
      Subgroup.centralizer ({(⟨blockEnd A hp hpF hA t ht D, htH⟩ : ↥H)} : Set ↥H) := by
  intro g hg
  have hgfix : ∀ u ∈ blockSpace A D.1, ((g : ↥H) : V ≃ₗ[K] V) u = u := mem_pointwiseStab.mp hg
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply]
  obtain ⟨u, r, -, rfl⟩ :=
    exists_coe_add_of_isCompl (isCompl_blockSpace_ker A hp hpF hA D) v
  have hr : (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    rw [LinearMap.mem_ker]; exact r.2
  have hgr : ((g : ↥H) : V ≃ₗ[K] V) (r : V) ∈ LinearMap.ker (projBlock A hp hpF hA D) := by
    have horth : ((g : ↥H) : V ≃ₗ[K] V) (r : V) ∈
        Submodule.orthogonalBilin B (blockSpace A D.1) := by
      rw [Submodule.mem_orthogonalBilin]
      intro u' hu'
      have h1 : ((g : ↥H) : V ≃ₗ[K] V) u' = u' := hgfix u' hu'
      calc B u' (((g : ↥H) : V ≃ₗ[K] V) (r : V))
          = B (((g : ↥H) : V ≃ₗ[K] V) u') (((g : ↥H) : V ≃ₗ[K] V) (r : V)) := by rw [h1]
        _ = B u' (r : V) := hbH _ g.2 u' (r : V)
        _ = 0 := blockSpace_ker_sesq_orthogonal A hp hpF hA B hB D hu' hr
    rwa [orthogonalBilin_blockSpace_eq_ker A hp hpF hA hB hrefl hBn D] at horth
  have hsum : ((g : ↥H) : V ≃ₗ[K] V) ((u : V) + (r : V)) =
      (u : V) + ((g : ↥H) : V ≃ₗ[K] V) (r : V) := by
    rw [map_add, hgfix (u : V) u.2]
  have hmem : ((t D : ↥A) : V ≃ₗ[K] V) (u : V) ∈ blockSpace A D.1 :=
    blockSpace_invariant A hp hpF hA u.2
  have LHS : (blockEnd A hp hpF hA t ht D)
      (((g : ↥H) : V ≃ₗ[K] V) ((u : V) + (r : V))) =
      ((t D : ↥A) : V ≃ₗ[K] V) (u : V) + ((g : ↥H) : V ≃ₗ[K] V) (r : V) := by
    rw [hsum, map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hgr]
  have RHS : ((g : ↥H) : V ≃ₗ[K] V)
      ((blockEnd A hp hpF hA t ht D) ((u : V) + (r : V))) =
      ((t D : ↥A) : V ≃ₗ[K] V) (u : V) + ((g : ↥H) : V ≃ₗ[K] V) (r : V) := by
    rw [map_add, blockEnd_apply_mem A hp hpF hA t ht D u.2,
      blockEnd_apply_of_ker A hp hpF hA t ht D hr, map_add, hgfix _ hmem]
  rw [LHS, RHS]

theorem ker_projBlock_eq_ker_blockEnd_sub_one (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) :
    LinearMap.ker (projBlock A hp hpF hA D) =
      LinearMap.ker ((blockEnd A hp hpF hA t ht D : V →ₗ[K] V) - 1) := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.sub_apply,
    show (1 : V →ₗ[K] V) v = v from rfl, sub_eq_zero]
  rw [show (blockEnd A hp hpF hA t ht D : V →ₗ[K] V) v =
    v + ((t D : V ≃ₗ[K] V) (projBlock A hp hpF hA D v) - projBlock A hp hpF hA D v) from
    blockEnd_apply_eq A hp hpF hA t ht D v]
  constructor
  · intro hv
    rw [hv]; simp
  · intro hv
    have h2 : (t D : V ≃ₗ[K] V) (projBlock A hp hpF hA D v) = projBlock A hp hpF hA D v := by
      have h3 : v + ((t D : V ≃ₗ[K] V) (projBlock A hp hpF hA D v) -
          projBlock A hp hpF hA D v) = v + 0 := by rw [add_zero]; exact hv
      exact sub_eq_zero.mp (add_left_cancel h3)
    have h4 : projBlock A hp hpF hA D v = 0 :=
      eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) (projBlock_apply_mem A hp hpF hA D v) h2
    exact h4

theorem centralizer_mapsTo_blockSpace (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    {D : Hyperplane A p} {g : V ≃ₗ[K] V}
    (hg : g * blockEnd A hp hpF hA t ht D = blockEnd A hp hpF hA t ht D * g)
    {v : V} (hv : v ∈ blockSpace A D.1) : g v ∈ blockSpace A D.1 := by
  rw [← LinEngine.range_blockEnd_sub_one A hp hpF hA t ht D] at hv ⊢
  obtain ⟨w, rfl⟩ := hv
  refine ⟨g w, ?_⟩
  have hgw : (blockEnd A hp hpF hA t ht D : V →ₗ[K] V) (g w) =
      g ((blockEnd A hp hpF hA t ht D : V →ₗ[K] V) w) := by
    have h := congrArg (fun e : V ≃ₗ[K] V => (e : V ≃ₗ[K] V) w) hg
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    exact h.symm
  rw [LinearMap.sub_apply, LinearMap.sub_apply, hgw, map_sub]
  rfl


theorem pointwiseStab_normal_in_centralizer [Finite K] (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (D : Hyperplane A p) (hbD : blockEnd A hp hpF hA t ht D ∈ sesqSpecialUnitaryGroupLE B) :
    ((pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)).subgroupOf
      (Subgroup.centralizer ({(⟨blockEnd A hp hpF hA t ht D, hbD⟩ :
        ↥(sesqSpecialUnitaryGroupLE B))} : Set ↥(sesqSpecialUnitaryGroupLE B)))).Normal := by
  refine pointwiseStab_normal (H := sesqSpecialUnitaryGroupLE B) (U := blockSpace A D.1) ?_
  intro g hg x hx
  have hcomm : ((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[K] V) *
      blockEnd A hp hpF hA t ht D =
      blockEnd A hp hpF hA t ht D * ((g : ↥(sesqSpecialUnitaryGroupLE B)) : V ≃ₗ[K] V) := by
    have h := Subgroup.mem_centralizer_iff.mp hg ⟨blockEnd A hp hpF hA t ht D, hbD⟩
      (Set.mem_singleton _)
    simpa using (congrArg Subtype.val h).symm
  exact centralizer_mapsTo_blockSpace A hp hpF hA t ht hcomm hx

theorem dvd_card_pointwiseStab_sesq [Finite K] (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1)
    (hbH : ∀ D, blockEnd A hp hpF hA t ht D ∈ sesqSpecialUnitaryGroupLE B)
    {D E : Hyperplane A p} (hDE : E ≠ D) (hE : blockSpace A E.1 ≠ ⊥) :
    p ∣ Nat.card (pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)) :=
  dvd_card_pointwiseStab A hp hpF hA t ht hbH hDE hE

theorem isQuasisimple_pointwiseStab_blockSpace_of_two_le (A : Subgroup (V ≃ₗ[K] V)) [Fintype A]
    (hp : p.Prime) (hpK : (p : K) ≠ 0) (hA : IsElemAbelian p A) (hB : InvariantSesq A B)
    (hBsym : B.IsSymm) (hBn : B.SeparatingLeft) (D : Hyperplane A p)
    (hdim : 2 ≤ Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1)))
    (hq2 : Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1)) = 2 → 4 ≤ 2 ^ n)
    (hq3 : Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1)) = 3 → 3 ≤ 2 ^ n) :
    CFSG.IsQuasisimple ↥(pointwiseStab (sesqSpecialUnitaryGroupLE B) (blockSpace A D.1)) := by
  have hW : (B.domRestrict₁₂ (Submodule.orthogonalBilin B (blockSpace A D.1))
      (Submodule.orthogonalBilin B (blockSpace A D.1))).SeparatingLeft :=
    separatingLeft_domRestrict_orthogonalBilin hBsym.isRefl hBn
      (isCompl_blockSpace_orthogonalBilin A hp hpK hA hB hBsym.isRefl hBn D)
  have hSU : CFSG.IsQuasisimple ↥(sesqSpecialUnitaryGroupLE (B.domRestrict₁₂
      (Submodule.orthogonalBilin B (blockSpace A D.1))
      (Submodule.orthogonalBilin B (blockSpace A D.1)))) := by
    rcases Nat.lt_or_ge (Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1))) 3
      with h2 | h3
    · obtain ⟨e2⟩ := sesqSpecialUnitaryGroupLE_mulEquiv (B := B.domRestrict₁₂
        (Submodule.orthogonalBilin B (blockSpace A D.1))
        (Submodule.orthogonalBilin B (blockSpace A D.1)))
      refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm ?_
      exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup h
        (hBsym.domRestrict _) hW (by omega) (hq2 (by omega))
    · obtain ⟨e2⟩ := sesqSpecialUnitaryGroupLE_mulEquiv (B := B.domRestrict₁₂
        (Submodule.orthogonalBilin B (blockSpace A D.1))
        (Submodule.orthogonalBilin B (blockSpace A D.1)))
      refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e2.symm ?_
      refine CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_sesqSpecialUnitaryGroup_of_three_le
        h (hBsym.domRestrict _) hW h3 ?_
      intro hcon
      have h1 : Module.finrank K (Submodule.orthogonalBilin B (blockSpace A D.1)) = 3 :=
        congrArg Prod.fst hcon
      have h2 : 2 ^ n = 2 := congrArg Prod.snd hcon
      rw [h1] at hq3
      have h3' := hq3 rfl
      omega
  obtain ⟨e⟩ := pointwiseStab_blockSpace_mulEquiv (A := A) (B := B) hp hpK hA hB hBsym.isRefl hBn D
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSU


section DimensionBound

variable {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

private theorem aeval_map_bar_pow (P : K[X]) (x : AlgebraicClosure K) :
    (Polynomial.aeval x (P.map h.bar)) ^ (2 ^ n) = Polynomial.aeval (x ^ (2 ^ n)) P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  haveI : CharP (AlgebraicClosure K) 2 := charP_of_injective_algebraMap
    (algebraMap K (AlgebraicClosure K)).injective 2
  induction P using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C, UnitaryFieldData.bar_apply,
        ← map_pow, ← pow_mul]
      rw [show 2 ^ n * 2 ^ n = Nat.card K from by rw [h.card]; ring]
      haveI : Finite K := h.finite
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
  | add p q hp hq =>
      rw [Polynomial.map_add, Polynomial.aeval_add, Polynomial.aeval_add, add_pow_char_pow, hp, hq]
  | monomial m a ih =>
      have hstep : Polynomial.C a * Polynomial.X ^ (m + 1) =
          (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [hstep, Polynomial.map_mul, Polynomial.map_X, Polynomial.aeval_mul, Polynomial.aeval_mul,
        mul_pow, ih, Polynomial.aeval_X, Polynomial.aeval_mul, Polynomial.aeval_X]

private theorem aeval_inv_pow_of_root {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hBsym : B.IsSymm)
    (hBsep : B.SeparatingLeft) {g : W ≃ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y)
    {x : AlgebraicClosure K} (hx0 : x ≠ 0)
    (hx : Polynomial.aeval x (LinearMap.charpoly (g : W →ₗ[K] W)) = 0) :
    Polynomial.aeval ((x⁻¹) ^ (2 ^ n)) (LinearMap.charpoly (g : W →ₗ[K] W)) = 0 := by
  classical
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hBsym hBsep
  set M : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K :=
    LinearMap.toMatrix e e (g : W →ₗ[K] W) with hM
  have hP : LinearMap.charpoly (g : W →ₗ[K] W) = M.charpoly := by
    rw [hM]
    exact (LinearMap.charpoly_toMatrix (g : W →ₗ[K] W) e).symm
  have hgram : (M.map h.bar).transpose * M = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.map_apply]
    have hsum : (∑ k, h.bar (M k i) * M k j) = B (g (e i)) (g (e j)) := by
      rw [sesq_eq_sum_repr (b := e) (B := B) he (g (e i)) (g (e j))]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hM, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
      rfl
    rw [hsum, hg, he i j]
  have hMinv : M⁻¹ = (M.map h.bar).transpose := Matrix.inv_eq_left_inv hgram
  have hchar : M⁻¹.charpoly = (M.charpoly).map h.bar := by
    rw [hMinv, Matrix.charpoly_transpose, Matrix.charpoly_map]
  have hx' : Polynomial.aeval x M.charpoly = 0 := by rw [← hP]; exact hx
  have hroot_inv : Polynomial.aeval x⁻¹ M⁻¹.charpoly = 0 := by
    have hunit : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det]
      have := congrArg Matrix.det hgram
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one_right _ this
    exact CFSG.Quasithin.Z4c2.aeval_inv_charpoly_inv M hunit hx0 hx'
  have hroot_map : Polynomial.aeval x⁻¹ ((M.charpoly).map h.bar) = 0 := by
    rw [← hchar]; exact hroot_inv
  have hpow := aeval_map_bar_pow (n := n) (h := h) M.charpoly x⁻¹
  rw [hroot_map, zero_pow (by positivity : (2 : ℕ) ^ n ≠ 0)] at hpow
  rw [hP]
  exact hpow.symm





private theorem exists_eigenvalue [Finite K] {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hBsym : B.IsSymm)
    (hBsep : B.SeparatingLeft) {g : W ≃ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y)
    (hp : p.Prime) (hp2 : p ≠ 2) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ ζ : AlgebraicClosure K, ζ ≠ 1 ∧ ζ ^ p = 1 ∧
      Polynomial.aeval ζ (LinearMap.charpoly (g : W →ₗ[K] W)) = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := h.charP
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hgp' : ((g : W →ₗ[K] W)) ^ p = 1 := by
    rw [← LinearEquiv.toLinearMap_pow, hgp]
    rfl
  set Φ : K[X] := ∑ i ∈ Finset.range p, (Polynomial.X : K[X]) ^ i with hΦdef
  have hΦA : Polynomial.aeval (g : W →ₗ[K] W) Φ * ((g : W →ₗ[K] W) - 1) = 0 := by
    have h := geom_sum_mul (g : W →ₗ[K] W) p
    rw [hgp', sub_self] at h
    simpa [hΦdef, map_sum] using h
  have hnc : ¬ IsCoprime Φ (LinearMap.charpoly (g : W →ₗ[K] W)) := by
    rintro ⟨u, v, huv⟩
    have h1 := congrArg (Polynomial.aeval (g : W →ₗ[K] W)) huv
    rw [map_add, map_mul, map_mul, LinearMap.aeval_self_charpoly, mul_zero, add_zero,
      map_one] at h1
    have h2 : (g : W →ₗ[K] W) - 1 = 0 := by
      calc (g : W →ₗ[K] W) - 1
          = (Polynomial.aeval (g : W →ₗ[K] W) u *
              Polynomial.aeval (g : W →ₗ[K] W) Φ) * ((g : W →ₗ[K] W) - 1) := by rw [h1, one_mul]
        _ = Polynomial.aeval (g : W →ₗ[K] W) u *
              (Polynomial.aeval (g : W →ₗ[K] W) Φ * ((g : W →ₗ[K] W) - 1)) := by rw [mul_assoc]
        _ = 0 := by rw [hΦA, mul_zero]
    exact hg1 (LinearEquiv.ext fun v => sub_eq_zero.mp (congrArg (fun f => f v) h2))
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K (AlgebraicClosure K)] at hnc
  push Not at hnc
  obtain ⟨ζ, hζΦ, hζχ⟩ := hnc
  have hζp : ζ ^ p = 1 := by
    have h := geom_sum_mul ζ p
    have hs : (∑ i ∈ Finset.range p, ζ ^ i) = 0 := by
      simpa [hΦdef, map_sum] using hζΦ
    rw [hs, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  refine ⟨ζ, ?_, hζp, hζχ⟩
  rintro rfl
  have hs : (∑ i ∈ Finset.range p, (1 : AlgebraicClosure K) ^ i) = 0 := by
    simpa [hΦdef, map_sum] using hζΦ
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  have hpL : ((p : ℕ) : AlgebraicClosure K) = 0 := by simpa using hs
  exact hpK ((algebraMap K (AlgebraicClosure K)).injective (by rw [map_natCast, hpL, map_zero]))

theorem orderOf_neg_le_finrank [Finite K] {B : W →ₛₗ[h.bar] W →ₗ[K] K} (hBsym : B.IsSymm)
    (hBsep : B.SeparatingLeft) {g : W ≃ₗ[K] W} (hg : ∀ x y, B (g x) (g y) = B x y)
    (hp : p.Prime) (hp2 : p ≠ 2) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    orderOf (-(2 ^ n : ZMod p)) ≤ Module.finrank K W := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ1, hζp, hroot⟩ := exists_eigenvalue hBsym hBsep hg hp hp2 hgp hg1
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hζp⟩
  have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ1
  set P : K[X] := LinearMap.charpoly (g : W →ₗ[K] W) with hP
  have hPne : P ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
  have hPdeg : P.natDegree = Module.finrank K W := LinearMap.charpoly_natDegree _
  have hstep : ∀ k : ℕ,
      ((ζ ^ (((-(2 ^ n) : ZMod p) ^ k).val))⁻¹) ^ (2 ^ n) =
        ζ ^ (((-(2 ^ n) : ZMod p) ^ (k + 1)).val) := by
    intro k
    set m := ((-(2 ^ n) : ZMod p) ^ k).val with hm
    have hinv : (ζ ^ (m * 2 ^ n))⁻¹ = ζ ^ ((m * 2 ^ n) * (p - 1)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add]
      have harith : m * 2 ^ n + (m * 2 ^ n) * (p - 1) = (m * 2 ^ n) * p := by
        nth_rewrite 2 [show p = (p - 1) + 1 from (Nat.sub_one_add_one hp.ne_zero).symm]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [harith, show (m * 2 ^ n) * p = p * (m * 2 ^ n) from Nat.mul_comm _ _, pow_mul, hζp,
        one_pow]
    have hmod : ((m * 2 ^ n) * (p - 1)) ≡ (((-(2 ^ n) : ZMod p) ^ (k + 1)).val) [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have h1 : (((m * 2 ^ n) * (p - 1) : ℕ) : ZMod p) = (-(2 ^ n) : ZMod p) ^ (k + 1) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, ZMod.natCast_self,
          ZMod.natCast_zmod_val, pow_succ']
        simp only [Nat.cast_pow]
        ring
      have h2 : ((((-(2 ^ n) : ZMod p) ^ (k + 1)).val : ℕ) : ZMod p) =
          (-(2 ^ n) : ZMod p) ^ (k + 1) := ZMod.natCast_zmod_val _
      rw [h1, h2]
    rw [inv_pow, ← pow_mul, hinv]
    exact (hfin.pow_eq_pow_iff_modEq).mpr (by rwa [hord])
  set S : Finset (ZMod p) := Finset.univ.filter (fun a => Polynomial.aeval (ζ ^ a.val) P = 0)
    with hS
  have hmemS : ∀ a : ZMod p, a ∈ S ↔ Polynomial.aeval (ζ ^ a.val) P = 0 := by
    intro a
    rw [hS, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩
  have hS_card : S.card ≤ P.natDegree := by
    calc S.card = (Finset.image (fun a : ZMod p => ζ ^ a.val) S).card := by
          rw [Finset.card_image_of_injOn]
          intro a _ b _ hab
          have h1 : a.val ≡ b.val [MOD p] := by
            have h2 := (hfin.pow_eq_pow_iff_modEq).mp hab
            rwa [hord] at h2
          have h3 : a.val = b.val := h1.eq_of_lt_of_lt (ZMod.val_lt a) (ZMod.val_lt b)
          exact ZMod.val_injective p h3
      _ ≤ (P.aroots (AlgebraicClosure K)).toFinset.card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
          rw [Multiset.mem_toFinset, Polynomial.mem_aroots]
          exact ⟨hPne, (hmemS a).mp ha⟩
      _ ≤ Multiset.card (P.aroots (AlgebraicClosure K)) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots_map_le_natDegree _
  have hT : ∀ k : ℕ, Polynomial.aeval (ζ ^ (((-(2 ^ n) : ZMod p) ^ k).val)) P = 0 := by
    intro k
    induction k with
    | zero =>
        have h1 : ((-(2 ^ n) : ZMod p) ^ 0) = 1 := pow_zero _
        rw [h1]
        haveI : Fact (1 < p) := ⟨hp.one_lt⟩
        rw [ZMod.val_one p]
        simpa using hroot
    | succ k ih =>
        rw [← hstep k]
        exact aeval_inv_pow_of_root hBsym hBsep hg (pow_ne_zero _ hζ0) ih
  have hT_sub : (Finset.image (fun k => (-(2 ^ n) : ZMod p) ^ k)
      (Finset.range (orderOf (-(2 ^ n) : ZMod p)))) ⊆ S := by
    intro a ha
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
    exact (hmemS _).mpr (hT k)
  have hinjT : Set.InjOn (fun k => (-(2 ^ n) : ZMod p) ^ k)
      ↑(Finset.range (orderOf (-(2 ^ n) : ZMod p))) := by
    intro i hi j hj hij
    exact pow_injOn_Iio_orderOf (by simpa using hi) (by simpa using hj) hij
  have hcard : (Finset.image (fun k => (-(2 ^ n) : ZMod p) ^ k)
      (Finset.range (orderOf (-(2 ^ n) : ZMod p)))).card = orderOf (-(2 ^ n) : ZMod p) :=
    (Finset.card_image_of_injOn hinjT).trans (Finset.card_range _)
  calc orderOf (-(2 ^ n : ZMod p))
      = (Finset.image (fun k => (-(2 ^ n) : ZMod p) ^ k)
          (Finset.range (orderOf (-(2 ^ n : ZMod p))))).card := hcard.symm
    _ ≤ S.card := Finset.card_le_card hT_sub
    _ ≤ P.natDegree := hS_card
    _ = Module.finrank K W := hPdeg


theorem orderOf_neg_le_finrank_blockSpace [Finite K] (hp : p.Prime) (hpF : (p : K) ≠ 0)
    (hA : IsElemAbelian p A) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : InvariantSesq A B)
    (hBsym : B.IsSymm) (hBn : B.SeparatingLeft) (hp2 : p ≠ 2)
    (t : Hyperplane A p → ↥A) (ht : ∀ D, t D ∉ D.1) {D : Hyperplane A p}
    (hD : blockSpace A D.1 ≠ ⊥) :
    orderOf (-(2 ^ n : ZMod p)) ≤ Module.finrank K (blockSpace A D.1) := by
  have h1 : ∀ u ∈ blockSpace A D.1, (t D : V ≃ₗ[K] V) u ∈ blockSpace A D.1 :=
    fun u hu => blockSpace_invariant A hp hpF hA hu
  have h2 : ∀ u ∈ blockSpace A D.1, (t D : V ≃ₗ[K] V).symm u ∈ blockSpace A D.1 :=
    fun u hu => blockSpace_invariant A hp hpF hA (a := (t D)⁻¹) hu
  set gg : ↥(blockSpace A D.1) ≃ₗ[K] ↥(blockSpace A D.1) :=
    restrictEquiv (blockSpace A D.1) (t D : V ≃ₗ[K] V) h1 h2 with hgg
  have hrestr : ∀ u v : ↥(blockSpace A D.1),
      (B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1)) (gg u) (gg v) =
        (B.domRestrict₁₂ (blockSpace A D.1) (blockSpace A D.1)) u v := by
    intro u v
    simp only [hgg, LinearMap.domRestrict₁₂_apply, coe_restrictEquiv]
    exact hB (t D) u.1 v.1
  have htDp : ((t D : V ≃ₗ[K] V) ^ p) = 1 := by
    rw [hA.2 (t D) (t D).2]
  have hpow : gg ^ p = 1 := by
    ext u
    have hcoe : ∀ (m : ℕ) (x : ↥(blockSpace A D.1)),
        (((gg ^ m) x : ↥(blockSpace A D.1)) : V) = ((t D : V ≃ₗ[K] V) ^ m) x := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
          intro x
          calc (((gg ^ (m + 1)) x : ↥(blockSpace A D.1)) : V)
              = (((gg ^ m) (gg x) : ↥(blockSpace A D.1)) : V) := by
                rw [pow_succ, LinearEquiv.mul_apply]
            _ = (((t D : V ≃ₗ[K] V) ^ m) ((t D : V ≃ₗ[K] V) x) : V) := by
                rw [ih, hgg, coe_restrictEquiv]
            _ = (((t D : V ≃ₗ[K] V) ^ (m + 1)) x : V) := by
                rw [pow_succ, LinearEquiv.mul_apply]
    rw [hcoe p u, htDp]
    rfl
  have hgne : gg ≠ 1 := by
    intro h
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have hfix : (t D : V ≃ₗ[K] V) v = v := by
      have h1 := congrArg (fun e : ↥(blockSpace A D.1) ≃ₗ[K] ↥(blockSpace A D.1) =>
        ((e ⟨v, hv⟩ : ↥(blockSpace A D.1)) : V)) h
      simpa [hgg, coe_restrictEquiv] using h1
    exact hv0 (eq_zero_of_fixed_mem_blockSpace A hp hpF hA (ht D) hv hfix)
  exact orderOf_neg_le_finrank (n := n) (h := h) (B := B.domRestrict₁₂
    (blockSpace A D.1) (blockSpace A D.1)) (hBsym.domRestrict _)
    (blockSpace_sesq_nondegenerate A hp hpF hA hB hBn D) hrestr hp hp2 hpow hgne

end DimensionBound

end CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
