module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineSplit

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.SeitzPlane
  CFSG.HardMathSupport.Lang.TwE6Step3 CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
open scoped Matrix

set_option linter.unusedSectionVars false

section Comp

variable
  {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem twLine_weyl_smul_neg (w : WeylGroup Tag.E6) (x : Fin Tag.E6.rank → ℤ) :
    w • (-x) = -(w • x) := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_neg, weylMatrix_mulVec]

theorem twLine_tw6W_conj_tw6Delta {w : WeylGroup Tag.E6} (h : w * e6T3W = e6T3W * w) :
    tw6W * tw6Delta w * tw6W⁻¹ = w := by
  rw [mul_inv_eq_iff_eq_mul]
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul]
  conv_lhs => rw [← permLattice_e6Rho_e6Rho (Pi.single i 1)]
  rw [weylTwist_E6_smul_permLattice,
    tw6W_smul (permLattice e6Rho (w • permLattice e6Rho (Pi.single i 1))),
    permLattice_e6Rho_e6Rho, tw6W_smul (Pi.single i 1), twLine_weyl_smul_neg, ← mul_smul,
    ← mul_smul, h]

theorem twLine_tw6Theta_canonicalRep (w : WeylGroup Tag.E6) :
    tw6Theta Ω Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) =
      tw6N Ω * canonicalRep (coxeterSystem Tag.E6) Ω (tw6Delta w) * (tw6N Ω)⁻¹ := by
  have h1 : twistE6 Ω Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) =
      canonicalRep (coxeterSystem Tag.E6) Ω (tw6Delta w) :=
    twistHom_canonicalRep TwistTag.E6 Ω Fr w
  rw [tw6Theta_apply, h1]

theorem twLine_mapsRootLines_tw6Theta_canonicalRep (w : WeylGroup Tag.E6) :
    MapsRootLines (tw6Theta Ω Fr (canonicalRep (coxeterSystem Tag.E6) Ω w))
      (tw6W * tw6Delta w * tw6W⁻¹) := by
  rw [twLine_tw6Theta_canonicalRep]
  exact ((mapsRootLines_canonicalRep (R := Ω) tw6W).mul (mapsRootLines_canonicalRep _)).mul
    (mapsRootLines_canonicalRep (R := Ω) tw6W).inv

theorem twLine_tw6Theta_canonicalRep_mem_monomial (w : WeylGroup Tag.E6) :
    tw6Theta Ω Fr (canonicalRep (coxeterSystem Tag.E6) Ω w) ∈ monomialSubgroup Tag.E6 Ω := by
  rw [twLine_tw6Theta_canonicalRep]
  exact mul_mem (mul_mem (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _)
    (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _))
    (inv_mem (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _))

theorem twLine_tw6Theta_monomial [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ monomialSubgroup Tag.E6 Ω) {w : WeylGroup Tag.E6}
    (hw : MapsRootLines g w) :
    tw6Theta Ω Fr g ∈ monomialSubgroup Tag.E6 Ω ∧
      MapsRootLines (tw6Theta Ω Fr g) (tw6W * tw6Delta w * tw6W⁻¹) := by
  obtain ⟨w', k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines (k * canonicalRep (coxeterSystem Tag.E6) Ω w') w' := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w')
  have hww : w' = w := MapsRootLines.unique hmaps hw
  subst hww
  have hk' := tw6Theta_mem_torusGroup hFr hk
  rw [map_mul]
  refine ⟨mul_mem (Subgroup.mem_sup_left hk') (twLine_tw6Theta_canonicalRep_mem_monomial _), ?_⟩
  simpa using (mapsRootLines_of_mem_torusGroup hk').mul
    (twLine_mapsRootLines_tw6Theta_canonicalRep (Fr := Fr) w')

theorem twLine_list_prod_mem_monomial (l : List (Fin Tag.E6.rank)) :
    (l.map fun i => weylElt Tag.E6 Ω i 1).prod ∈ monomialSubgroup Tag.E6 Ω := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, rfl⟩)

theorem twLine_exists_fixed_of_lift [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) {S : Set (Fin Tag.E6.rank → ℤ)} (hSr : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hSu : ∀ α ∈ S, e6T3W • α ∈ S) (hSn : ∀ α ∈ S, -(e6T3W • α) ∈ S) {x : WeylGroup Tag.E6}
    {J : Set (Fin Tag.E6.rank)} (hx : (x • ·) '' S = parabolicRoots Tag.E6 J)
    {w : WeylGroup Tag.E6} (hw : w * e6T3W = e6T3W * w) {m : ModGL Tag.E6 Ω}
    (hm : m ∈ rootSpan Tag.E6 Ω S) (hmono : m ∈ monomialSubgroup Tag.E6 Ω)
    (hmaps : MapsRootLines m w) :
    ∃ n ∈ rootSpan Tag.E6 Ω S, tw6Theta Ω Fr n = n ∧ n ∈ monomialSubgroup Tag.E6 Ω ∧
      MapsRootLines n w := by
  obtain ⟨hθmono, hθmaps⟩ := twLine_tw6Theta_monomial hFr hmono hmaps
  rw [twLine_tw6W_conj_tw6Delta hw] at hθmaps
  have hzH : m⁻¹ * tw6Theta Ω Fr m ∈ torusGroup Tag.E6 Ω := by
    refine CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one
      (mul_mem (inv_mem hmono) hθmono) ?_
    have h := hmaps.inv.mul hθmaps
    rwa [inv_mul_cancel] at h
  have hzS : m⁻¹ * tw6Theta Ω Fr m ∈ rootSpan Tag.E6 Ω S :=
    mul_mem (inv_mem hm) (tw6Theta_mem_rootSpan hSr hSn hm)
  obtain ⟨t, ht, hte⟩ := twLine_lang hq hFr hSr hSu hx _
    (Subgroup.mem_inf.2 ⟨inv_mem hzH, inv_mem hzS⟩)
  obtain ⟨htH, htS⟩ := Subgroup.mem_inf.1 ht
  refine ⟨m * t, mul_mem hm htS, ?_, mul_mem hmono (Subgroup.mem_sup_left htH), ?_⟩
  · have hθt : tw6Theta Ω Fr t = t * (m⁻¹ * tw6Theta Ω Fr m)⁻¹ := by
      rw [← hte]
      group
    have hcomm := twLine_torusGroup_comm t htH _ hzH
    rw [map_mul, hθt]
    calc tw6Theta Ω Fr m * (t * (m⁻¹ * tw6Theta Ω Fr m)⁻¹) =
        m * ((m⁻¹ * tw6Theta Ω Fr m) * t) * (m⁻¹ * tw6Theta Ω Fr m)⁻¹ := by group
      _ = m * (t * (m⁻¹ * tw6Theta Ω Fr m)) * (m⁻¹ * tw6Theta Ω Fr m)⁻¹ := by rw [← hcomm]
      _ = m * t := by group
  · have h := hmaps.mul (mapsRootLines_of_mem_torusGroup htH)
    rwa [mul_one] at h

theorem twLine_rot_mem (j : Fin 2) :
    ((twLineRWord j).map fun i => weylElt Tag.E6 Ω i 1).prod ∈
      rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 support13) := by
  have hi : ∀ i ∈ twLineRWord j, i = 0 ∨ i = 2 := by
    fin_cases j <;> decide
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, hi', rfl⟩ := List.mem_map.1 hg
  obtain ⟨h1, h2⟩ := single_mem_parabolicRoots_support13 (hi i hi')
  exact twLine_weylElt_mem_rootSpan h1 h2 1

theorem twLine_exists_fixed_rot [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (j : Fin 2) :
    ∃ n ∈ rootSpan Tag.E6 Ω (twLineDS j), tw6Theta Ω Fr n = n ∧
      n ∈ monomialSubgroup Tag.E6 Ω ∧ MapsRootLines n (twLineCW j) := by
  have hm : (canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j))⁻¹ *
      ((twLineRWord j).map fun i => weylElt Tag.E6 Ω i 1).prod *
        canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j) ∈ rootSpan Tag.E6 Ω (twLineDS j) :=
    twLine_inv_conj_mem_rootSpan_of_image (fun α hα => twLineDS_root hα) (twLineDS_conj j)
      (twLine_rot_mem j)
  have hmono : (canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j))⁻¹ *
      ((twLineRWord j).map fun i => weylElt Tag.E6 Ω i 1).prod *
        canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j) ∈ monomialSubgroup Tag.E6 Ω :=
    mul_mem (mul_mem (inv_mem (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _))
      (twLine_list_prod_mem_monomial _))
      (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _)
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j))⁻¹ *
      ((twLineRWord j).map fun i => weylElt Tag.E6 Ω i 1).prod *
        canonicalRep (coxeterSystem Tag.E6) Ω (twLineXW j)) (twLineCW j) := by
    have h := ((mapsRootLines_canonicalRep (R := Ω) (twLineXW j)).inv.mul
      (mapsRootLines_list_prod (R := Ω) (twLineRWord j))).mul
        (mapsRootLines_canonicalRep (R := Ω) (twLineXW j))
    rwa [← twLineCW_eq] at h
  exact twLine_exists_fixed_of_lift hq hFr (fun α hα => twLineDS_root hα)
    (fun α hα => twLineDS_stable hα) (fun α hα => twLineDS_neg_stable hα) (twLineDS_conj j)
    (twLineCW_comm j) hm hmono hmaps

theorem twLine_exists_fixed_comp [IsAlgClosed Ω] {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) :
    ∃ n₀ ∈ rootSpan Tag.E6 Ω (twLineDS 0), tw6Theta Ω Fr n₀ = n₀ ∧
      ∃ n₁ ∈ rootSpan Tag.E6 Ω (twLineDS 1), tw6Theta Ω Fr n₁ = n₁ ∧
        ∃ t ∈ torusGroup Tag.E6 Ω,
          n₀ * n₁ = canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl * t := by
  obtain ⟨n₀, h₀, hθ₀, hm₀, hl₀⟩ := twLine_exists_fixed_rot hq hFr 0
  obtain ⟨n₁, h₁, hθ₁, hm₁, hl₁⟩ := twLine_exists_fixed_rot hq hFr 1
  refine ⟨n₀, h₀, hθ₀, n₁, h₁, hθ₁,
    (canonicalRep (coxeterSystem Tag.E6) Ω twLineWeyl)⁻¹ * (n₀ * n₁), ?_, by group⟩
  refine CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one
    (mul_mem (inv_mem (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup Ω _))
      (mul_mem hm₀ hm₁)) ?_
  have h := (mapsRootLines_canonicalRep (R := Ω) twLineWeyl).inv.mul (hl₀.mul hl₁)
  rwa [twLineCW_mul, inv_mul_cancel] at h

end Comp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
