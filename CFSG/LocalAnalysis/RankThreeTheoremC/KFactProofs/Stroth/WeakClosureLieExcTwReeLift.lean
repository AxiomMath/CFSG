module

public import CFSG.RankThree.PartOne.KLR.TwistPerm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNGenFix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwAct

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4 CFSG.RankThree.PartOne.KLR
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix)

open scoped commutatorElement Matrix

section Det

theorem det_one_sub_smul_ne_zero_of_pow_eq_smul {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℤ) {n : ℕ}
    (hn : n ≠ 0) {c : ℤ} (hY : Y ^ n = c • (1 : Matrix (Fin r) (Fin r) ℤ)) {θ : ℤ}
    (hθ : θ ^ n * c ≠ 1) : (1 - θ • Y).det ≠ 0 := by
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_eq_zero] at hv
  have iter : ∀ j : ℕ, v = (θ ^ j) • ((Y ^ j) *ᵥ v) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc v = (θ ^ j) • ((Y ^ j) *ᵥ v) := ih
        _ = (θ ^ j) • ((Y ^ j) *ᵥ (θ • (Y *ᵥ v))) := by rw [← hv]
        _ = (θ ^ (j + 1)) • ((Y ^ (j + 1)) *ᵥ v) := by
          rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ, smul_smul, ← pow_succ]
  have h1 := iter n
  rw [hY, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv0
  have h2 : v i = (θ ^ n * c) * v i := by
    conv_lhs => rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h3 : (θ ^ n * c - 1) * v i = 0 := by linarith
  rcases mul_eq_zero.1 h3 with h | h
  · exact hθ (by linarith)
  · exact hi h

end Det

section Matrix

@[expose] def reeB : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ :=
  Matrix.of fun i k => if i = ReeTag.F4.perm k then ((ReeTag.F4.relationExponent 0 i : ℕ) : ℤ) else 0

theorem relationExponent_eq_two_pow_mul (a : ℕ) (j : Fin ReeTag.F4.tag.rank) :
    ((ReeTag.F4.relationExponent a j : ℕ) : ℤ) = 2 ^ a * ((ReeTag.F4.relationExponent 0 j : ℕ) : ℤ) := by
  by_cases hj : j ∈ ReeTag.F4.longSet
  · rw [relExp_long a j hj, relExp_long 0 j hj]
    push_cast
    ring
  · rw [relExp_short a j hj, relExp_short 0 j hj]
    push_cast
    ring

variable {L : Type} [Field L] {a : ℕ}

theorem reeTuple_eq_zpowMatrix [CharP L 2] (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    reeTuple a b = zpowMatrix ((2 ^ a : ℤ) • reeB) b := by
  funext k
  rw [zpowMatrix_apply, Finset.prod_eq_single (ReeTag.F4.perm k)]
  · simp only [reeTuple, reeB, Matrix.smul_apply, Matrix.of_apply, if_true, smul_eq_mul]
    rw [← zpow_natCast, ← relationExponent_eq_two_pow_mul]
  · intro i _ hi
    simp [reeB, hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem weylTuple_reeTuple [CharP L 2] (w : WeylGroup ReeTag.F4.tag)
    (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    weylTuple w (reeTuple a b) = zpowMatrix ((2 ^ a : ℤ) • (reeB * weylMat w⁻¹)) b := by
  rw [weylTuple_eq_zpowMatrix, reeTuple_eq_zpowMatrix, zpowMatrix_zpowMatrix, Matrix.smul_mul]

end Matrix

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_reeFrob_correction (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag)
    (hdet : (1 - (2 ^ a : ℤ) • (reeB * weylMat w⁻¹)).det ≠ 0)
    (b : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ c : Fin ReeTag.F4.tag.rank → Lˣ, rootDiagUnit ReeTag.F4.tag c *
      (canonicalRep (coxeterSystem ReeTag.F4.tag) L w * Fext F (rootDiagUnit ReeTag.F4.tag c) *
        (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)⁻¹)⁻¹ = rootDiagUnit ReeTag.F4.tag b := by
  obtain ⟨c, hc⟩ := exists_zpowMatrix_eq _ hdet b
  refine ⟨c, ?_⟩
  rw [hF.fext_rootDiagUnit c, canonicalRep_conj_rootDiagUnit, rootDiagUnit_inv,
    ← rootDiagUnit_mul]
  congr 1
  rw [← hc, zpowMatrix_sub, CFSG.Timmesfeld.ExceptionalOrders.zpowMatrix_one, weylTuple_reeTuple]

theorem exists_reeFrob_lift (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag)
    (hdet : (1 - (2 ^ a : ℤ) • (reeB * weylMat w⁻¹)).det ≠ 0) {u : WeylGroup ReeTag.F4.tag}
    (hu : w * ReeTag.F4.weylPerm u = u * w) :
    ∃ y : ModGL ReeTag.F4.tag L, y ∈ monomialSubgroup ReeTag.F4.tag L ∧
      y ∈ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧ TwActsAs y u := by
  set n₀ := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn₀
  set nu := canonicalRep (coxeterSystem ReeTag.F4.tag) L u with hnu
  set nσ := canonicalRep (coxeterSystem ReeTag.F4.tag) L (ReeTag.F4.weylPerm u) with hnσ
  have hFu : Fext F nu = nσ := hF.fext_canonicalRep u
  set s : ModGL ReeTag.F4.tag L := n₀ * nσ * n₀⁻¹ * nu⁻¹ with hs
  have hsm : s ∈ monomialSubgroup ReeTag.F4.tag L := by
    rw [hs]
    exact mul_mem (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup L w)
      (canonicalRep_mem_monomialSubgroup L _)) (inv_mem (canonicalRep_mem_monomialSubgroup L w)))
      (inv_mem (canonicalRep_mem_monomialSubgroup L u))
  have hs1 : MapsRootLines s 1 := by
    have h := (((mapsRootLines_canonicalRep (R := L) w).mul
      (mapsRootLines_canonicalRep (R := L) (ReeTag.F4.weylPerm u))).mul
        (mapsRootLines_canonicalRep (R := L) w).inv).mul
      (mapsRootLines_canonicalRep (R := L) u).inv
    have e : w * ReeTag.F4.weylPerm u * w⁻¹ * u⁻¹ = 1 := by
      rw [hu, mul_inv_cancel_right, mul_inv_cancel]
    rw [e] at h
    rw [hs]
    exact h
  have hstor : s ∈ torusGroup ReeTag.F4.tag L :=
    CFSG.LieType.Chevalley.mem_torusGroup_of_mapsRootLines_one hsm hs1
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hstor
  obtain ⟨c, hc⟩ := exists_reeFrob_correction hF w hdet a'
  rw [← ha'] at hc
  have hTadj : rootDiagUnit ReeTag.F4.tag c ∈ adjointGroup ReeTag.F4.tag L :=
    torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup c)
  have hnuadj : nu ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L u
  have hF' : n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹ ∈ torusGroup ReeTag.F4.tag L := by
    rw [hF.fext_rootDiagUnit c, canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm := torusGroup_mul_comm (rootDiagUnit_mem_torusGroup c) (inv_mem hF')
  have hfix : n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c * nu) * n₀⁻¹ =
      rootDiagUnit ReeTag.F4.tag c * nu := by
    rw [Fext_mul F hTadj hnuadj, hFu]
    have e1 : n₀ * (Fext F (rootDiagUnit ReeTag.F4.tag c) * nσ) * n₀⁻¹ =
        (n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹) * (n₀ * nσ * n₀⁻¹ * nu⁻¹) * nu := by
      group
    rw [e1, ← hs]
    congr 1
    rw [← hc]
    calc (n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹) *
          (rootDiagUnit ReeTag.F4.tag c * (n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹)⁻¹)
        = (n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹) *
          ((n₀ * Fext F (rootDiagUnit ReeTag.F4.tag c) * n₀⁻¹)⁻¹ * rootDiagUnit ReeTag.F4.tag c) := by
          rw [hcomm]
      _ = rootDiagUnit ReeTag.F4.tag c := by group
  have hmon : rootDiagUnit ReeTag.F4.tag c * nu ∈ monomialSubgroup ReeTag.F4.tag L :=
    mul_mem (torusGroup_le_monomialSubgroup' (rootDiagUnit_mem_torusGroup c))
      (canonicalRep_mem_monomialSubgroup L u)
  exact ⟨rootDiagUnit ReeTag.F4.tag c * nu, hmon,
    ⟨monomialSubgroup_le_adjointGroup' hmon, hfix⟩,
    (twActsAs_canonicalRep u).torus_mul (rootDiagUnit_mem_torusGroup c)⟩

end Lang

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
