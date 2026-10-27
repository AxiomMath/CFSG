module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriD4Lab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.D4Outer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxD4Three
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GTri

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

section D4Fix


theorem triD4_graph (hRig : GGLabelRigidInput) {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {g : adjointGroup Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ} {ε : ℕ}
    (hε : ε = 1 ∨ ε = 2) {α' : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α' ^ 3 = 1)
    (hα' : α' = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))
    {X : Type} [Group X] [Finite X] {C J : Subgroup X} (e : ↥C ≃* ↥(fixSubgroup α'))
    (hJ : GLAPComponent 3 C J) {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) : (canonLabel labJ).n = n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₃, _, _, Fr, hK₃, hFr, φ, hφ3, hφout, ⟨eD⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual.exists_dual_fixEquiv (ℓ := 2) (f := n) (by omega) K hK α' hα3 g a hε hα'
  exact triOuter_canon_n hRig hn hK₃ Fr hFr φ hφ3 hφout (e.trans eD) hJ hlabJ

theorem triD4_graphField (hRig : GGLabelRigidInput) {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) {g : adjointGroup Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K}
    {ε : ℕ} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hε : ε = 1 ∨ ε = 2)
    {α' : MulAut ↥(adjointGroup Tag.D4 K)} (hα3 : α' ^ 3 = 1)
    (hα' : α' = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε))
    {X : Type} [Group X] [Finite X] {C J : Subgroup X} (e : ↥C ≃* ↥(fixSubgroup α'))
    (hJ : GLAPComponent 3 C J) {labJ : GLALabel}
    (hlabJ : HasLabel ↥J (fun l : GLALabel => l = labJ)) :
    ∃ m : ℕ, 1 ≤ m ∧ n = m * 3 ∧ canonLabel labJ = ⟨.triD4, 0, m⟩ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar2 : CharP K 2 := CFSG.StandardType.charP_two_of_card hK
  obtain ⟨ℓ, m, T, hℓ, hcharℓ, hm, hKℓ, hT, hσT⟩ := exists_frobenius_data_D4 σ hσ1 hσ3
  obtain rfl : ℓ = 2 := CharP.eq K hcharℓ hchar2
  have hnm : n = m * 3 :=
    Nat.pow_right_injective (le_refl 2) (show 2 ^ n = 2 ^ (m * 3) by rw [← hK, hKℓ])
  have hK3 : Nat.card K = (2 ^ m) ^ 3 := by rw [hK, hnm, pow_mul]
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK, hnm]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨m, hm, hnm, ?_⟩
  have hfixeq : ∀ φ : MulAut ↥(adjointGroup Tag.D4 K), fixSubgroup φ =
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup φ :=
    fun φ => Subgroup.ext fun _ => Iff.rfl
  rcases hσT with hσT | hσT
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 hm hnm.symm σ hT α'
      hα3 g a ε hα'
    have eF : ↥(fixSubgroup α') ≃* ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (ε : ℤ) σ)) :=
      (fixSubgroupConjEquiv ψ α').trans (MulEquiv.subgroupCongr (congrArg fixSubgroup hψ))
    have hj : (ε : ℤ) % 3 = 1 ∨ (ε : ℤ) % 3 = 2 := by omega
    obtain ⟨eG⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_fixedSubgroup_twistedEntrywiseAut_D4_equiv_graphFixed
      (ℓ := 2) (e := m) Nat.prime_two hm hK3 σ hT (ε : ℤ) hj
    exact triCanon_triD4 hRig hm hK3 σ hT
      (e.trans (eF.trans ((MulEquiv.subgroupCongr (hfixeq _)).trans eG))) hJ hlabJ
  · subst hσT
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 hm hnm.symm T T⁻¹
      hT (mul_inv_cancel T) α' hα3 g a ε hα'
    have eF : ↥(fixSubgroup α') ≃* ↥(fixSubgroup (twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T)) :=
      (MulEquiv.subgroupCongr
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_inv_eq α').symm).trans
        ((fixSubgroupConjEquiv ψ α'⁻¹).trans (MulEquiv.subgroupCongr (congrArg fixSubgroup hψ)))
    have hj : (-(ε : ℤ)) % 3 = 1 ∨ (-(ε : ℤ)) % 3 = 2 := by omega
    obtain ⟨eG⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_fixedSubgroup_twistedEntrywiseAut_D4_equiv_graphFixed
      (ℓ := 2) (e := m) Nat.prime_two hm hK3 T hT (-(ε : ℤ)) hj
    exact triCanon_triD4 hRig hm hK3 T hT
      (e.trans (eF.trans ((MulEquiv.subgroupCongr (hfixeq _)).trans eG))) hJ hlabJ

end D4Fix

end CFSG.LocalAnalysis.GLTheoremA.Y10GTri
