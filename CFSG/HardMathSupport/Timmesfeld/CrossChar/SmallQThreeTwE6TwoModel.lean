module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwo
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyStep

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false

section W0

theorem e6RhoFour_eq_twistPerm : e6RhoFour = TwistTag.E6.perm := by
  ext i
  fin_cases i <;> rfl

theorem twistPerm_symm_E6 : TwistTag.E6.perm.symm = TwistTag.E6.perm := by
  ext i
  fin_cases i <;> rfl

theorem twistPerm_symm_symm_apply_E6 (i : Fin TwistTag.E6.tag.rank) :
    TwistTag.E6.perm.symm (TwistTag.E6.perm.symm i) = i := by
  rw [twistPerm_symm_E6]
  fin_cases i <;> rfl

noncomputable abbrev twE6W0 : WeylGroup TwistTag.E6.tag := e6W0Four

theorem twE6W0_smul (z : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6W0 • z = -(permLattice TwistTag.E6.perm z) := by
  have h := e6W0Four_smul z
  rw [e6RhoFour_eq_twistPerm] at h
  exact h

theorem permLattice_twistPerm_twistPerm (z : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm z) = z := by
  have h := permLattice_symm_permLattice TwistTag.E6.perm z
  rwa [twistPerm_symm_E6] at h

theorem twE6W0_smul_permLattice (z : Fin TwistTag.E6.tag.rank → ℤ) :
    twE6W0 • permLattice TwistTag.E6.perm z = -z := by
  rw [twE6W0_smul, permLattice_twistPerm_twistPerm]

theorem twE6W0_smul_smul (z : Fin TwistTag.E6.tag.rank → ℤ) : twE6W0 • twE6W0 • z = z := by
  rw [twE6W0_smul z, smul_neg, twE6W0_smul_permLattice, neg_neg]

theorem twE6W0_inv_smul (z : Fin TwistTag.E6.tag.rank → ℤ) : twE6W0⁻¹ • z = twE6W0 • z := by
  rw [inv_smul_eq_iff, twE6W0_smul_smul]

end W0

section Step

variable {L : Type} [Field L]

theorem twE6Two_twFrob_rootDiagUnit {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 2)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr
        (rootDiagUnit TwistTag.E6.tag a) = (rootDiagUnit TwistTag.E6.tag a)⁻¹ ^ 2 := by
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twFrob_rootDiagUnit, rootDiagUnit_inv,
    rootDiagUnit_pow]
  congr 1
  funext i
  have hi : (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      permLattice TwistTag.E6.perm (Pi.single (TwistTag.E6.perm.symm i) 1) := by
    rw [permLattice_single, Equiv.apply_symm_apply]
  rw [weylTuple, twE6W0_inv_smul, hi, twE6W0_smul_permLattice, rootChar_neg_vec_E6Four,
    rootChar, Finset.prod_eq_single (TwistTag.E6.perm.symm i) (fun j _ hj => by
      rw [Pi.single_eq_of_ne hj, zpow_zero]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Pi.single_eq_same, zpow_one]
  ext1
  simp [hFr, Pi.pow_apply, twistPerm_symm_symm_apply_E6]

theorem exists_twE6Two_twFrob_rootSL2 (Fr : L →+* L) {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) :
    ∃ μ : Lˣ, ∀ A : SL2 L,
      twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr
          (rootSL2 TwistTag.E6.tag L α A) =
        rootSL2 TwistTag.E6.tag L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
          (Matrix.SpecialLinearGroup.map Fr A)) := by
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.twFrob_rootSL2 TwistTag.E6
    (canonicalRep_mem_monomialSubgroup L twE6W0) Fr hα
  have hw : weylQuotientHom TwistTag.E6.tag L
      ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0,
        canonicalRep_mem_monomialSubgroup L twE6W0⟩ = twE6W0 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.KGD.exists_rootSL2_neg_eq (L := L) hα
  refine ⟨a * s, fun A => ?_⟩
  rw [hs, hw, twE6W0_smul_permLattice, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]

end Step

noncomputable abbrev twE6TwoF
    (L : Type) [Field L] [CharP L 2] : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0)
    (iterateFrobenius L 2 1)

@[expose] noncomputable def twE6TwoModel
    (L : Type) [Field L] [CharP L 2] : Subgroup (ModGL Tag.E6 L) :=
  fixModel (twE6TwoF L)

section Model

variable {L : Type} [Field L] [CharP L 2]

theorem twE6TwoF_rootDiagUnit (a : Fin Tag.E6.rank → Lˣ) :
    twE6TwoF L (rootDiagUnit Tag.E6 a) = (rootDiagUnit Tag.E6 a)⁻¹ ^ 2 :=
  twE6Two_twFrob_rootDiagUnit iterateFrobenius_two_one a

theorem exists_twE6TwoF_rootSL2 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ μ : Lˣ, ∀ A : SL2 L, twE6TwoF L (rootSL2 Tag.E6 L α A) =
      rootSL2 Tag.E6 L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)) :=
  exists_twE6Two_twFrob_rootSL2 (iterateFrobenius L 2 1) hα

theorem twE6Two_dV_mem_model [IsAlgClosed L] {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (x : Fin Tag.E6.rank → ZMod 3) : dV ω x ∈ twE6TwoModel L := by
  refine ⟨torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _), ?_⟩
  change twE6TwoF L (rootDiagUnit Tag.E6 (torV ω x)) = dV ω x
  rw [twE6TwoF_rootDiagUnit]
  have h3 := dV_pow_three (τ := Tag.E6) hω3 x
  change (dV ω x)⁻¹ ^ 2 = dV ω x
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ', h3])

theorem twE6Two_rootSL2_HSL_mem_model {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) {ζ : Lˣ}
    (hζ : ζ ^ 3 = 1) : rootSL2 Tag.E6 L α (HSL ζ) ∈ twE6TwoModel L := by
  obtain ⟨μ, hμ⟩ := exists_twE6TwoF_rootSL2 (L := L) hα
  refine ⟨rootSpan_le_adjointGroup L {α, -α} (rootSL2_mem_rootSpan_pair hα _), ?_⟩
  change twE6TwoF L (rootSL2 Tag.E6 L α (HSL ζ)) = rootSL2 Tag.E6 L α (HSL ζ)
  rw [hμ, twFix_HSL μ hζ]

theorem exists_twE6Two_rootSL2_nSL_mem_model [IsAlgClosed L] {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) : ∃ c : Lˣ, rootSL2 Tag.E6 L α (nSL c) ∈ twE6TwoModel L := by
  obtain ⟨μ, hμ⟩ := exists_twE6TwoF_rootSL2 (L := L) hα
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-((μ⁻¹ : Lˣ) : L)) (n := 3) (by norm_num)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num), zero_eq_neg] at hz
    exact Units.ne_zero _ hz
  set c : Lˣ := Units.mk0 z hz0 with hc
  refine ⟨c, rootSpan_le_adjointGroup L {α, -α} (rootSL2_mem_rootSpan_pair hα _), ?_⟩
  change twE6TwoF L (rootSL2 Tag.E6 L α (nSL c)) = rootSL2 Tag.E6 L α (nSL c)
  rw [hμ, map_nSL, conjSL_swap_nSL]
  have hc3 : (c : L) ^ 3 = -((μ⁻¹ : Lˣ) : L) := by rw [hc, Units.val_mk0, hz]
  suffices h : -(μ * Units.map (iterateFrobenius L 2 1).toMonoidHom c)⁻¹ = c by rw [h]
  ext1
  rw [Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mul, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, iterateFrobenius_two_one]
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  have hcz : (c : L) ≠ 0 := Units.ne_zero c
  rw [Units.val_inv_eq_inv_val] at hc3
  have hc3' : (μ : L) * (c : L) ^ 3 = -1 := by rw [hc3, mul_neg, mul_inv_cancel₀ hμ0]
  field_simp
  linear_combination -hc3'

theorem twE6Two_rootSL2_HSL_mem_commutator [IsAlgClosed L] {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) {ζ : Lˣ} (hζ : ζ ^ 3 = 1) :
    rootSL2 Tag.E6 L α (HSL ζ) ∈ ⁅twE6TwoModel L, twE6TwoModel L⁆ := by
  obtain ⟨c, hc⟩ := exists_twE6Two_rootSL2_nSL_mem_model (L := L) hα
  have hζ2 : (ζ ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h1 := Subgroup.commutator_mem_commutator (twE6Two_rootSL2_HSL_mem_model hα hζ2) hc
  have hn0 : ((nSL c : SL2 L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 := rfl
  have hn1 : ((nSL c : SL2 L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 := rfl
  have h4 : (ζ ^ 2) ^ 2 = ζ := by
    rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hζ, one_mul]
  rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    HSL_conj_antidiag (ζ ^ 2) hn0 hn1, h4] at h1
  exact h1

theorem twE6Two_torusElt_eq_rootSL2 (i : Fin Tag.E6.rank) (u : Lˣ) :
    torusElt Tag.E6 L i u = rootSL2 Tag.E6 L (Pi.single i 1) (HSL u) := by
  rw [← Hel_root_eq_rootSL2 (Or.inr (Or.inl rfl)) (isRoot_single _ i), torusElt_eq_rootDiagUnit]
  unfold Hel
  congr 1
  funext j
  simp only [Hchar]
  congr 1
  rw [iform_single_left, symmetrizer_eq_one_of_simplyLaced (Or.inr (Or.inl rfl)), one_mul,
    Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, mul_one]

theorem twE6Two_dV_e6InnerVec_mem_commutator [IsAlgClosed L] {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (i : Fin 5) : dV ω (e6InnerVec i) ∈ ⁅twE6TwoModel L, twE6TwoModel L⁆ := by
  rw [dV_e6InnerVec hω3 i, twE6Two_torusElt_eq_rootSL2]
  exact twE6Two_rootSL2_HSL_mem_commutator (isRoot_single _ _) hω3

end Model

section Transport

variable {K : Type} [Field K] [CharP K 2]

theorem exists_twE6Two_lang (K : Type) [Field K] [CharP K 2] :
    ∃ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) ∧
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact lang_conjugator_twisted K (ℓ := 2) (f := 1) le_rfl (AlgebraicClosure K) twE6W0

noncomputable def twE6TwoEquiv (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0) :
    twistedE6RootGroup K σ ≃*
      ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))) :=
  twistedE6EquivΓ (ℓ := 2) (f := 1) Nat.prime_two le_rfl (by rw [hK]; norm_num)
    (fun c => by rw [hσ]; norm_num) (fun c => by rw [iterateFrobenius_two_one]; norm_num)
    (LangDatum.ofTwist TwistTag.E6 (iterateFrobenius (AlgebraicClosure K) 2 1) 2
      iterateFrobenius_two_one twE6W0 hg0C hg0) rfl

theorem coe_twE6TwoEquiv (hK : Nat.card K = 4) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2)
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K)
      (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0)
    (h : twistedE6RootGroup K σ) :
    (((twE6TwoEquiv hK σ hσ hg0C hg0 h : ↥(⁅twE6TwoModel (AlgebraicClosure K),
        twE6TwoModel (AlgebraicClosure K)⁆ : Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) :
          ModGL Tag.E6 (AlgebraicClosure K)) : ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL TwistTag.E6.tag K) * g0 :=
  coe_twistedE6EquivΓ (ℓ := 2) (f := 1) Nat.prime_two le_rfl (by rw [hK]; norm_num)
    (fun c => by rw [hσ]; norm_num) (fun c => by rw [iterateFrobenius_two_one]; norm_num)
    (LangDatum.ofTwist TwistTag.E6 (iterateFrobenius (AlgebraicClosure K) 2 1) 2
      iterateFrobenius_two_one twE6W0 hg0C hg0) rfl h

end Transport

@[expose] def TwE6TwoRigid :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ ω : (AlgebraicClosure K)ˣ, orderOf ω = 3 → ∀ y : Fin 5 → ZMod 3, y ≠ 0 →
    ∀ t : twistedE6RootGroup K σ,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL TwistTag.E6.tag K) =
        g0 * dV (τ := TwistTag.E6.tag) ω (subLin (τ := TwistTag.E6.tag) e6InnerVec y) * g0⁻¹ →
    ∀ α : MulAut (twistedE6RootGroup K σ), Nat.Coprime 3 (orderOf α) →
      (∀ z ∈ Subgroup.centralizer {t}, α z = z) →
        α ∈ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut (twistedE6RootGroup K σ)

@[expose] def TwE6TwoFusion : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 4 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
    ∀ g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K),
      g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) twE6W0 →
    ∀ ω : (AlgebraicClosure K)ˣ, orderOf ω = 3 →
    ∀ s ∈ (⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))), s ^ 3 = 1 →
      ∃ m ∈ twE6TwoModel (AlgebraicClosure K), ∃ y : Fin 5 → ZMod 3,
        m * s * m⁻¹ = dV (τ := .E6) ω (subLin (τ := .E6) e6InnerVec y)

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

end
