module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLSL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLLU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCaseLUMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsDiag
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Foundations
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsProp65
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped IsMulCommutative

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_caseL_lin_of_lu
    (hLU : ∀ {n : ℕ}, 5 ≤ n → ∀ {K : Type} [Field K] [Finite K] {τ : K →+* K},
      p.Prime → ∀ [S.Normal], IsElemAbelian p B → p ^ 4 ≤ Nat.card B →
      Nat.card ↥(B ⊓ centModSubgroup p S) = p → GLAPPrimeCore p ↥S = ⊥ →
      (2 : K) ≠ 0 → (p : K) ≠ 0 →
      ∀ {H : Subgroup (GL (Fin n) K)} {β : (Fin n → K) →ₗ[K] (Fin n → K) →ₛₗ[τ] K},
      H ≤ isomGL β → (β = 0 ∨ β.SeparatingLeft) →
      (∀ g ∈ isomGL β, (g : Matrix (Fin n) (Fin n) K).det = 1 → g ∈ H) →
      (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧
        Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β) →
      ∀ {Qbig : Prop}, Qbig →
      (∀ U W : Submodule K (Fin n → K), IsCompl U W →
        (∀ u ∈ U, ∀ w ∈ W, β u w = 0 ∧ β w u = 0) →
        (β = 0 ∨ ∀ u ∈ U, (∀ u' ∈ U, β u u' = 0) → u = 0) →
        (3 ≤ Module.finrank K U ∨ (Module.finrank K U = 2 ∧ Qbig)) →
        blkI β U W ≤ H ∧ CFSG.Open.IsQuasisimple ↥(blkI β U W) ∧
        (∀ x ∈ blkSub β U W, orderOf x = p → p ∣ Nat.card ↥(blkI β U W)) ∧
        (∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → (∀ j ∈ blkI β U W, y * j = j * y) →
          ∃ c : K, ∀ u ∈ U, glEquiv y u = c • u) ∧
        (∀ (A : GL (Fin n) K) (σ : K ≃+* K), orderOf σ = p →
          (∀ u ∈ U, ModelGen.semiMap A σ u ∈ U) →
          ∀ y : GL (Fin n) K, (∀ u ∈ U, glEquiv y u ∈ U) → ∀ k : ℕ, 0 < k → k < p →
            ¬ ∀ j ∈ blkI β U W, y * (ModelGen.semiConj A σ ^ k) j * y⁻¹ = j)) →
      (∀ (Aε : Subgroup (GL (Fin n) K)) [IsMulCommutative Aε], (∀ a : ↥Aε, a ^ p = 1) →
        Aε ≤ isomGL β → IsMaxElem β (glRep Aε) p ∅ →
        (∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧
          Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ isomGL β) →
        ∀ H' : Hyperplane ↥Aε p, weightSpace (glRep Aε) H'.1 ≠ ⊥ →
          Module.finrank K (weightSpace (glRep Aε) H'.1) = 1) →
      ∀ (φ : ↥H →* Ω), φ.range = S → φ.ker ≤ (StatedScalars (Fin n) K).subgroupOf H →
      ∀ {B₁ : Subgroup Ω} (θ : ↥B₁ →* GL (Fin n) K), B₁ ≤ B →
      B ⊓ Subgroup.centralizer (S : Set Ω) ≤ B₁ →
      θ.range ≤ isomGL β → IsElemAbelian p θ.range →
      θ.range ⊓ StatedScalars (Fin n) K = ⊥ →
      (∀ x : ↥B₁, θ x = 1 ↔ (x : Ω) ∈ Subgroup.centralizer (S : Set Ω)) →
      (∀ (x : ↥B₁) (k : ↥H), ∃ k' : ↥H,
        (k' : GL (Fin n) K) = θ x * k * (θ x)⁻¹ ∧ φ k' = x * φ k * x⁻¹) →
      p ^ (n - 2) ≤ Nat.card θ.range →
      (B₁ = B ∨ ∃ b ∈ B, b ∉ B₁ ∧ B = B₁ ⊔ Subgroup.zpowers b ∧
        Subgroup.zpowers b ⊓ B₁ = ⊥ ∧ ∃ (A : GL (Fin n) K) (σ : K ≃+* K),
          ModelGen.FieldAct p φ b A σ ∧ ModelGen.FormRel β A σ ∧
          ∀ x : ↥B₁, ModelGen.semiConj A σ (θ x) * (θ x)⁻¹ ∈ StatedScalars (Fin n) K) →
      S267ConcA p S B)
    (hp : p.Prime) (hp2 : p ≠ 2) [hSn : S.Normal] (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4))
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ)
    (hdiag : p ∣ Nat.gcd n (Nat.card K - 1)) (e : PSimple p S ≃* StatedProj (StatedSL n K)) :
    S267ConcA p S B := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hpn : p ∣ n := hdiag.trans (Nat.gcd_dvd_left _ _)
  have hpK1 : p ∣ Nat.card K - 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | hn4
  · exfalso
    have hle := ModelGen.card_le_of_caseL_lin hp hp2 hperf hcore hn hℓ hℓ2 hf hK hdiag e hB hBC
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hpn
    subst hp3
    exact hp3B ⟨rfl, le_antisymm hle h4⟩
  have hn5 : 5 ≤ n := by
    by_contra h
    have h4' : n = 4 := by omega
    rw [h4'] at hpn
    have h1 : p ∣ 2 ^ 2 := hpn
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  obtain ⟨φ, hφS, hφk, B₁, θ, hB₁B, hB₀B₁, hθβ, hθel, hθZ, hθ1, hθact, hθc, hsplit⟩ :=
    ModelGen.exists_caseLData_lin hp hp2 hperf hcore hn4 hℓ hℓ2 hf hK hpℓ hdiag e hB hBC hrank
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K ℓ 2).1 (by exact_mod_cast h)
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 this)
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K ℓ p).1 h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 this).symm
  have hq : p ∣ Fintype.card K - 1 := by rw [← Nat.card_eq_fintype_card]; exact hpK1
  have hK4 : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have h0 : 0 < Nat.card K - 1 := by omega
    have := Nat.le_of_dvd h0 hpK1
    omega
  have hiso : ∀ g : GL (Fin n) K,
      g ∈ isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) :=
    fun g => mem_isomGL.2 fun _ _ => rfl
  obtain ⟨ζ, hζp, hζ1⟩ := exists_root_ne_one hp hq
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hsc : ∃ c : Kˣ, c ≠ 1 ∧ c ^ p = 1 ∧ Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      isomGL (0 : (Fin n → K) →ₗ[K] (Fin n → K) →ₗ[K] K) :=
    ⟨Units.mk0 ζ hζ0, fun h => hζ1 (congrArg Units.val h),
      Units.ext (by simp [hζp]), hiso _⟩
  refine hLU hn5 (τ := RingHom.id K) hp hB h4 hBC hcore h2 hpK
    (H := StatedSL n K) (β := 0) (fun g _ => hiso g) (Or.inl rfl)
    (fun g _ hg => CFSG.Open.StatedAPI.mem_statedSL_of_det hg) hsc hK4 ?_ ?_ φ hφS hφk θ
    hB₁B hB₀B₁ hθβ hθel hθZ hθ1 hθact hθc hsplit
  · intro U W hUW _ _ hdim
    exact ⟨blkI_le_statedSL 0 U W, isQuasisimple_blkI_zero hUW hdim,
      fun x hx hxp => dvd_card_blkI_zero hUW hdim hp hx hxp,
      fun y hyU hy => exists_smul_of_commute_blkI_zero hUW hdim hyU hy,
      fun A σ hσ hU y hyU k hk0 hkp => not_forall_semiConj_pow_zero hUW hdim hσ hU hyU hk0 hkp⟩
  · intro Aε _ hA _ hmax _ H' hH'
    exact finrank_weightSpace_eq_one_lin (glRep Aε) hp hA hpK hmax hq H' hH'

theorem concA_caseL_lin (hp : p.Prime) (hp2 : p ≠ 2) [hSn : S.Normal] (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (h4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4))
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hpℓ : p ≠ ℓ)
    (hdiag : p ∣ Nat.gcd n (Nat.card K - 1)) (e : PSimple p S ≃* StatedProj (StatedSL n K)) :
    S267ConcA p S B :=
  concA_caseL_lin_of_lu concA_caseL_lu hp hp2 hperf hcore hB hrank h4 hBC hp3B hn hℓ hℓ2 hf hK
    hpℓ hdiag e

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
