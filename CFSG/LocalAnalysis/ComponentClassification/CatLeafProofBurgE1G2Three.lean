module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.RankThree.SteinbergR3ESmallReeRadical
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1G2Traces
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Data.ExceptionalSL3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_conj_mul_pow {G : Type*} [Group G] (g : G) (ψ : MulAut G) (j : ℕ) :
    ∃ g' : G, (MulAut.conj g * ψ) ^ j = MulAut.conj g' * ψ ^ j := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨g', hg'⟩ := ih
    refine ⟨g' * (ψ ^ j) g, ?_⟩
    rw [pow_succ, hg', pow_succ]
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem coe_G2_finiteFrobeniusAut_pow
    (k : ℕ) (g : adjointGroup ReeTag.G2.tag K) :
    have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
    ((ReeTag.G2.finiteFrobeniusAut K ^ k) g : ModGL ReeTag.G2.tag K) =
      Units.map (entrywiseHom ((frobeniusEquiv K 3) ^ k).toRingHom)
        (g : ModGL ReeTag.G2.tag K) := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  intro _
  induction k with
  | zero =>
    refine Units.ext ?_
    simp only [pow_zero, MulAut.one_apply, Units.coe_map]
    exact (entrywise_id _).symm
  | succ k ih =>
    refine Units.ext ?_
    rw [pow_succ', MulAut.mul_apply, ReeTag.coe_finiteFrobeniusAut, entrywiseGL, Units.coe_map,
      ih, Units.coe_map, Units.coe_map]
    change entrywise (frobenius K ReeTag.G2.prime)
        (entrywise ((frobeniusEquiv K 3) ^ k).toRingHom _) =
      entrywise ((frobeniusEquiv K 3) ^ (k + 1)).toRingHom _
    rw [entrywise_entrywise]
    congr 1
    refine RingHom.ext fun c => ?_
    rw [pow_succ', RingHom.comp_apply]
    rfl

theorem G2_three_eq_conj_frobenius_of_odd
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (η : MulAut (adjointGroup ReeTag.G2.tag K))
    (hη : Odd (orderOf η)) :
    ∃ (g : adjointGroup ReeTag.G2.tag K) (n : ℕ),
      η = MulAut.conj g * ReeTag.G2.finiteFrobeniusAut K ^ n := by
  obtain ⟨-, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, m⟩, hgm, -⟩ := hNF η
  dsimp only at hgm
  set φ := ReeTag.G2.finiteExceptionalAut K
  have hcomm : ∀ (ψ : MulAut (adjointGroup ReeTag.G2.tag K)) (x : adjointGroup ReeTag.G2.tag K),
      ψ * MulAut.conj x = MulAut.conj (ψ x) * ψ := fun ψ x => by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  have h2 : η ^ 2 = MulAut.conj (g * (φ ^ (m : ℕ)) g) *
      ReeTag.G2.finiteFrobeniusAut K ^ (m : ℕ) := by
    have e1 : ReeTag.G2.finiteFrobeniusAut K ^ (m : ℕ) = φ ^ (m : ℕ) * φ ^ (m : ℕ) := by
      rw [← finiteExceptionalAut_pow_two_mul ReeTag.G2 (m : ℕ), ← pow_add, two_mul]
    rw [hgm, sq, e1, map_mul]
    calc MulAut.conj g * φ ^ (m : ℕ) * (MulAut.conj g * φ ^ (m : ℕ)) =
        MulAut.conj g * (φ ^ (m : ℕ) * MulAut.conj g) * φ ^ (m : ℕ) := by group
      _ = _ := by rw [hcomm]; group
  obtain ⟨r, hr⟩ := hη
  have hηη : η = (η ^ 2) ^ (r + 1) := by
    rw [← pow_mul, show 2 * (r + 1) = orderOf η + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  obtain ⟨g', hg'⟩ := exists_conj_mul_pow (g * (φ ^ (m : ℕ)) g)
    (ReeTag.G2.finiteFrobeniusAut K ^ (m : ℕ)) (r + 1)
  exact ⟨g', (m : ℕ) * (r + 1), by rw [hηη, h2, hg', ← pow_mul]⟩

theorem G2_three_descended_root_SL2_pointwise_odd
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (M : Type) [Field M] [Algebra K M] (A : GL (Fin 2) M) (h : ModGL ReeTag.G2.tag M)
    (hU : ∀ B : SL2 K, h * simpleRootSL2 ReeTag.G2.tag M g2Long (conjGL A
        (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) * h⁻¹ ∈
          (adjointGroup ReeTag.G2.tag K).map (baseChangeGL (algebraMap K M)))
    (Z : Subgroup (MulAut (adjointGroup ReeTag.G2.tag K)))
    (hZ : ∀ η ∈ Z, ∀ (u : adjointGroup ReeTag.G2.tag K) (B : SL2 K),
      baseChangeGL (algebraMap K M) (u : ModGL ReeTag.G2.tag K) =
        h * simpleRootSL2 ReeTag.G2.tag M g2Long
          (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) * h⁻¹ → η u = u) :
    ∀ η ∈ Z, Odd (orderOf η) → η ∈ (MulAut.conj : adjointGroup ReeTag.G2.tag K →*
      MulAut (adjointGroup ReeTag.G2.tag K)).range := by
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  intro η hη hodd
  obtain ⟨g, n, hgn⟩ := G2_three_eq_conj_frobenius_of_odd hf hK η hodd
  set σ := (frobeniusEquiv K 3) ^ n with hσdef
  have hFrx : ∀ x : adjointGroup ReeTag.G2.tag K,
      ((ReeTag.G2.finiteFrobeniusAut K ^ n) x : ModGL ReeTag.G2.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (x : ModGL ReeTag.G2.tag K) :=
    fun x => coe_G2_finiteFrobeniusAut_pow n x
  have hexpr : ∀ x : adjointGroup ReeTag.G2.tag K, (η x : ModGL ReeTag.G2.tag K) =
      (g : ModGL ReeTag.G2.tag K) * Units.map (entrywiseHom σ.toRingHom)
        (x : ModGL ReeTag.G2.tag K) * (g : ModGL ReeTag.G2.tag K)⁻¹ := by
    intro x
    rw [hgn, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hFrx]
  have hσ : σ = 1 := by
    have key : ∀ B : SL2 K, ∃ y : K, σ y = y ∧ algebraMap K M y = LinearMap.trace M
        (RootModule ReeTag.G2.tag M)
        ((h * simpleRootSL2 ReeTag.G2.tag M g2Long
          (conjGL A (Matrix.SpecialLinearGroup.map (algebraMap K M) B)) *
          h⁻¹ : ModGL ReeTag.G2.tag M) : Module.End M (RootModule ReeTag.G2.tag M)) := by
      intro B
      obtain ⟨y, hyC, hy⟩ := hU B
      have hfix : η ⟨y, hyC⟩ = ⟨y, hyC⟩ := hZ η hη ⟨y, hyC⟩ B hy
      have h1 : LinearMap.trace K (RootModule ReeTag.G2.tag K)
          ((η ⟨y, hyC⟩ : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K)) =
        σ (LinearMap.trace K (RootModule ReeTag.G2.tag K)
          ((y : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K))) :=
        trace_apply_of_G2_expression η g σ hexpr ⟨y, hyC⟩
      rw [hfix] at h1
      refine ⟨LinearMap.trace K (RootModule ReeTag.G2.tag K)
        ((y : ModGL ReeTag.G2.tag K) : Module.End K (RootModule ReeTag.G2.tag K)), h1.symm, ?_⟩
      rw [← hy, trace_baseChangeGL]
    exact ringEquiv_eq_one_of_fixes_G2_root_SL2_traces M A h σ key
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ n = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hFrx, hσ]
    exact Units.ext (entrywise_id _)
  exact MonoidHom.mem_range.2 ⟨g, by rw [hgn, hFr, mul_one]⟩

theorem pPrimeCore_fixedSubgroup_finiteReeAut
    (a : ℕ) (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    pPrimeCore 2 (fixedSubgroup (ReeTag.G2.finiteReeAut K a)) = ⊥ := by
  obtain ⟨hsolv, -⟩ := RankThree.small_Ree_native_fixed_groups_solvable_radical_trivial a K hK
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  let e : fixedSubgroup (ReeTag.G2.finiteReeAut K a) ≃* ReeTag.G2.reeGamma K a :=
    (fixedSubgroup (ReeTag.G2.finiteReeAut K a)).equivMapOfInjective _
      (adjointGroup ReeTag.G2.tag K).subtype_injective
  have h2 : pPrimeCore 2 (ReeTag.G2.reeGamma K a) = ⊥ :=
    hsolv _ pPrimeCore_normal
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
  have h1 := pPrimeCore_map_iso 2 e.symm
  rw [h2, Subgroup.map_bot] at h1
  exact h1.symm

end CFSG.ComponentClassification.CatLeafProof
