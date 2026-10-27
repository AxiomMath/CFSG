module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTwisted
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti CFSG.LieType.SeitzGeneration.ExcHighThree
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Steinberg

section Pure

theorem twE6_rootChar_neg {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (v : Fin τ.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem twE6_rootChar_pow_three {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i ^ 3 = 1) (v : Fin τ.rank → ℤ) : rootChar a v ^ 3 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha i, one_zpow]

theorem twE6_pow_eq_inv_of_dvd {K : Type} [Field K] {u : Kˣ} (hu : u ^ 3 = 1) {q : ℕ}
    (hq : 3 ∣ q + 1) : u ^ q = u⁻¹ := by
  obtain ⟨m, hm⟩ := hq
  have hq' : q = 3 * m - 1 := by omega
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    subst this
    omega
  have : u ^ q * u = 1 := by
    rw [← pow_succ, show q + 1 = 3 * m by omega, pow_mul, hu, one_pow]
  exact eq_inv_of_mul_eq_one_left this

theorem twE6_perm_symm : TwistTag.E6.perm.symm = TwistTag.E6.perm := by
  ext i
  fin_cases i <;> decide

theorem twE6_permLattice_permLattice (y : Fin TwistTag.E6.tag.rank → ℤ) :
    permLattice TwistTag.E6.perm (permLattice TwistTag.E6.perm y) = y := by
  funext i
  simp only [permLattice, Function.comp_apply]
  rw [twE6_perm_symm]
  congr 1
  fin_cases i <;> decide

end Pure

section Twisted


theorem TwLangData.rootChar_smul_v {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ A)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) *
        D.g0)
    (y : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar a (D.v • y) = Units.map D.Fr.toMonoidHom
      (rootChar a (permLattice TwistTag.E6.perm.symm y)) := by
  have hT : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)
        (twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr) := by
    obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
    have hsz' : D.g0 * s * D.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) := hsz
    have hs_eq : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) * D.g0 = s := by
      rw [← hsz']
      group
    rw [hs_eq]
    exact hs
  have h1 := mem_twistedTorusOf.1 hT
  rw [← ha] at h1
  have h2 : twistHom TwistTag.E6 (AlgebraicClosure K) D.Fr (rootDiagUnit TwistTag.E6.tag a) =
      rootDiagUnit TwistTag.E6.tag (fun i => Units.map D.Fr.toMonoidHom
        (a (TwistTag.E6.perm.symm i))) := twistHom_rootDiagUnit_eq a
  have hconj : rootDiagUnit TwistTag.E6.tag a =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v *
        rootDiagUnit TwistTag.E6.tag (fun i => Units.map D.Fr.toMonoidHom
          (a (TwistTag.E6.perm.symm i))) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) D.v)⁻¹ := by
    rw [← h2]
    exact h1.2.symm
  rw [(rootDiagUnit_eq_conj_canonicalRep_iff a _ D.v).1 hconj y, rootChar_permLattice,
    rootChar_map_tuple]

theorem rootDiagUnit_pow_mul_eq {K : Type} [Field K] [Finite K]
    (g0 : ModGL Tag.E6 (AlgebraicClosure K)) (c x₁ x₂ z : ModGL Tag.E6 K)
    (a₁ a₂ : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (h₁ : rootDiagUnit Tag.E6 a₁ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x₁ * c⁻¹ : ModGL Tag.E6 K) * g0)
    (h₂ : rootDiagUnit Tag.E6 a₂ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * x₂ * c⁻¹ : ModGL Tag.E6 K) * g0)
    (m₁ m₂ : ℕ) (hz : x₁ ^ m₁ * x₂ ^ m₂ = z) :
    rootDiagUnit Tag.E6 (a₁ ^ m₁ * a₂ ^ m₂) = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (c * z * c⁻¹ : ModGL Tag.E6 K) * g0 := by
  have h1 : diagG g0 c x₁ = rootDiagUnit Tag.E6 a₁ := (diagG_apply _ _ _).trans h₁.symm
  have h2 : diagG g0 c x₂ = rootDiagUnit Tag.E6 a₂ := (diagG_apply _ _ _).trans h₂.symm
  have e1 : rootDiagUnit Tag.E6 (a₁ ^ m₁ * a₂ ^ m₂) =
      rootDiagUnit Tag.E6 a₁ ^ m₁ * rootDiagUnit Tag.E6 a₂ ^ m₂ :=
    (map_mul (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) _ _).trans
      (congrArg₂ _ (map_pow (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) a₁ m₁)
        (map_pow (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) a₂ m₂))
  calc rootDiagUnit Tag.E6 (a₁ ^ m₁ * a₂ ^ m₂)
      = rootDiagUnit Tag.E6 a₁ ^ m₁ * rootDiagUnit Tag.E6 a₂ ^ m₂ := e1
    _ = diagG g0 c x₁ ^ m₁ * diagG g0 c x₂ ^ m₂ := by rw [h1, h2]
    _ = diagG g0 c (x₁ ^ m₁ * x₂ ^ m₂) := by rw [map_mul, map_pow, map_pow]
    _ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c * z * c⁻¹ : ModGL Tag.E6 K) * g0 := by rw [hz]; exact diagG_apply _ _ _

theorem TwLangData.mem_rootCharStabilizer {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) (hq3 : 3 ∣ q + 1)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ A)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : rootDiagUnit TwistTag.E6.tag a = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹ : ModGL TwistTag.E6.tag K) *
        D.g0)
    (ha3 : ∀ i, a i ^ 3 = 1) {w' : WeylGroup TwistTag.E6.tag}
    (hw' : ∀ y, w' • y = -permLattice TwistTag.E6.perm (D.v⁻¹ • y)) :
    w' ∈ rootCharStabilizer a := by
  intro y
  have h := D.rootChar_smul_v hx ha (D.v⁻¹ • y)
  rw [smul_inv_smul, twE6_perm_symm] at h
  have hFr : Units.map D.Fr.toMonoidHom (rootChar a (permLattice TwistTag.E6.perm (D.v⁻¹ • y))) =
      (rootChar a (permLattice TwistTag.E6.perm (D.v⁻¹ • y)))⁻¹ := by
    rw [← twE6_pow_eq_inv_of_dvd (twE6_rootChar_pow_three a ha3 _) hq3]
    exact Units.ext (by simp [D.hFr])
  rw [hFr] at h
  rw [hw' y, twE6_rootChar_neg, h]

theorem smul_perm_eq_neg_of_fixed {v w' : WeylGroup TwistTag.E6.tag}
    (hw' : ∀ y, w' • y = -permLattice TwistTag.E6.perm (v⁻¹ • y))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : w' • β = β) :
    v • permLattice TwistTag.E6.perm β = -β := by
  have h1 : -permLattice TwistTag.E6.perm (v⁻¹ • β) = β := by rw [← hw' β, hβ]
  have h2 : permLattice TwistTag.E6.perm (v⁻¹ • β) = -β := neg_eq_iff_eq_neg.1 h1
  have h3 : permLattice TwistTag.E6.perm β = -(v⁻¹ • β) := by
    have := congrArg (permLattice TwistTag.E6.perm) h2
    rw [twE6_permLattice_permLattice] at this
    rw [this]
    funext i
    simp [permLattice]
  rw [h3, smul_neg, smul_inv_smul]

end Twisted

end CFSG.LieType.SeitzGeneration.ExcWideThree
