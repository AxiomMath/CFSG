module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoFusion

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace TwE6InnerAbs

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE


theorem iform_neg_neg' {τ : Tag}
    (x y : Fin τ.rank → ℤ) : iform (-x) (-y) = iform x y := by
  simp only [iform, Pi.neg_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rootChar_neg' {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (v : Fin τ.rank → ℤ) : rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem rootChar_pow_eq_one' {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ} {p : ℕ}
    (hap : ∀ i, a i ^ p = 1) (v : Fin τ.rank → ℤ) : rootChar a v ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast (a i ^ v i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hap i,
    one_zpow]

theorem rootChar_torV_subLin_e6Omega3 {K : Type} [Field K] {ω : Kˣ} (hω3 : ω ^ 3 = 1)
    (y : Fin 5 → ZMod 3) :
    rootChar (torV ω (subLin (τ := Tag.E6) e6InnerVec y)) e6Omega3 = 1 := by
  have hdvd : ∀ y : Fin 5 → ZMod 3,
      (∑ i, (((subLin (τ := Tag.E6) e6InnerVec y i).val : ℕ) : ℤ) * e6Omega3 i) % 3 = 0 := by
    decide +kernel
  rw [rootChar_torV]
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero (hdvd y)
  rw [hk, zpow_mul]
  have : ω ^ (3 : ℤ) = 1 := by exact_mod_cast hω3
  rw [this, one_zpow]

theorem map_conj_commutator_eq {G : Type*} [Group G] {M : Subgroup G} {m : G} (hm : m ∈ M) :
    ⁅M, M⁆.map (MulAut.conj m).toMonoidHom = ⁅M, M⁆ := by
  have hM : M.map (MulAut.conj m).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)
    · intro hx
      refine ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  rw [Subgroup.map_commutator, hM]

section Datum


variable {L : Type} [Field L] [CharP L 2]

noncomputable abbrev stdDatum {g0 : ModGL TwistTag.E6.tag L}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : twistHom TwistTag.E6 L (iterateFrobenius L 2 1) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) : LangDatum TwistTag.E6.tag L :=
  LangDatum.ofTwist TwistTag.E6 (iterateFrobenius L 2 1) 2 iterateFrobenius_two_one twE6W0 hg0C hg0

theorem iterateFrobenius_surjective [IsAlgClosed L] :
    Function.Surjective (iterateFrobenius L 2 1) := fun y => by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
  exact ⟨x, by rw [iterateFrobenius_two_one, hx]⟩

theorem frobRootMap_neg [IsAlgClosed L] {g0 : ModGL TwistTag.E6.tag L}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag L)
    (hg0 : twistHom TwistTag.E6 L (iterateFrobenius L 2 1) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) :
    FrobRootMap (stdDatum hg0C hg0) (Equiv.neg (Fin TwistTag.E6.tag.rank → ℤ)) where
  isRoot_iff γ := ⟨fun h => by simpa using IsRoot.neg h, fun h => IsRoot.neg h⟩
  neg_eq γ := rfl
  iform_eq γ δ := iform_neg_neg' γ δ
  map_rootSubgroup γ hγ := by
    have h := map_twFrob_rootSubgroup TwistTag.E6 (iterateFrobenius_surjective (L := L))
      twE6W0 hγ
    rw [twE6W0_smul_permLattice] at h
    exact h
  rootChar_eq a ha γ hγ := by
    have hx := (mem_twistedTorusOf.1 ha).2
    have hF : twE6TwoF L (rootDiagUnit Tag.E6 a) = (rootDiagUnit Tag.E6 a)⁻¹ ^ 2 :=
      twE6TwoF_rootDiagUnit a
    have h2 : (rootDiagUnit Tag.E6 a)⁻¹ ^ 2 = rootDiagUnit Tag.E6 a := by
      rw [← hF]
      exact hx
    have h3 : (rootDiagUnit Tag.E6 a) ^ 3 = 1 := by
      calc (rootDiagUnit Tag.E6 a) ^ 3 = rootDiagUnit Tag.E6 a * (rootDiagUnit Tag.E6 a) ^ 2 := by
            group
        _ = (rootDiagUnit Tag.E6 a)⁻¹ ^ 2 * (rootDiagUnit Tag.E6 a) ^ 2 := by rw [h2]
        _ = 1 := by group
    have ha3 : a ^ 3 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)
      rw [← rootDiagUnit_pow, rootDiagUnit_one]
      exact h3
    have hap : ∀ i, a i ^ 3 = 1 := fun i => by simpa using congrFun ha3 i
    have h4 := rootChar_pow_eq_one' hap γ
    change rootChar a (-γ) = rootChar a γ ^ 2
    rw [rootChar_neg']
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact h4

end Datum

theorem natCast_three_ne_zero_of_charTwo {L : Type} [Field L] [CharP L 2] : ((3 : ℕ) : L) ≠ 0 := by
  have h2 : ((2 : ℕ) : L) = 0 := CharP.cast_eq_zero L 2
  have e : ((3 : ℕ) : L) = ((2 : ℕ) : L) + 1 := by norm_num
  rw [e, h2, zero_add]
  exact one_ne_zero

theorem exists_orderOf_three {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ω : Lˣ, orderOf ω = 3 := by
  haveI : NeZero ((3 : ℕ) : L) := ⟨natCast_three_ne_zero_of_charTwo⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot ((hu.unit : Lˣ) : L) 3 := by simpa using hζ₀
  exact ⟨hu.unit, (IsPrimitiveRoot.coe_units_iff.1 hζ).eq_orderOf.symm⟩

section Setup


theorem exists_stdSetup_of_inner {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2) {s : twistedE6RootGroup K σ} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5) (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K)),
      S.D.q = 2 ∧ (∀ γ, S.ρ γ = -γ) ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ i, a i ^ 3 = 1) ∧
      rootDiagUnit Tag.E6 a ≠ 1 ∧ rootChar a e6Omega3 = 1 ∧ Function.Injective ι ∧
      ι.range = S.Γ ∧ ι s = rootDiagUnit Tag.E6 a := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI hcK : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  haveI hcL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨g0, hg0C, hg0⟩ := exists_twE6Two_lang K
  have hK2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ]; norm_num
  have hFr : ∀ c : AlgebraicClosure K, iterateFrobenius (AlgebraicClosure K) 2 1 c =
      c ^ (2 ^ 1) := fun c => by rw [iterateFrobenius_two_one]; norm_num
  have hfin : Finite (stdDatum hg0C hg0).model :=
    finite_model_twistedE6 Nat.prime_two le_rfl hK2 hσ2 hFr (stdDatum hg0C hg0) rfl
  let eΓ := twE6TwoEquiv hK σ hσ hg0C hg0
  obtain ⟨ω, hω⟩ := exists_orderOf_three (L := AlgebraicClosure K)
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hŝ : ((eΓ s : ↥(⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
      Subgroup (ModGL Tag.E6 (AlgebraicClosure K)))) : ModGL Tag.E6 (AlgebraicClosure K)) ^ 3 =
        1 := by
    have h : eΓ (s ^ 3) = 1 := by rw [hs3, map_one]
    rw [map_pow] at h
    exact congrArg Subtype.val h
  obtain ⟨m, hmM, y₀, hm⟩ := twE6TwoFusion_holds K hK σ hσ g0 hg0C hg0 ω hω _ (eΓ s).2 hŝ
  let ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (MulAut.conj m).toMonoidHom.comp
      ((⁅twE6TwoModel (AlgebraicClosure K), twE6TwoModel (AlgebraicClosure K)⁆ :
        Subgroup (ModGL Tag.E6 (AlgebraicClosure K))).subtype.comp eΓ.toMonoidHom)
  have hι : ∀ t, ι t = m * ((eΓ t : ModGL Tag.E6 (AlgebraicClosure K))) * m⁻¹ := fun t => rfl
  have hιinj : Function.Injective ι := fun t t' h => by
    have h1 : (MulAut.conj m) (eΓ t : ModGL Tag.E6 (AlgebraicClosure K)) =
        (MulAut.conj m) (eΓ t' : ModGL Tag.E6 (AlgebraicClosure K)) := h
    exact eΓ.injective (Subtype.ext ((MulAut.conj m).injective h1))
  have hrange : ι.range = ⁅twE6TwoModel (AlgebraicClosure K),
      twE6TwoModel (AlgebraicClosure K)⁆ := by
    rw [← map_conj_commutator_eq hmM]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(eΓ t : ModGL Tag.E6 (AlgebraicClosure K)), (eΓ t).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨t, ht⟩ := eΓ.surjective ⟨y, hy⟩
      exact ⟨t, by rw [hι, ht]; rfl⟩
  set a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    torV ω (subLin (τ := Tag.E6) e6InnerVec y₀) with ha
  have hd : rootDiagUnit Tag.E6 a = dV (τ := Tag.E6) ω (subLin (τ := Tag.E6) e6InnerVec y₀) := rfl
  have hιs : ι s = rootDiagUnit Tag.E6 a := by
    rw [hd, hι, ← hm]
  refine ⟨(stdDatum hg0C hg0).toSetup 5 (Equiv.neg _) (frobRootMap_neg hg0C hg0)
      Nat.prime_five (Or.inl le_rfl) ⟨Nat.prime_two.isPrimePow, CharP.cast_eq_zero _ 2⟩
      (show ¬ 5 ∣ 2 by norm_num) hfin, a, ι, rfl, fun γ => rfl, ?_, ?_, ?_, ?_, hιinj, ?_, hιs⟩
  · refine mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
    exact (twE6Two_dV_mem_model (L := AlgebraicClosure K) hω3
      (subLin (τ := Tag.E6) e6InnerVec y₀)).2
  · intro i
    simp only [ha, torV]
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  · intro h1
    apply hs1
    apply hιinj
    rw [hιs, h1, map_one]
  · exact rootChar_torV_subLin_e6Omega3 hω3 y₀
  · exact hrange

end Setup

end TwE6InnerAbs

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
