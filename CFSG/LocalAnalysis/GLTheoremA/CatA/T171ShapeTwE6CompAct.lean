module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcW
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.PerfectCentralQuotient
  CFSG.ComponentClassification.FixedCommutingProduct
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise commutatorElement


theorem twE6_langSetup_and_component {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hKcard : Nat.card K = (q.p ^ q.exponent) ^ 2)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (x : ↥(twistedE6RootGroup K σ)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (Kc : Subgroup ↥(twistedE6RootGroup K σ))
    (hKc : CFSG.Assembly.IsComponentOf Kc (fixedSubgroup (MulAut.conj x))) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(twistedE6RootGroup K σ) →* ModGL Tag.E6 (AlgebraicClosure K))
      (i : KernelComponent (rootCharHom a)),
      S.D.q = q.p ^ q.exponent ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ (q.p ^ q.exponent)) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr) ∧
      rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ p = 1) ∧
      rootDiagUnit Tag.E6 a ^ p = 1 ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c, ι ((MulAut.conj x) c) =
        rootDiagUnit Tag.E6 a * ι c * (rootDiagUnit Tag.E6 a)⁻¹) ∧
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
      Kc.map ι = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, hq2, ← pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp hp2
  obtain ⟨S, a, ι, hSq, huntw, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_twE6_of_prime (ℓ := q.p) (f := q.exponent) q.prime_p
      q.exponent_pos hKcard σ hσ hp (by rw [hq2]; exact hp2) (p₀ := 5) Nat.prime_five
      (by rw [hq2]; norm_num) (Or.inl le_rfl) hmon (MulAut.conj x) x.1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom x.2) (fun c => rfl)
      (by simpa using congrArg Subtype.val hxp) (fun h => hx1 (Subtype.ext h))
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have hp2' : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 p).1 h0)).symm
    exact hp2 hp2'
  have hTame := langSetup_hTame_of_prime S hp hpL (fun h => by cases h) hT hap h1
  have hKc' : CFSG.Open.IsComponentOf Kc (fixSubgroup (MulAut.conj x)) :=
    CFSG.Assembly.isComponentOf_iff_open.1 hKc
  obtain ⟨i, hqs, hKR⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_of_langSetup S hp ι hinj hrange
      (MulAut.conj x) hconj hT hap h1 hTame hKc'
  exact ⟨S, a, ι, i, hSq, huntw, hT, hap, rootDiagUnit_pow_eq_one_of_forall hap, h1, hinj,
    hrange, hconj, hqs, hKR⟩

theorem twE6_mem_torusGroup_sup_rootSpan {K : Type} [Field K]
    [CharP (AlgebraicClosure K) 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
    (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (hnot3 : p = 3 → ¬ 3 ∣ S.D.q + 1)
    (hFr : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
    (hC : TwE6CentralizerConnOdd)
    {y : ModGL Tag.E6 (AlgebraicClosure K)}
    (hyC : y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a)
    (hyF : S.D.step y = y) :
    y ∈ torusGroup Tag.E6 (AlgebraicClosure K) ⊔
      rootSpan Tag.E6 (AlgebraicClosure K) (kernelRoots (rootCharHom a)) := by
  by_cases hp3 : p = 3
  · have hap3 : ∀ j, a j ^ 3 = 1 := by
      intro j
      rw [← hp3]
      exact hap j
    exact hC (L := AlgebraicClosure K) (p₀ := 5) S hFr (hnot3 hp3) a hT hap3 y hyC hyF
  · have hW := rootCharStabilizerSubgroup_le_kernelReflectionGroup_of_odd hp hp2
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun _ => hp3) hap
    have hZeq :=
      toralCentralizer_eq_toralRootGroup_of_stabilizer_le Tag.E6 (AlgebraicClosure K) a hW
    rw [hZeq] at hyC
    exact hyC

theorem twE6ComponentAction_aux
    (hK : ExcKernelCompAction) (hC : TwE6CentralizerConnOdd)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} (hq2 : q.p = 2)
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hKcard : Nat.card K = (q.p ^ q.exponent) ^ 2)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent))
    (hnot3 : p = 3 → ¬ 3 ∣ q.p ^ q.exponent + 1)
    (x w : ↥(twistedE6RootGroup K σ)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxw : x * w = w * x)
    (Kc : Subgroup ↥(twistedE6RootGroup K σ))
    (hKc : CFSG.Assembly.IsComponentOf Kc (fixedSubgroup (MulAut.conj x)))
    (hstab : MulAut.conj w ∈ CFSG.GroupActions.subgroupStabAut Kc)
    (h360 : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) ≠ 360) :
    centerQuotientHom ↥Kc
        (CFSG.GroupActions.subgroupStabRestrict Kc ⟨MulAut.conj w, hstab⟩) ∈
      innAutDerived (↥Kc ⧸ Subgroup.center ↥Kc) := by
  classical
  obtain ⟨S, a, ι, i, hSq, huntw, hT, hap, hTp, h1, hinj, hrange, hconj, hqs, hKR⟩ :=
    twE6_langSetup_and_component hp hp2 hq2 σ hKcard hσ x hx1 hxp Kc hKc
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcharK : CharP K 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hKcard, hq2, ← pow_mul])
  haveI hcharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set y : ModGL Tag.E6 (AlgebraicClosure K) := ι w with hydef
  have hιconj : ∀ c : ↥(twistedE6RootGroup K σ),
      ι ((MulAut.conj w) c) = MulAut.conj y (ι c) := by
    intro c
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hydef]
  have hyΓ : y ∈ S.Γ := by
    rw [hydef, ← hrange]
    exact ⟨w, rfl⟩
  have hyF : S.D.step y = y := ((Subgroup.commutator_le_self S.D.model) hyΓ).2
  have hyAdj : y ∈ adjointGroup Tag.E6 (AlgebraicClosure K) :=
    ((Subgroup.commutator_le_self S.D.model) hyΓ).1
  have hyx : (MulAut.conj x) w = w := by
    rw [MulAut.conj_apply, hxw, mul_inv_cancel_right]
  have hyd : rootDiagUnit Tag.E6 a * y * (rootDiagUnit Tag.E6 a)⁻¹ = y := by
    rw [← hconj w, hydef, hyx]
  have hyC : y ∈ toralCentralizer Tag.E6 (AlgebraicClosure K) a :=
    mem_toralCentralizer.2 ⟨hyAdj, hyd⟩
  have hnot3' : p = 3 → ¬ 3 ∣ S.D.q + 1 := by
    intro hp3
    rw [hSq]
    exact hnot3 hp3
  have hFr' : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      (∀ c, Fr c = c ^ S.D.q) ∧
        S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := by
    obtain ⟨Fr, hFr, hΦ⟩ := huntw
    exact ⟨Fr, fun c => by rw [hSq]; exact hFr c, hΦ⟩
  have hyZ := twE6_mem_torusGroup_sup_rootSpan hp hp2 S a hT hap hnot3' hFr' hC hyC hyF
  set R := rationalComponent S.ρ S.Γ (rootCharHom a) i with hR
  have hyStab : MulAut.conj y ∈ subgroupStabAut R := by
    change R.map (MulAut.conj y).toMonoidHom = R
    have hcomp : (MulAut.conj y).toMonoidHom.comp ι =
        ι.comp (MulAut.conj w).toMonoidHom :=
      MonoidHom.ext fun c => (hιconj c).symm
    have hwK : Kc.map (MulAut.conj w).toMonoidHom = Kc := hstab
    rw [← hKR, Subgroup.map_map, hcomp, ← Subgroup.map_map, hwK]
  let eG : ↥Kc ≃* ↥R :=
    (Kc.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hKR)
  have heG : ∀ k : ↥Kc, (eG k : ModGL Tag.E6 (AlgebraicClosure K)) = ι k := fun k => rfl
  have hc : Nat.card (↥Kc ⧸ Subgroup.center ↥Kc) =
      Nat.card (↥R ⧸ Subgroup.center ↥R) :=
    Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥Kc) (Subgroup.center ↥R) eG
      (Subgroup.map_center_eq eG)).toEquiv
  have hNR : Nat.card (↥R ⧸ Subgroup.center ↥R) ≠ 360 := fun h => h360 (hc.trans h)
  have hmain : centerQuotientHom ↥R (subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩) ∈
      innAutDerived (↥R ⧸ Subgroup.center ↥R) :=
    hK (τ := Tag.E6) (L := AlgebraicClosure K) S Nat.prime_five (by norm_num) hp hp2
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hT hap hTp h1 (fun h => by cases h) i hqs hNR
      hyZ hyF hyStab
  haveI hperfK : Group.IsPerfect ↥Kc := ⟨hKc.2.2.1⟩
  have hαγ : ∀ g : ↥Kc,
      subgroupStabRestrict R ⟨MulAut.conj y, hyStab⟩ (eG g) =
        eG (subgroupStabRestrict Kc ⟨MulAut.conj w, hstab⟩ g) := by
    intro g
    apply Subtype.ext
    simp only [subgroupStabRestrict_apply, heG, MulAut.conj_apply]
    exact (hιconj (g : ↥(twistedE6RootGroup K σ))).symm
  have hker : eG.toMonoidHom.ker ≤ Subgroup.center ↥Kc := by
    intro z hz
    have h1 : z = 1 := eG.injective (by simpa using hz)
    rw [h1]
    exact Subgroup.one_mem _
  exact (centerQuotientHom_mem_innAutDerived_iff_of_surjective eG.toMonoidHom eG.surjective
    hker hαγ).1 hmain

theorem twE6ComponentAction_holds : TwE6ComponentAction :=
  fun hK hC p hp hp2 q hq2 K _ _ σ hKcard hσ hnot3 x w hx1 hxp hxw Kc hKc hstab h360 =>
    twE6ComponentAction_aux hK hC hp hp2 hq2 σ hKcard hσ hnot3 x w hx1 hxp hxw Kc hKc hstab
      h360

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
