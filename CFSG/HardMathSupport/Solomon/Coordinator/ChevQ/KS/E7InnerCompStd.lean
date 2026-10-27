module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwo
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE7
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E7InnerAbs

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.LangTorus

set_option linter.unusedSectionVars false

section Datum

variable {L : Type} [Field L] [CharP L 2]

noncomputable abbrev stdDatum {g0 : ModGL Tag.E7 L}
    (hg0C : g0 ∈ adjointGroup Tag.E7 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 1)) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) L e7Neg) : LangDatum Tag.E7 L :=
  LangDatum.ofFrobenius (iterateFrobenius L 2 1) 2 iterateFrobenius_two_one e7Neg hg0C hg0

theorem frobRootMap_neg [IsAlgClosed L] {g0 : ModGL Tag.E7 L}
    (hg0C : g0 ∈ adjointGroup Tag.E7 L)
    (hg0 : Units.map (entrywiseHom (iterateFrobenius L 2 1)) g0 =
      g0 * canonicalRep (coxeterSystem Tag.E7) L e7Neg) :
    FrobRootMap (stdDatum hg0C hg0) (Equiv.neg (Fin Tag.E7.rank → ℤ)) where
  isRoot_iff γ := ⟨fun h => by simpa using IsRoot.neg h, fun h => IsRoot.neg h⟩
  neg_eq γ := rfl
  iform_eq γ δ := by
    simpa only [Equiv.neg_apply, e7Neg_smul] using (iform_smul e7Neg γ δ)
  map_rootSubgroup γ hγ := by
    have hsurj : Function.Surjective (iterateFrobenius L 2 1) := fun y => by
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 2)
      exact ⟨x, by rw [iterateFrobenius_two_one, hx]⟩
    simpa only [Equiv.neg_apply, e7Neg_smul] using
      (stdDatum hg0C hg0).map_step_rootSubgroup hsurj rfl (w := e7Neg) rfl hγ
  rootChar_eq a ha γ _ := by
    have hfix := (mem_twistedTorusOf.1 ha).2
    have h2 : (rootDiagUnit Tag.E7 a)⁻¹ ^ 2 = rootDiagUnit Tag.E7 a := by
      exact (twFrob_rootDiagUnit e7Neg_smul a).symm.trans hfix
    have hd3 : rootDiagUnit Tag.E7 a ^ 3 = 1 := by
      calc rootDiagUnit Tag.E7 a ^ 3 =
          rootDiagUnit Tag.E7 a * rootDiagUnit Tag.E7 a ^ 2 := by group
        _ = (rootDiagUnit Tag.E7 a)⁻¹ ^ 2 * rootDiagUnit Tag.E7 a ^ 2 := by rw [h2]
        _ = 1 := by group
    have ha3 : a ^ 3 = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective (by
      rw [← CFSG.LieType.Chevalley.rootDiagUnit_pow, hd3, rootDiagUnit_one])
    have hχ3 : rootChar a γ ^ 3 = 1 := by
      rw [rootChar, ← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      have hi : a i ^ 3 = 1 := congrFun ha3 i
      rw [← zpow_natCast (a i ^ γ i) 3, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hi, one_zpow]
    change rootChar a (-γ) = rootChar a γ ^ 2
    rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]
    calc (rootChar a γ)⁻¹ = (rootChar a γ)⁻¹ * rootChar a γ ^ 3 := by rw [hχ3, mul_one]
      _ = rootChar a γ ^ 2 := by group

end Datum

theorem exists_stdSetup_of_inner_frobenius_conj_baseChange {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {s : ↥(adjointGroup Tag.E7 F)} (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) :
    ∃ (S : LangSetup Tag.E7 (AlgebraicClosure F) 5)
      (a : Fin Tag.E7.rank → (AlgebraicClosure F)ˣ)
      (ι : ↥(adjointGroup Tag.E7 F) →* ModGL Tag.E7 (AlgebraicClosure F)),
      S.D.q = 2 ∧ (∀ γ, S.ρ γ = -γ) ∧ rootDiagUnit Tag.E7 a ∈ S.D.torus ∧
      (∀ i, a i ^ 3 = 1) ∧ rootDiagUnit Tag.E7 a ≠ 1 ∧ Function.Injective ι ∧
      ι.range = S.Γ ∧ ι s = rootDiagUnit Tag.E7 a ∧
      (∀ c, ι (MulAut.conj s c) =
        rootDiagUnit Tag.E7 a * ι c * (rootDiagUnit Tag.E7 a)⁻¹) ∧
      (∃ Fr : AlgebraicClosure F →+* AlgebraicClosure F, (∀ c, Fr c = c ^ 2) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      S.D.n = canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure F) e7Neg ∧
      ∃ h ∈ adjointGroup Tag.E7 (AlgebraicClosure F), ∀ z,
        ι z = h * baseChangeGL (algebraMap F (AlgebraicClosure F))
          (z : ModGL Tag.E7 F) * h⁻¹ := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  haveI : CharP (AlgebraicClosure F) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E7 F e7Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure F) 2 1 := by
    ext c
    rw [hFr, hF, iterateFrobenius_two_one]
  subst Fr
  let D := stdDatum hg0C hg0
  let ι₀ := (baseChangeGL (τ := Tag.E7) (algebraMap F (AlgebraicClosure F))).comp
    (adjointGroup Tag.E7 F).subtype
  have hι₀ : Function.Injective ι₀ :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hd : LangDescent D 7 ι₀ := by
    have hperf : commutator ↥(adjointGroup Tag.E7 F) = ⊤ :=
      single_edge_perfect Tag.E7 F (by simp)
    exact langDescent_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hFr D rfl
      Nat.prime_seven (by norm_num) hperf
  let eΓ := hd.mulEquiv' hι₀
  have hŝ3 : (eΓ s : ModGL Tag.E7 (AlgebraicClosure F)) ^ 3 = 1 := by
    have h : eΓ (s ^ 3) = 1 := by rw [hs3, map_one]
    rw [map_pow] at h
    exact congrArg Subtype.val h
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one F (L := AlgebraicClosure F) (N := 3)
    (by rw [hF])
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hLang : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure F)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E7 (AlgebraicClosure F) a,
        ∃ z ∈ toralCentralizer Tag.E7 (AlgebraicClosure F) a, z⁻¹ * frobTwistGL Tag.E7
          (AlgebraicClosure F) 2 1 (canonicalRep (coxeterSystem Tag.E7)
            (AlgebraicClosure F) e7Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E7_three 2 (AlgebraicClosure F) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e7Neg_smul ha3) c hc
  obtain ⟨u, hu, x, hx⟩ := exists_conj_dV_twModel
    (isAlgebraic_zmod_algebraicClosure_of_finite F 2)
    (monomialToralAt_three_of_block a2BlockToral_E7) e7Neg_smul hLang hω
    (hd.Γ_le_model (eΓ s).2) hŝ3
  let ι : ↥(adjointGroup Tag.E7 F) →* ModGL Tag.E7 (AlgebraicClosure F) :=
    (MulAut.conj u).toMonoidHom.comp (D.Γ.subtype.comp eΓ.toMonoidHom)
  have hιinj : Function.Injective ι :=
    (MulAut.conj u).injective.comp (D.Γ.subtype_injective.comp eΓ.injective)
  have hM : D.model.map (MulAut.conj u).toMonoidHom = D.model := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hu hz) (inv_mem hu)
    · intro hy
      refine ⟨u⁻¹ * y * u, mul_mem (mul_mem (inv_mem hu) hy) hu, ?_⟩
      change u * (u⁻¹ * y * u) * u⁻¹ = y
      group
  have hrange : ι.range = D.Γ := by
    have hr : eΓ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.2 eΓ.surjective
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hr,
      Subgroup.map_top, Subgroup.range_subtype]
    change ⁅D.model, D.model⁆.map (MulAut.conj u).toMonoidHom = ⁅D.model, D.model⁆
    rw [Subgroup.map_commutator, hM]
  let a : Fin Tag.E7.rank → (AlgebraicClosure F)ˣ := torV ω x
  have hιs : ι s = rootDiagUnit Tag.E7 a := hx
  refine ⟨D.toSetup 5 (Equiv.neg _) (frobRootMap_neg hg0C hg0)
      Nat.prime_five (Or.inl le_rfl) ⟨Nat.prime_two.isPrimePow, CharP.cast_eq_zero _ 2⟩
      (show ¬ 5 ∣ 2 by norm_num) hd.finite_model, a, ι, rfl, fun γ => rfl,
      ?_, ?_, ?_, hιinj, hrange, hιs, ?_,
      ⟨iterateFrobenius (AlgebraicClosure F) 2 1, iterateFrobenius_two_one, rfl⟩, rfl, ?_⟩
  · exact mem_twistedTorusOf.2 ⟨rootDiagUnit_mem_torusGroup_E7 a,
      (dV_mem_twModel rootDiagUnit_mem_torusGroup_E7 e7Neg_smul hω3 x).2⟩
  · intro i
    change (ω ^ (x i).val) ^ 3 = 1
    rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  · intro h1
    apply hs1
    apply hιinj
    rw [hιs, h1, map_one]
  · intro c
    change ι (s * c * s⁻¹) = _
    rw [map_mul, map_mul, map_inv, hιs]
  · refine ⟨u * g0⁻¹, mul_mem (mem_twModel.1 hu).1 (inv_mem hg0C), ?_⟩
    intro z
    change u * ((hd.mulEquiv' hι₀ z : D.Γ) : ModGL Tag.E7 (AlgebraicClosure F)) * u⁻¹ = _
    rw [hd.coe_mulEquiv' hι₀ z]
    change u * (g0⁻¹ * baseChangeGL (algebraMap F (AlgebraicClosure F))
      (z : ModGL Tag.E7 F) * g0) * u⁻¹ = _
    group

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E7InnerAbs

end
