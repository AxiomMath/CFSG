module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.TwE6InnerCompStd
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE

section Datum


variable {L : Type} [Field L]

theorem twE6Eight_twFrob_rootDiagUnit {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 8)
    (a : Fin TwistTag.E6.tag.rank → Lˣ) :
    twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr
        (rootDiagUnit TwistTag.E6.tag a) = (rootDiagUnit TwistTag.E6.tag a)⁻¹ ^ 8 := by
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


theorem frobRootMap_neg8 [IsAlgClosed L] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ 8)
    (D : LangDatum TwistTag.E6.tag L) (hΦ : D.Φ = twistHom TwistTag.E6 L Fr) (hq : D.q = 8)
    (hn : D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) :
    FrobRootMap D (Equiv.neg (Fin TwistTag.E6.tag.rank → ℤ)) where
  isRoot_iff γ := ⟨fun h => by simpa using IsRoot.neg h, fun h => IsRoot.neg h⟩
  neg_eq γ := rfl
  iform_eq γ δ := TwE6InnerAbs.iform_neg_neg' γ δ
  map_rootSubgroup γ hγ := by
    have hsurj : Function.Surjective Fr := fun y => by
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (by norm_num : 0 < 8)
      exact ⟨x, by rw [hFr, hx]⟩
    have h := map_twFrob_rootSubgroup TwistTag.E6 hsurj twE6W0 hγ
    rw [twE6W0_smul_permLattice] at h
    have hstep : D.step = twFrob TwistTag.E6
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr := by
      unfold LangDatum.step
      rw [hΦ, hn]
      rfl
    rw [hstep]
    exact h
  rootChar_eq a ha γ hγ := by
    have hx := (mem_twistedTorusOf.1 ha).2
    have hF : twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0) Fr
        (rootDiagUnit TwistTag.E6.tag a) = (rootDiagUnit TwistTag.E6.tag a)⁻¹ ^ 8 :=
      twE6Eight_twFrob_rootDiagUnit hFr a
    have h2 : (rootDiagUnit TwistTag.E6.tag a)⁻¹ ^ 8 = rootDiagUnit TwistTag.E6.tag a := by
      rw [← hF]
      change D.n * D.Φ (rootDiagUnit TwistTag.E6.tag a) * D.n⁻¹ = _ at hx
      rw [hΦ, hn] at hx
      exact hx
    have h9 : (rootDiagUnit TwistTag.E6.tag a) ^ 9 = 1 := by
      set x := rootDiagUnit TwistTag.E6.tag a with hxdef
      rw [inv_pow] at h2
      calc x ^ 9 = x ^ 8 * x := pow_succ x 8
        _ = x ^ 8 * (x ^ 8)⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel _
    have ha9 : a ^ 9 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)
      rw [← rootDiagUnit_pow, rootDiagUnit_one]
      exact h9
    have hap : ∀ i, a i ^ 9 = 1 := fun i => by simpa using congrFun ha9 i
    have h4 := TwE6InnerAbs.rootChar_pow_eq_one' hap γ
    change rootChar a (-γ) = rootChar a γ ^ D.q
    rw [hq, TwE6InnerAbs.rootChar_neg']
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ]
    exact h4


theorem exists_stdSetup8 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 8) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (S : LangSetup Tag.E6 L 3)
      (Fr : L →+* L), (∀ c, Fr c = c ^ 8) ∧ S.D.q = 8 ∧ (∀ γ, S.ρ γ = -γ) ∧
        S.D.Φ = twistHom TwistTag.E6 L Fr ∧
        S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0 ∧ S.IsAlgebraic ∧
        Nonempty (twistedE6RootGroup K σ ≃* S.Γ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = (2 ^ 3) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 3) := fun c => by rw [hσ]; norm_num
  haveI hcK : CharP K 2 := charP_of_card_eq_prime_pow (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  set L := AlgebraicClosure K with hL
  haveI hcL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI hL' : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨Fr, hFr, D, hΦ, hDq, hDn⟩ :=
    exists_langDatum_twistedE6 Nat.prime_two (by norm_num : 1 ≤ 3) K hK2 twE6W0
  have hFr8 : ∀ c, Fr c = c ^ 8 := fun c => by rw [hFr c]; norm_num
  have hDq8 : D.q = 8 := by rw [hDq]; norm_num
  have hfin := finite_model_twistedE6 Nat.prime_two (by norm_num : 1 ≤ 3) hK2 hσ2 hFr D hΦ
  refine ⟨L, inferInstance, hL', hcL, D.toSetup 3 (Equiv.neg _)
    (frobRootMap_neg8 hFr8 D hΦ hDq8 hDn) Nat.prime_three (Or.inr (by rw [hDq8]; norm_num))
    ⟨hDq8 ▸ (Nat.prime_two.isPrimePow.pow (by norm_num : 3 ≠ 0) : IsPrimePow 8),
      by rw [hDq8]; exact_mod_cast (CharP.cast_eq_zero_iff L 2 8).2 (by norm_num)⟩
    (by rw [hDq8]; norm_num) hfin, Fr, hFr8, hDq8, fun γ => rfl, hΦ, hDn, ?_,
    ⟨twistedE6EquivΓ Nat.prime_two (by norm_num : 1 ≤ 3) hK2 hσ2 hFr D hΦ⟩⟩
  exact LangSetup.isAlgebraic_of_isAlgClosure _ K 2
    (by show Nat.card K = D.q ^ 2; rw [hK, hDq8]; norm_num)


structure Std8 (L : Type) [Field L] [IsAlgClosed L] where
  S : LangSetup Tag.E6 L 3
  Fr : L →+* L
  hFr : ∀ c, Fr c = c ^ 8
  hq : S.D.q = 8
  hρ : ∀ γ, S.ρ γ = -γ
  hΦ : S.D.Φ = twistHom TwistTag.E6 L Fr
  hn : S.D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) L twE6W0
  hAlg : S.IsAlgebraic

theorem exists_std8 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 8) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (D : Std8 L),
      Nonempty (twistedE6RootGroup K σ ≃* D.S.Γ) := by
  obtain ⟨L, _, _, _, S, Fr, hFr, hq, hρ, hΦ, hn, hAlg, e⟩ := exists_stdSetup8 hK σ hσ
  exact ⟨L, inferInstance, inferInstance, inferInstance, ⟨S, Fr, hFr, hq, hρ, hΦ, hn, hAlg⟩, e⟩

end Datum

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
