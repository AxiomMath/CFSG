module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.SteinbergD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTorality
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

set_option linter.unusedSectionVars false


theorem planesToralBar_D4_three : PlanesToralBar Tag.D4 3 :=
  planesToralBar_three_of_block a2BlockToral_D4 fun _ _ a h3 =>
    (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_D4_three a h3).le

theorem triD4PlaneToralLang {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hexp : ∀ x ∈ A, x ^ 3 = 1)
    (hcard : Nat.card A = 3 ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    ∃ v : WeylGroup TwistTag.D4.tag, ∃ g0 ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K),
      twistHom TwistTag.D4 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K) v ∧
      ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.D4.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.D4 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))).symm
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) ℓ f :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  subst hFr'
  set L := AlgebraicClosure K with hL
  set A' : Subgroup (ModGL TwistTag.D4.tag L) := A.map (triEmb K σ L) with hA'
  have hA'adj : A' ≤ adjointGroup TwistTag.D4.tag L := by
    rintro _ ⟨x, -, rfl⟩
    exact triEmb_mem_adjointGroup x
  have hA'exp : ∀ x ∈ A', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hA'card : Nat.card A' = 3 ^ 2 := by
    rw [hA', ← Nat.card_congr (A.equivMapOfInjective (triEmb K σ L) triEmb_injective).toEquiv]
    exact hcard
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := A') hA'card).is_comm
    intro x hx y hy
    exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨g, hg, hgA⟩ := planesToralBar_D4_three K h3 A' hA'adj hA'comm hA'exp hA'card
  have hcomm : (algebraMap K L).comp σ.toRingHom = (iterateFrobenius L ℓ f).comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      iterateFrobenius_def, hσ, map_pow]
  have hFix : ∀ x ∈ A', twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x := by
    rintro _ ⟨x, -, rfl⟩
    exact triEmb_fixed _ hcomm x
  obtain ⟨v, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus_twisted ℓ TwistTag.D4 f hf hFix
    hg hgA
  exact ⟨v, g0, hg0, hF, fun x hx => hmem _ ⟨x, hx, rfl⟩⟩

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
