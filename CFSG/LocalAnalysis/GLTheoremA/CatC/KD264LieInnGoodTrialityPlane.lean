module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TriD4
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots

public section

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.KE

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn


theorem mem_torusGroup_of_monomial_pow_eq_one {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) {L : Type} [Field L] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (hnp : n ^ p = 1) : n ∈ torusGroup τ L := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  have hπ : weylQuotientHom τ L ⟨_, hn⟩ = w := weylQuotientHom_torus_mul hk w hn
  have hw : w ^ p = 1 := by rw [← hπ]; exact weylQuotientHom_pow_eq_one hn hnp
  have hw1 : w = 1 := by
    by_contra hne
    have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hw
    have h2 : orderOf w = p :=
      ((Nat.dvd_prime hp).1 h1).resolve_left (fun h => hne (orderOf_eq_one_iff.1 h))
    apply hW
    rw [← h2]
    exact orderOf_dvd_natCard w
  rw [hw1, canonicalRep_one, mul_one]
  exact hk

theorem planesToralBar_of_not_dvd_weyl {τ : Tag} {p : ℕ} (hp : p.Prime)
    (hW : ¬ p ∣ Nat.card (WeylGroup τ)) : PlanesToralBar τ p := by
  intro K _ _ hpK A hA hcomm hexp hcard
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, hℓK⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have hℓ : ℓ ≠ p := by
    rintro rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
    apply hpK
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self ℓ n.ne_zero
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hAfin : (A : Set (ModGL τ (AlgebraicClosure K))).Finite := Set.toFinite _
  obtain ⟨C, hC, hCN⟩ := exists_conj_le_monomial_bar hℓ
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) hA hAfin hexp
  refine ⟨C⁻¹, inv_mem hC, fun x hx => ?_⟩
  rw [inv_inv]
  exact mem_torusGroup_of_monomial_pow_eq_one hp hW (hCN x hx) (conj_pow_eq_one' C (hexp x hx))

theorem triD4PlaneToralLang_of_not_dvd {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 2) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
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
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h)))
  have hFr' : Fr = iterateFrobenius (AlgebraicClosure K) ℓ f :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def]
  subst hFr'
  set L := AlgebraicClosure K with hL
  set A' : Subgroup (ModGL TwistTag.D4.tag L) := A.map (triEmb K σ L) with hA'
  have hA'adj : A' ≤ adjointGroup TwistTag.D4.tag L := by
    rintro _ ⟨x, -, rfl⟩
    exact triEmb_mem_adjointGroup x
  have hA'exp : ∀ x ∈ A', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hA'card : Nat.card A' = p ^ 2 := by
    rw [hA', ← Nat.card_congr (A.equivMapOfInjective (triEmb K σ L) triEmb_injective).toEquiv]
    exact hcard
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := A') hA'card).is_comm
    intro x hx y hy
    exact congrArg Subtype.val (hc.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hW : ¬ p ∣ Nat.card (WeylGroup TwistTag.D4.tag) :=
    not_dvd_card_weylGroup_D4 hp (by omega)
  obtain ⟨g, hg, hgA⟩ := planesToralBar_of_not_dvd_weyl hp hW K hpK A' hA'adj hA'comm hA'exp hA'card
  have hcomm : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L ℓ f).comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      iterateFrobenius_def, hσ, map_pow]
  have hFix : ∀ x ∈ A', twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x := by
    rintro _ ⟨x, -, rfl⟩
    exact triEmb_fixed _ hcomm x
  obtain ⟨v, g0, hg0, hF, hmem⟩ := exists_lang_torus_of_conj_torus_twisted ℓ TwistTag.D4 f hf hFix
    hg hgA
  exact ⟨v, g0, hg0, hF, fun x hx => hmem _ ⟨x, hx, rfl⟩⟩

theorem exists_langSetup_of_plane {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpℓ : p ≠ ℓ) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hexp : ∀ x ∈ A, x ^ p = 1)
    (hcard : Nat.card A = p ^ 2) :
    ∃ (S : LangSetup TwistTag.D4.tag (AlgebraicClosure K) p)
      (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃* S.Γ), S.D.q = ℓ ^ f ∧
      ∀ x ∈ A, ∃ a : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
        rootDiagUnit TwistTag.D4.tag a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧
        ((e x : S.Γ) : ModGL TwistTag.D4.tag (AlgebraicClosure K)) =
          rootDiagUnit TwistTag.D4.tag a := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) ℓ f
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨v, g0, hg0C, hg0, hmem⟩ := triD4PlaneToralLang_of_not_dvd hℓ hp hp5 hpℓ hf K hK σ hσ A
    hexp hcard Fr hFr
  let D : LangDatum TwistTag.D4.tag (AlgebraicClosure K) :=
    LangDatum.ofTwist TwistTag.D4 Fr (ℓ ^ f) hFr v hg0C hg0
  have hΦ : D.Φ = twistHom TwistTag.D4 (AlgebraicClosure K) Fr := rfl
  have hd : LangDescent D p (triEmb K σ (AlgebraicClosure K)) :=
    langDescent_triD4_inner hℓ hf hK σ hσ hFr D hΦ
  have hfin : Finite D.model := hd.finite_model
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved TwistTag.D4.tag (AlgebraicClosure K) D
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 := by
    refine ⟨hℓ.isPrimePow.pow (by omega), (CharP.cast_eq_zero_iff (AlgebraicClosure K) ℓ _).2
      (dvd_pow_self ℓ (by omega))⟩
  have hpq : ¬ p ∣ D.q := by
    show ¬ p ∣ ℓ ^ f
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  let S : LangSetup TwistTag.D4.tag (AlgebraicClosure K) p :=
    D.toSetup p ρ hρ hp (Or.inl hp5) hqpow hpq hfin
  have hι : Function.Injective (triEmb K σ (AlgebraicClosure K)) := triEmb_injective
  have hSD : S.D = D := D.toSetup_D p ρ hρ hp (Or.inl hp5) hqpow hpq hfin
  have hΓ : D.Γ = S.Γ := (congrArg LangDatum.Γ hSD).symm
  refine ⟨S, (hd.mulEquiv' hι).trans (MulEquiv.subgroupCongr hΓ), rfl, fun x hx => ?_⟩
  have he : ∀ y, (((hd.mulEquiv' hι).trans (MulEquiv.subgroupCongr hΓ) y : S.Γ) :
      ModGL TwistTag.D4.tag (AlgebraicClosure K)) =
      D.g0⁻¹ * triEmb K σ (AlgebraicClosure K) y * D.g0 := fun y =>
    hd.coe_mulEquiv' hι y
  obtain ⟨y, hy, hyx⟩ := hmem x hx
  have h1 : D.g0⁻¹ * triEmb K σ (AlgebraicClosure K) x * D.g0 = y := by
    have h2 : g0 * y * g0⁻¹ = triEmb K σ (AlgebraicClosure K) x := hyx
    rw [← h2]
    change g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y
    group
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hy).1
  have hyp : y ^ p = 1 := by
    have h3 : (D.g0⁻¹ * triEmb K σ (AlgebraicClosure K) x * D.g0) ^ p = 1 := by
      have h := conj_pow (a := D.g0⁻¹) (b := triEmb K σ (AlgebraicClosure K) x) (i := p)
      rw [inv_inv] at h
      rw [h, ← map_pow, hexp x hx, map_one]
      group
    rwa [h1] at h3
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [← ha]
    exact hy
  · have h1' : rootDiagUnit TwistTag.D4.tag (a ^ p) = rootDiagUnit TwistTag.D4.tag 1 := by
      have : rootDiagUnit TwistTag.D4.tag (a ^ p) = rootDiagUnit TwistTag.D4.tag a ^ p :=
        (rootDiagUnitHom TwistTag.D4.tag (AlgebraicClosure K)).map_pow a p
      rw [this, ← ha, hyp, CFSG.LieType.Chevalley.rootDiagUnit_one]
    have h2 : a ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1'
    exact fun i => congrFun h2 i
  · rw [he x, h1, ha]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.TriInn

end
