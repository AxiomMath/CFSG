module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6Four
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.TauCetiBridge.Even CFSG.Open




namespace TwE6FourOutAux

theorem rootDiagUnit_compatDiag_mem_C0 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 2)
    (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ a)ˣ) :
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  classical
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr⟩ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      ∀ c, Fr c = c ^ 2 ^ 2 :=
    ⟨iterateFrobenius (AlgebraicClosure K) 2 2, fun c => by rw [iterateFrobenius_def]⟩
  have hισ : ∀ c : K, algebraMap K (AlgebraicClosure K) (σ c) =
      Fr (algebraMap K (AlgebraicClosure K) c) := by
    intro c
    rw [hσ, map_pow, hFr]
  have hcoeperm : ∀ i : Fin TwistTag.E6.tag.rank,
      ((compatDiag TwistTag.E6 σ u (TwistTag.E6.perm i) : Kˣ) : K) =
        σ ((compatDiag TwistTag.E6 σ u i : Kˣ) : K) := by
    intro i
    rw [compatDiag_perm]
    rfl
  have hle := (exceptional_ambient_twisted_Frobenius_fixed_normalizer (p := 2) (f := 2)
    TwistTag.E6 Nat.prime_two (by norm_num) K hK σ hσ (AlgebraicClosure K) Fr hFr).2.1
  have hT := inf_graphFixedTorus_map_eq (algebraMap K (AlgebraicClosure K)) σ Fr hle
  have hTcard := natCard_graphFixedTorus_E6 (ℓ := 2) (f := 2) (by norm_num) hFr
  have hcompat := natCard_compatTorus_E6_mul (ℓ := 2) (f := 2) Nat.prime_two (by norm_num) hK hσ
  have hgcd : Nat.gcd 3 (2 ^ 2 + 1) = 1 := by norm_num
  rw [hgcd, mul_one] at hcompat
  rw [graphFixedRootTorus_eq_compatTorus hσsurj] at hT
  have hmapcard : Nat.card ((compatTorus (t := TwistTag.E6) σ).map
      (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)))) =
      Nat.card (compatTorus (t := TwistTag.E6) σ) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective (τ := TwistTag.E6.tag) _)
  haveI : Finite (graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr) :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; norm_num)
  have hTeq : graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr ⊓
      (graphFixedRootGroup TwistTag.E6 K σ).map
        (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))) =
      graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr :=
    Subgroup.eq_of_le_of_card_ge inf_le_left
      (le_of_eq (by rw [hT, hmapcard, hcompat, hTcard]))
  have hTle : graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr ≤
      (graphFixedRootGroup TwistTag.E6 K σ).map
        (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))) := by
    have h := (inf_le_right : graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr ⊓
      (graphFixedRootGroup TwistTag.E6 K σ).map
        (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))) ≤ _)
    rwa [hTeq] at h
  have hDT : baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))
      (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ u)) ∈
      graphFixedTorus TwistTag.E6 (AlgebraicClosure K) Fr := by
    rw [baseChangeGL_rootDiagUnit]
    refine Subgroup.mem_inf.2 ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [mem_twistedFixedGroup_iff_twistHom]
    refine ⟨torusGroup_le_adjointGroup_of_field (rootDiagUnit_mem_torusGroup _), ?_⟩
    apply twistHom_rootDiagUnit
    intro i
    apply Units.ext
    simp only [Units.coe_map]
    rw [hcoeperm i]
    exact hισ _
  obtain ⟨g, hg, hgD⟩ := Subgroup.mem_map.1 (hTle hDT)
  have hgeq := baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)) hgD
  rw [← hgeq]
  exact hg

theorem mulAut_pow_three_mem_range {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 2) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 2)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ 3 = 1) :
    β ∈ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
  obtain ⟨-, -, -, -, -, hcoeU, -, hdec, ⟨Θ, hΘ, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (p := 2) (f := 2) Nat.prime_two
      (by norm_num) K hK σ hσ
  obtain ⟨g, u, δ, hβe⟩ := hdec β
  have hΘβ : Θ β = δ := hΘ β g u δ hβe
  have h3 : (Θ β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hK4 : Nat.card K = 2 ^ 4 := by rw [hK]; norm_num
  have hcard : Nat.card (RingAut K) = 4 := (card_ringAut_and_isCyclic Nat.prime_two K hK4).1
  have h4 : orderOf (Θ β) ∣ 4 := hcard ▸ orderOf_dvd_natCard (Θ β)
  have h3' : orderOf (Θ β) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hgcd : Nat.gcd 4 3 = 1 := by norm_num
  have h1 := Nat.dvd_gcd h4 h3'
  rw [hgcd] at h1
  have hΘ1 : Θ β = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have hδ : δ = 1 := hΘβ.symm.trans hΘ1
  have hD := rootDiagUnit_compatDiag_mem_C0 hK σ.toRingHom (fun c => hσ c) u
  refine ⟨g * ⟨_, hD⟩, ?_⟩
  have hΔ : compatDiagAutHom TwistTag.E6 K σ.toRingHom u = MulAut.conj ⟨_, hD⟩ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hcoeU u x]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [map_mul, ← hΔ, hβe, hδ, fieldActor_one, mul_one]

theorem transport_mem_range {S C : Type} [Group S] [Group C] (e : S ≃* C)
    (H : ∀ β : MulAut C, β ^ 3 = 1 → β ∈ (MulAut.conj : C →* MulAut C).range)
    (E : Subgroup (MulAut S)) (hE : ∀ x ∈ E, x ^ 3 = 1) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  intro α hα
  have h3 : MulAut.congr e α ^ 3 = 1 := by
    rw [← map_pow, hE α hα, map_one]
  obtain ⟨c, hc⟩ := H _ h3
  refine ⟨e.symm c, MulEquiv.ext fun s => ?_⟩
  have hx := congrArg (fun φ : MulAut C => φ (e s)) hc
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at hx
  have hy : e.symm (c * e s * c⁻¹) = α s := by
    rw [hx, MulEquiv.symm_apply_apply]
  rw [← hy]
  simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, MulAut.conj_apply]

theorem twistedE6_case (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hq : IsTwoPow q 2) {S : Type} [Group S]
    (eS : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩)
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨hq2, hqe⟩ := hq
  have hKcard : Nat.card (GaloisField 2 4) = (2 ^ 2) ^ 2 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  let σ0 : GaloisField 2 4 →+* GaloisField 2 4 := iterateFrobenius (GaloisField 2 4) 2 2
  have hσ0 : ∀ c, σ0 c = c ^ 2 ^ 2 := fun c => by
    show iterateFrobenius (GaloisField 2 4) 2 2 c = c ^ 2 ^ 2
    rw [iterateFrobenius_def]
  let σE : GaloisField 2 4 ≃+* GaloisField 2 4 :=
    RingEquiv.ofBijective σ0 ⟨σ0.injective, Finite.surjective_of_injective σ0.injective⟩
  have hσE : ∀ c, σE c = c ^ 2 ^ 2 := hσ0
  have hqcard : q.card = 2 ^ 2 := by
    rw [TauCeti.PrimePower.card_def, hq2, hqe]
  have hK' : Nat.card (GaloisField 2 4) = q.card ^ TwistTag.E6.order := by
    rw [hKcard, hqcard]
    rfl
  obtain ⟨eB⟩ := twistedBridgeEven_twistedE6 q hv hq2 (GaloisField 2 4) hK' σE.toRingHom
    (fun c => by rw [hqcard]; exact hσE c)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨eC⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form (p := 2) (f := 2) Nat.prime_two
      (by norm_num) (GaloisField 2 4) hKcard σE hσE
  exact transport_mem_range ((eS.trans eB.symm).trans eC)
    (fun β hβ => mulAut_pow_three_mem_range hKcard σE hσE β hβ) E (fun x hx => hE.2 x hx)

end TwE6FourOutAux

theorem twE6FourOut_holds : TwE6FourOut := by
  intro S _ _ d hd hS E hE
  obtain ⟨eS⟩ := hS
  obtain ⟨d1, hv⟩ := d
  have key : ∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.twistedE6 q ∧ IsTwoPow q 2 := by
    cases d1 with
    | twistedE6 q => exact ⟨q, rfl, hd⟩
    | _ => simp [IsTwistedE6FourIndex] at hd
  obtain ⟨q, rfl, hq⟩ := key
  exact TwE6FourOutAux.twistedE6_case q hv hq eS E hE

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
