module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalCentral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {p e : ℕ} [Fact p.Prime]

theorem trialityD4_map_eq_conj_fixed (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (he : 1 ≤ e)
    [Finite (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))]
    {L : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    {z : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hL : IsClassicalMember p e L z) :
    ∃ g₁ ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
        (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
          (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))),
      ∃ β : Fin d4.rank → ℤ, IsRoot d4 β ∧ rho β = β ∧
        L.map (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
          (fixedPointsIn (rootSubgroup TwistTag.D4.tag
                (AlgebraicClosure (GaloisField p (3 * e))) β)
              (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
                (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) ⊔
            fixedPointsIn (rootSubgroup TwistTag.D4.tag
                (AlgebraicClosure (GaloisField p (3 * e))) (-β))
              (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
                (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))).map
            (MulAut.conj g₁⁻¹).toMonoidHom := by
  classical
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hcardF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  set K0 := GaloisField p (3 * e) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set F := frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.D4.tag k) F with hR
  set Φ := trialityD4Phi p e k with hΦ
  have hrange : Φ.range = ⁅R, R⁆ := range_trialityD4Phi p e hp2 he
  have hinj : Function.Injective Φ := trialityD4Phi_injective p e k
  have hΦR : ∀ y, Φ y ∈ R := trialityD4Phi_mem_fixedPointsIn p e hp2 he
  let Φ' : twistedGroup (iterateFrobenius K0 p e) →* ↥⁅R, R⁆ :=
    Φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Finite ↥⁅R, R⁆ := Finite.of_surjective Φ' hΦ'surj
  have hker' : Φ'.ker ≤ Subgroup.center (twistedGroup (iterateFrobenius K0 p e)) := by
    rw [MonoidHom.ker_codRestrict, (MonoidHom.ker_eq_bot_iff Φ).2 hinj]
    exact bot_le
  have hz1 : z ≠ 1 := by
    intro h1
    have := hL.orderOf_eq_two
    rw [h1, orderOf_one] at this
    omega
  have hz' : Φ' z ≠ 1 := fun h1 => hz1 (hinj ((congrArg Subtype.val h1).trans (map_one Φ).symm))
  have hL' := isClassicalMember_map_central Φ' hΦ'surj hker' hodd hL hz'
  have hL'cent : L.map Φ' ≤ Subgroup.centralizer ({Φ' z} : Set ↥⁅R, R⁆) :=
    isSubnormal_le hL'.subnormal
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by omega
  have hP := isPComponent_two_of_isClassicalMember h4 hL'
  have hPM := isPComponent_inf_centralizer_of_isPComponent ⁅R, R⁆ (Φ' z) hL'cent hP
  set x : ModGL TwistTag.D4.tag k := Φ z with hx_def
  have hxR : x ∈ R := hΦR z
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two] at this
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, hz2, map_one]
  set L₁ : Subgroup (ModGL TwistTag.D4.tag k) := (L.map Φ').map (⁅R, R⁆).subtype with hL₁
  have hL₁Φ : L₁ = L.map Φ := by
    rw [hL₁, Subgroup.map_map]
    rfl
  have hL₁le : L₁ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hL'cent hy)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
  obtain ⟨eY⟩ := hL'.nonempty_equiv
  obtain ⟨g₁, hg₁G, hFg₁, β, hβ, hβfix, hLeq⟩ := d4_exists_conj_eq_fixedRankOne p hp2
    (isAlgebraic_zmod_of_isAlgClosure p K0 k) he hxR hx2 hL₁le hPM
    ((L.map Φ').equivMapOfInjective (⁅R, R⁆).subtype (⁅R, R⁆).subtype_injective)
    (classicalInvolutionOddCore (L.map Φ')) (CFSG.ComponentClassification.OddCore.odd_card _)
    hcardF hq eY
  exact ⟨g₁, mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩, β, hβ, hβfix, by rw [← hL₁Φ]; exact hLeq⟩

theorem map_conj_sup_fixedPointsIn_rootSubgroup_of_torus {τ : Tag} {k : Type} [Field k]
    (F : ModGL τ k →* ModGL τ k) {u : ModGL τ k} (hu : u ∈ torusGroup τ k) (hFu : F u = u)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    (fixedPointsIn (rootSubgroup τ k β) F ⊔ fixedPointsIn (rootSubgroup τ k (-β)) F).map
        (MulAut.conj u).toMonoidHom =
      fixedPointsIn (rootSubgroup τ k β) F ⊔ fixedPointsIn (rootSubgroup τ k (-β)) F := by
  rw [Subgroup.map_sup, map_conj_fixedPointsIn_rootSubgroup_of_torus F hu hFu hβ,
    map_conj_fixedPointsIn_rootSubgroup_of_torus F hu hFu (IsRoot.neg hβ)]

theorem map_twistedRootGroup_sup_fixed_d4 (hp2 : p ≠ 2) (he : 1 ≤ e) {β : Fin d4.rank → ℤ}
    (hβ : IsRoot d4 β) (hfix : rho β = β) :
    (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β) ⊔
        twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (-proj β)).map
          (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
      fixedPointsIn (rootSubgroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) β)
          (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
            (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) ⊔
        fixedPointsIn (rootSubgroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e)))
            (-β)) (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
          (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) := by
  have hρneg : rho (-β) = -β := (permLattice_neg _ β).trans (congrArg Neg.neg hfix)
  rw [Subgroup.map_sup, map_twistedRootGroup_fixed_d4 p e hp2 he hβ hfix, ← map_neg proj β,
    map_twistedRootGroup_fixed_d4 p e hp2 he (IsRoot.neg hβ) hρneg]

theorem map_conj_mul_inv_eq {M : Type*} [Group M] (S : Subgroup M) {u : M}
    (hu : S.map (MulAut.conj u⁻¹).toMonoidHom = S) (y : M) :
    S.map (MulAut.conj (u * y)⁻¹).toMonoidHom = S.map (MulAut.conj y⁻¹).toMonoidHom := by
  have h : (MulAut.conj (u * y)⁻¹).toMonoidHom =
      (MulAut.conj y⁻¹).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun w => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev,
      inv_inv]
    group
  rw [h, ← Subgroup.map_map, hu]

theorem trialityD4_exists_conj_eq_rootGroup (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (he : 1 ≤ e)
    [Finite (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))]
    {L : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    {z : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hL : IsClassicalMember p e L z) :
    ∃ (g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) (β : Fin d4.rank → ℤ),
      IsRoot d4 β ∧ rho β = β ∧
      L = (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β) ⊔
        twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (-proj β)).map
          (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨g₁, hg₁R, β, hβ', hβfix', hLeq⟩ := trialityD4_map_eq_conj_fixed hp2 hq he hL
  obtain ⟨u, huT, huF, x₀, hx₀⟩ := exists_torus_mul_of_mem_fixedPointsIn_d4 p e hp2 he hg₁R
  have hSu := map_conj_sup_fixedPointsIn_rootSubgroup_of_torus
    (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
      (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))
    (inv_mem huT) (by rw [map_inv, huF]) hβ'
  rw [hx₀, map_conj_mul_inv_eq _ hSu, ← map_twistedRootGroup_sup_fixed_d4 hp2 he hβ' hβfix',
    Subgroup.map_map] at hLeq
  refine ⟨x₀⁻¹, β, hβ', hβfix', Subgroup.map_injective
    (trialityD4Phi_injective p e (AlgebraicClosure (GaloisField p (3 * e)))) ?_⟩
  rw [hLeq, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun y => ?_
  simp [map_mul, map_inv]

end CFSG.ClassicalInvolution.ModelFacts
