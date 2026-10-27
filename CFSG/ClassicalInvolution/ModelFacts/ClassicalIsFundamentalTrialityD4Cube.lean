module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeRoots
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Long

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {p e : ℕ} [Fact p.Prime]

theorem trialityD4_map_eq_conj_triple (hp2 : p ≠ 2) (hq : 5 ≤ p ^ (3 * e)) (he : 1 ≤ e)
    [Finite (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))]
    {L : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    {z : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hL : IsClassicalMember p (3 * e) L z) :
    ∃ g₁ ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))))
        (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
          (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))),
      ∃ β : Fin d4.rank → ℤ, IsRoot d4 β ∧ rho β ≠ β ∧
        L.map (trialityD4Phi p e (AlgebraicClosure (GaloisField p (3 * e)))) =
          (fixedPointsIn (tripleGroup (AlgebraicClosure (GaloisField p (3 * e))) β)
              (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
                (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e))))) ⊔
            fixedPointsIn (tripleGroup (AlgebraicClosure (GaloisField p (3 * e))) (-β))
              (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
                (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))).map
            (MulAut.conj g₁⁻¹).toMonoidHom := by
  classical
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hcardF : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := card_galoisField_three_mul p e he
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
  have hx1 : Φ z ≠ 1 := fun h1 => hz1 (hinj (h1.trans (map_one Φ).symm))
  have hz' : Φ' z ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
  have hL' := isClassicalMember_map_central Φ' hΦ'surj hker' hodd hL hz'
  have hL'cent : L.map Φ' ≤ Subgroup.centralizer ({Φ' z} : Set ↥⁅R, R⁆) :=
    isSubnormal_le hL'.subnormal
  have h4 : 4 ≤ Nat.card K0 := by omega
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
  obtain ⟨g₁, hg₁G, hFg₁, β, hβ, hβne, hLeq⟩ := d4_exists_conj_eq_fixedTriple p hp2
    (isAlgebraic_zmod_of_isAlgClosure p K0 k) he hxR hx1 hx2 hL₁le hPM
    ((L.map Φ').equivMapOfInjective (⁅R, R⁆).subtype (⁅R, R⁆).subtype_injective)
    (classicalInvolutionOddCore (L.map Φ')) hcardF eY
  exact ⟨g₁, mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩, β, hβ, hβne, by rw [← hL₁Φ]; exact hLeq⟩

theorem map_conj_sup_fixedPointsIn_tripleGroup_of_torus (k : Type) [Field k]
    (F : ModGL d4 k →* ModGL d4 k) {u : ModGL d4 k} (hu : u ∈ torusGroup d4 k) (hFu : F u = u)
    {β : Fin d4.rank → ℤ} (hβ : IsRoot d4 β) :
    (fixedPointsIn (tripleGroup k β) F ⊔ fixedPointsIn (tripleGroup k (-β)) F).map
        (MulAut.conj u).toMonoidHom =
      fixedPointsIn (tripleGroup k β) F ⊔ fixedPointsIn (tripleGroup k (-β)) F := by
  have hT : ∀ γ : Fin d4.rank → ℤ, IsRoot d4 γ →
      (tripleGroup k γ).map (MulAut.conj u).toMonoidHom = tripleGroup k γ := by
    intro γ hγ
    rw [tripleGroup, Subgroup.map_sup, Subgroup.map_sup, map_conj_rootSubgroup_of_torus hu hγ,
      map_conj_rootSubgroup_of_torus hu (isRoot_rho hγ),
      map_conj_rootSubgroup_of_torus hu (isRoot_rho (isRoot_rho hγ))]
  rw [Subgroup.map_sup, map_conj_fixedPointsIn_of_fixed _ F hFu (hT β hβ),
    map_conj_fixedPointsIn_of_fixed _ F hFu (hT (-β) (IsRoot.neg hβ))]

theorem trialityD4_exists_conj_eq_rootGroup_cube (hp2 : p ≠ 2) (hq : 5 ≤ p ^ (3 * e))
    (he : 1 ≤ e) [Finite (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))]
    {L : Subgroup (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))}
    {z : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)}
    (hL : IsClassicalMember p (3 * e) L z) :
    ∃ (g : twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
      (β : Fin d4.rank → ℤ), IsRoot d4 β ∧ rho β ≠ β ∧
      L = (twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (proj β) ⊔
        twistedRootGroup (iterateFrobenius (GaloisField p (3 * e)) p e) (-proj β)).map
          (MulAut.conj g).toMonoidHom := by
  classical
  obtain ⟨g₁, hg₁R, β, hβ', hβne, hLeq⟩ := trialityD4_map_eq_conj_triple hp2 hq he hL
  obtain ⟨u, huT, huF, x₀, hx₀⟩ := exists_torus_mul_of_mem_fixedPointsIn_d4 p e hp2 he hg₁R
  have hSu := map_conj_sup_fixedPointsIn_tripleGroup_of_torus
    (AlgebraicClosure (GaloisField p (3 * e)))
    (frobTwistGL TwistTag.D4.tag (AlgebraicClosure (GaloisField p (3 * e))) p e
      (diagramMap TwistTag.D4 (AlgebraicClosure (GaloisField p (3 * e)))))
    (inv_mem huT) (by rw [map_inv, huF]) hβ'
  rw [hx₀, map_conj_mul_inv_eq _ hSu, ← map_twistedRootGroup_sup_orbit_d4 p e hp2 he hβ' hβne,
    Subgroup.map_map] at hLeq
  refine ⟨x₀⁻¹, β, hβ', hβne, Subgroup.map_injective
    (trialityD4Phi_injective p e (AlgebraicClosure (GaloisField p (3 * e)))) ?_⟩
  rw [hLeq, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun y => ?_
  simp [map_mul, map_inv]

end CFSG.ClassicalInvolution.ModelFacts
