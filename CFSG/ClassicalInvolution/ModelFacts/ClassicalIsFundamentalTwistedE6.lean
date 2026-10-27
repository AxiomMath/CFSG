module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Chain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectNodes
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} [Fact p.Prime]

theorem twistedE6_map_eq_conj_fixed (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) [Finite (twistedE6Group p f)]
    {L : Subgroup (twistedE6Group p f)} {z : twistedE6Group p f} (hL : IsClassicalMember p f L z) :
    ∃ g₁ ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))))
        (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
          (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))),
      ∃ β : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 β ∧ rho β = β ∧
        L.map (twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f)))) =
          (fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) β)
              (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
                (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))) ⊔
            fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f)))
              (-β)) (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
                (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f)))))).map
            (MulAut.conj g₁⁻¹).toMonoidHom := by
  classical
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  set F := frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Φ := twistedE6Phi p f k with hΦ
  have hrange : Φ.range = ⁅R, R⁆ := range_twistedE6Phi p f hp2 hf
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group p f) := ker_twistedE6Phi_le_center p f k
  have hΦR : ∀ y : twistedE6Group p f, Φ y ∈ R := twistedE6Phi_mem_fixedPointsIn p f hp2 hf
  have hqs := isQuasisimple_twistedE6 p f hf
  have hz : Φ z ≠ 1 := by
    intro h1
    have hzc : z ∈ Subgroup.center (twistedE6Group p f) := hker (MonoidHom.mem_ker.2 h1)
    obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := exists_two_involutions_fixedGroup (frobQ p f)
      (two_ne_zero_galoisField (2 * f) hp2)
    by_cases h : y₁ = z
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₂
        (fun h' => hne (h.trans h'.symm))
    · exact false_of_isClassicalMember_of_central (open_isQuasisimple hqs) hodd hL hzc hy₁ h
  let Φ' : twistedE6Group p f →* ↥⁅R, R⁆ :=
    Φ.codRestrict _ (fun g => by rw [← hrange]; exact ⟨g, rfl⟩)
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have : Finite ↥⁅R, R⁆ := Finite.of_surjective Φ' hΦ'surj
  have hker' : Φ'.ker ≤ Subgroup.center (twistedE6Group p f) := by
    rw [MonoidHom.ker_codRestrict]
    exact hker
  have hz' : Φ' z ≠ 1 := fun h1 => hz (congrArg Subtype.val h1)
  have hL' := isClassicalMember_map_central Φ' hΦ'surj hker' hodd hL hz'
  have hL'cent : L.map Φ' ≤ Subgroup.centralizer ({Φ' z} : Set ↥⁅R, R⁆) :=
    isSubnormal_le hL'.subnormal
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by omega
  have hP := isPComponent_two_of_isClassicalMember h4 hL'
  have hPM := isPComponent_inf_centralizer_of_isPComponent ⁅R, R⁆ (Φ' z) hL'cent hP
  set x : ModGL TwistTag.E6.tag k := Φ z with hx_def
  have hxR : x ∈ R := hΦR z
  have hz2 : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two] at this
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, hz2, map_one]
  set L₁ : Subgroup (ModGL TwistTag.E6.tag k) := (L.map Φ').map (⁅R, R⁆).subtype with hL₁
  have hL₁Φ : L₁ = L.map Φ := by
    rw [hL₁, Subgroup.map_map]
    rfl
  have hL₁le : L₁ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer {x} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hL'cent hy)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
  obtain ⟨eY⟩ := hL'.nonempty_equiv
  obtain ⟨g₁, hg₁G, hFg₁, β, hβ, hβfix, hLeq⟩ := e6_exists_conj_eq_fixedRankOne p hp2
    (isAlgebraic_zmod_of_isAlgClosure p K0 k) hf hxR hx2 hL₁le hPM
    ((L.map Φ').equivMapOfInjective (⁅R, R⁆).subtype (⁅R, R⁆).subtype_injective)
    (classicalInvolutionOddCore (L.map Φ')) (CFSG.ComponentClassification.OddCore.odd_card _)
    hcardF hq eY
  exact ⟨g₁, mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩, β, hβ, hβfix, by rw [← hL₁Φ]; exact hLeq⟩

theorem twistedE6_exists_conj_eq_rootGroup (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) [Finite (twistedE6Group p f)]
    {L : Subgroup (twistedE6Group p f)} {z : twistedE6Group p f} (hL : IsClassicalMember p f L z) :
    ∃ (g : twistedE6Group p f) (β : Fin (Tag.rank .E6) → ℤ), IsRoot .E6 β ∧ rho β = β ∧
      L = (twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (proj β) ⊔
        twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (-proj β)).map
          (MulAut.conj g).toMonoidHom := by
  classical
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨g₁, hg₁R, β, hβ', hβfix', hLeq⟩ := twistedE6_map_eq_conj_fixed hp2 hq hadm hL
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  set F := frobTwistGL TwistTag.E6.tag k p f (diagramMap TwistTag.E6 k) with hF
  set Φ := twistedE6Phi p f k with hΦ
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group p f) := ker_twistedE6Phi_le_center p f k
  have hβneg : IsRoot .E6 (-β) := IsRoot.neg hβ'
  have hρneg : rho (-β) = -β := (permLattice_neg _ β).trans (congrArg Neg.neg hβfix')
  obtain ⟨u, huT, huF, x₀, hx₀⟩ := exists_torus_mul_of_mem_fixedPointsIn p f hp2 hf hg₁R
  have hx₀' : g₁ = u * Φ x₀ := hx₀
  set S := fixedPointsIn (rootSubgroup TwistTag.E6.tag k β) F ⊔
    fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-β)) F with hS
  have hSu : S.map (MulAut.conj u⁻¹).toMonoidHom = S := by
    have hFu' : F u⁻¹ = u⁻¹ := by rw [map_inv, huF]
    rw [hS, Subgroup.map_sup,
      map_conj_fixedPointsIn_rootSubgroup_of_torus F (inv_mem huT) hFu' hβ',
      map_conj_fixedPointsIn_rootSubgroup_of_torus F (inv_mem huT) hFu' hβneg]
  have hconj : (MulAut.conj g₁⁻¹).toMonoidHom =
      (MulAut.conj (Φ x₀)⁻¹).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp only [hx₀', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, inv_inv]
    group
  have hLeq' : L.map Φ = S.map (MulAut.conj (Φ x₀)⁻¹).toMonoidHom := by
    rw [hLeq, hconj, ← Subgroup.map_map, hSu]
  set Rγ := twistedRootGroup K0 (frobQ p f) (proj β) ⊔
    twistedRootGroup K0 (frobQ p f) (-proj β) with hRγ
  have hSΦ : S = Rγ.map Φ := by
    rw [hRγ, Subgroup.map_sup, map_twistedRootGroup_fixed p f hp2 hf hβ' hβfix', ← map_neg proj β,
      map_twistedRootGroup_fixed p f hp2 hf hβneg hρneg]
  have hlong := isLongestRoot_twistedDatum_proj (frobQ p f) hβ' hβfix'
  have hRγmem : Rγ ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f) :=
    ⟨1, proj β, Or.inl hlong, (conjSub_one Rγ).symm⟩
  have hRγperf : ⁅Rγ, Rγ⁆ = Rγ := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_)
      (fundPerfect_twistedE6 p f hadm (by omega) Rγ hRγmem)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hRperf : ⁅Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom, Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom⁆ =
      Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom := by
    rw [← Subgroup.map_commutator, hRγperf]
  have hmap : L.map Φ = (Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom).map Φ := by
    rw [hLeq', hSΦ, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp [map_mul, map_inv]
  exact ⟨x₀⁻¹, β, hβ', hβfix',
    eq_of_map_eq_of_isPerfect Φ hker (Subgroup.isPerfect_iff.1 hL.perfect) hRperf hmap⟩

theorem twistedE6_mem_fundamentalSubgroups (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) [Finite (twistedE6Group p f)]
    {L : Subgroup (twistedE6Group p f)} {z : twistedE6Group p f} (hL : IsClassicalMember p f L z) :
    L ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f) := by
  obtain ⟨g, β, hβ, hβfix, hLeq⟩ := twistedE6_exists_conj_eq_rootGroup hp2 hq hadm hL
  exact ⟨g, proj β, Or.inl (isLongestRoot_twistedDatum_proj (frobQ p f) hβ hβfix), hLeq⟩

theorem classicalMembersFundamental_twistedE6 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hadm : StatedLieAdmissible .twistedE6 n p f) :
    ClassicalMembersFundamental p f .twistedE6 n f hp := by
  obtain rfl : n = 0 := hadm.2.2
  have hfin' : Finite (modelUniv .twistedE6 0 p f hp).K := finite_modelUniv_twistedE6 hp
  have hfin : Finite (twistedE6Group p f) := hfin'
  intro L z hL
  exact twistedE6_mem_fundamentalSubgroups hp2 hq hadm hL

end CFSG.ClassicalInvolution.ModelFacts
