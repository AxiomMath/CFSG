module

public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Tw
public import CFSG.ClassicalInvolution.Q3.Q3ExcCenterE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance CFSG.LieType.Steinberg.Minuscule
open scoped MatrixGroups

theorem exc3_minGroup_rootGroup_pow_three_of_char {τ : Tag} {D : MinData τ} (hV : D.Valid)
    (k : Type) [Field k] (h3 : (3 : k) = 0) (γ : Fin τ.rank → ℤ) :
    ∀ a ∈ hV.rootGroup k γ, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 ha
  have h3' : c + c + c = 0 := by linear_combination c * h3
  have e : hV.xm k γ c ^ 3 = hV.xm k γ (c + c + c) := by
    rw [hV.xm_add, hV.xm_add, show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
  rw [e, h3', hV.xm_zero]

theorem exc3_twistedRootGroup_pow_three {K0 : Type} [Field K0] (h3 : (3 : K0) = 0)
    (θ : K0 →+* K0) {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (hfix : rho β = β) :
    ∀ a ∈ twistedRootGroup K0 θ (proj β), a ^ 3 = 1 := by
  intro a ha
  rw [mem_twistedRootGroup_iff θ hβ rfl, hfix, sup_idem] at ha
  have h := exc3_minGroup_rootGroup_pow_three_of_char e6Data_valid K0 h3 β
    (a : ↥(e6Data_valid.minGroup K0)) ha
  exact Subtype.ext (by simpa using h)

section Lift

variable (hp : Nat.Prime 3)

include hp

theorem tw6_lift {L : Subgroup (twistedE6Group 3 1)}
    (hZ2 : IsPGroup 2 (twistedE6Phi 3 1 (AlgebraicClosure (GaloisField 3 (2 * 1)))).ker)
    (eL : SL(2, ZMod 3) ≃* L)
    {g₁ : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1)))}
    (hg₁R : g₁ ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag
        (AlgebraicClosure (GaloisField 3 (2 * 1))))
      (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1))) 3 1
        (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField 3 (2 * 1))))))
    {β : Fin (Tag.rank .E6) → ℤ} (hβ : IsRoot .E6 β) (hβfix : rho β = β)
    (hLeq : L.map (twistedE6Phi 3 1 (AlgebraicClosure (GaloisField 3 (2 * 1)))) =
      (fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1))) β)
          (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1))) 3 1
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField 3 (2 * 1))))) ⊔
        fixedPointsIn (rootSubgroup TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1)))
          (-β)) (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField 3 (2 * 1))) 3 1
            (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField 3 (2 * 1)))))).map
        (MulAut.conj g₁⁻¹).toMonoidHom) :
    L ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum 3 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  set K0 := GaloisField 3 (2 * 1) with hK0
  set k := AlgebraicClosure K0 with hk
  have hCharK : CharP K0 3 := inferInstance
  have h3 : (3 : K0) = 0 := by
    have := CharP.cast_eq_zero K0 3
    exact_mod_cast this
  set F := frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k) with hF
  set Φ := twistedE6Phi 3 1 k with hΦ
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group 3 1) := ker_twistedE6Phi_le_center 3 1 k
  have hβneg : IsRoot .E6 (-β) := IsRoot.neg hβ
  have hρneg : rho (-β) = -β := (permLattice_neg _ β).trans (congrArg Neg.neg hβfix)
  obtain ⟨u, huT, huF, x₀, hx₀⟩ := exists_torus_mul_of_mem_fixedPointsIn 3 1 hp2 hf hg₁R
  have hx₀' : g₁ = u * Φ x₀ := hx₀
  set S := fixedPointsIn (rootSubgroup TwistTag.E6.tag k β) F ⊔
    fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-β)) F with hS
  have hSu : S.map (MulAut.conj u⁻¹).toMonoidHom = S := by
    have hFu' : F u⁻¹ = u⁻¹ := by rw [map_inv, huF]
    rw [hS, Subgroup.map_sup,
      map_conj_fixedPointsIn_rootSubgroup_of_torus F (inv_mem huT) hFu' hβ,
      map_conj_fixedPointsIn_rootSubgroup_of_torus F (inv_mem huT) hFu' hβneg]
  have hconj : (MulAut.conj g₁⁻¹).toMonoidHom =
      (MulAut.conj (Φ x₀)⁻¹).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    simp only [hx₀', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev, inv_inv]
    group
  have hLeq' : L.map Φ = S.map (MulAut.conj (Φ x₀)⁻¹).toMonoidHom := by
    rw [hLeq, hconj, ← Subgroup.map_map, hSu]
  set Rγ := twistedRootGroup K0 (frobQ 3 1) (proj β) ⊔
    twistedRootGroup K0 (frobQ 3 1) (-proj β) with hRγ
  have hSΦ : S = Rγ.map Φ := by
    rw [hRγ, Subgroup.map_sup, map_twistedRootGroup_fixed 3 1 hp2 hf hβ hβfix, ← map_neg proj β,
      map_twistedRootGroup_fixed 3 1 hp2 hf hβneg hρneg]
  have hmap : L.map Φ = (Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom).map Φ := by
    rw [hLeq', hSΦ, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    simp [map_mul, map_inv]
  have hA3 : ∀ a ∈ twistedRootGroup K0 (frobQ 3 1) (proj β), a ^ 3 = 1 :=
    exc3_twistedRootGroup_pow_three h3 (frobQ 3 1) hβ hβfix
  have hB3 : ∀ a ∈ twistedRootGroup K0 (frobQ 3 1) (-proj β), a ^ 3 = 1 := by
    rw [← map_neg proj β]
    exact exc3_twistedRootGroup_pow_three h3 (frobQ 3 1) hβneg hρneg
  have hconj3 : ∀ C : Subgroup (twistedE6Group 3 1), (∀ a ∈ C, a ^ 3 = 1) →
      ∀ a ∈ C.map (MulAut.conj x₀⁻¹).toMonoidHom, a ^ 3 = 1 := by
    rintro C hC _ ⟨a, ha, rfl⟩
    show (x₀⁻¹ * a * x₀⁻¹⁻¹) ^ 3 = 1
    rw [conj_pow, hC a ha]
    group
  have hRgen := exc3_closure_pow_three_eq_top (hconj3 _ hA3) (hconj3 _ hB3)
  have hRsup : Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom =
      (twistedRootGroup K0 (frobQ 3 1) (proj β)).map (MulAut.conj x₀⁻¹).toMonoidHom ⊔
        (twistedRootGroup K0 (frobQ 3 1) (-proj β)).map (MulAut.conj x₀⁻¹).toMonoidHom :=
    Subgroup.map_sup _ _ _
  have hLR : L = Rγ.map (MulAut.conj x₀⁻¹).toMonoidHom :=
    exc3_eq_of_map_eq hker hZ2 (exc3_closure_pow_three_of_equiv eL) (by rw [hRsup]; exact hRgen)
      hmap
  have hlong := isLongestRoot_twistedDatum_proj (frobQ 3 1) hβ hβfix
  exact ⟨x₀⁻¹, proj β, Or.inl hlong, hLR⟩

end Lift

section Core

variable (hp : Nat.Prime 3)

include hp

theorem tw6_core (hZ : Subgroup.center (twistedE6Group 3 1) = ⊥) {z : twistedE6Group 3 1}
    (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    oddCoreIn (Subgroup.centralizer ({z} : Set (twistedE6Group 3 1))) = ⊥ ∧
      ∀ L : Subgroup (twistedE6Group 3 1), IsClassicalMember3 L z →
        classicalInvolutionOddCore L = ⊥ →
        L ∈ Generic.fundamentalSubgroups .twistedE6 (twistedE6Datum 3 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hfin' : Finite (Generic.modelUniv .twistedE6 0 3 1 hp).K := finite_modelUniv_twistedE6 hp
  have : Finite (twistedE6Group 3 1) := hfin'
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  set K0 := GaloisField 3 (2 * 1) with hK0
  set k := AlgebraicClosure K0 with hk
  set F := frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set Φ := twistedE6Phi 3 1 k with hΦ
  have hker : Φ.ker ≤ Subgroup.center (twistedE6Group 3 1) := ker_twistedE6Phi_le_center 3 1 k
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hrange : Φ.range = ⁅R, R⁆ := range_twistedE6Phi 3 1 hp2 hf
  have hΦR : ∀ g, Φ g ∈ R := twistedE6Phi_mem_fixedPointsIn 3 1 hp2 hf
  have hk' : letI := ZMod.algebra k 3; Algebra.IsAlgebraic (ZMod 3) k :=
    isAlgebraic_zmod_of_isAlgClosure 3 K0 k
  have hdec : ∀ g ∈ R, ∃ u ∈ torusGroup TwistTag.E6.tag k, F u = u ∧ ∃ a ∈ ⁅R, R⁆, g = u * a := by
    intro g hg
    obtain ⟨u, huT, huF, x', hx'⟩ := exists_torus_mul_of_mem_fixedPointsIn 3 1 hp2 hf hg
    exact ⟨u, huT, huF, Φ x', hrange ▸ ⟨x', rfl⟩, hx'⟩
  set x := Φ z with hx_def
  have hx2 : x ^ 2 = 1 := by rw [hx_def, ← map_pow, pow_two, hz2, map_one]
  have hx1 : x ≠ 1 := fun h => hz1 (hΦinj (by rw [← hx_def, h, map_one]))
  obtain ⟨g₁, hg₁G, hFg₁, hA, hB⟩ := e6tw_core (p := 3) (e := 1) hp2 hf (by norm_num) hk' hdec
    (hΦR z) hx2 hx1
  have hmap : (Subgroup.centralizer ({z} : Set (twistedE6Group 3 1))).map Φ =
      ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hrange ▸ ⟨c, rfl⟩, ?_⟩
      have := congrArg Φ hc
      simpa [map_mul] using this
    · rintro ⟨hyH, hyx⟩
      rw [← hrange] at hyH
      obtain ⟨c, rfl⟩ := hyH
      refine ⟨c, ?_, rfl⟩
      apply hΦinj
      simpa [map_mul] using hyx
  refine ⟨?_, ?_⟩
  · set O := oddCoreIn (Subgroup.centralizer ({z} : Set (twistedE6Group 3 1))) with hO
    have hOle : O ≤ Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)) := oddCoreIn_le _
    have hOG : O.map Φ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) := by
      rw [← hmap]
      exact Subgroup.map_mono hOle
    have hnorm : ∀ y ∈ ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)),
        ∀ n ∈ O.map Φ, y * n * y⁻¹ ∈ O.map Φ := by
      rw [← hmap]
      rintro _ ⟨c, hc, rfl⟩ _ ⟨o, ho, rfl⟩
      have h := conj_mem_oddCoreIn hc ho
      have h2 := Subgroup.mem_map_of_mem Φ h
      rw [map_mul, map_mul, map_inv] at h2
      exact h2
    have hodd : Odd (Nat.card (O.map Φ)) := by
      rw [← Nat.card_congr (O.equivMapOfInjective Φ hΦinj).toEquiv]
      exact odd_card_oddCoreIn _
    exact (Subgroup.map_eq_bot_iff_of_injective O hΦinj).1 (hA _ hOG hnorm hodd)
  · intro L hL hO
    obtain ⟨e₀⟩ := hL.nonempty_equiv_sl2 hO
    have hLC : L ≤ Subgroup.centralizer ({z} : Set (twistedE6Group 3 1)) :=
      isSubnormal_le hL.subnormal
    have hLG : L.map Φ ≤ ⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k)) := by
      rw [← hmap]
      exact Subgroup.map_mono hLC
    have hLsub : IsSubnormal (L.map Φ)
        (⁅R, R⁆ ⊓ Subgroup.centralizer ({x} : Set (ModGL TwistTag.E6.tag k))) := by
      have h1 := CFSG.ComponentClassification.Components.chain_map Φ hL.subnormal
      rwa [hmap] at h1
    obtain ⟨β, hβ, hfix, hLeq⟩ := hB (L.map Φ) hLG
      ⟨e₀.symm.trans (L.equivMapOfInjective Φ hΦinj)⟩ hLsub
    have hg₁R : g₁ ∈ R := mem_fixedPointsIn.2 ⟨hg₁G, hFg₁⟩
    have hZ2 : IsPGroup 2 Φ.ker := fun g => ⟨0, by
      have h1 : (g : twistedE6Group 3 1) = 1 := by
        apply hΦinj
        rw [map_one]
        exact MonoidHom.mem_ker.1 g.2
      have hg1 : g = 1 := Subtype.ext (by simpa using h1)
      simp [hg1]⟩
    exact tw6_lift hp hZ2 e₀.symm hg₁R hβ hfix hLeq

end Core

theorem classicalMembersFundamental3Tag_twistedE6 : ClassicalMembersFundamental3Tag .twistedE6 := by
  intro n hp hFT hadm L z hL hO
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, hZ2⟩ := modelFiniteCenterTwoGroup3 .twistedE6 0 hp hFT hadm
  have hZ := exc3_center_twistedE6_model hp
  have : Finite (twistedE6Group 3 1) := hfin
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hL.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := by
    intro h
    have := hL.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  exact (tw6_core hp hZ hz2 hz1).2 L hL hO

theorem simpleOddCentralizerFreeTag_twistedE6 : SimpleOddCentralizerFreeTag .twistedE6 := by
  intro n hp hadm s hs
  obtain rfl : n = 0 := hadm.2.2
  obtain ⟨hfin, hZ2⟩ := modelFiniteCenterTwoGroup3 .twistedE6 0 hp trivial hadm
  have hZ := exc3_center_twistedE6_model hp
  have : Finite (twistedE6Group 3 1) := hfin
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hqs := isQuasisimple_twistedE6 3 1 le_rfl
  refine exc3_simpleOddCentralizer_of_cover (MonoidHom.id _) Function.surjective_id ?_ ?_ s hs
  · rw [MonoidHom.ker_id, hZ]
  · intro c hc2
    by_cases hc1 : c = 1
    · subst hc1
      have hC : Subgroup.centralizer ({1} : Set (Generic.modelUniv .twistedE6 0 3 1 hp).K) = ⊤ := by
        simp
      rw [hC]
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_isQuasisimple (open_isQuasisimple hqs)
      exact oddCoreIn_top_eq_bot_of_isQuasisimple (open_isQuasisimple hqs) hZ2 ⟨x, hx⟩
    · exact (tw6_core hp hZ hc2 hc1).1

theorem oddCentralizerFreeTag_twistedE6 : OddCentralizerFreeTag .twistedE6 :=
  oddCentralizerFreeTag_of_simple _ simpleOddCentralizerFreeTag_twistedE6

end CFSG.ClassicalInvolution.Q3
