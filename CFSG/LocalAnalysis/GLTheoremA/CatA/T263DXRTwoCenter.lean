module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXLangSel2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXRLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXRLayerTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterQ2TwoD
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs141f
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement


theorem centreTwoFree_of_commute_central {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hI : ∀ z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
      (∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute z x) →
        ∀ g ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i),
          Commute z g) :
    CentreTwoFree S i := by
  intro z hz hzc hz2
  have hz' : z ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := Subgroup.commutator_le_self _ hz
  obtain ⟨hzA, hzΓ⟩ := Subgroup.mem_inf.1 hz'
  have hzM : z ∈ S.D.model := Subgroup.commutator_le_self S.D.model hzΓ
  have hall := commute_orbit_of_commute_component S hT i hzM (hI z hz hzc)
  obtain ⟨N, hN, hzN⟩ := exists_odd_pow_of_mem_center_orbit S hK2 hT i hzA
    (Subgroup.mem_centralizer_iff.2 fun g hg => (hall g hg).symm.eq)
  exact eq_one_of_two_of_odd hz2.choose_spec hN hzN

private theorem centreTwoFree_of_shapeComm {τ : Tag} {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) {p₀ : ℕ} (S : LangSetup τ (AlgebraicClosure K) p₀)
    {a : Fin τ.rank → (AlgebraicClosure K)ˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (hsc : ShapeComm S (componentRoots (rootCharHom a) i)) :
    CentreTwoFree S i := by
  classical
  refine centreTwoFree_of_commute_central hK2 S hT i ?_
  have hrat : ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i,
      γ ∈ componentRoots (rootCharHom a) i := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    induction k generalizing δ with
    | zero => exact hδ
    | succ k ih => rw [Function.iterate_succ_apply]; exact ih _ (hρ δ hδ)
  intro z hzR hzc g hg
  have hzspan : z ∈ rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) :=
    rootSpan_mono hrat (Subgroup.commutator_le_self _ hzR).1
  have hPle : rootSpan τ (AlgebraicClosure K) (componentRoots (rootCharHom a) i) ⊓ S.D.model ≤
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    refine le_rationalComponent_of_perfect S i ?_ (Subgroup.isPerfect_iff.1 hsc.1.1)
    exact le_inf (inf_le_left.trans (rootSpan_mono fun γ hγ => ⟨0, γ, hγ, rfl⟩)) inf_le_right
  exact hsc.2 z hzspan (fun u hu => (hzc u (hPle hu)).eq) g
    (rootSpan_mono (fun γ hγ => hγ) hg)

theorem twoCenterOdd_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : TwoCenterOdd p := by
  classical
  intro τ K _ _ hK2 p₀ S a hq2 hτ hT hap h1
  haveI : CharP K 2 := hK2 ▸ ringChar.charP K
  haveI hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) 2]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h
    omega
  have hTp : rootDiagUnit τ a ^ p = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  intro i hk
  have hmem := outerD_two_mem_rationalComponent hK2 S hp hp2 hT hap h1 i hk
  rcases hk with hk | hk
  ·
    by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
    · refine centreTwoFree_of_commute hK2 S hT i fun z hzc => ?_
      exact commute_rootSpan_of_commute_component_twoD_two S hτ hq2 hT i hk h5 hmem z hzc
    ·
      obtain ⟨-, h4, -⟩ := twoD_kind_unpack hk
      have hr : compRank (componentRoots (rootCharHom a) i) = 4 := by
        have h5' : compRank (componentRoots (rootCharHom a) i) < 5 := not_le.1 h5
        omega
      obtain ⟨hρ, hsc⟩ := shapeComm_of_layer S hp hpL hT hTp h1 i
        (Or.inl ⟨hk, hr⟩) shapeComm_of_d4_twE6
      exact centreTwoFree_of_shapeComm hK2 S hT i hρ hsc
  ·
    obtain ⟨hρ, hsc⟩ := shapeComm_of_layer S hp hpL hT hTp h1 i (Or.inr hk)
      shapeComm_of_d4_twE6
    exact centreTwoFree_of_shapeComm hK2 S hT i hρ hsc

theorem twoCenterOdd_five_seven : ∀ p : ℕ, (p = 5 ∨ p = 7) → TwoCenterOdd p :=
  fun p hp => by
    rcases hp with rfl | rfl <;> exact twoCenterOdd_holds (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.T263.DX

end
