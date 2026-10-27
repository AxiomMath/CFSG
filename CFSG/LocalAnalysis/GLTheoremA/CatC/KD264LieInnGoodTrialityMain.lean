module

import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTrialityPlane
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTrialityBig
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieTriInnGoodMain
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyPlane
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

theorem innGoodAt_three_of_triInnGoodAt {S : Type} [Group S] (h : TriInnGoodAt S)
    (d : TauCeti.LieTypeIndex) : InnGoodAt 3 d S := by
  intro D hD hcard hDle
  left
  have hne : D ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨⟨β, hβD⟩, hβ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hβ1' : β ≠ 1 := fun h1 => hβ1 (Subtype.ext h1)
  obtain ⟨P, hPfix, hPperf, hPdvd⟩ := h β (hDle hβD) (hD.2 β hβD) hβ1'
  exact ⟨β, hβD, hβ1', P, hPfix, hPperf, hPdvd⟩


section Plane

namespace TriInn

theorem forall_pow_eq_one_of_rootDiagUnit {τ : Tag} {L : Type} [Field L] {p : ℕ}
    {b : Fin τ.rank → Lˣ} (h : rootDiagUnit τ b ^ p = 1) : ∀ i, b i ^ p = 1 := by
  have h1 : rootDiagUnit τ (b ^ p) = rootDiagUnit τ 1 := by
    have : rootDiagUnit τ (b ^ p) = rootDiagUnit τ b ^ p :=
      (rootDiagUnitHom τ L).map_pow b p
    rw [this, h, CFSG.LieType.Chevalley.rootDiagUnit_one]
  have h2 : b ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  exact fun i => congrFun h2 i

theorem perfectCentralizerPlanes_trialityModel
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    PerfectCentralizerPlanes p ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro A hA hcard
  obtain ⟨S, e, hSq, hT⟩ :=
    exists_langSetup_of_plane hℓ hp hp5 hpℓ hf K hK σ hσ A hA.2 hcard
  let ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      ModGL TwistTag.D4.tag (AlgebraicClosure K) := S.Γ.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιe : ∀ x, ι x = ((e x : S.Γ) : ModGL TwistTag.D4.tag (AlgebraicClosure K)) :=
    fun x => rfl
  set D₁ : Subgroup (ModGL TwistTag.D4.tag (AlgebraicClosure K)) := A.map ι with hD₁
  have hD₁card : Nat.card D₁ = p ^ 2 := by
    rw [hD₁, Subgroup.card_map_of_injective hι, hcard]
  have hD₁E : D₁ ≤ S.E := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, haT, -, hxa⟩ := hT x hx
    refine S.E_all _ ⟨?_, ?_⟩ ?_
    · rw [hιe, hxa]
      exact haT
    · exact (e x).2
    · rw [← map_pow, hA.2 x hx, map_one]
  obtain ⟨γ, hγr, hγn⟩ := S.exists_root_not_mem_planeKernel hD₁E hD₁card
  obtain ⟨a, haD, ha1, hγa⟩ := S.exists_nontrivial_killing hD₁E hD₁card γ
  obtain ⟨b, hbD, hγb⟩ : ∃ b : Fin TwistTag.D4.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.D4.tag b ∈ D₁ ∧ rootChar b γ ≠ 1 := by
    by_contra h
    push Not at h
    exact hγn ⟨hγr, h⟩
  have haE := hD₁E haD
  have hbE := hD₁E hbD
  have haT : rootDiagUnit TwistTag.D4.tag a ∈ S.D.torus := (S.E_le haE).1
  have hbT : rootDiagUnit TwistTag.D4.tag b ∈ S.D.torus := (S.E_le hbE).1
  have hTp : rootDiagUnit TwistTag.D4.tag a ^ p = 1 := S.E_exp _ haE
  have hbp : ∀ j, b j ^ p = 1 := forall_pow_eq_one_of_rootDiagUnit (S.E_exp _ hbE)
  have hpL : ((p : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ
  have hmem : γ ∈ kernelRoots (rootCharHom a) := ⟨hγr, hγa⟩
  set i : KernelComponent (rootCharHom a) := ⟦⟨γ, hmem⟩⟧ with hi
  have hγi : γ ∈ componentRoots (rootCharHom a) i := ⟨hmem, rfl⟩
  have hshape := typeAShape_d4Class S hp hpL hTp ha1 i
  obtain ⟨hperf, hdvd⟩ := typeA_perfect_dvd_p S hp hp5 hpL haT hbT hTp hbp i hshape hγi hγb
  have hRle := (langSubnormal_of_mem_torus S haT i).1
  have hRrange : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := by
    have hr : ι.range = S.Γ := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hy
        obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩
    rw [hr]
    exact hRle.trans inf_le_left
  have hmap : ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := Subgroup.map_comap_eq_self hRrange
  obtain ⟨x, hxA, hx⟩ := haD
  refine ⟨x, hxA, fun h1 => ha1 (by rw [← hx, h1, map_one]),
    (rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι, ?_, ?_, ?_⟩
  · intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : ι c * rootDiagUnit TwistTag.D4.tag a = rootDiagUnit TwistTag.D4.tag a * ι c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hRle hc)).2
    apply hι
    rw [map_mul, map_mul, hx]
    exact hcomm
  · apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmap]
    exact hperf
  · rw [← Subgroup.card_map_of_injective hι, hmap]
    exact hdvd

end TriInn

end Plane

section Model

theorem innGoodAt_trialityModel
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (h3 : ¬ (p = 3 ∧ q.p ^ q.exponent = 2)) (d : TauCeti.LieTypeIndex) :
    InnGoodAt p d ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  by_cases hp3 : p = 3
  · subst hp3
    have hq3 : q.p ≠ 3 := fun h => hpq h.symm
    have hq4 : 4 ≤ q.p ^ q.exponent := by
      have h2 : 2 ≤ q.p ^ q.exponent :=
        q.prime_p.two_le.trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
      have h2' : q.p ^ q.exponent ≠ 2 := fun h => h3 ⟨rfl, h⟩
      have h33 : q.p ^ q.exponent ≠ 3 := fun h =>
        hq3 ((Nat.Prime.pow_eq_iff Nat.prime_three).1 h).1
      omega
    exact innGoodAt_three_of_triInnGoodAt (triInnGoodAt_trialityModel hK σ hσ hq3 hq4) d
  · have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      have h4 : p ≠ 4 := by
        rintro rfl
        exact absurd hp (by norm_num)
      omega
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
    haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
    have hinner : ∀ β ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        β ^ p = 1 → β ∈ inner ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
      fun β hβ _ => sup_le le_rfl
        (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
          q.prime_p q.exponent_pos hK σ hσ) hβ
    exact innGoodAt_of_inner_planes hZ hinner
      (TriInn.perfectCentralizerPlanes_trialityModel q.prime_p hp hp5 hpq q.exponent_pos K hK σ
        hσ) d

theorem lieInnGood_triality :
    LieInnGood isTrialityIdx := by
  intro d p hp hp2 hpc h3 h5 hP
  obtain ⟨e, hv⟩ := d
  cases e with
  | trialityD4 q =>
    have hpq : p ≠ q.p := by
      rw [TauCeti.LieTypeIndex.characteristic_trialityD4] at hpc
      exact hpc
    have h3' : ¬ (p = 3 ∧ q.p ^ q.exponent = 2) := by
      rintro ⟨h, h2⟩
      apply h3
      refine ⟨h, ?_⟩
      change fieldSize (TauCeti.LieTypeIndex.trialityD4 q) = 2
      rw [show fieldSize (TauCeti.LieTypeIndex.trialityD4 q) = q.p ^ q.exponent from
        TauCeti.PrimePower.card_def q, h2]
    obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    letI := hfield
    letI := hfinite
    exact innGoodAt_of_mulEquiv eK.symm (innGoodAt_trialityModel hK σ hσ hp hp2 hpq h3' _)
  | _ => exact absurd hP (by simp [isTrialityIdx])

end Model

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
