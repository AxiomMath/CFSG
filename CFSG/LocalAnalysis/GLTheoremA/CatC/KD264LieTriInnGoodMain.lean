module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieTriInnGoodComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieTriInnGoodKer
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal

public section

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

@[expose] def TriInnGoodAt (S : Type) [Group S] : Prop :=
  ∀ β ∈ innAutDerived S, β ^ 3 = 1 → β ≠ 1 →
    ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P

theorem TriInnGoodAt.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : TriInnGoodAt S) : TriInnGoodAt S' := by
  intro b hbmem hb3 hb1
  set α : MulAut S := MulAut.congr e.symm b with hα
  have hconj : MulAut.congr e α = b := by
    rw [hα]
    ext y
    simp [MulAut.congr_apply]
  have hαmem : α ∈ innAutDerived S := by
    rw [← mem_innAutDerived_congr e, hconj]
    exact hbmem
  have hα3 : α ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one, hconj]
    exact hb3
  have hα1 : α ≠ 1 := by
    intro h1
    apply hb1
    rw [← hconj, h1, map_one]
  obtain ⟨P, hPfix, hPperf, hPdvd⟩ := h α hαmem hα3 hα1
  refine ⟨P.map (e : S →* S'), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [mem_fixSubgroup]
    have hy' : α y = y := hPfix hy
    have hb : b = MulAut.congr e α := hconj.symm
    rw [hb]
    change e (α (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hy']
  · rw [← Subgroup.map_commutator, hPperf]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hPdvd

section Model


theorem triInnGoodAt_trialityModel
    {q : TauCeti.PrimePower} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (q.p ^ q.exponent) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (q.p ^ q.exponent)) (hq3 : q.p ≠ 3) (hq4 : 4 ≤ q.p ^ q.exponent) :
    TriInnGoodAt ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro β hβmem hβ3 hβ1
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      q.prime_p q.exponent_pos hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hx3 : x ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ3, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hpq : (3 : ℕ) ≠ q.p := fun h => hq3 h.symm
  have hmon : MonomialToralAt Tag.D4 3 :=
    monomialToralAt_three_of_block a2BlockToral_D4
  obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ :=
    exists_setup_prime q.prime_p q.exponent_pos Nat.prime_three (by norm_num) hpq
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime q.prime_p q.exponent_pos hK σ hσ Nat.prime_three hpq
      hp₀ hp₀ℓ hq₀ hmon x hx3 hx1
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne q.prime_p Nat.prime_three hK hpq
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨i⟩ := TriInn.nonempty_kernelComponent_d4 (L := AlgebraicClosure K) hap
  have hA := typeAShape_d4Class S Nat.prime_three hpL hTp h1 i
  have hQ : 4 ≤ S.D.q := hSq ▸ hq4
  obtain ⟨hperf, h3⟩ := TriInn.typeA_perfect_dvd_three S Nat.prime_three hpL hT hTp i hA hQ
  have hRle := (langSubnormal_of_mem_torus S hT i).1
  have hRrange : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤ ι.range := by
    rw [hrange]
    exact hRle.trans inf_le_left
  have hmap : ((rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι).map ι =
      rationalComponent S.ρ S.Γ (rootCharHom a) i := Subgroup.map_comap_eq_self hRrange
  refine ⟨(rationalComponent S.ρ S.Γ (rootCharHom a) i).comap ι, ?_, ?_, ?_⟩
  · intro c hc
    rw [mem_fixSubgroup]
    have hcomm : ι c * rootDiagUnit Tag.D4 a = rootDiagUnit Tag.D4 a * ι c :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hRle hc)).2
    apply hinj
    rw [hconj c, mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hmap]
    exact hperf
  · rw [← Subgroup.card_map_of_injective hinj, hmap]
    exact h3

theorem kd264TriInnGood_holds :
    KD264TriInnGood := by
  intro d hd h3 β hβ hβ3 hβ1
  obtain ⟨q, hq, hq2⟩ := hd
  obtain ⟨e, hv⟩ := d
  change e = .trialityD4 q at hq
  subst hq
  have hq3 : q.p ≠ 3 := by
    intro h
    exact h3 (by rw [TauCeti.LieTypeIndex.characteristic_trialityD4, h])
  have hq4 : 4 ≤ q.p ^ q.exponent := by
    have hc : q.p ^ q.exponent = q.card := (TauCeti.PrimePower.card_def q).symm
    have h2 : 2 < q.p ^ q.exponent := by rw [hc]; exact hq2
    have h33 : q.p ^ q.exponent ≠ 3 := fun h => hq3 ((Nat.Prime.pow_eq_iff Nat.prime_three).1 h).1
    omega
  obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  letI := hfield
  letI := hfinite
  exact (TriInnGoodAt.of_mulEquiv eK.symm (triInnGoodAt_trialityModel hK σ hσ hq3 hq4)) β hβ hβ3 hβ1

end Model

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
