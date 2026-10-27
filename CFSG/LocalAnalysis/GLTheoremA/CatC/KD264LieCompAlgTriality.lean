module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxTriality
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoLang
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4InnerAux.SteinbergD4
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyTw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.PartOne.KGD
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

section Triality


theorem exists_langSetup_of_inner_triD4_eq_kd264alg
    {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀ℓ : p₀ ≠ ℓ) (hq₀ : 5 ≤ p₀ ∨ 4 ≤ ℓ ^ f)
    (hmon : MonomialToralAt Tag.D4 p)
    (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hp1 : x ^ p = 1) (hx1 : x ≠ 1) :
    ∃ (S : LangSetup Tag.D4 (AlgebraicClosure K) p₀)
      (a : Fin Tag.D4.rank → (AlgebraicClosure K)ˣ)
      (ι : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* ModGL Tag.D4 (AlgebraicClosure K)),
      S.D.q = ℓ ^ f ∧
      rootDiagUnit Tag.D4 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧ rootDiagUnit Tag.D4 a ≠ 1 ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ ι x = rootDiagUnit Tag.D4 a := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c =>
    iterateFrobenius_def ℓ f c
  have hcomm : (algebraMap K L).comp σ.toRingHom =
      (iterateFrobenius L ℓ f).comp (algebraMap K L) := by
    refine RingHom.ext fun c => ?_
    change algebraMap K L (σ c) = iterateFrobenius L ℓ f (algebraMap K L c)
    rw [hσ c, iterateFrobenius_def, map_pow]
  set u : ModGL TwistTag.D4.tag L := triEmb K σ L x with hu
  have huG : u ∈ adjointGroup TwistTag.D4.tag L := triEmb_mem_adjointGroup x
  have hufix : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) u = u := triEmb_fixed _ hcomm x
  have hup : u ^ p = 1 := by rw [hu, ← map_pow, hp1, map_one]
  have hu1 : u ≠ 1 := fun h' => hx1 (triEmb_injective (by rw [map_one]; exact h'))
  have hconj := exists_conj_torusGroup_of_pow_eq_one hp hmon hpℓ.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ) huG hup
  obtain ⟨D, hΦ, hDq, hmem⟩ := exists_langDatum_of_toral_twisted TwistTag.D4 f hf hufix hconj
  have hd := langDescent_triD4_inner (K := K) (L := L) hℓ hf hK σ hσ hFr D hΦ (p := p)
  have hβ' : ∀ c, triEmb K σ L (MulAut.conj x c) = u * triEmb K σ L c * u⁻¹ := fun c => by
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hq' : 5 ≤ p₀ ∨ 4 ≤ D.q := by
    rw [hDq]
    exact hq₀
  obtain ⟨S, a, ι, rfl, hT, hap, h1, hinj, hrange, hx, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_langSetup_of_toral_datum_of_prime_eq
      hℓ hf D hDq hp₀ hp₀ℓ hq' hd.finite_model (triEmb K σ L) triEmb_injective hd.Γ_eq
      (MulAut.conj x) hβ' hmem hup hu1 x rfl
  exact ⟨S, a, ι, hDq, hT, hap, h1, hinj, hrange, hx⟩

theorem compAlgAt_trialityModel
    {K : Type} [Field K] (hK : Nat.card K = 8 ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 8) :
    CompAlgAt ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  intro β hβmem hβ3 hβ1 J hJ e he hiso x' hx'mem _ hβx' hx'stab
  have hK' : Nat.card K = (2 ^ 3) ^ 3 := by rw [hK]; norm_num
  have hσ' : ∀ c, σ c = c ^ (2 ^ 3) := fun c => by rw [hσ c]; norm_num
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hinn : innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≤
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      Nat.prime_two (by norm_num) hK' σ hσ')
  obtain ⟨x, rfl⟩ := hinn hβmem
  obtain ⟨w, rfl⟩ := hinn hx'mem
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hx3 : x ^ 3 = 1 :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ3, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hxw : x * w = w * x :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZ (by rw [map_mul, map_mul]; exact hβx')
  have hmon : MonomialToralAt Tag.D4 3 := monomialToralAt_three_of_block a2BlockToral_D4
  obtain ⟨S, a, ι, hSq, hT, hap, h1, hinj, hrange, hx⟩ :=
    exists_langSetup_of_inner_triD4_eq_kd264alg Nat.prime_two (by norm_num) hK' σ hσ'
      Nat.prime_three (by norm_num) Nat.prime_three (by norm_num) (Or.inr (by norm_num)) hmon x hx3
      hx1
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 3 * 3)
    (by rw [← Nat.card_eq_fintype_card, hK', ← pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 :=
    natCast_ne_zero_algebraicClosure_of_ne Nat.prime_two Nat.prime_three hK' (by norm_num)
  have hTame := langSetup_hTame_of_prime S Nat.prime_three hpL (fun h => absurd h (by decide)) hT
    hap h1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hW : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a :=
    (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_D4_three
      a hap).le
  have hN := card_eq_of_compAlgEight_kd264alg e he hiso
  exact centerQuotientHom_mem_innAutDerived_of_langSetup_kd264alg S (by rw [hSq]; norm_num) ι hinj
    hrange hT hap h1 hW hTame (fun i _ _ => typeAShape_d4Class S Nat.prime_three hpL hTp h1 i) hx
    hJ hN hxw hx'stab

theorem lieCompAlg_triality :
    LieCompAlg isTrialityIdx := by
  intro d hP hfield
  obtain ⟨e, hv⟩ := d
  cases e with
  | trialityD4 q =>
    have hq8 : q.p ^ q.exponent = 8 := by
      have hfs : fieldSize (TauCeti.LieTypeIndex.trialityD4 q) = q.p ^ q.exponent :=
        TauCeti.PrimePower.card_def q
      rw [← hfs]
      exact hfield
    obtain ⟨K, hfield', hfinite, σ, hK, hσ, -, ⟨eK⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
    letI := hfield'
    letI := hfinite
    rw [hq8] at hK hσ
    exact compAlgAt_of_mulEquiv eK.symm (compAlgAt_trialityModel hK σ hσ)
  | _ => exact absurd hP (by simp [isTrialityIdx])

end Triality

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
