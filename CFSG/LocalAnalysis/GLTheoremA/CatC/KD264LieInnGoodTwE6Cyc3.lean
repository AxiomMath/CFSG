module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Plane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.E6 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2 CFSG.Open
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

set_option linter.unusedSectionVars false


theorem perfectCentralizerPlanes_twistedE6_three_cyc {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type)
    [Field K] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) : PerfectCentralizerPlanes p (twistedE6RootGroup K σ) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let Ω := AlgebraicClosure K
  haveI : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, (iterateFrobenius Ω ℓ f) c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω phi3V)
  intro E hE hEcard
  have hpg : IsPGroup p E := IsPGroup.of_card hEcard
  obtain ⟨c₀, hc₀⟩ := KETw3.exists_conj_into_TStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn E hpg
  have hc₀' : ∀ e ∈ E, frameEmb K σ Ω g c₀ e ∈
      phi3TStar K σ.toRingHom Ω (iterateFrobenius Ω ℓ f) g := fun e he => by
    rw [frameEmb_apply]
    exact hc₀ e he
  obtain ⟨-, hord, e, he, he1, hA2A2⟩ :=
    plane_data hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ E hEcard hE.2 hc₀'
  obtain ⟨R, -, hRD, -, hq, hpR⟩ :=
    layerA2A2 hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ e (hc₀' e he) (hord e he he1) hA2A2
  refine ⟨e, he, he1, R, hRD, ?_, (Nat.Prime.dvd_iff_not_coprime hp).2 hpR⟩
  haveI : Group.IsPerfect ↥R := hq.1
  exact Subgroup.commutator_eq_self

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
