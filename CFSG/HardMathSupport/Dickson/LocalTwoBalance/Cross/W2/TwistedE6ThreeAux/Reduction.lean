module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Plane
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.Chevalley CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6
open CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2
open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.LocalTwo
open scoped Pointwise commutatorElement Matrix MatrixGroups

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_twistedE6_three_R3 {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1) : InnerPlaneBalance p (twistedE6RootGroup K σ) := by
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
  intro E hEin hE hcard H hH
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (twistedE6RootGroup K σ) := E.comap
    (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)) = E := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hq
  obtain ⟨c₀, hc₀⟩ := KETw3.exists_conj_into_TStar hℓ hf hK hσ hFr hp hp3 hpq hg hgn A₀ hpg
  have hc₀' : ∀ e ∈ A₀, frameEmb K σ Ω g c₀ e ∈
      phi3TStar K σ.toRingHom Ω (iterateFrobenius Ω ℓ f) g := fun e he => by
    rw [frameEmb_apply]
    exact hc₀ e he
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  refine eq_one_of_fixes hℓ hf hK hσ hFr hp hp3 hpq hg hgn c₀ A₀ hA₀card hA₀exp hc₀'
    (fun e he he1 htype => ?_)
  have hord : orderOf (frameEmb K σ Ω g c₀ e) = p := by
    rw [orderOf_frameEmb]
    exact orderOf_eq_prime (hA₀exp e he) he1
  exact fixes_layer hℓ hf hK hσ hFr hp hp3 hpq hg hgn hH hz c₀ e he he1 (hc₀' e he) hord htype

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwE6Three
