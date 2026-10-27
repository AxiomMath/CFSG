module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwActor
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwNormal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FourAux.R3TwCoord
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer
public import CFSG.RankThree.PartOne.KE.E6TwFourFinal
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.E6 (weylMatrix e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_twistedE6_four_R3 {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K]
    [Finite K] [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpd : p ∣ (ℓ ^ f) ^ 2 + 1) : InnerPlaneBalance p (twistedE6RootGroup K σ) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hp3 : 3 < p := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by exact_mod_cast hpd
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  set n : ModGL Tag.E6 L := canonicalRep (coxeterSystem Tag.E6) L (e6F4U * e6NegRho) with hn
  have hcm : n ∈ monomialSubgroup Tag.E6 L :=
    canonicalRep_mem_monomialSubgroup L (e6F4U * e6NegRho)
  have hπ : weylQuotientHom Tag.E6 L ⟨n, hcm⟩ = e6F4U * e6NegRho :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep _)
  have hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hcm⟩ • x = e6SM (-1) *ᵥ permLattice e6Rho x :=
    fun x => by
      rw [hπ]
      exact e6TwFour_weylImage x
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_tw_four_frame K hf hK σ hσ hp hp3 hpq L n hcm hnW
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
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  refine eq_bot_iff.2 fun z hz => ?_
  have hex : ∀ i : Fin Tag.E6.rank, ∃ (q : twistedE6RootGroup K σ) (b : Fin Tag.E6.rank → Lˣ),
      q ∈ A₀ ∧ q ≠ 1 ∧ orderOf q = p ∧
      rootDiagUnit Tag.E6 b = g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∧
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ rootCharKernel b ∧ z q = q ∧
      ∀ d ∈ (⁅Subgroup.centralizer ({q} : Set (twistedE6RootGroup K σ)),
        Subgroup.centralizer ({q} : Set (twistedE6RootGroup K σ))⁆ :
          Subgroup (twistedE6RootGroup K σ)), z d = d := by
    intro i
    obtain ⟨q, hqA, hq1, b, hb, hbi⟩ :=
      e6_tw_four_exists_nonregular_at K σ hp L n g0 A₀ hA₀card hA₀exp c hc i
    have hqp : orderOf q = p := orderOf_eq_prime (hA₀exp q hqA) hq1
    obtain ⟨hquasi, hpR⟩ := e6_tw_four_derived K hf hK σ hσ hp hp3 hordq hΦ L n hcm hnW g0 hg0C
      hg0 hperf hT hqp c (hc q hqA) hb ⟨_, hbi⟩
    obtain ⟨hzq, hzD⟩ := fixes_of_mem_localDeltaIn hp hinj hH hz hqA hq1 hquasi hpR
    exact ⟨q, b, hqA, hq1, hqp, hb, hbi, hzq, hzD⟩
  choose q b hqA hq1 hqp hb hbi hzq hzD using hex
  have i0 : Fin Tag.E6.rank := ⟨0, by decide⟩
  obtain ⟨a, haC, haF, hae⟩ := e6_tw_four_normal_of_fixes K hf hK σ hσ hp hp3 hordq hΦ L n hcm hnW
    g0 hg0C hg0 hperf hT (hqp i0) c (hc (q i0) (hqA i0)) (hb i0) ⟨_, hbi i0⟩ (hzq i0) (hzD i0)
  have hcoord : ∀ i : Fin Tag.E6.rank, ∃ a' : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit Tag.E6 a' = g0⁻¹ * twE6Emb K σ L c * a * (twE6Emb K σ L c)⁻¹ * g0 ∧
        a' i = 1 := by
    intro i
    obtain ⟨a', ha', hker⟩ := e6_tw_four_coordinates K hf hK σ hσ hp hp3 hordq hΦ L n hcm hnW g0
      hg0C hg0 hperf hT (hqp i) c (hc (q i) (hqA i)) (hb i) ⟨_, hbi i⟩ a haC
      (by rw [← hae (q i), hzq i]) (fun d hd => by rw [← hae d, hzD i d hd])
    refine ⟨a', ha', ?_⟩
    have := hker _ (hbi i)
    rwa [CTTorus.rootChar_single] at this
  choose a' ha' hai using hcoord
  have hcommon : ∀ i, a' i = a' i0 := fun i =>
    rootDiagUnit_injective ((ha' i).trans (ha' i0).symm)
  have hone : a' i0 = 1 := funext fun j => by
    have := hai j
    rwa [hcommon j] at this
  have hM : g0⁻¹ * twE6Emb K σ L c * a * (twE6Emb K σ L c)⁻¹ * g0 = 1 := by
    rw [← ha' i0, hone, rootDiagUnit_one]
  have ha1 : a = 1 := by
    have h1 : a = (twE6Emb K σ L c)⁻¹ * g0 * (g0⁻¹ * twE6Emb K σ L c * a *
        (twE6Emb K σ L c)⁻¹ * g0) * g0⁻¹ * twE6Emb K σ L c := by group
    rw [h1, hM]
    group
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro y
  apply twE6Emb_injective (K := K) (σ := σ) (L := L)
  rw [hae y, ha1]
  simp

theorem innerPlaneBalance_twistedE6_four_R3' {ℓ f : ℕ} (hℓ : ℓ.Prime) (K : Type) [Field K]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpd : p ∣ (ℓ ^ f) ^ 2 + 1) :
    InnerPlaneBalance p (twistedE6RootGroup K σ) := by
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  exact innerPlaneBalance_twistedE6_four_R3 K hf hK σ hσ hp hp5 hpd

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
