module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGood
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SymplecticPlaneQ
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxSymplectic
public import CFSG.Adapters.CatalogueFieldBridges.Symplectic
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic

public section

namespace CFSG.RankThree.PartOne.KCSpFull

open CFSG.Open CFSG.RankThree.Classical

theorem SpPlaneDecomp.exists_spEnd_ne_of_mem_spLineSpace {r : ℕ} {K : Type} [Field K]
    {p : ℕ} {Ahat : Subgroup (StatedSp r K)} (D : SpPlaneDecomp p Ahat)
    {M : Subgroup ↥Ahat} {u : Fin r ⊕ Fin r → K} (hu : u ∈ spLineSpace M) (hu0 : u ≠ 0) :
    ∃ y ∈ Ahat, spEnd y u ≠ u := by
  by_contra hcon
  push Not at hcon
  have hu₀ : u ∈ spPlaneFix Ahat :=
    CFSG.RankThree.Classical.mem_fixSub.mpr fun a _ => hcon a a.2
  have huo := (Submodule.mem_inf.mp hu).2
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at huo
  have := (D.nondeg none).2 ⟨u, hu₀⟩ fun z => huo z z.2
  exact hu0 (congrArg Subtype.val this)

end CFSG.RankThree.PartOne.KCSpFull

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.KCPrimary
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.Classical (spForm spLin spEnd SpPrimaryBlocks)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

private theorem exists_good_of_spFixedLayer
    {ℓ f p r : ℕ} {K : Type} [Field K] [Finite K]
    {Ahat : Subgroup (StatedSp r K)}
    {E : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    {M : Subgroup ↥Ahat} {x : StatedSp r K}
    (hp : p.Prime) (hp2 : p ≠ 2) (hr1 : 1 ≤ r)
    (hM : Nat.card M = p) (hV : spLineSpace M ≠ ⊥)
    (hxA : x ∈ Ahat) (hxM : (⟨x, hxA⟩ : ↥Ahat) ∈ M) (hx1 : x ≠ 1)
    (D : SpPlaneDecomp p Ahat)
    (hblocks : SpPrimaryBlocks ℓ f p x (proj r K x))
    (hlisted : SpFixedListed x)
    (hF : SpListedFacts p (innerAut (StatedProj (StatedSp r K))) (proj r K x)
      (spFixedLayerImage x))
    (hpow : ∀ y ∈ Ahat, y ^ p = 1)
    (hmul : ∀ y ∈ Ahat, y * x = x * y)
    (hlift : IsSpPlaneLift r K p E Ahat) :
    ∃ β ∈ E, β ≠ 1 ∧ ∃ P : Subgroup (StatedProj (StatedSp r K)),
      P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  have hβE : MulAut.conj (proj r K x) ∈ E := by
    rw [← hlift.2.2.1]
    exact Subgroup.mem_map_of_mem _ hxA
  have hβ1 : MulAut.conj (proj r K x) ≠ 1 := by
    intro h
    have h1 : spInnerLift r K x = 1 := by rw [spInnerLift_apply]; exact h
    exact hx1 (hlift.2.2.2 hxA (one_mem _) (h1.trans (map_one _).symm))
  refine ⟨MulAut.conj (proj r K x), hβE, hβ1, spFixedLayerImage x, ?_, ?_, ?_⟩
  · intro g hg
    rw [mem_fixSubgroup, MulAut.conj_apply]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hF.1 hg)
    rw [← hcomm]
    group
  · haveI : Group.IsPerfect ↥(spFixedLayerImage x) := hF.2.1.1
    exact Subgroup.commutator_eq_self
  · obtain ⟨u, huM, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    obtain ⟨y, hyA, hyu⟩ := D.exists_spEnd_ne_of_mem_spLineSpace huM hu0
    have hu : u ∈ LinearMap.ker (spEnd x - 1) := by
      rw [D.ker_eq_sup hM hxA hxM hx1]
      exact Submodule.mem_sup_right huM
    exact dvd_card_spFixedLayerImage hr1 hp hp2 hblocks hlisted (hmul y hyA) (hpow y hyA) hu hyu

private theorem exists_good_of_planeSetupQ
    {ℓ f p r : ℕ} {K : Type} [Field K] [Finite K]
    {Ahat : Subgroup (StatedSp r K)}
    {E : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (S : SpPlaneSetupQ ℓ f p r K Ahat) (hp2 : p ≠ 2)
    (hlift : IsSpPlaneLift r K p E Ahat) :
    ∃ β ∈ E, β ≠ 1 ∧ ∃ P : Subgroup (StatedProj (StatedSp r K)),
      P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  have hp := S.prime_p
  have hℓ := S.prime_ell
  have hf := S.one_le_f
  have hK := S.card_K
  have hpℓ := S.ne_char
  have hr := S.two_le_r
  have hr1 : 1 ≤ r := by omega
  have Dd := S.decomp
  obtain ⟨M₁, _, hM₁, _, _, hV₁, _⟩ := Dd.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  obtain ⟨hlisted, -⟩ := S.spFixedListed Dd hM₁ hV₁ t₁.2 ht₁ ht₁1'
  have hblocks := S.blocks t₁.2 ht₁1'
  have hF : SpListedFacts p (innerAut (StatedProj (StatedSp r K))) (proj r K t₁)
      (spFixedLayerImage (t₁ : StatedSp r K)) :=
    (spListedFacts_q hℓ hf hK S.four_le_q hp hp2 hpℓ hr
      (innerAut (StatedProj (StatedSp r K))) le_rfl (t₁ : StatedSp r K)
      (S.orderOf_eq t₁.2 ht₁1')).2 hlisted
  exact exists_good_of_spFixedLayer hp hp2 hr1 hM₁ hV₁ t₁.2 ht₁ ht₁1' Dd hblocks hlisted hF
    (fun y hy => S.pow_eq_one hy)
    (fun y hy => congrArg Subtype.val (S.mul_comm_elem ⟨y, hy⟩ t₁)) hlift

private theorem exists_good_of_planeSetup
    {ℓ f p r : ℕ} {K : Type} [Field K] [Finite K]
    {Ahat : Subgroup (StatedSp r K)}
    {E : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (S : SpPlaneSetup ℓ f p r K Ahat) (hp2 : p ≠ 2)
    (hEinner : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K)))
    (hEel : CFSG.IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hlift : IsSpPlaneLift r K p E Ahat) :
    ∃ β ∈ E, β ≠ 1 ∧ ∃ P : Subgroup (StatedProj (StatedSp r K)),
      P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  have hp := S.prime_p
  have hℓ := S.prime_ell
  have hf := S.one_le_f
  have hK := S.card_K
  have hp3 := S.three_lt_p
  have hpℓ := S.ne_char
  have hr := S.two_le_r
  have hne := S.not_exceptional
  have hr1 : 1 ≤ r := by omega
  have Dd := S.decomp
  obtain ⟨M₁, _, hM₁, _, _, hV₁, _⟩ := Dd.two_active
  obtain ⟨t₁, ht₁, ht₁1⟩ := S.exists_ne_one_mem hM₁
  have ht₁1' : (t₁ : StatedSp r K) ≠ 1 := fun h => ht₁1 (Subtype.ext h)
  obtain ⟨hlisted, -⟩ := S.spFixedListed Dd hM₁ hV₁ t₁.2 ht₁ ht₁1'
  have hblocks := S.blocks t₁.2 ht₁1'
  have horder : orderOf (t₁ : StatedSp r K) = p := S.orderOf_eq t₁.2 ht₁1'
  have hproj_mem : proj r K (t₁ : StatedSp r K) ∈
      E.comap (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))) := by
    rw [← hlift.2.2.1]
    exact Subgroup.mem_map_of_mem _ t₁.2
  have hproj_ne : proj r K (t₁ : StatedSp r K) ≠ 1 := by
    intro h
    have h1 := S.orderOf_proj t₁.2 ht₁1'
    rw [h, orderOf_one] at h1
    omega
  have hA0 := CFSG.RankThree.PartOne.comap_conj_plane S.conj_injective hEinner hEel hEcard
  have hFx := symplectic_inner_plane_below_prime_local_core_centralization hℓ hf hK hp hp3
    hpℓ hr hne (innerAut (StatedProj (StatedSp r K))) le_rfl
    (E.comap (MulAut.conj : StatedProj (StatedSp r K) →*
      MulAut (StatedProj (StatedSp r K)))) hA0.1 hA0.2 (proj r K (t₁ : StatedSp r K))
    hproj_mem hproj_ne (t₁ : StatedSp r K) rfl horder
  have hF : SpListedFacts p (innerAut (StatedProj (StatedSp r K))) (proj r K t₁)
      (spFixedLayerImage (t₁ : StatedSp r K)) := hFx.2.1 hlisted
  exact exists_good_of_spFixedLayer hp hp2 hr1 hM₁ hV₁ t₁.2 ht₁ ht₁1' Dd hblocks hlisted hF
    (fun y hy => S.pow_eq_one hy)
    (fun y hy => congrArg Subtype.val (S.mul_comm_elem ⟨y, hy⟩ t₁)) hlift

theorem innGoodAt_statedProj_sp {p r ℓ f : ℕ} {K : Type} [Field K] [Finite K]
    (d : TauCeti.LieTypeIndex) (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hne : ¬ (r = 2 ∧ ℓ ^ f = 2)) (hpℓ : p ≠ ℓ)
    (h32 : ¬ (p = 3 ∧ ℓ ^ f = 2)) :
    InnGoodAt p d (StatedProj (StatedSp r K)) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : NeZero r := ⟨by omega⟩
  have hr1 : 1 ≤ r := by omega
  have hinj := spConj_injective (r := r) (K := K) hℓ hf hK hr hne
  intro E hE hEcard hEle
  have hEinner : E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp r K)) := fun x hx =>
    mem_inner_of_mem_innAutDerived_statedSp hp hp2 hℓ hf hK hr hne (hEle hx) (hE.2 x hx)
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hE.2 x x.2) }
  obtain ⟨Ahat, hlift, -⟩ := exists_unique_spPlaneLift hr1 hp hp2 hinj E hEinner hEel hEcard
  by_cases hq4 : 4 ≤ ℓ ^ f
  · have S : SpPlaneSetupQ ℓ f p r K Ahat :=
      { prime_ell := hℓ, one_le_f := hf, card_K := hK, prime_p := hp, p_ne_two := hp2,
        ne_char := hpℓ, two_le_r := hr, four_le_q := hq4, elem := hlift.1,
        card_plane := hlift.2.1 }
    exact Or.inl (exists_good_of_planeSetupQ S hp2 hlift)
  · have hq2le : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have hq23 : ℓ ^ f = 2 ∨ ℓ ^ f = 3 := by omega
    have hp3 : 3 < p := by
      have hp3ne : p ≠ 3 := by
        rcases hq23 with hq2 | hq3
        · rintro rfl
          exact h32 ⟨rfl, hq2⟩
        · rintro rfl
          have hℓ3 : ℓ = 3 := by
            have hdvd : ℓ ∣ 3 := by
              rw [← hq3]
              exact dvd_pow_self ℓ (by omega)
            exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp hdvd
          exact hpℓ hℓ3.symm
      have hp2le : 2 ≤ p := hp.two_le
      omega
    have S : SpPlaneSetup ℓ f p r K Ahat :=
      { prime_ell := hℓ, one_le_f := hf, card_K := hK, prime_p := hp, three_lt_p := hp3,
        ne_char := hpℓ, two_le_r := hr, not_exceptional := hne, elem := hlift.1,
        card_plane := hlift.2.1 }
    exact Or.inl (exists_good_of_planeSetup S hp2 hEinner hEel hEcard hlift)

theorem lieInnGood_symplectic : LieInnGood isSymplecticIdx := by
  intro d p hp hp2 hpc h3 h5 hd
  obtain ⟨r, hr, hne, hcard, ⟨e⟩⟩ := exists_mulEquiv_statedProj_of_isSymplecticIdx hd
  haveI : Finite ↥d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  have hℓ : d.characteristic.Prime := d.characteristic_prime
  have hf : 1 ≤ d.fieldExponent := d.fieldExponent_pos
  have hK : Nat.card ↥d.fixedField = d.characteristic ^ d.fieldExponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
  have hfs : fieldSize d.1 = d.characteristic ^ d.fieldExponent := hcard.symm.trans hK
  have hne' : ¬ (r = 2 ∧ d.characteristic ^ d.fieldExponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne ⟨h1, by rw [hfs]; exact h2⟩
  have h32 : ¬ (p = 3 ∧ d.characteristic ^ d.fieldExponent = 2) := by
    rintro ⟨hp3, h2⟩
    exact h3 ⟨hp3, by
      show fieldSize d.1 = 2
      rw [hfs]
      exact h2⟩
  have hmodel := innGoodAt_statedProj_sp (p := p) (r := r) (ℓ := d.characteristic)
    (f := d.fieldExponent) (K := ↥d.fixedField) (d := d.1) hp hp2 hℓ hf hK hr hne'
    hpc h32
  exact innGoodAt_of_mulEquiv e hmodel

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
