module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenAbs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenArith
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenDefs
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.GH74.KGH
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDInputs
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Open Subgroup
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel ReeTitsModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.Coordinator (OuterFixedOrderBoundCyc)

@[expose] def NotDvdDivisorInput : Prop :=
  ∀ {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f p : ℕ},
    StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f → p.Prime → p ≠ 2 →
    Subgroup.center K = ⊥ → (∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p) →
    ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) ∧ ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3)

theorem kFactFieldAutEven_of_props
    (hBridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hSpor : ∀ s : TauCeti.SporadicName,
      Nonempty (CFSG.Blueprint.NativeSporadic.Carrier s ≃*
        (TauCeti.CFSGIndex.sporadic s).Group))
    (hSporOut : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hTits : ∀ (G : Type) [Group G] (p f : ℕ), ReeTitsModel G .Tits p f → IsPGroup 2 (Outer G) ∧
        Group.IsSolvable (Outer G)) (hLie : LieOrderFormulasInput) (hDiv : NotDvdDivisorInput)
    (hFix : OuterFixedOrderBoundCyc)
    (hLB : ∀ t, FixedLowerBoundAt t) (hOL : ∀ t, OvergroupLocalAt t) : KFactFieldAutEven := by
  intro J _ _ p α T hp hp5 hα hpJ hs hna hK hT hnoU
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup J := hs
  have hp2 : p ≠ 2 := by omega
  have hab : ∃ a b : J, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hna h
  have hZ : Subgroup.center J = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot J hab
  have hcat : IsCatalogGroup J :=
    hK.isCatalogGroup_of_surjective ⊤ hab (Subgroup.topEquiv (G := J)).toMonoidHom
      (Subgroup.topEquiv (G := J)).surjective
  have hαp : α ^ p = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hαin : α ∉ inner J := fun h => hpJ (dvd_card_of_mem_inner h hα)
  have hA : ∀ A : Subgroup J, IsElemAbelian p A → Nat.card A ≤ p := by
    intro A hA'
    have hA1 : A = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hord : orderOf x = p := orderOf_eq_prime (hA'.2 x hx) hx1
      exact hpJ (hord ▸ orderOf_dvd_natCard x)
    rw [hA1, Subgroup.card_bot]
    exact hp.one_lt.le
  have hev : Even (Nat.card J) := CFSG.GH74.even_card_of_nonabelian_simple hab
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases (hBridge J hab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  ·
    exfalso
    obtain ⟨a, b, hab'⟩ := hab
    exact hab' (e.injective (by rw [map_mul, map_mul, mul_comm]))
  ·
    exfalso
    refine hαin (mem_inner_of_not_dvd_card_outer hp ?_ hαp)
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  ·
    by_cases ht : t = .Tits
    ·
      subst ht
      exfalso
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [CFSG.Blueprint.classicalTags] at h
      · simp [CFSG.Blueprint.chevalleyExceptionalTags] at h
      · obtain ⟨k, hk⟩ := (hTits J ℓ f hree).1.exists_card_eq
        refine hαin (mem_inner_of_not_dvd_card_outer hp (fun hd => ?_) hαp)
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · obtain ⟨hdivp, hD4⟩ := hDiv hadm hmodel hp hp2 hZ hA
      have hT3 : ¬ (t = .trialityD4 ∧ p = 3) := fun h => by omega
      obtain ⟨f₀, hf, -⟩ := hFix J t n ℓ f hadm hmodel ht p hp hp2 hdivp hD4 hT3 α hαp hαin
      have hLBt := hLB t J n ℓ f f₀ p hadm hmodel ht hp hp5 hpJ hdivp hf α hαp hαin
      have hℓ : ℓ.Prime := hadm.1
      have hf1 : 1 ≤ f := hadm.2.1
      have hf₀ : 1 ≤ f₀ := by
        rcases Nat.eq_zero_or_pos f₀ with h0 | h0
        · rw [h0, mul_zero] at hf
          omega
        · exact h0
      have hCne : Nat.card (fixedSubgroup α) ≠ 0 := Nat.card_pos.ne'
      by_cases hℓ2 : ℓ = 2
      ·
        subst hℓ2
        obtain ⟨r, hr, hrloc⟩ := hOL t J hs hab n f f₀ p hadm hmodel ht hp hp5 hpJ hdivp hf
        haveI : Fact r.Prime := ⟨hr⟩
        have hD0 : lieOrderDivisor t n (2 ^ f₀) ≠ 0 :=
          lieOrderDivisor_ne_zero t n _ (by
            calc 2 = 2 ^ 1 := (pow_one 2).symm
              _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀)
        have hvle : padicValNat r (lieOrderNumerator t n (2 ^ f₀)) ≤
            padicValNat r (lieOrderDivisor t n (2 ^ f₀)) +
              padicValNat r (Nat.card (fixedSubgroup α)) := by
          rw [← padicValNat.mul hD0 hCne]
          exact padicValNat_le_of_dvd' hr (mul_ne_zero hD0 hCne) hLBt
        exact closure_eq_top_of_overgroupPrime α T hr (fun Y hTY hY => by
          have := hrloc T Y hT hTY hY
          omega)
      ·
        exfalso
        have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
        have hℓ3 : 3 ≤ ℓ := by
          have := hℓ.two_le
          omega
        have hx3 : 3 ≤ ℓ ^ f₀ :=
          calc 3 ≤ ℓ := hℓ3
            _ = ℓ ^ 1 := (pow_one ℓ).symm
            _ ≤ ℓ ^ f₀ := Nat.pow_le_pow_right (by omega) hf₀
        have hqp : ℓ ^ f = (ℓ ^ f₀) ^ p := by rw [hf, mul_comm, pow_mul]
        have hpodd : Odd p := hp.odd_of_ne_two hp2
        obtain ⟨-, hcard, -⟩ := hLie J t n ℓ f hadm hmodel
        have hn1 : (t = .POmegaPlus ∨ t = .POmegaMinus) → 1 ≤ n := by
          intro h
          rcases h with rfl | rfl
          · have h4 : 4 ≤ n := hadm.2.2
            omega
          · have h4 : 4 ≤ n := hadm.2.2
            omega
        have hv := v2Le_numerator t n (x := ℓ ^ f₀) (p := p) hℓodd.pow hx3 hpodd hn1
        rw [← hqp] at hv
        obtain ⟨hN, hN0, hvle⟩ := hv
        have hq2 : 2 ≤ ℓ ^ f := by
          have : ℓ ^ f₀ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) (by rw [hf]; nlinarith)
          omega
        have hD : lieOrderDivisor t n (ℓ ^ f) ≠ 0 := lieOrderDivisor_ne_zero t n _ hq2
        have hD0 : lieOrderDivisor t n (ℓ ^ f₀) ≠ 0 := lieOrderDivisor_ne_zero t n _ (by omega)
        have hDdvd : lieOrderDivisor t n (ℓ ^ f₀) ∣ lieOrderDivisor t n (ℓ ^ f) := by
          rw [hqp]
          exact lieOrderDivisor_dvd_pow t n _ hpodd
        have e1 : (Nat.card J).factorization 2 + (lieOrderDivisor t n (ℓ ^ f)).factorization 2 =
            (lieOrderNumerator t n (ℓ ^ f)).factorization 2 := by
          rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' hD]
          simp
        have e2 : (lieOrderNumerator t n (ℓ ^ f₀)).factorization 2 ≤
            (lieOrderDivisor t n (ℓ ^ f₀)).factorization 2 +
              (Nat.card (fixedSubgroup α)).factorization 2 := by
          have := (Nat.factorization_le_iff_dvd hN0 (mul_ne_zero hD0 hCne)).mpr hLBt 2
          rwa [Nat.factorization_mul hD0 hCne] at this
        have e3 : (lieOrderDivisor t n (ℓ ^ f₀)).factorization 2 ≤
            (lieOrderDivisor t n (ℓ ^ f)).factorization 2 :=
          (Nat.factorization_le_iff_dvd hD0 hD).mpr hDdvd 2
        obtain ⟨U, hU, hfix⟩ := exists_sylow_fixed_of_factorization_le α (by omega)
        exact hnoU ⟨U, hU, hfix⟩
  ·
    exfalso
    obtain ⟨e'⟩ := hSpor s
    refine hαin (mem_inner_of_not_dvd_card_outer hp ?_ hαp)
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact hSporOut s p hp hp2

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
