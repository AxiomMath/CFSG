module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductN2
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Quot
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusTwo
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialLayer (ExactClosure)
open CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases (FieldAlternative ProductAlternative)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase (centerMod centralizerMod IsQuotientIso zc
  mem_centerMod_iff commutator_mem_iff_proj)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (Sl2Pair mem_conj_iff conj_eq_of_mem_normalizer)
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1LayerD6Aux
  (map_conj_eq_iff_mem_normalizer mem_normalizer_sup' mem_normalizer_inf')
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1QuotAux
  (mem_normalizer_centerMod centerMod_conj normalizer_le_normalizer_series)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductN2CharAux

open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.SL2MinimalFaithful

theorem exists_units_pow_two_pow_eq {k : Type*} [Field k] [CharP k 2] [Finite k] (a : ℕ)
    (ρ : kˣ) : ∃ ρ' : kˣ, ρ' ^ (2 ^ a) = ρ := by
  induction a generalizing ρ with
  | zero => exact ⟨ρ, by simp⟩
  | succ a ih =>
    obtain ⟨ρ₁, hρ₁⟩ := Common.exists_units_sq_eq ρ
    obtain ⟨ρ₂, hρ₂⟩ := ih ρ₁
    refine ⟨ρ₂, ?_⟩
    rw [pow_succ, pow_mul, hρ₂, hρ₁]

theorem exists_odd_irreducible {G : Type*} [Group G] [Finite G] {k : Type*} [Field k]
    [CharP k 2] [Finite k] {N D P : Subgroup G} (φ : N →* SL(2, k))
    (hφ : Function.Surjective φ) (hker : φ.ker = D.subgroupOf N) (hDP : D ≤ P) (hPN : P ≤ N)
    (hcard : D.relIndex P = Nat.card k) :
    ∃ g ∈ N, g ∈ normalizer (P : Set G) ∧ Odd (orderOf g) ∧
      ∀ R : Subgroup G, D ≤ R → R ≤ P → g ∈ normalizer (R : Set G) → R = D ∨ R = P := by
  classical
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  have hk2 : Nat.card k = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hDN : D ≤ N := hDP.trans hPN
  have hker_mem : ∀ x : N, φ x = 1 ↔ (x : G) ∈ D := fun x => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  let ψ : P →* SL(2, k) := φ.comp (Subgroup.inclusion hPN)
  let S' : Subgroup SL(2, k) := ψ.range
  have hS'card : Nat.card S' = Nat.card k := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker] at h1
    have h2 : Nat.card ψ.ker = Nat.card D := by
      exact Nat.card_congr
        { toFun := fun p => ⟨p.1.1, (hker_mem ⟨p.1.1, hPN p.1.2⟩).1 (MonoidHom.mem_ker.1 p.2)⟩
          invFun := fun d => ⟨⟨d.1, hDP d.2⟩,
            MonoidHom.mem_ker.2 ((hker_mem ⟨d.1, hDN d.2⟩).2 d.2)⟩
          left_inv := fun p => rfl
          right_inv := fun d => rfl }
    have h3 := Subgroup.relIndex_mul_card D P
    rw [inf_of_le_left hDP, hcard] at h3
    have h4 : Nat.card P = Nat.card ψ.ker * Nat.card S' := h1.symm
    rw [h2] at h4
    have hpos : 0 < Nat.card D := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← h4, ← h3, mul_comm]
  have hPmem : ∀ x : N, (x : G) ∈ P ↔ φ x ∈ S' := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨p, hp⟩
      have h1 : φ ⟨(p : G), hPN p.2⟩ = φ x := hp
      have h2 : ((⟨(p : G), hPN p.2⟩ : N)⁻¹ * x : N) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : ((p : G))⁻¹ * (x : G) ∈ D := (hker_mem _).1 h2
      have e : (x : G) = (p : G) * ((p : G)⁻¹ * (x : G)) := by group
      rw [e]
      exact mul_mem p.2 (hDP h3)
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem Nat.prime_two hk2 hS'card
  have hS'eq : (upperSL k).map (MulAut.conj g).toMonoidHom = S' := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
      exact hg t.toAdd
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_upperSL, hS'card]
  have hmemS' : ∀ s : SL(2, k), s ∈ S' ↔ ∃ c : k, s = g * unipotent c * g⁻¹ := by
    intro s
    rw [← hS'eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨c, rfl⟩ := mem_upperSL_iff.1 hu
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨unipotent c, unipotent_mem_upperSL c, rfl⟩
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := kˣ)
  obtain ⟨g₀, hg₀⟩ := hφ (g * diagSL μ * g⁻¹)
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g₀).ne'
  set g₁ : N := g₀ ^ (2 ^ a) with hg₁
  have hφg₁ : φ g₁ = g * diagSL (μ ^ (2 ^ a)) * g⁻¹ := by
    rw [hg₁, map_pow, hg₀, conj_pow]
    congr 2
    exact (map_pow (diagSLHom (k := k)) μ (2 ^ a)).symm
  have hdz : ∀ (ρ : kˣ) (m : ℤ), (diagSL ρ) ^ m = diagSL (ρ ^ m) := fun ρ m =>
    (map_zpow (diagSLHom (k := k)) ρ m).symm
  set ν : kˣ := μ ^ (2 ^ a) with hν
  have hodd : Odd (orderOf (g₁ : G)) := by
    rw [Subgroup.orderOf_coe, hg₁,
      orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hab ▸ dvd_mul_right _ _), hab,
      Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
    exact hb
  have hconjS : ∀ (ρ : kˣ) (s : SL(2, k)), s ∈ S' →
      (g * diagSL ρ * g⁻¹) * s * (g * diagSL ρ * g⁻¹)⁻¹ ∈ S' := by
    intro ρ s hs
    obtain ⟨c, rfl⟩ := (hmemS' s).1 hs
    refine (hmemS' _).2 ⟨(ρ : k) ^ 2 * c, ?_⟩
    rw [← diagSL_conj_unipotent ρ c]
    group
  have hnorm : (g₁ : G) ∈ normalizer (P : Set G) := by
    refine mem_normalizer_fintype fun p hp => ?_
    simp only [SetLike.mem_coe] at hp ⊢
    have hpN : p ∈ N := hPN hp
    have h1 : (g₁ : G) * p * (g₁ : G)⁻¹ = ((g₁ * ⟨p, hpN⟩ * g₁⁻¹ : N) : G) := rfl
    rw [h1, hPmem, map_mul, map_mul, map_inv, hφg₁]
    exact hconjS ν _ ((hPmem ⟨p, hpN⟩).1 hp)
  refine ⟨(g₁ : G), g₁.2, hnorm, hodd, fun R hDR hRP hgR => ?_⟩
  by_cases hRD : R ≤ D
  · left
    exact le_antisymm hRD hDR
  right
  obtain ⟨r, hrR, hrD⟩ := Set.not_subset.1 hRD
  refine le_antisymm hRP fun p hp => ?_
  by_cases hpD : p ∈ D
  · exact hDR hpD
  have hrN : r ∈ N := hPN (hRP hrR)
  have hpN : p ∈ N := hPN hp
  obtain ⟨c, hc⟩ := (hmemS' _).1 ((hPmem ⟨r, hrN⟩).1 (hRP hrR))
  obtain ⟨c', hc'⟩ := (hmemS' _).1 ((hPmem ⟨p, hpN⟩).1 hp)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hrD
    refine (hker_mem ⟨r, hrN⟩).1 ?_
    rw [hc, unipotent_zero]
    group
  have hc'0 : c' ≠ 0 := by
    rintro rfl
    apply hpD
    refine (hker_mem ⟨p, hpN⟩).1 ?_
    rw [hc', unipotent_zero]
    group
  obtain ⟨ρ₁, hρ₁⟩ := Common.exists_units_sq_eq (Units.mk0 (c' / c) (div_ne_zero hc'0 hc0))
  obtain ⟨ρ₂, hρ₂⟩ := exists_units_pow_two_pow_eq a ρ₁
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hμ ρ₂)
  have hρν : ρ₁ = ν ^ m := by
    rw [← hρ₂, ← hm, hν, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hρ₁k : ((ρ₁ : kˣ) : k) ^ 2 * c = c' := by
    have := congrArg (fun u : kˣ => (u : k)) hρ₁
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
    rw [this]
    field_simp
  have hgm : (g₁ : G) ^ m ∈ normalizer (R : Set G) := Subgroup.zpow_mem _ hgR m
  have hr'R : (g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹ ∈ R := (mem_normalizer_iff.1 hgm r).1 hrR
  have hr'N : (g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.zpow_mem g₁.2 m) hrN) (N.inv_mem (N.zpow_mem g₁.2 m))
  have hφr' : φ ⟨(g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹, hr'N⟩ = φ ⟨p, hpN⟩ := by
    have e : (⟨(g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹, hr'N⟩ : N) = g₁ ^ m * ⟨r, hrN⟩ * (g₁ ^ m)⁻¹ :=
      rfl
    rw [e, map_mul, map_mul, map_inv, map_zpow, hφg₁, hc, hc']
    have e2 : (g * diagSL ν * g⁻¹) ^ m = g * diagSL ρ₁ * g⁻¹ := by
      rw [conj_zpow, hρν, hdz]
    rw [e2]
    have e3 : (g * diagSL ρ₁ * g⁻¹) * (g * unipotent c * g⁻¹) * (g * diagSL ρ₁ * g⁻¹)⁻¹ =
        g * (diagSL ρ₁ * unipotent c * (diagSL ρ₁)⁻¹) * g⁻¹ := by group
    rw [e3, diagSL_conj_unipotent ρ₁ c, hρ₁k]
  have h2 : ((⟨p, hpN⟩ : N)⁻¹ * ⟨(g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹, hr'N⟩ : N) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφr', inv_mul_cancel]
  have h3 : p⁻¹ * ((g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹) ∈ D :=
    (hker_mem _).1 (MonoidHom.mem_ker.1 h2)
  have h4 : ((g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹)⁻¹ * p ∈ D := by
    simpa using D.inv_mem h3
  have e : p = ((g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹) *
      (((g₁ : G) ^ m * r * ((g₁ : G) ^ m)⁻¹)⁻¹ * p) := by group
  rw [e]
  exact R.mul_mem hr'R (hDR h4)


theorem mem_normalizer_factor_of_odd {G : Type} [Group G] [Finite G] {F : Type} [Field F]
    [Finite F] {N D K K' : Subgroup G} (hS : Sl2Pair F N D K K') {g : G}
    (hgN : g ∈ normalizer (N : Set G)) (hgD : g ∈ normalizer (D : Set G))
    (hodd : Odd (orderOf g)) : g ∈ normalizer (K : Set G) := by
  rcases hS.conj_factor hgN hgD with h | h
  · exact map_conj_eq_iff_mem_normalizer.1 h
  · exfalso
    have h' : K'.map (MulAut.conj g).toMonoidHom = K := by
      rcases hS.symm.conj_factor hgN hgD with h2 | h2
      · exact absurd (Subgroup.map_injective (MulAut.conj g).injective (h.trans h2.symm)) hS.ne
      · exact h2
    have hg2 : g ^ 2 ∈ normalizer (K : Set G) := by
      refine mem_normalizer_fintype fun x hx => ?_
      have h1 : g * x * g⁻¹ ∈ K' := by
        rw [← h]
        exact ⟨x, hx, by simp⟩
      have h2 : g * (g * x * g⁻¹) * g⁻¹ ∈ K := by
        rw [← h']
        exact ⟨_, h1, by simp⟩
      have e : g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by
        rw [pow_two]
        group
      rw [e]
      exact h2
    obtain ⟨n, hn⟩ := hodd
    have hgn : g ^ (2 * n + 1) = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one g
    have hgg : g = (g ^ 2) ^ (n + 1) := by
      rw [← pow_mul, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, pow_succ, hgn, one_mul]
    have hgK : g ∈ normalizer (K : Set G) := by
      rw [hgg]
      exact Subgroup.pow_mem _ hg2 _
    exact hS.ne ((map_conj_eq_iff_mem_normalizer.2 hgK).symm.trans h)


open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient (proj bar Bar isPGroup_bar bar_mono
  bar_le_normalizer_bar proj_mem_bar proj_eq_one_iff proj_surjective mem_bar_iff)

theorem exists_mem_centerMod_of_normal {G : Type} [Group G] [Finite G] {W Z P : Subgroup G}
    (hP : IsPGroup 2 P) (hWZ : W ≤ Z) (hne : W ≠ Z) (hZP : Z ≤ P)
    (hPW : P ≤ normalizer (W : Set G)) (hPZ : P ≤ normalizer (Z : Set G)) :
    ∃ z ∈ Z, z ∉ W ∧ z ∈ centerMod W P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWP : W ≤ P := hWZ.trans hZP
  set B : Subgroup (Bar W) := bar W P with hB
  haveI : Group.IsNilpotent B := (isPGroup_bar hP).isNilpotent
  have hbZP : bar W Z ≤ B := bar_mono hZP
  have hnorm : B ≤ normalizer (bar W Z : Set (Bar W)) := bar_le_normalizer_bar hWZ hPZ
  haveI : ((bar W Z).subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hbZP).2 hnorm
  obtain ⟨z₀, hz₀Z, hz₀W⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hWZ hne)
  have hz₀N : z₀ ∈ normalizer (W : Set G) := hPW (hZP hz₀Z)
  have hbot : (bar W Z).subgroupOf B ≠ ⊥ := by
    intro h
    have hmem : (⟨proj W ⟨z₀, hz₀N⟩, proj_mem_bar (hZP hz₀Z)⟩ : B) ∈
        (bar W Z).subgroupOf B := proj_mem_bar hz₀Z
    rw [h, Subgroup.mem_bot] at hmem
    exact hz₀W (proj_eq_one_iff.1 (congrArg Subtype.val hmem))
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hbot)
  obtain ⟨hyZ, hyc⟩ := Subgroup.mem_inf.1 y.2
  obtain ⟨⟨z, hzN⟩, hzy⟩ := proj_surjective (A := W) (y : B).1
  have hzZ : z ∈ Z := by
    have : proj W ⟨z, hzN⟩ ∈ bar W Z := hzy ▸ mem_subgroupOf.1 hyZ
    exact (mem_bar_iff hWZ ⟨z, hzN⟩).1 this
  have hzW : z ∉ W := by
    intro hzW
    apply hy
    have h1 : (y : B).1 = 1 := by
      rw [← hzy]
      exact proj_eq_one_iff.2 hzW
    exact Subtype.ext (Subtype.ext h1)
  refine ⟨z, hzZ, hzW, (mem_centerMod_iff hWP).2 ⟨hZP hzZ, hzN, fun a haP haN => ?_⟩⟩
  have hc := Subgroup.mem_center_iff.1 hyc ⟨proj W ⟨a, haN⟩, proj_mem_bar haP⟩
  have h2 := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul] at h2
  rw [← hzy] at h2
  exact (commutator_mem_iff_proj hzN haN).1 h2


theorem barMap_mem_normalClosure {G : Type} [Group G] {X CU NC : Subgroup G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X))) (n : NC) :
    barMap X ⟨(n : G), hNCN n.2⟩ ∈ normalClosure (barSub X CU : Set (BarM X)) := by
  rw [← hbar]
  exact ⟨⟨(n : G), hNCN n.2⟩, mem_subgroupOf.mpr n.2, rfl⟩

theorem exists_hom_of_barSub {G : Type} [Group G] {X CU NC : Subgroup G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X))) {T : Type*} [Group T]
    (ψ : normalClosure (barSub X CU : Set (BarM X)) ≃* T) :
    ∃ φ : NC →* T, Function.Surjective φ ∧ φ.ker = X.subgroupOf NC ∧
      ∀ n : NC, φ n = ψ ⟨barMap X ⟨(n : G), hNCN n.2⟩, barMap_mem_normalClosure hNCN hbar n⟩ := by
  let ρ₁ : NC →* normalClosure (barSub X CU : Set (BarM X)) :=
    ((barMap X).comp (Subgroup.inclusion hNCN)).codRestrict _
      (barMap_mem_normalClosure hNCN hbar)
  have hρ₁surj : Function.Surjective ρ₁ := by
    rintro ⟨x, hx⟩
    rw [← hbar] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    exact ⟨⟨m, mem_subgroupOf.mp hm⟩, Subtype.ext rfl⟩
  refine ⟨ψ.toMonoidHom.comp ρ₁, ψ.surjective.comp hρ₁surj, ?_, fun n => rfl⟩
  ext n
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  change ψ (ρ₁ n) = 1 ↔ (n : G) ∈ X
  refine (map_eq_one_iff ψ ψ.injective).trans ?_
  rw [Subtype.ext_iff]
  exact CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure.barMap_eq_one_iff
    (a := ⟨(n : G), hNCN n.2⟩)

theorem exists_rho {G : Type} [Group G] {K : Type} [Field K] {X CU NC : Subgroup G} {t : G}
    (hNCN : NC ≤ normalizer (X : Set G))
    (hbar : barSub X NC = normalClosure (barSub X CU : Set (BarM X)))
    (ht : t ∈ normalizer (X : Set G)) (hτ : barMap X ⟨t, ht⟩ * barMap X ⟨t, ht⟩ = 1)
    (α : ↥(barSub X CU) ≃* SL(2, K))
    (hP : ProductAlternative (barSub X CU) α (barMap X ⟨t, ht⟩)) :
    ∃ ρ : NC →* SL(2, K) × SL(2, K), Function.Surjective ρ ∧ ρ.ker = X.subgroupOf NC ∧
      ∀ x y : NC, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap := by
  obtain ⟨ψ, -, hψswap⟩ := hP
  obtain ⟨ρ, hρ, hker, hρψ⟩ := exists_hom_of_barSub hNCN hbar ψ
  refine ⟨ρ, hρ, hker, fun x y hxy => ?_⟩
  rw [hρψ x, hρψ y]
  refine hψswap _ _ ?_
  have hy : barMap X ⟨(y : G), hNCN y.2⟩ =
      barMap X ⟨t, ht⟩ * barMap X ⟨(x : G), hNCN x.2⟩ * (barMap X ⟨t, ht⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hxy)
  show barMap X ⟨(y : G), hNCN y.2⟩ =
    (barMap X ⟨t, ht⟩)⁻¹ * barMap X ⟨(x : G), hNCN x.2⟩ * barMap X ⟨t, ht⟩
  rw [hy, inv_eq_of_mul_eq_one_right hτ]

theorem isFactor_of_rho {G : Type} [Group G] {K : Type} [Field K] {X N : Subgroup G} {t : G}
    (hXN : X ≤ N) (ht2 : t * t = 1) (hN : t ∈ normalizer (N : Set G))
    (ρ : N →* SL(2, K) × SL(2, K)) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = X.subgroupOf N)
    (hswap : ∀ x y : N, (y : G) = t * x * t⁻¹ → ρ y = (ρ x).swap) :
    IsFactor X N (Common.prodFst ρ) t K := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hmem := fun g => Common.mem_map_conj_prodFst_iff (ρ := ρ) hN ht2 hswap (g := g)
  have hconj : (Common.prodFst ρ)ᵍ[t] = (Common.prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    rw [hti]
  refine ⟨Common.le_prodFst hXN hker, Common.prodFst_le ρ, ?_, ?_, ?_, ?_⟩
  · rw [hconj]
    exact Common.prodFst_sup_map_conj hN ht2 hswap hρ
  · rw [hconj]
    refine le_antisymm (fun g hg => ?_) (le_inf (Common.le_prodFst hXN hker) fun g hg => ?_)
    · obtain ⟨hg1, hg2⟩ := mem_inf.1 hg
      obtain ⟨hgN, hg2'⟩ := (Common.mem_prodFst_iff ρ).1 hg1
      obtain ⟨_, hg1'⟩ := (hmem g).1 hg2
      have : (⟨g, hgN⟩ : N) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        exact Prod.ext hg1' hg2'
      rw [hker, mem_subgroupOf] at this
      exact this
    · have hgN : g ∈ N := hXN hg
      refine (hmem g).2 ⟨hgN, ?_⟩
      have : (⟨g, hgN⟩ : N) ∈ ρ.ker := by
        rw [hker, mem_subgroupOf]
        exact hg
      rw [MonoidHom.mem_ker] at this
      rw [this]
      rfl
  · rw [hconj]
    exact Common.commutator_prodFst_map_conj_le hN ht2 hswap hker
  · exact ⟨Common.prodFstHom ρ, Common.surjective_prodFstHom hρ, Common.ker_prodFstHom hker⟩

theorem sl2Pair_of_isFactor {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
    [CharP K 2] (h4 : 4 ≤ Nat.card K) {X N Λ : Subgroup G} {t : G}
    (hΛ : IsFactor X N Λ t K) (htX : t ∈ normalizer (X : Set G)) :
    Sl2Pair K N X Λ (Λᵍ[t]) where
  charTwo := inferInstance
  four_le := h4
  sup_eq := hΛ.sup
  inf_eq := hΛ.inf
  comm_le := hΛ.comm
  isoK := hΛ.quot
  isoK' := by
    have h1 := CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux.IsQuotientIso.conj
      hΛ.quot t
    rwa [conj_eq_of_mem_normalizer htX] at h1

theorem eq_of_invariant {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {N D Λ P C : Subgroup G} {t : G} (ht2 : t * t = 1) (hS : Sl2Pair F N D Λ (Λᵍ[t]))
    (hP : IsSylowOf 2 P N) (hDC : D ≤ C) (hCP : C ≤ P) (hne : C ≠ P)
    (hinv : N ⊓ normalizer (P : Set G) ≤ normalizer (C : Set G))
    (htC : t ∈ normalizer (C : Set G)) : C = D := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hDΛ : Λ ⊓ Λᵍ[t] = D := hS.inf_eq
  have hmem : ∀ x, x ∈ Λᵍ[t] ↔ t * x * t⁻¹ ∈ Λ := fun x => mem_conj_iff
  rcases hS.invariant hP (hDC.trans hCP) hDC hCP hinv with h1 | h2 | h3 | h4
  · exact h1
  · refine le_antisymm (fun x hx => ?_) hDC
    have hx1 : x ∈ Λ := (h2 ▸ hx : x ∈ P ⊓ Λ).2
    have hx2 : t * x * t⁻¹ ∈ C := (mem_normalizer_iff.1 htC x).1 hx
    have hx3 : t * x * t⁻¹ ∈ Λ := (h2 ▸ hx2 : t * x * t⁻¹ ∈ P ⊓ Λ).2
    rw [← hDΛ]
    exact mem_inf.2 ⟨hx1, (hmem x).2 hx3⟩
  · refine le_antisymm (fun x hx => ?_) hDC
    have hx1 : x ∈ Λᵍ[t] := (h3 ▸ hx : x ∈ P ⊓ Λᵍ[t]).2
    have hx2 : t * x * t⁻¹ ∈ C := (mem_normalizer_iff.1 htC x).1 hx
    have hx3 : t * x * t⁻¹ ∈ Λᵍ[t] := (h3 ▸ hx2 : t * x * t⁻¹ ∈ P ⊓ Λᵍ[t]).2
    have hx4 : t * (t * x * t⁻¹) * t⁻¹ ∈ Λ := (hmem _).1 hx3
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [hti, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ht2]
      group
    rw [e] at hx4
    rw [← hDΛ]
    exact mem_inf.2 ⟨hx4, hx1⟩
  · exact absurd h4 hne

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamadaK₁_le_normalizer_D₇ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G) :=
  (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₁ d ≤ L ⊓ normalizer (d.U : Set G)).trans
    (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).1

theorem yamadaK₂_le_normalizer_M₆ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G) :=
  (commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) :
        yamadaK₂ d ≤ L ⊓ normalizer (d.Y : Set G)).trans
    (h.normalizer_L_le_yamadaD₇_M₆ hW d hK hQ).2

theorem card_facts (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaW₃ d t) = Nat.card K ^ 6 ∧ Nat.card (yamadaY₂ d t) = Nat.card K ^ 4 ∧
      Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 ∧ Nat.card (yamadaM₆ d t) = Nat.card K ^ 10 ∧
      Nat.card (yamadaD₇ d t) = Nat.card K ^ 10 ∧ Nat.card (yamadaP d t) = Nat.card K ^ 12 := by
  have hD := hQ.doubling
  obtain ⟨-, -, -, hF₅c, -, -, hM₆c, -, -⟩ := h.card_yamada_five_six hW d hK hQ
  exact ⟨(h.yamadaW₃_facts hW d hK hD).2.2.2.2.2.2, h.card_yamadaY₂ d hK hD, hF₅c, hM₆c,
    h.card_yamadaD₇ hW d hK hQ, h.card_yamadaP hW d hK hQ⟩

theorem normalizer_yamadaP_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hp : ProductHyp d t f) :
    normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaM₆ d t : Set G) ∧
      normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaN₂ d t : Set G) ∧
      normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨α, hex, -⟩ := hp.exact₂
  have hNM := (h.yamadaP_inf_centralizer_yamadaY₂ hW d hK hQ hex).2
  have hKN := yamadaK₂_le_normalizer_M₆ hW h d hK hQ
  have hNN₂ : normalizer (yamadaM₆ d t : Set G) ≤ normalizer (yamadaN₂ d t : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (yamadaN₂_le_normalizer d t hKN)).1
      (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hKN)
  have hY₂ : normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaY₂ d t : Set G) := by
    rw [← (h.yamada_5_57_1 hW d hK hQ).2.1]
    exact normalizer_le_normalizer_series _ 2
  have hY₂N₂ : yamadaY₂ d t ≤ yamadaN₂ d t :=
    (h.yamadaY₂_le_yamadaM₆ hW d hK hQ).trans (yamadaM₆_le_yamadaN₂ d t)
  have hcen := (h.yamadaN₂_centers hW d hK hQ hp.sylow₂ hex).2.1
  refine ⟨hNM, hNM.trans hNN₂, fun g hg => ?_⟩
  rw [← hcen]
  exact mem_normalizer_centerMod hY₂N₂ (hY₂ hg) (hNN₂ (hNM hg))

end Local

end ProductN2CharAux

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem yamada_7_3_eight (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ¬ FieldAlternative (yamadaBarK₁ d t) (yamadaT₁ d t) f := by
  classical
  rintro ⟨k₂, hfld, hfin, hk₂, ψ, -, -⟩
  letI := hfld
  letI := hfin
  have hq : 1 < Nat.card K := hQ.one_lt
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · rw [pow_zero] at hK
      omega
    · exact hf
  have hk₂' : Nat.card k₂ = Nat.card K ^ 2 := by rw [Nat.card_eq_fintype_card, hk₂, hK]
  haveI : CharP k₂ 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ 2 * f)
    (by rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm])
  obtain ⟨α₂, hex₂, -⟩ := hp.exact₂
  obtain ⟨hNM, hNN₂, hNW⟩ := ProductN2CharAux.normalizer_yamadaP_le hW h d hK hQ hp
  obtain ⟨hW₃c, -, hF₅c, hM₆c, hD₇c, hPc⟩ := ProductN2CharAux.card_facts hW h d hK hQ
  have hK₁N := ProductN2CharAux.yamadaK₁_le_normalizer_D₇ hW h d hK hQ
  have hN₁D : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hK₁N
  obtain ⟨φ, hφ, hker, -⟩ := ProductN2CharAux.exists_hom_of_barSub hN₁D
    (barSub_yamadaN₁ d t hK₁N) ψ
  have hDP := yamadaD₇_le_yamadaP d t
  have hPN : yamadaP d t ≤ yamadaN₁ d t := hp.sylow₁.le
  have hrel : (yamadaD₇ d t).relIndex (yamadaP d t) = Nat.card k₂ := by
    have h1 := Subgroup.relIndex_mul_card (yamadaD₇ d t) (yamadaP d t)
    rw [inf_of_le_left hDP, hD₇c, hPc] at h1
    have hq10 : 0 < Nat.card K ^ 10 := pow_pos Nat.card_pos 10
    rw [hk₂']
    refine Nat.eq_of_mul_eq_mul_right hq10 ?_
    rw [h1]
    ring
  obtain ⟨g, hgN, hgP, hgodd, hirr⟩ :=
    ProductN2CharAux.exists_odd_irreducible φ hφ hker hDP hPN hrel
  have hgD : g ∈ normalizer (yamadaD₇ d t : Set G) := hN₁D hgN
  have hgM := hNM hgP
  have hgN₂ := hNN₂ hgP
  have hgW := hNW hgP
  obtain ⟨Λ₂, hΛ⟩ := exists_isFactor₂ hW h d hK hQ hp
  obtain ⟨-, htM, -⟩ := (h.yamada_5_44_1 hW d hK hQ).1
  have hS₂ := ProductN2CharAux.sl2Pair_of_isFactor hQ.four_le hΛ htM
  have hgΛ : g ∈ normalizer (Λ₂ : Set G) :=
    ProductN2CharAux.mem_normalizer_factor_of_odd hS₂ hgN₂ hgM hgodd
  obtain ⟨⟨hZcard, hZsup, -⟩, -⟩ := yamada_7_3 hW h d hK hQ hp hΛ
  have hW₃M : yamadaW₃ d t ≤ yamadaM₆ d t := h.yamadaW₃_le_yamadaM₆ hW d hK hQ
  have hM₆P : yamadaM₆ d t ≤ yamadaP d t := h.yamadaM₆_le_yamadaP hW d hK hQ
  have hW₃Λ : yamadaW₃ d t ≤ Λ₂ := hW₃M.trans hΛ.X_le
  have hW₃Z : yamadaW₃ d t ≤ centerMod (yamadaW₃ d t) Λ₂ := by
    unfold centerMod CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.upperCenterMod
    exact Common.NormalizerQuotient.le_lift _
  have hZg : g ∈ normalizer (centerMod (yamadaW₃ d t) Λ₂ : Set G) :=
    mem_normalizer_centerMod hW₃Λ hgW hgΛ
  have hZM : centerMod (yamadaW₃ d t) Λ₂ ≤ yamadaM₆ d t := hZsup ▸ le_sup_left
  have hZP : centerMod (yamadaW₃ d t) Λ₂ ≤ yamadaP d t := hZM.trans hM₆P
  have hRg : g ∈ normalizer ((yamadaD₇ d t ⊔ centerMod (yamadaW₃ d t) Λ₂ : Subgroup G) :
      Set G) := mem_normalizer_sup' hgD hZg
  obtain ⟨⟨-, htP, -⟩, -⟩ := h.yamada_5_51 hW d hK hQ
  have htW := hNW htP
  have hF₅ := (h.yamadaN₂_centers hW d hK hQ hp.sylow₂ hex₂).2.2.2.1
  have hW₃P : yamadaW₃ d t ≤ yamadaP d t := hW₃M.trans hM₆P
  have htF₅ : t ∈ normalizer (yamadaF₅ d t : Set G) :=
    hF₅ ▸ mem_normalizer_centerMod hW₃P htW htP
  rcases hirr _ le_sup_left (sup_le hDP hZP) hRg with hRD | hRP
  ·
    have hZD : centerMod (yamadaW₃ d t) Λ₂ ≤ yamadaD₇ d t := hRD ▸ le_sup_right
    have hZF : centerMod (yamadaW₃ d t) Λ₂ ≤ yamadaF₅ d t :=
      (h.yamadaM₆_inf_yamadaD₇ hW d hK hQ) ▸ le_inf hZM hZD
    have hZt : centerMod (yamadaW₃ d t) (Λ₂ᵍ[t]) ≤ yamadaF₅ d t := by
      rw [← centerMod_conj hW₃Λ htW]
      exact (Subgroup.map_mono hZF).trans (conj_eq_of_mem_normalizer htF₅).le
    have hM₆F : yamadaM₆ d t ≤ yamadaF₅ d t := hZsup ▸ sup_le hZF hZt
    have := Subgroup.card_le_of_le hM₆F
    rw [hM₆c, hF₅c] at this
    exact absurd this (not_le.2 (Nat.pow_lt_pow_right hq (by norm_num)))
  ·
    have hZcard' : Nat.card (centerMod (yamadaW₃ d t) Λ₂) = Nat.card K ^ 8 := by
      have h1 := Subgroup.relIndex_mul_card (yamadaW₃ d t) (centerMod (yamadaW₃ d t) Λ₂)
      rw [inf_of_le_left hW₃Z, hZcard, hW₃c] at h1
      rw [← h1]
      ring
    have hPZn : yamadaP d t ≤ normalizer (centerMod (yamadaW₃ d t) Λ₂ : Set G) := fun p hpP =>
      mem_normalizer_centerMod hW₃Λ (hNW (Subgroup.le_normalizer hpP))
        (hS₂.le_normalizer (hp.sylow₂.le hpP))
    have hZne : yamadaW₃ d t ≠ centerMod (yamadaW₃ d t) Λ₂ := by
      intro e
      have h1 : Nat.card K ^ 6 < Nat.card K ^ 8 := Nat.pow_lt_pow_right hq (by norm_num)
      rw [e, hZcard'] at hW₃c
      omega
    obtain ⟨z, hzZ, hzW, hzF⟩ := ProductN2CharAux.exists_mem_centerMod_of_normal hp.sylow₁.isPGroup
      hW₃Z hZne hZP (fun p hpP => hNW (Subgroup.le_normalizer hpP)) hPZn
    have hzD : z ∈ yamadaD₇ d t := by
      rw [hF₅] at hzF
      exact h.yamadaF₅_le_yamadaD₇ hW d hK hQ hzF
    have hZD7 : centerMod (yamadaW₃ d t) Λ₂ ≤ normalizer (yamadaD₇ d t : Set G) :=
      hZP.trans (h.yamadaP_le_normalizer_D₇_M₆ hW d hK hQ).1
    have h2 := Common.card_sup_mul_card_inf_eq (A := yamadaD₇ d t) hZD7
    rw [hRP, hPc, hD₇c, hZcard'] at h2
    have h3 : Nat.card (yamadaD₇ d t ⊓ centerMod (yamadaW₃ d t) Λ₂ : Subgroup G) =
        Nat.card K ^ 6 := by
      refine Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := K)) 12) ?_
      rw [h2]
      ring
    have hW₃D : yamadaW₃ d t ≤ yamadaD₇ d t := h.yamadaW₃_le_yamadaD₇ hW d hK hQ
    have h4 : yamadaW₃ d t = yamadaD₇ d t ⊓ centerMod (yamadaW₃ d t) Λ₂ :=
      Subgroup.eq_of_le_of_card_ge (le_inf hW₃D hW₃Z) (by rw [h3, hW₃c])
    exact hzW (h4 ▸ mem_inf.2 ⟨hzD, hzZ⟩)

theorem exists_isFactor₁ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    ∃ Λ₁ : Subgroup G, IsFactor (yamadaD₇ d t) (yamadaN₁ d t) Λ₁ t K := by
  obtain ⟨α, hex⟩ := hp.exact₁
  have hnF := yamada_7_3_eight hW h d hK hQ hp
  have hPA : ProductAlternative (yamadaBarK₁ d t) α (yamadaT₁ d t) := by
    rcases CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialCases.xor_of_exactClosure hex with
      ⟨hPA, -⟩ | ⟨hFA, -⟩
    · exact hPA
    · exact absurd hFA hnF
  obtain ⟨-, htN, -⟩ := (h.yamada_5_51 hW d hK hQ).2.2
  have ht2 : t * t = 1 := h.t_mul_t
  have hK₁N := ProductN2CharAux.yamadaK₁_le_normalizer_D₇ hW h d hK hQ
  have hNCN : yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
    yamadaN₁_le_normalizer d t hK₁N
  have hbar := barSub_yamadaN₁ d t hK₁N
  have hτ : barMap (yamadaD₇ d t) ⟨t, htN⟩ * barMap (yamadaD₇ d t) ⟨t, htN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htN⟩ * ⟨t, htN⟩ : normalizer (yamadaD₇ d t : Set G)) = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hPA' : ProductAlternative (barSub (yamadaD₇ d t) (yamadaK₁ d)) α
      (barMap (yamadaD₇ d t) ⟨t, htN⟩) := by
    rw [← yamadaT₁_eq d htN]
    exact hPA
  obtain ⟨ρ, hρ, hker, hswap⟩ :=
    ProductN2CharAux.exists_rho (X := yamadaD₇ d t) (CU := yamadaK₁ d) (NC := yamadaN₁ d t)
      hNCN hbar htN hτ α hPA'
  have hN₁ : t ∈ normalizer (yamadaN₁ d t : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNCN).1
      (Common.RankOneLayerRadical.normal_subgroupOf_normalClosureInNormalizer hK₁N) htN
  exact ⟨Common.prodFst ρ, ProductN2CharAux.isFactor_of_rho (yamadaD₇_le_yamadaN₁ d t) ht2 hN₁
    ρ hρ hker hswap⟩

theorem yamada_7_3_char (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (hp : ProductHyp d t f) :
    normalizer (yamadaP d t : Set G) =
        normalizer (yamadaM₆ d t : Set G) ⊓ normalizer (yamadaD₇ d t : Set G) ∧
      normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaW₃ d t : Set G) := by
  have hq : 1 < Nat.card K := hQ.one_lt
  obtain ⟨hNM, hNN₂, hNW⟩ := ProductN2CharAux.normalizer_yamadaP_le hW h d hK hQ hp
  obtain ⟨Λ₁, hΛ₁⟩ := exists_isFactor₁ hW h d hK hQ hp
  obtain ⟨hW₃c, hY₂c, -, -, -, -⟩ := ProductN2CharAux.card_facts hW h d hK hQ
  have hDP := yamadaD₇_le_yamadaP d t
  refine ⟨le_antisymm (le_inf hNM ?_) ?_, hNW⟩
  ·
    obtain ⟨⟨-, htP, -⟩, -, ⟨-, htD, -⟩⟩ := h.yamada_5_51 hW d hK hQ
    have ht2 : t * t = 1 := h.t_mul_t
    have hser := h.yamada_5_57_1 hW d hK hQ
    have hNU : normalizer (yamadaP d t : Set G) ≤ normalizer (yamadaU₁ d t : Set G) := by
      rw [← hser.1]
      exact normalizer_le_normalizer_series _ 1
    have hPU : yamadaP d t ≤ normalizer (yamadaU₁ d t : Set G) := fun p hpP =>
      hNU (Subgroup.le_normalizer hpP)
    have hW₃D : yamadaW₃ d t ≤ yamadaD₇ d t := h.yamadaW₃_le_yamadaD₇ hW d hK hQ
    have hW₃P : yamadaW₃ d t ≤ yamadaP d t := hW₃D.trans hDP
    have hDC : yamadaD₇ d t ≤
        yamadaP d t ⊓ centralizerModulo (yamadaU₁ d t) (yamadaW₃ d t) := by
      intro x hx
      refine mem_inf.2 ⟨hDP hx, mem_centralizerModulo_iff.2 ⟨hPU (hDP hx), fun w hw => ?_⟩⟩
      have := Subgroup.commutator_mem_commutator hx (hW₃D hw)
      rw [(h.yamada_5_55_1 hW d hK hQ).1.2] at this
      simpa [commutatorElement_def] using this
    have hNC : ∀ g ∈ normalizer (yamadaP d t : Set G), g ∈ normalizer
        ((yamadaP d t ⊓ centralizerModulo (yamadaU₁ d t) (yamadaW₃ d t) : Subgroup G) :
          Set G) := fun g hg =>
      mem_normalizer_inf' hg (mem_normalizer_centralizerModulo (hNU hg) (hNW hg))
    have hCne : yamadaP d t ⊓ centralizerModulo (yamadaU₁ d t) (yamadaW₃ d t) ≠ yamadaP d t := by
      intro hCP
      have hW₃Y₂ : yamadaW₃ d t ≤ yamadaY₂ d t := by
        intro w hw
        rw [← hser.2.1, mem_map_upperCentralSeries_succ]
        refine ⟨hW₃P hw, fun y hy => ?_⟩
        have hyC : y ∈ yamadaP d t ⊓ centralizerModulo (yamadaU₁ d t) (yamadaW₃ d t) := hCP.ge hy
        have h1 := (mem_centralizerModulo_iff.1 (mem_inf.1 hyC).2).2 w hw
        have h2 : w * y * w⁻¹ * y⁻¹ = (y * w * y⁻¹ * w⁻¹)⁻¹ := by group
        rw [h2, hser.1]
        exact inv_mem h1
      have h3 := Subgroup.card_le_of_le hW₃Y₂
      rw [hW₃c, hY₂c] at h3
      exact absurd h3 (not_le.2 (Nat.pow_lt_pow_right hq (by norm_num)))
    have hS₁ := ProductN2CharAux.sl2Pair_of_isFactor hQ.four_le hΛ₁ htD
    have hCD := ProductN2CharAux.eq_of_invariant ht2 hS₁ hp.sylow₁ hDC inf_le_left hCne
      (fun g hg => hNC g hg.2) (hNC t htP)
    intro g hg
    have := hNC g hg
    rwa [hCD] at this
  ·
    intro g hg
    have := mem_normalizer_sup' (mem_inf.1 hg).1 (mem_inf.1 hg).2
    rwa [(h.yamada_5_57_2 hW d hK hQ).2.2.2.2.1] at this

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
