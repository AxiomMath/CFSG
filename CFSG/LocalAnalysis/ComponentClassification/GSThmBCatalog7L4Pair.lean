module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4Comp
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.HBlocks
open CFSG.ComponentClassification.CatFactsL4U4.TBlocks
open scoped commutatorElement

variable {k : Type} [Field k]

theorem nontrivial_of_isPComponent' {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (hK : IsPComponent 2 K) : Nontrivial K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 K).mp hK
  obtain ⟨-, hs, -⟩ := hq
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have : Nontrivial ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := hs.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K))
  obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨a'', rfl⟩ := QuotientGroup.mk'_surjective _ a'
  obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
  obtain ⟨b'', rfl⟩ := QuotientGroup.mk'_surjective _ b'
  exact hab (by rw [Subsingleton.elim a'' b''])

@[expose] def negTwo (k : Type) [Field k] : SpecialLinearGroup (Fin 2) k :=
  ⟨-1, by rw [det_neg, det_one, Fintype.card_fin]; norm_num⟩

theorem orderOf_negTwo (htwo : (2 : k) ≠ 0) : orderOf (negTwo k) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    apply Subtype.ext
    show (-1 : Matrix (Fin 2) (Fin 2) k) * (-1) = (1 : Matrix (Fin 2) (Fin 2) k)
    simp
  · intro h
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) k => (M : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp only [negTwo, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
      Matrix.one_apply_eq] at this
    apply htwo
    linear_combination -this

theorem bdL_comm {g : SpecialLinearGroup (Fin 4) k} {b : k}
    (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) (U : SpecialLinearGroup (Fin 2) k) :
    bdL k U * g = g * bdL k U := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_bdL, hg]
  exact bd_comm_X1 _ _ b

theorem bdR_comm {g : SpecialLinearGroup (Fin 4) k} {b : k}
    (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) (W : SpecialLinearGroup (Fin 2) k) :
    bdR k W * g = g * bdR k W := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_bdR, hg]
  exact bd_comm_X1 _ _ b

theorem isPComponent_factor [Finite k] (htwo : (2 : k) ≠ 0) (hk4 : 4 ≤ Nat.card k)
    {g : SpecialLinearGroup (Fin 4) k} (ι : SpecialLinearGroup (Fin 2) k →*
      SpecialLinearGroup (Fin 4) k) (hι : Function.Injective ((proj 4 k).comp ι))
    (hιg : ∀ U, ι U * g = g * ι U)
    (hιn : ∀ Z : SpecialLinearGroup (Fin 4) k, Z * g = g * Z → ∀ U, Z * ι U * Z⁻¹ ∈ ι.range) :
    ((proj 4 k).comp ι).range ≤ centralizer ({proj 4 k g} : Set (projectiveSL 4 k)) ∧
      IsPComponent 2 ((((proj 4 k).comp ι).range).subgroupOf
        (centralizer ({proj 4 k g} : Set (projectiveSL 4 k)))) ∧
      IsQuasisimple ↥((((proj 4 k).comp ι).range).subgroupOf
        (centralizer ({proj 4 k g} : Set (projectiveSL 4 k)))) := by
  classical
  set C := centralizer ({proj 4 k g} : Set (projectiveSL 4 k)) with hC
  set A := ((proj 4 k).comp ι).range with hA
  set N₀ := centralizer ({g} : Set (SpecialLinearGroup (Fin 4) k)) with hN₀
  set N := N₀.map (proj 4 k) with hN
  have hAC : A ≤ C := by
    rintro _ ⟨U, rfl⟩
    rw [hC, mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul, hιg]
  have hNC : N ≤ C := by
    rintro _ ⟨Z, hZ, rfl⟩
    rw [hC, mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (mem_centralizer_singleton_iff.mp hZ)]
  have hAN : A ≤ N := by
    rintro _ ⟨U, rfl⟩
    exact ⟨ι U, mem_centralizer_singleton_iff.mpr (hιg U), rfl⟩
  have hSL : IsQuasisimple (SpecialLinearGroup (Fin 2) k) := by
    have hns : ¬ (2 = 1 ∨ 2 = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)) := by omega
    exact ((CatalogueBGeneralLinear.generalLinear_p_components 2 k (by norm_num)).2.2 hns).1
  have eA : SpecialLinearGroup (Fin 2) k ≃* A := MonoidHom.ofInjective hι
  have hAq : IsQuasisimple ↥(A.subgroupOf C) :=
    (isQuasisimple_congr ((subgroupOfEquivOfLe hAC).trans eA.symm)).2 hSL
  have hNn : (N.subgroupOf C).Normal := by
    constructor
    rintro ⟨n, hnC⟩ hn ⟨c, hc⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨W, hW, rfl⟩ := hn
    obtain ⟨Z, rfl⟩ := proj_surjective 4 k c
    have hZ : Z * g * Z⁻¹ * g⁻¹ ∈ center (SpecialLinearGroup (Fin 4) k) := by
      rw [← scalars_eq_center, ← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
        mem_centralizer_singleton_iff.mp hc]
      group
    refine ⟨Z * W * Z⁻¹, mem_centralizer_singleton_iff.mpr
      (conj_comm_of_central hZ (mem_centralizer_singleton_iff.mp hW)), ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hAn : ((A.subgroupOf C).subgroupOf (N.subgroupOf C)).Normal := by
    constructor
    rintro ⟨⟨a, haC⟩, haN⟩ ha ⟨⟨n, hnC⟩, hnN⟩
    rw [mem_subgroupOf, mem_subgroupOf] at ha ⊢
    rw [mem_subgroupOf] at hnN
    obtain ⟨W, hW, rfl⟩ := hnN
    obtain ⟨U, rfl⟩ := ha
    obtain ⟨U', hU'⟩ := hιn W (mem_centralizer_singleton_iff.mp hW) U
    refine ⟨U', ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.comp_apply, hU', map_mul, map_inv]
  have hAN' : A.subgroupOf C ≤ N.subgroupOf C := fun y hy => hAN hy
  have hsn : (A.subgroupOf C).IsSubnormal :=
    IsSubnormal.step _ _ hAN' hNn.isSubnormal hAn
  have hnot : ¬ A.subgroupOf C ≤ pPrimeCore 2 ↥C := by
    intro hle
    set e := (proj 4 k).comp ι (negTwo k) with he
    have heA : e ∈ A := ⟨negTwo k, rfl⟩
    have hmem : (⟨e, hAC heA⟩ : ↥C) ∈ pPrimeCore 2 ↥C := hle (by rw [mem_subgroupOf]; exact heA)
    have hord : orderOf (⟨⟨e, hAC heA⟩, hmem⟩ : ↥(pPrimeCore 2 ↥C)) = 2 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, he, orderOf_injective _ hι,
        orderOf_negTwo htwo]
    have hdvd := orderOf_dvd_natCard (⟨⟨e, hAC heA⟩, hmem⟩ : ↥(pPrimeCore 2 ↥C))
    rw [hord] at hdvd
    have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    exact absurd (Nat.Coprime.coprime_dvd_right hdvd hcop) (by norm_num)
  exact ⟨hAC, isPComponent_of_isComponent_of_not_le 2 ⟨hAq, hsn⟩ hnot, hAq⟩

theorem eq_factor_of_pComponent [Finite k] (htwo : (2 : k) ≠ 0)
    {g : SpecialLinearGroup (Fin 4) k} {b : k} (hb : b ≠ 0)
    (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b) {K : Subgroup (projectiveSL 4 k)}
    (hKle : K ≤ centralizer ({proj 4 k g} : Set (projectiveSL 4 k)))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({proj 4 k g} : Set (projectiveSL 4 k))))) :
    K = factorL k ∨ K = factorR k := by
  classical
  set C := centralizer ({proj 4 k g} : Set (projectiveSL 4 k)) with hC
  set N₀ := centralizer ({g} : Set (SpecialLinearGroup (Fin 4) k)) with hN₀
  have hlift : ∀ y ∈ C, ∃ Z : SpecialLinearGroup (Fin 4) k, proj 4 k Z = y ∧
      Z * g * Z⁻¹ * g⁻¹ ∈ center (SpecialLinearGroup (Fin 4) k) := by
    intro y hy
    obtain ⟨Z, rfl⟩ := proj_surjective 4 k y
    refine ⟨Z, rfl, ?_⟩
    rw [← scalars_eq_center, ← proj_eq_one_iff, map_mul, map_mul, map_mul, map_inv, map_inv,
      mem_centralizer_singleton_iff.mp hy]
    group
  have hperf : Group.IsPerfect K := by
    have := CatalogueBAlternating.pComponent_perfect hK
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKle).toMonoidHom)
      (subgroupOfEquivOfLe hKle).surjective
  have hnt : Nontrivial K := by
    have := nontrivial_of_isPComponent' hK
    exact (subgroupOfEquivOfLe hKle).symm.toEquiv.nontrivial
  have hKN : K ≤ N₀.map (proj 4 k) := by
    rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
    intro y hy y' hy'
    obtain ⟨Z, rfl, hZ⟩ := hlift y (hKle hy)
    obtain ⟨Z', rfl, hZ'⟩ := hlift y' (hKle hy')
    exact ⟨⁅Z, Z'⁆, mem_centralizer_singleton_iff.mpr (commutator_comm_of_central hZ hZ'),
      map_commutatorElement _ _ _⟩
  have hKF : K ≤ factorL k ⊔ factorR k := by
    rw [← Subgroup.commutator_eq_self (H := K), Subgroup.commutator_le]
    intro y hy y' hy'
    obtain ⟨Z, hZ, rfl⟩ := hKN hy
    obtain ⟨Z', hZ', rfl⟩ := hKN hy'
    have hmem := comm_mem_sup htwo hb hg (mem_centralizer_singleton_iff.mp hZ)
      (mem_centralizer_singleton_iff.mp hZ')
    have hmap : ((bdL k).range ⊔ (bdR k).range).map (proj 4 k) = factorL k ⊔ factorR k := by
      rw [Subgroup.map_sup, factorL, factorR, MonoidHom.range_comp, MonoidHom.range_comp]
    rw [← map_commutatorElement, ← hmap]
    exact mem_map_of_mem _ hmem
  have hcomm_false : (∀ y ∈ K, ∀ y' ∈ factorL k ⊔ factorR k, y * y' = y' * y) → False := by
    intro hc
    have hbot : ⁅K, K⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro y hy y' hy'
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc y hy y' (hKF hy')
    rw [Subgroup.commutator_eq_self (H := K)] at hbot
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt hbot
  by_cases hk3 : Nat.card k = 3
  ·
    exfalso
    have hsl : Group.IsSolvable (SpecialLinearGroup (Fin 2) k) := by
      have := CatalogueBGeneralLinear.generalLinear_small_solvable 2 k (Or.inr ⟨rfl, Or.inr hk3⟩)
      exact Group.isSolvable_of_isSolvable_injective (f := SpecialLinearGroup.toGL)
        SpecialLinearGroup.toGL_injective
    set μ : SpecialLinearGroup (Fin 2) k × SpecialLinearGroup (Fin 2) k →* projectiveSL 4 k :=
      (proj 4 k).comp (MonoidHom.noncommCoprod (bdL k) (bdR k) fun U W => bdL_mul_bdR U W)
      with hμ
    have hFμ : factorL k ⊔ factorR k ≤ μ.range := by
      refine sup_le ?_ ?_
      · rintro _ ⟨U, rfl⟩
        refine ⟨(U, 1), ?_⟩
        change proj 4 k (bdL k U * bdR k 1) = proj 4 k (bdL k U)
        rw [map_one, mul_one]
      · rintro _ ⟨W, rfl⟩
        refine ⟨(1, W), ?_⟩
        change proj 4 k (bdL k 1 * bdR k W) = proj 4 k (bdR k W)
        rw [map_one, one_mul]
    have : Group.IsSolvable μ.range := Group.isSolvable_of_surjective μ.rangeRestrict_surjective
    have : Group.IsSolvable K :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hKF.trans hFμ))
    exact Group.IsPerfect.not_isSolvable K inferInstance
  have hk4 : 4 ≤ Nat.card k := by
    have h2 : 2 ≤ Nat.card k := Finite.one_lt_card
    have hne2 : Nat.card k ≠ 2 := by
      intro h
      have := Fintype.ofFinite k
      have h0 := FiniteField.cast_card_eq_zero k
      rw [← Nat.card_eq_fintype_card, h] at h0
      exact htwo (by exact_mod_cast h0)
    omega
  obtain ⟨hLC, hL, hqL⟩ := isPComponent_factor htwo hk4 (bdL k) proj_bdL_injective
    (bdL_comm hg) (fun _ hZ U => conj_bdL_mem htwo hb hg hZ U)
  obtain ⟨hRC, hR, hqR⟩ := isPComponent_factor htwo hk4 (bdR k) proj_bdR_injective
    (bdR_comm hg) (fun _ hZ W => conj_bdR_mem htwo hb hg hZ W)
  by_contra hne
  push Not at hne
  obtain ⟨hneL, hneR⟩ := hne
  have hsub : ∀ {A : Subgroup (projectiveSL 4 k)}, A ≤ C → K ≠ A →
      K.subgroupOf C ≠ A.subgroupOf C := by
    intro A hA hKA h
    apply hKA
    have := subgroupOf_inj.mp h
    rwa [inf_of_le_left hKle, inf_of_le_left hA] at this
  have hcL := ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
    hK hL).2 (hsub hLC hneL)).2.2.2 (Or.inr hqL)
  have hcR := ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
    hK hR).2 (hsub hRC hneR)).2.2.2 (Or.inr hqR)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcL hcR
  apply hcomm_false
  intro y hy y' hy'
  have hyC : (⟨y, hKle hy⟩ : ↥C) ∈ K.subgroupOf C := by rw [mem_subgroupOf]; exact hy
  have hyA : ∀ {A : Subgroup (projectiveSL 4 k)} (hA : A ≤ C),
      K.subgroupOf C ≤ centralizer ((A.subgroupOf C : Subgroup ↥C) : Set ↥C) →
      ∀ a ∈ A, a * y = y * a := by
    intro A hA hKA a ha
    have h1 := mem_centralizer_iff.mp (hKA hyC) ⟨a, hA ha⟩
      (show (⟨a, hA ha⟩ : ↥C) ∈ A.subgroupOf C by rw [mem_subgroupOf]; exact ha)
    exact congrArg Subtype.val h1
  have hcent : factorL k ⊔ factorR k ≤ centralizer ({y} : Set (projectiveSL 4 k)) :=
    sup_le (fun a ha => mem_centralizer_singleton_iff.mpr (hyA hLC hcL a ha))
      (fun a ha => mem_centralizer_singleton_iff.mpr (hyA hRC hcR a ha))
  exact (mem_centralizer_singleton_iff.mp (hcent hy')).symm

theorem pairConfig_factors [Finite k] (htwo : (2 : k) ≠ 0) {g : SpecialLinearGroup (Fin 4) k}
    {b : k} (hb : b ≠ 0) (hg : (g : Matrix (Fin 4) (Fin 4) k) = X1 b)
    {K₁ K₂ : Subgroup (projectiveSL 4 k)}
    (hc : Sp4Rec.PairConfig (projectiveSL 4 k) (proj 4 k g) K₁ K₂) :
    (K₁ = factorL k ∧ K₂ = factorR k) ∨ (K₁ = factorR k ∧ K₂ = factorL k) := by
  rcases eq_factor_of_pComponent htwo hb hg hc.K_le hc.isPComponent_K with h1 | h1 <;>
  rcases eq_factor_of_pComponent htwo hb hg hc.K'_le hc.isPComponent_K' with h2 | h2
  · exact absurd (h1.trans h2.symm) hc.ne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hc.ne

end Catalog7L4

end CFSG.ComponentClassification.GSThmB
