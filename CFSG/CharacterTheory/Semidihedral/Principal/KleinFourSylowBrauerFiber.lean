module

public import CFSG.CharacterTheory.Semidihedral.Principal.OrderEightFourGroupDefectParity
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralLinearBlockAssociates

public section

open scoped BigOperators Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.BlockOrbits

namespace KleinFourFiber

variable {G : Type*} [Group G]

theorem mem_centralizer_subgroupOf_iff {S C : Subgroup G} (hSC : S ≤ C) (x : C) :
    x ∈ Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ↔
      (x : G) ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h g hg
    exact congrArg Subtype.val (h ⟨g, hSC hg⟩ (Subgroup.mem_subgroupOf.mpr hg))
  · intro h y hy
    exact Subtype.ext (h y (Subgroup.mem_subgroupOf.mp hy))

@[expose] def centralizerSubgroupOfEquiv {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) :
    Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ≃*
      Subgroup.centralizer (S : Set G) where
  toFun x := ⟨((x : C) : G), (mem_centralizer_subgroupOf_iff hSC x).mp x.2⟩
  invFun w := ⟨⟨w, hWC w.2⟩, (mem_centralizer_subgroupOf_iff hSC _).mpr w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem centralizerSubgroupOfEquiv_apply {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C)
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    ((centralizerSubgroupOfEquiv hSC hWC x : Subgroup.centralizer (S : Set G)) : G) =
      ((x : C) : G) := rfl

theorem centralizerSubgroupOfEquiv_symm_apply {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (w : Subgroup.centralizer (S : Set G)) :
    ((((centralizerSubgroupOfEquiv hSC hWC).symm w :
      Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) : C) : G) = w := rfl

@[expose] def fiberConj {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G)) :
    Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) ≃*
      Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C) :=
  ((centralizerSubgroupOfEquiv hSC hWC).trans (centralizerConjugation S n hn)).trans
    (centralizerSubgroupOfEquiv hSC hWC).symm

theorem fiberConj_apply {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G))
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    (((fiberConj hSC hWC n hn x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
      C) : G) = n * ((x : C) : G) * n⁻¹ := rfl

theorem centralizerSubgroupOfEquiv_fiberConj {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G))
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    centralizerSubgroupOfEquiv hSC hWC (fiberConj hSC hWC n hn x) =
      centralizerConjugation S n hn (centralizerSubgroupOfEquiv hSC hWC x) := rfl

theorem mem_normalizer_of_subgroupOf {S C : Subgroup G} (hSC : S ≤ C) (c : C)
    (hc : c ∈ Subgroup.normalizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    (c : G) ∈ Subgroup.normalizer (S : Set G) := by
  have hnorm := Subgroup.mem_normalizer_iff.mp hc
  have hfwd : ∀ g ∈ S, (c : G) * g * (c : G)⁻¹ ∈ S := by
    intro g hg
    have h := (hnorm ⟨g, hSC hg⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
    exact Subgroup.mem_subgroupOf.mp h
  have hbwd : ∀ g ∈ S, (c : G)⁻¹ * g * c ∈ S := by
    intro g hg
    have hmem : (c⁻¹ * ⟨g, hSC hg⟩ * c : C) ∈ S.subgroupOf C := by
      apply (hnorm _).mpr
      have hval : c * (c⁻¹ * ⟨g, hSC hg⟩ * c) * c⁻¹ = ⟨g, hSC hg⟩ := by group
      rw [hval]
      exact Subgroup.mem_subgroupOf.mpr hg
    exact Subgroup.mem_subgroupOf.mp hmem
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact hfwd g
  · intro h
    have := hbwd _ h
    simpa [mul_assoc] using this

theorem sq_mem_centralizer {S : Subgroup G} (hS : IsKleinFour S) {t : G} (htS : t ∈ S)
    (ht1 : t ≠ 1) {c : G} (hcN : c ∈ Subgroup.normalizer (S : Set G)) (hct : c * t = t * c) :
    c * c ∈ Subgroup.centralizer (S : Set G) := by
  have : IsKleinFour S := hS
  have hnorm := Subgroup.mem_normalizer_iff.mp hcN
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hconjt : c * t * c⁻¹ = t := by rw [hct]; group
  have hcs : c * s * c⁻¹ ∈ S := (hnorm s).mp hs
  have hfix_or_swap : c * s * c⁻¹ = s ∨ c * s * c⁻¹ = t * s := by
    by_cases hs1 : s = 1
    · left
      rw [hs1]
      group
    by_cases hst : s = t
    · left
      rw [hst, hconjt]
    by_cases heq : c * s * c⁻¹ = s
    · exact Or.inl heq
    · right
      have h1 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ 1 := fun h => hs1 (by
        have hval : c * s * c⁻¹ = 1 := congrArg Subtype.val h
        exact conj_eq_one_iff.mp hval)
      have h2 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ ⟨t, htS⟩ := fun h => hst (by
        have hval : c * s * c⁻¹ = t := congrArg Subtype.val h
        rw [← hconjt] at hval
        exact mul_left_cancel (mul_right_cancel hval))
      have h3 : (⟨c * s * c⁻¹, hcs⟩ : S) ≠ ⟨s, hs⟩ := fun h => heq (congrArg Subtype.val h)
      have ht' : (⟨t, htS⟩ : S) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
      have hs' : (⟨s, hs⟩ : S) ≠ 1 := fun h => hs1 (congrArg Subtype.val h)
      have hts : (⟨t, htS⟩ : S) ≠ ⟨s, hs⟩ := fun h => hst (congrArg Subtype.val h).symm
      have hmul := IsKleinFour.eq_mul_of_ne_all ht' hs' hts h1 h2 h3
      exact congrArg Subtype.val hmul
  have htt : t * t = 1 := by
    have h := IsKleinFour.mul_self (⟨t, htS⟩ : S)
    exact congrArg Subtype.val h
  have hc2 : c * c * s * (c * c)⁻¹ = s := by
    rcases hfix_or_swap with h | h
    · calc c * c * s * (c * c)⁻¹ = c * (c * s * c⁻¹) * c⁻¹ := by group
        _ = s := by rw [h, h]
    · calc c * c * s * (c * c)⁻¹ = c * (c * s * c⁻¹) * c⁻¹ := by group
        _ = c * (t * s) * c⁻¹ := by rw [h]
        _ = (c * t * c⁻¹) * (c * s * c⁻¹) := by group
        _ = t * (t * s) := by rw [hconjt, h]
        _ = s := by rw [← mul_assoc, htt, one_mul]
  calc s * (c * c) = c * c * s * (c * c)⁻¹ * (c * c) := by rw [hc2]
    _ = c * c * s := by group

theorem kleinFour_comm {S : Subgroup G} (hS : IsKleinFour S) :
    ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  intro a ha b hb
  have : IsKleinFour S := hS
  exact congrArg Subtype.val
    ((IsKleinFour.isMulCommutative (G := S)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem isKleinFour_subgroupOf {S K : Subgroup G} (hS : IsKleinFour S) (hSK : S ≤ K) :
    IsKleinFour (S.subgroupOf K) where
  card_four := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv]
    exact hS.card_four
  exponent_two := by
    rw [Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSK)]
    exact hS.exponent_two

variable [Finite G]

omit [Finite G] in
theorem centralizer_subgroupOf_normalizer_normal (S : Subgroup G) :
    ((Subgroup.centralizer (S : Set G)).subgroupOf (Subgroup.normalizer (S : Set G))).Normal := by
  constructor
  intro w hw n
  rw [Subgroup.mem_subgroupOf] at hw ⊢
  change (n : G) * w * (n : G)⁻¹ ∈ Subgroup.centralizer (S : Set G)
  exact (centralizer_conjugation_mem_iff S n w n.property).mpr hw

theorem odd_index_centralizer (S : Sylow 2 G)
    (hSab : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * b = b * a) :
    Odd ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index := by
  have hSW : (S : Subgroup G) ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
    OrbitIdempotents.le_centralizer_self_of_comm _ hSab
  have hle : (S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSW (Subgroup.mem_subgroupOf.mp hx))
  have hSylow := Sylow.not_dvd_index (S.subtype (Subgroup.le_normalizer))
  rw [Sylow.coe_subtype] at hSylow
  refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hSylow ?_)
  exact h.trans (Subgroup.index_dvd_of_le hle)

theorem index_centralizer_eq (S : Sylow 2 G) (hS : IsKleinFour (S : Subgroup G)) :
    ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 1 ∨
      ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3 := by
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G)
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  have hK : IsKleinFour ((S : Subgroup G).subgroupOf N) := isKleinFour_subgroupOf hS hSN
  have h6 := FourGroupParity.index_centralizer_dvd_six ((S : Subgroup G).subgroupOf N) hK
  have hceq : Subgroup.centralizer (((S : Subgroup G).subgroupOf N : Subgroup N) : Set N) =
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N := by
    ext x
    rw [mem_centralizer_subgroupOf_iff hSN, Subgroup.mem_subgroupOf]
  rw [hceq] at h6
  have hodd := odd_index_centralizer S (kleinFour_comm hS)
  have hle := Nat.le_of_dvd (by norm_num) h6
  set k := ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf N).index
  obtain ⟨j, hj⟩ := hodd
  interval_cases k <;> omega

theorem mem_centralizer_of_fix (S : Sylow 2 G) (hS : IsKleinFour (S : Subgroup G)) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht1 : t ≠ 1) {c : G}
    (hcN : c ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (hct : c * t = t * c) :
    c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
  have hc2 := sq_mem_centralizer hS htS ht1 hcN hct
  have : ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal :=
    centralizer_subgroupOf_normalizer_normal _
  have hk := Subgroup.pow_index_mem ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((S : Subgroup G) : Set G))) ⟨c, hcN⟩
  rw [Subgroup.mem_subgroupOf] at hk
  obtain ⟨j, hj⟩ := odd_index_centralizer S (kleinFour_comm hS)
  set k := ((Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((S : Subgroup G) : Set G))).index with hkdef
  have hck : c ^ k ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := hk
  have hc : c = ((c * c) ^ j)⁻¹ * c ^ k := by
    rw [hj, ← sq, ← pow_mul, pow_succ]
    group
  rw [hc]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc2 j)) hck

omit [Finite G] in
theorem normalizer_zpowers_le {t : G} (ht1 : t ≠ 1) (htt : t * t = 1) :
    Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  intro g hg
  apply DihedralAssociates.mem_centralizer_zpowers_of_commute
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, htt]) ht1
  have hmem : g * t * g⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hg t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hk
  have hconj : g * t * g⁻¹ = t := by
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact absurd (conj_eq_one_iff.mp hk.symm) ht1
    · rw [h1, zpow_one] at hk
      exact hk.symm
  calc g * t = (g * t * g⁻¹) * g := by group
    _ = t * g := by rw [hconj]

omit [Finite G] in
theorem coefficientBlockDefect_of_normal_sylow [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (P : Sylow p G) [(P : Subgroup G).Normal] (χ : basis.index) :
    coefficientBlockDefect basis ideal p χ P := by
  obtain ⟨D, hD⟩ := coefficientBlockDefect_exists basis ideal p χ
  have hPD := normal_p_le_coefficientBlockDefect basis ideal p P P.isPGroup' hD
  have hDP := CompatibleFamily.pSubgroup_subconjugate_sylow P
    (coefficientBlockDefect_isPGroup basis ideal hD)
  have heq : (P : Subgroup G) = D :=
    Subgroup.eq_of_le_of_card_ge hPD (subgroupSubconjugate_card_le hDP)
  rw [heq]
  exact hD

variable [Fintype G]

omit [Finite G] in
theorem brauerProjection_composite (ring : Subring ℂ) (P S C : Subgroup G) (hPS : P ≤ S)
    (hCP : Subgroup.centralizer (P : Set G) ≤ C) (hCN : C ≤ Subgroup.normalizer (P : Set G))
    (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
    (z : centralCoefficientSubring (G := G) ring) :
    centralCoefficientTransport ring (centralizerSubgroupOfEquiv hSC hWC)
        (centralNormalizerCoefficientProjection ring (S.subgroupOf C)
          (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) le_rfl
          (Subgroup.centralizer_le_normalizer _)
          (centralNormalizerCoefficientProjection ring P C hCP hCN z)) =
      centralNormalizerCoefficientProjection ring S (Subgroup.centralizer (S : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) z := by
  apply Subtype.ext
  ext w
  have hwP : (w : G) ∈ Subgroup.centralizer (P : Set G) := Subgroup.centralizer_le hPS w.property
  rw [centralCoefficientTransport_coeff, centralNormalizerCoefficientProjection_coeff,
    centralNormalizerCoefficientProjection_coeff, centralNormalizerCoefficientProjection_coeff,
    ite_eq_left ((centralizerSubgroupOfEquiv hSC hWC).symm w).property, ite_eq_left w.property]
  split_ifs with h
  · rfl
  · exact absurd hwP h

omit [Finite G] in
theorem brauer_composite (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ)
    [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P S C : Subgroup G)
    (hP : IsPGroup p P) (hSp : IsPGroup p S) (hPS : P ≤ S)
    (hCP : Subgroup.centralizer (P : Set G) ≤ C) (hCN : C ≤ Subgroup.normalizer (P : Set G))
    (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
    (cb : FiniteIrreducibleCharacterBasis C)
    (wb : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)))
    (gb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (S : Set G)))
    {γ : wb.index} {γG : gb.index}
    (hγ : LabelTransport wb gb (centralizerSubgroupOfEquiv hSC hWC) γ γG) {c : cb.index}
    (hc : brauerNormalizerCharacterResidueHom ideal p (S.subgroupOf C) hSp.comap_subtype
      (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) le_rfl
      (Subgroup.centralizer_le_normalizer _) wb γ = centralCharacterResidueHom cb ideal c) :
    brauerNormalizerCharacterResidueHom ideal p P hP C hCP hCN cb c =
      brauerNormalizerCharacterResidueHom ideal p S hSp (Subgroup.centralizer (S : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) gb γG := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom cb ideal c (centralNormalizerCoefficientProjection _ P C hCP hCN
    z) = centralCharacterResidueHom gb ideal γG (centralNormalizerCoefficientProjection _ S _ le_rfl
      (Subgroup.centralizer_le_normalizer _) z)
  rw [← hc, ← brauerProjection_composite _ P S C hPS hCP hCN hSC hWC z,
    centralCharacterResidueHom_labelTransport wb gb ideal _ hγ]
  rfl

omit [Finite G] in
theorem brauer_eq_of_same {K : Type*} [Group K] [Fintype K]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (P : Subgroup K) (hP : IsPGroup p P)
    (L : Subgroup K) (hCL : Subgroup.centralizer (P : Set K) ≤ L)
    (hLN : L ≤ Subgroup.normalizer (P : Set K)) (lb : FiniteIrreducibleCharacterBasis L)
    {γ₁ γ₂ : lb.index} (hsame : sameCoefficientBlock lb (localizedComplexIntegerRing ideal) γ₁ γ₂) :
    brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₁ =
      brauerNormalizerCharacterResidueHom ideal p P hP L hCL hLN lb γ₂ := by
  apply RingHom.ext
  intro z
  change centralCharacterResidueHom lb ideal γ₁ _ = centralCharacterResidueHom lb ideal γ₂ _
  rw [(sameCoefficientBlock_iff_centralCharacterResidueHom_eq lb ideal γ₁ γ₂).mp hsame]

omit [Finite G] in
theorem brauer_centralizer_eq_iff (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (S : Sylow p G)
    (gb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer ((S : Subgroup G) : Set G)))
    (θ₁ θ₂ : gb.index) :
    brauerNormalizerCharacterResidueHom ideal p S S.isPGroup'
        (Subgroup.centralizer ((S : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) gb θ₁ =
      brauerNormalizerCharacterResidueHom ideal p S S.isPGroup'
        (Subgroup.centralizer ((S : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) gb θ₂ ↔
    ∃ (n : G) (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (θ' : gb.index),
      LabelTransport gb gb (centralizerConjugation (S : Subgroup G) n hn) θ₁ θ' ∧
      sameCoefficientBlock gb (localizedComplexIntegerRing ideal) θ' θ₂ := by
  obtain ⟨nb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.normalizer ((S : Subgroup G) : Set G))
  obtain ⟨-, -, horbit, hext, hinj, hiff⟩ := external_block_orbits ideal p (S : Subgroup G)
    (Subgroup.normalizer ((S : Subgroup G) : Set G)) S.isPGroup' Subgroup.le_normalizer
    (Subgroup.centralizer_le_normalizer _) le_rfl nb gb
  let SN : Sylow p (Subgroup.normalizer ((S : Subgroup G) : Set G)) :=
    S.subtype Subgroup.le_normalizer
  have : (SN : Subgroup (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal := by
    change ((S : Subgroup G).subgroupOf (Subgroup.normalizer ((S : Subgroup G) : Set G))).Normal
    infer_instance
  have hdef : ∀ χ : nb.index, coefficientBlockDefect nb ideal p χ ((S : Subgroup G).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))) := fun χ =>
    coefficientBlockDefect_of_normal_sylow nb ideal p SN χ
  have hW_N : ∀ (χ : nb.index) (θ : gb.index),
      ExternalResidueMatch (S : Subgroup G) (Subgroup.normalizer ((S : Subgroup G) : Set G))
        (Subgroup.centralizer_le_normalizer _) nb ideal gb χ θ →
      brauerNormalizerCharacterResidueHom ideal p S S.isPGroup'
          (Subgroup.centralizer ((S : Subgroup G) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) gb θ =
        brauerNormalizerCharacterResidueHom ideal p S S.isPGroup'
          (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
          le_rfl nb χ := by
    intro χ θ hmatch
    apply RingHom.ext
    intro z
    rw [external_brauer_apply_of_match ideal p (S : Subgroup G) _ S.isPGroup'
      (Subgroup.centralizer_le_normalizer _) le_rfl nb gb hmatch z]
    change centralCharacterResidueHom gb ideal θ (centralNormalizerCoefficientProjection _
      (S : Subgroup G) _ le_rfl (Subgroup.centralizer_le_normalizer _) z) = _
    rw [normalCentralizer_brauerProjection_eq]
  obtain ⟨χ₁, h₁⟩ := hext θ₁
  obtain ⟨χ₂, h₂⟩ := hext θ₂
  rw [hW_N χ₁ θ₁ h₁, hW_N χ₂ θ₂ h₂]
  constructor
  · intro hBr
    have hsame := defect_normalizer_brauer_injective ideal p (S : Subgroup G) S.isPGroup' nb
      (hdef χ₁) (hdef χ₂) hBr
    have h₂' := (hiff χ₁ χ₂ hsame θ₂).mpr h₂
    obtain ⟨n, θ', hθ', hsame'⟩ := ((horbit χ₁).2 θ₁ h₁ θ₂).mp h₂'
    exact ⟨n, n.property, θ', hθ', hsame'⟩
  · rintro ⟨n, hn, θ', hθ', hsame'⟩
    have h₂' : ExternalResidueMatch (S : Subgroup G)
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) (Subgroup.centralizer_le_normalizer _)
        nb ideal gb χ₁ θ₂ := ((horbit χ₁).2 θ₁ h₁ θ₂).mpr ⟨⟨n, hn⟩, θ', hθ', hsame'⟩
    have hsame := hinj χ₁ χ₂ θ₂ h₂' h₂
    exact brauer_eq_of_same ideal p (S : Subgroup G) S.isPGroup' _ _ le_rfl nb hsame

omit [Finite G] [Fintype G] in
theorem le_centralizer_zpowers {S : Subgroup G} (hS : IsKleinFour S) {t : G} (htS : t ∈ S) :
    S ≤ Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) := fun y hy =>
  DihedralAssociates.mem_centralizer_zpowers_of_commute (kleinFour_comm hS y hy t htS)

omit [Finite G] in
theorem labelTransport_fiberConj {S C : Subgroup G} (hSC : S ≤ C)
    (hWC : Subgroup.centralizer (S : Set G) ≤ C) (n : G)
    (hn : n ∈ Subgroup.normalizer (S : Set G))
    (wb : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)))
    (gb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (S : Set G)))
    {γ γ' : wb.index} {γG γ'G : gb.index}
    (h1 : LabelTransport wb wb (fiberConj hSC hWC n hn) γ γ')
    (h2 : LabelTransport wb gb (centralizerSubgroupOfEquiv hSC hWC) γ γG)
    (h3 : LabelTransport wb gb (centralizerSubgroupOfEquiv hSC hWC) γ' γ'G) :
    LabelTransport gb gb (centralizerConjugation S n hn) γG γ'G := by
  intro w
  obtain ⟨x, rfl⟩ := (centralizerSubgroupOfEquiv hSC hWC).surjective w
  rw [← centralizerSubgroupOfEquiv_fiberConj, h3, h1, h2]

omit [Finite G] [Fintype G] in
theorem coefficientBlock_eq_iff {K : Type*} [Group K] [Fintype K]
    (basis : FiniteIrreducibleCharacterBasis K) (ring : Subring ℂ) (χ ψ : basis.index) :
    coefficientBlock basis ring χ = coefficientBlock basis ring ψ ↔
      sameCoefficientBlock basis ring χ ψ := by
  constructor
  · intro h
    rw [← coefficientBlock_mem_iff, h]
    exact coefficientBlock_self_mem _ _ _
  · intro h
    exact (coefficientBlock_eq_of_mem basis ring ((coefficientBlock_mem_iff _ _ _ _).mpr h)).symm

omit [Finite G] [Fintype G] in
theorem card_image_eq_of_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  apply Finset.card_bij (fun b hb => g (Finset.mem_image.mp hb).choose)
  · intro b hb
    exact Finset.mem_image_of_mem g (Finset.mem_image.mp hb).choose_spec.1
  · intro b₁ hb₁ b₂ hb₂ heq
    obtain ⟨hx₁, hfx₁⟩ := (Finset.mem_image.mp hb₁).choose_spec
    obtain ⟨hx₂, hfx₂⟩ := (Finset.mem_image.mp hb₂).choose_spec
    rw [← hfx₁, ← hfx₂]
    exact (h _ hx₁ _ hx₂).mpr heq
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨f x, Finset.mem_image_of_mem f hx, ?_⟩
    obtain ⟨hx', hfx'⟩ := (Finset.mem_image.mp (Finset.mem_image_of_mem f hx)).choose_spec
    exact (h _ hx' _ hx).mp hfx'

section Action

variable {S C : Subgroup G} (hSC : S ≤ C) (hWC : Subgroup.centralizer (S : Set G) ≤ C)
  (wb : FiniteIrreducibleCharacterBasis
    (Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)))

omit [Finite G] [Fintype G] in
theorem fiberConj_mul (n m : Subgroup.normalizer (S : Set G))
    (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    fiberConj hSC hWC ((n * m : Subgroup.normalizer (S : Set G)) : G) (n * m).2 x =
      fiberConj hSC hWC n n.2 (fiberConj hSC hWC m m.2 x) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fiberConj_apply, fiberConj_apply, fiberConj_apply, Subgroup.coe_mul]
  group

omit [Finite G] [Fintype G] in
theorem fiberConj_one (x : Subgroup.centralizer ((S.subgroupOf C : Subgroup C) : Set C)) :
    fiberConj hSC hWC ((1 : Subgroup.normalizer (S : Set G)) : G)
      (1 : Subgroup.normalizer (S : Set G)).2 x = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [fiberConj_apply, Subgroup.coe_one]
  group

@[expose] noncomputable def fiberLabel (n : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    wb.index :=
  (labelTransport_exists wb wb (fiberConj hSC hWC n n.2) γ).choose

omit [Finite G] in
theorem fiberLabel_spec (n : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    LabelTransport wb wb (fiberConj hSC hWC n n.2) γ (fiberLabel hSC hWC wb n γ) :=
  (labelTransport_exists wb wb (fiberConj hSC hWC n n.2) γ).choose_spec

omit [Finite G] in
theorem fiberLabel_one (γ : wb.index) : fiberLabel hSC hWC wb 1 γ = γ :=
  labelTransport_unique (fiberLabel_spec hSC hWC wb 1 γ) (fun x => by rw [fiberConj_one])

omit [Finite G] in
theorem fiberLabel_mul (n m : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    fiberLabel hSC hWC wb (n * m) γ = fiberLabel hSC hWC wb n (fiberLabel hSC hWC wb m γ) :=
  labelTransport_unique (fiberLabel_spec hSC hWC wb (n * m) γ) (fun x => by
    rw [fiberConj_mul]
    exact (fiberLabel_spec hSC hWC wb n (fiberLabel hSC hWC wb m γ) _).trans
      (fiberLabel_spec hSC hWC wb m γ x))

@[expose, instance_reducible] noncomputable def fiberAction :
    MulAction (Subgroup.normalizer (S : Set G)) wb.index where
  smul := fiberLabel hSC hWC wb
  one_smul := fiberLabel_one hSC hWC wb
  mul_smul := fiberLabel_mul hSC hWC wb

omit [Finite G] in
theorem fiberLabel_of_mem_centralizer (n : Subgroup.normalizer (S : Set G))
    (hn : (n : G) ∈ Subgroup.centralizer (S : Set G)) (γ : wb.index) :
    fiberLabel hSC hWC wb n γ = γ := by
  apply labelTransport_unique (fiberLabel_spec hSC hWC wb n γ)
  intro x
  set w := (centralizerSubgroupOfEquiv hSC hWC).symm ⟨n, hn⟩
  have hx : fiberConj hSC hWC n n.2 x = w * x * w⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hx]
  exact Representation.char_conj (wb.representation γ).representation x w

omit [Finite G] in
theorem image_coefficientBlock (ring : Subring ℂ) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (hring : ring = localizedComplexIntegerRing ideal)
    (n : Subgroup.normalizer (S : Set G)) (γ : wb.index) :
    (coefficientBlock wb ring γ).image (fiberLabel hSC hWC wb n) =
      coefficientBlock wb ring (fiberLabel hSC hWC wb n γ) := by
  subst hring
  let := fiberAction hSC hWC wb
  have hsmul : ∀ (m : Subgroup.normalizer (S : Set G)) (δ : wb.index),
      m • δ = fiberLabel hSC hWC wb m δ := fun _ _ => rfl
  ext δ
  simp only [Finset.mem_image, coefficientBlock_mem_iff]
  constructor
  · rintro ⟨ε, hε, rfl⟩
    exact (sameCoefficientBlock_labelTransport_iff wb wb ideal _ (fiberLabel_spec hSC hWC wb n γ)
      (fiberLabel_spec hSC hWC wb n ε)).mp hε
  · intro hδ
    refine ⟨n⁻¹ • δ, ?_, ?_⟩
    · have hinv : fiberLabel hSC hWC wb n (n⁻¹ • δ) = δ := by
        rw [← hsmul, smul_inv_smul]
      apply (sameCoefficientBlock_labelTransport_iff wb wb ideal _
        (fiberLabel_spec hSC hWC wb n γ) (fiberLabel_spec hSC hWC wb n (n⁻¹ • δ))).mpr
      rw [hinv]
      exact hδ
    · rw [← hsmul, smul_inv_smul]

omit [Finite G] in
theorem card_orbit_blocks_dvd (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    (β : wb.index) :
    ((Finset.univ.filter fun γ => ∃ (n : G) (hn : n ∈ Subgroup.normalizer (S : Set G)),
      LabelTransport wb wb (fiberConj hSC hWC n hn) β γ).image
        (coefficientBlock wb (localizedComplexIntegerRing ideal))).card ∣
      (Subgroup.centralizer (S : Set G)).relIndex (Subgroup.normalizer (S : Set G)) := by
  let := fiberAction hSC hWC wb
  have hsmul : ∀ (m : Subgroup.normalizer (S : Set G)) (δ : wb.index),
      m • δ = fiberLabel hSC hWC wb m δ := fun _ _ => rfl
  set Y₀ := coefficientBlock wb (localizedComplexIntegerRing ideal) β
  have horbit : ((Finset.univ.filter fun γ => ∃ (n : G)
      (hn : n ∈ Subgroup.normalizer (S : Set G)),
        LabelTransport wb wb (fiberConj hSC hWC n hn) β γ).image
          (coefficientBlock wb (localizedComplexIntegerRing ideal)) : Set (Finset wb.index)) =
      MulAction.orbit (Subgroup.normalizer (S : Set G)) Y₀ := by
    ext Y
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image,
      Set.mem_ofPred_eq, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨γ, ⟨n, hn, hγ⟩, rfl⟩
      refine ⟨⟨n, hn⟩, ?_⟩
      rw [Finset.smul_finset_def]
      change (coefficientBlock wb _ β).image (fiberLabel hSC hWC wb ⟨n, hn⟩) = _
      rw [image_coefficientBlock hSC hWC wb _ ideal rfl,
        labelTransport_unique (fiberLabel_spec hSC hWC wb ⟨n, hn⟩ β) hγ]
    · rintro ⟨n, rfl⟩
      refine ⟨fiberLabel hSC hWC wb n β, ⟨n, n.2, fiberLabel_spec hSC hWC wb n β⟩, ?_⟩
      rw [Finset.smul_finset_def]
      change _ = (coefficientBlock wb _ β).image (fiberLabel hSC hWC wb n)
      rw [image_coefficientBlock hSC hWC wb _ ideal rfl]
  have hcard : ((Finset.univ.filter fun γ => ∃ (n : G)
      (hn : n ∈ Subgroup.normalizer (S : Set G)),
        LabelTransport wb wb (fiberConj hSC hWC n hn) β γ).image
          (coefficientBlock wb (localizedComplexIntegerRing ideal))).card =
      (MulAction.stabilizer (Subgroup.normalizer (S : Set G)) Y₀).index := by
    rw [MulAction.index_stabilizer, ← horbit, Set.ncard_coe_finset]
  rw [hcard]
  apply Subgroup.index_dvd_of_le
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn
  rw [MulAction.mem_stabilizer_iff, Finset.smul_finset_def]
  change Y₀.image (fiberLabel hSC hWC wb n) = Y₀
  have hid : fiberLabel hSC hWC wb n = id := funext fun γ =>
    fiberLabel_of_mem_centralizer hSC hWC wb n hn γ
  rw [hid, Finset.image_id]

end Action

end KleinFourFiber

open KleinFourFiber

theorem klein_four_sylow_maximal_block_brauer_fiber_one_or_three {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (S : Sylow 2 G)
    (hS : IsKleinFour (S : Subgroup G)) (t : G) (htS : t ∈ (S : Subgroup G)) (ht1 : t ≠ 1)
    (cb : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
    (wb : FiniteIrreducibleCharacterBasis (Subgroup.centralizer
      (((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
          Subgroup (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) :
        Set (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))))
    (b : cb.index)
    (hb : coefficientBlockDefect cb ideal 2 b ((S : Subgroup G).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))))
    (B : basis.index)
    (hB : brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
      (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) cb b = centralCharacterResidueHom basis ideal B) :
    (∃ β : wb.index, brauerNormalizerCharacterResidueHom ideal 2
        ((S : Subgroup G).subgroupOf
          (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
        S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb β =
          centralCharacterResidueHom cb ideal b ∧
      ∀ β' : wb.index, brauerNormalizerCharacterResidueHom ideal 2
          ((S : Subgroup G).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
          S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb β' =
            centralCharacterResidueHom cb ideal b →
        sameCoefficientBlock wb (localizedComplexIntegerRing ideal) β β') ∧
    (∀ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
        (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _) cb c = centralCharacterResidueHom basis ideal B →
      coefficientBlockDefect cb ideal 2 c ((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))) ∧
    (∀ β : wb.index, brauerNormalizerCharacterResidueHom ideal 2
        ((S : Subgroup G).subgroupOf
          (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
        S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb β =
          centralCharacterResidueHom cb ideal b →
      (∀ (n : G) (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (γ : wb.index),
        LabelTransport wb wb (fiberConj (le_centralizer_zpowers hS htS)
          (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr htS)) n hn) β γ →
        ∃ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2
            ((S : Subgroup G).subgroupOf
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
            S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ =
              centralCharacterResidueHom cb ideal c ∧
          brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
            (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _)
              cb c = centralCharacterResidueHom basis ideal B) ∧
      (∀ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
          (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
          (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) cb c = centralCharacterResidueHom basis ideal B →
        ∃ (n : G) (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (γ : wb.index),
          LabelTransport wb wb (fiberConj (le_centralizer_zpowers hS htS)
            (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr htS)) n hn) β γ ∧
          brauerNormalizerCharacterResidueHom ideal 2
              ((S : Subgroup G).subgroupOf
                (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
              S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ =
            centralCharacterResidueHom cb ideal c) ∧
      (∀ γ₁ γ₂ : wb.index, brauerNormalizerCharacterResidueHom ideal 2
          ((S : Subgroup G).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
          S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ₁ =
        brauerNormalizerCharacterResidueHom ideal 2
          ((S : Subgroup G).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
          S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ₂ →
        sameCoefficientBlock wb (localizedComplexIntegerRing ideal) γ₁ γ₂)) ∧
    ((Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 1 ∨
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 3) ∧
    (((Finset.univ.filter fun c : cb.index => brauerNormalizerCharacterResidueHom ideal 2
        (Subgroup.zpowers t) (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
          cb c = centralCharacterResidueHom basis ideal B).image
          (coefficientBlock cb (localizedComplexIntegerRing ideal))).card = 1 ∨
      ((Finset.univ.filter fun c : cb.index => brauerNormalizerCharacterResidueHom ideal 2
        (Subgroup.zpowers t) (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
          cb c = centralCharacterResidueHom basis ideal B).image
          (coefficientBlock cb (localizedComplexIntegerRing ideal))).card = 3) := by
  have hSab := kleinFour_comm hS
  have hPS : Subgroup.zpowers t ≤ (S : Subgroup G) := (Subgroup.zpowers_le).mpr htS
  have hSC := le_centralizer_zpowers hS htS
  have hWC : Subgroup.centralizer ((S : Subgroup G) : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
    Subgroup.centralizer_le hPS
  have htp : IsPGroup 2 (Subgroup.zpowers t) := S.isPGroup'.to_le hPS
  have hSCp : IsPGroup 2 ((S : Subgroup G).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) :=
    S.isPGroup'.comap_subtype
  have htt : t * t = 1 := by
    have : IsKleinFour (S : Subgroup G) := hS
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨t, htS⟩ : (S : Subgroup G)))
  have hNC : Subgroup.normalizer (((S : Subgroup G).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
        Subgroup (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) :
      Set (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) ≤
      Subgroup.centralizer (((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
          Subgroup (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) :
        Set (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) := by
    intro c hc
    rw [mem_centralizer_subgroupOf_iff hSC]
    exact mem_centralizer_of_fix S hS htS ht1 (mem_normalizer_of_subgroupOf hSC c hc)
      (Subgroup.mem_centralizer_iff.mp c.property t (Subgroup.mem_zpowers t)).symm
  have hSW : (S : Subgroup G).subgroupOf
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤
      Subgroup.centralizer (((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
          Subgroup (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) :
        Set (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) := fun x hx =>
    (mem_centralizer_subgroupOf_iff hSC x).mpr
      (OrbitIdempotents.le_centralizer_self_of_comm _ hSab (Subgroup.mem_subgroupOf.mp hx))
  let SCsyl : Sylow 2 (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :=
    S.subtype hSC
  let SWsyl := SCsyl.subtype hSW
  have : SWsyl.toSubgroup.Normal := by
    constructor
    intro x hx w
    change (w * x * w⁻¹) ∈ ((S : Subgroup G).subgroupOf _).subgroupOf _
    change x ∈ ((S : Subgroup G).subgroupOf _).subgroupOf _ at hx
    have hcomm : w * x = x * w := (Subgroup.mem_centralizer_iff.mp w.property _
      (Subgroup.mem_subgroupOf.mp hx)) |>.symm |> fun h => Subtype.ext h
    rw [hcomm, mul_inv_cancel_right]
    exact hx
  have hWdef : ∀ β : wb.index, coefficientBlockDefect wb ideal 2 β
      (((S : Subgroup G).subgroupOf _).subgroupOf _) := fun β =>
    coefficientBlockDefect_of_normal_sylow wb ideal 2 SWsyl β
  obtain ⟨himage, -, hsurj, hinj⟩ := intermediate_normalizer_controlled_defect_correspondence cb
    ideal 2 _ hSCp _ le_rfl (Subgroup.centralizer_le_normalizer _) _ hSCp le_rfl hSW hNC wb
  have hBdef : coefficientBlockDefect basis ideal 2 B S := by
    obtain ⟨-, E, hE, hSE⟩ := centralizer_brauer_image_defect_contains_local_defect basis ideal 2
      (Subgroup.zpowers t) htp S S.isPGroup' hPS hSC cb b hb B hB
    have hES := CompatibleFamily.pSubgroup_subconjugate_sylow S
      (coefficientBlockDefect_isPGroup basis ideal hE)
    exact DihedralAssociates.coefficientBlockDefect_of_conj basis ideal hE
      (subgroupsConjugate_of_subconjugate_card_ge hES (subgroupSubconjugate_card_le hSE))
  have hclaim2 : ∀ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
      (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
      (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
      (Subgroup.centralizer_le_normalizer _) cb c = centralCharacterResidueHom basis ideal B →
      coefficientBlockDefect cb ideal 2 c ((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) := by
    intro c hc
    obtain ⟨Dc, hDc⟩ := coefficientBlockDefect_exists cb ideal 2 c
    obtain ⟨g, hg⟩ := CompatibleFamily.pSubgroup_subconjugate_sylow SCsyl
      (coefficientBlockDefect_isPGroup cb ideal hDc)
    obtain ⟨D', hD'def⟩ : ∃ D', D' = Dc.map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
    have hD' : coefficientBlockDefect cb ideal 2 c D' :=
      DihedralAssociates.coefficientBlockDefect_of_conj cb ideal hDc ⟨g, hD'def.symm⟩
    have hD'S : D' ≤ (S : Subgroup G).subgroupOf _ := hD'def ▸ hg
    have hPnormal : ((Subgroup.zpowers t).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))).Normal := by
      constructor
      intro a ha h
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hha : (h : G) * a = a * h := (Subgroup.mem_centralizer_iff.mp h.property a ha).symm
      have hval : ((h * a * h⁻¹ : Subgroup.centralizer
          ((Subgroup.zpowers t : Subgroup G) : Set G)) : G) = a := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hha]
        group
      rw [hval]
      exact ha
    have hPD' : (Subgroup.zpowers t).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) ≤ D' :=
      normal_p_le_coefficientBlockDefect cb ideal 2 ((Subgroup.zpowers t).subgroupOf _)
        htp.comap_subtype hD'
    have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, htt]) ht1
    have hcardS : Nat.card ((S : Subgroup G).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) = 2 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hS.card_four]
      norm_num
    have hcardP : Nat.card ((Subgroup.zpowers t).subgroupOf
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G))) = 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPS.trans hSC)).toEquiv,
        Nat.card_zpowers, hord]
    have hdvd1 := Subgroup.card_dvd_of_le hD'S
    have hdvd2 := Subgroup.card_dvd_of_le hPD'
    rw [hcardS] at hdvd1
    rw [hcardP] at hdvd2
    obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
    interval_cases i
    · rw [hDi] at hdvd2
      norm_num at hdvd2
    · exfalso
      have heq : (Subgroup.zpowers t).subgroupOf _ = D' :=
        Subgroup.eq_of_le_of_card_ge hPD' (by rw [hcardP, hDi]; norm_num)
      obtain ⟨-, hmapdef, -, -⟩ := intermediate_normalizer_controlled_defect_correspondence basis
        ideal 2 (Subgroup.zpowers t) htp _ le_rfl (Subgroup.centralizer_le_normalizer _)
        (Subgroup.zpowers t) htp le_rfl (hPS.trans hSC) (normalizer_zpowers_le ht1 htt) cb
      have hBt : coefficientBlockDefect basis ideal 2 B (Subgroup.zpowers t) :=
        hmapdef c B (heq ▸ hD') hc
      have hconj := coefficientBlockDefect_conjugate basis ideal hBt hBdef
      have hle := subgroupSubconjugate_card_le (subgroupsConjugate_subconjugate
        (subgroupsConjugate_symm hconj))
      rw [Nat.card_zpowers, hord, hS.card_four] at hle
      norm_num at hle
    · have heq : D' = (S : Subgroup G).subgroupOf _ :=
        Subgroup.eq_of_le_of_card_ge hD'S (by rw [hcardS, hDi])
      rw [← heq]
      exact hD'
  obtain ⟨gb⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer ((S : Subgroup G) : Set G))
  have hclaim3 : ∀ β : wb.index, brauerNormalizerCharacterResidueHom ideal 2
          ((S : Subgroup G).subgroupOf
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
          S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb β =
            centralCharacterResidueHom cb ideal b →
        (∀ (n : G) (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (γ : wb.index),
          LabelTransport wb wb (fiberConj (le_centralizer_zpowers hS htS)
            (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr htS)) n hn) β γ →
          ∃ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2
              ((S : Subgroup G).subgroupOf
                (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
              S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ =
                centralCharacterResidueHom cb ideal c ∧
            brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
              (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
              (Subgroup.centralizer_le_normalizer _)
                cb c = centralCharacterResidueHom basis ideal B) ∧
        (∀ c : cb.index, brauerNormalizerCharacterResidueHom ideal 2 (Subgroup.zpowers t)
            (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
            (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
            (Subgroup.centralizer_le_normalizer _) cb c = centralCharacterResidueHom basis ideal B →
          ∃ (n : G) (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) (γ : wb.index),
            LabelTransport wb wb (fiberConj (le_centralizer_zpowers hS htS)
              (Subgroup.centralizer_le ((Subgroup.zpowers_le).mpr htS)) n hn) β γ ∧
            brauerNormalizerCharacterResidueHom ideal 2
                ((S : Subgroup G).subgroupOf
                  (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
                S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ =
              centralCharacterResidueHom cb ideal c) ∧
        (∀ γ₁ γ₂ : wb.index, brauerNormalizerCharacterResidueHom ideal 2
            ((S : Subgroup G).subgroupOf
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
            S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ₁ =
          brauerNormalizerCharacterResidueHom ideal 2
            ((S : Subgroup G).subgroupOf
              (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)))
            S.isPGroup'.comap_subtype _ le_rfl (Subgroup.centralizer_le_normalizer _) wb γ₂ →
          sameCoefficientBlock wb (localizedComplexIntegerRing ideal) γ₁ γ₂) := by
    intro β hβ
    obtain ⟨βG, hβG⟩ := labelTransport_exists wb gb (centralizerSubgroupOfEquiv hSC hWC) β
    have hβB : brauerNormalizerCharacterResidueHom ideal 2 S S.isPGroup'
        (Subgroup.centralizer ((S : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
          gb βG = centralCharacterResidueHom basis ideal B := by
      rw [← brauer_composite ideal 2 (Subgroup.zpowers t) S _ htp S.isPGroup' hPS le_rfl
        (Subgroup.centralizer_le_normalizer _) hSC hWC cb wb gb hβG hβ]
      exact hB
    refine ⟨fun n hn γ hγ => ?_, fun c hc => ?_, fun γ₁ γ₂ h =>
      hinj γ₁ γ₂ (hWdef γ₁) (hWdef γ₂) h⟩
    · obtain ⟨c, hcγ⟩ := himage γ
      refine ⟨c, hcγ, ?_⟩
      obtain ⟨γG, hγG⟩ := labelTransport_exists wb gb (centralizerSubgroupOfEquiv hSC hWC) γ
      have htrans := labelTransport_fiberConj hSC hWC n hn wb gb hγ hβG hγG
      rw [brauer_composite ideal 2 (Subgroup.zpowers t) S _ htp S.isPGroup' hPS le_rfl
        (Subgroup.centralizer_le_normalizer _) hSC hWC cb wb gb hγG hcγ, ← hβB]
      exact ((brauer_centralizer_eq_iff ideal 2 S gb βG γG).mpr
        ⟨n, hn, γG, htrans, sameCoefficientBlock_refl _ _ _⟩).symm
    · obtain ⟨γ, -, hγc⟩ := hsurj c (hclaim2 c hc)
      obtain ⟨γG, hγG⟩ := labelTransport_exists wb gb (centralizerSubgroupOfEquiv hSC hWC) γ
      have hγB : brauerNormalizerCharacterResidueHom ideal 2 S S.isPGroup'
          (Subgroup.centralizer ((S : Subgroup G) : Set G)) le_rfl
          (Subgroup.centralizer_le_normalizer _) gb γG =
            centralCharacterResidueHom basis ideal B := by
        rw [← brauer_composite ideal 2 (Subgroup.zpowers t) S _ htp S.isPGroup' hPS le_rfl
          (Subgroup.centralizer_le_normalizer _) hSC hWC cb wb gb hγG hγc]
        exact hc
      obtain ⟨n, hn, θ', hθ', hsame⟩ :=
        (brauer_centralizer_eq_iff ideal 2 S gb βG γG).mp (hβB.trans hγB.symm)
      obtain ⟨γ₀, hγ₀⟩ := labelTransport_exists wb wb (fiberConj hSC hWC n hn) β
      obtain ⟨γ₀G, hγ₀G⟩ := labelTransport_exists wb gb (centralizerSubgroupOfEquiv hSC hWC) γ₀
      have ht0 := labelTransport_fiberConj hSC hWC n hn wb gb hγ₀ hβG hγ₀G
      have heq : γ₀G = θ' := labelTransport_unique ht0 hθ'
      have hsame' : sameCoefficientBlock wb (localizedComplexIntegerRing ideal) γ₀ γ :=
        (sameCoefficientBlock_labelTransport_iff wb gb ideal _ hγ₀G hγG).mpr (heq ▸ hsame)
      exact ⟨n, hn, γ₀, hγ₀, (brauer_eq_of_same ideal 2 _ hSCp _ le_rfl
        (Subgroup.centralizer_le_normalizer _) wb hsame').trans hγc⟩
  obtain ⟨β₀, -, hβ₀⟩ := hsurj b hb
  refine ⟨⟨β₀, hβ₀, fun β' hβ' => hinj β₀ β' (hWdef β₀) (hWdef β') (hβ₀.trans hβ'.symm)⟩,
    hclaim2, hclaim3, index_centralizer_eq S hS, ?_⟩
  obtain ⟨hmaps, hsurj', -⟩ := hclaim3 β₀ hβ₀
  let cOf : wb.index → cb.index := fun γ => (himage γ).choose
  have hcOf : ∀ γ, brauerNormalizerCharacterResidueHom ideal 2 _ hSCp _ le_rfl
      (Subgroup.centralizer_le_normalizer _) wb γ = centralCharacterResidueHom cb ideal (cOf γ) :=
    fun γ => (himage γ).choose_spec
  have hF : (Finset.univ.filter fun c : cb.index => brauerNormalizerCharacterResidueHom ideal 2
        (Subgroup.zpowers t) (S.isPGroup'.to_le ((Subgroup.zpowers_le).mpr htS))
        (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)) le_rfl
        (Subgroup.centralizer_le_normalizer _)
          cb c = centralCharacterResidueHom basis ideal B).image
        (coefficientBlock cb (localizedComplexIntegerRing ideal)) =
      (Finset.univ.filter fun γ => ∃ (n : G)
        (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)),
          LabelTransport wb wb (fiberConj hSC hWC n hn) β₀ γ).image
        (fun γ => coefficientBlock cb (localizedComplexIntegerRing ideal) (cOf γ)) := by
    ext Y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨n, hn, γ, hγ, hγc⟩ := hsurj' c hc
      refine ⟨γ, ⟨n, hn, hγ⟩, ?_⟩
      rw [coefficientBlock_eq_iff, sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
        ← hcOf γ, hγc]
    · rintro ⟨γ, ⟨n, hn, hγ⟩, rfl⟩
      obtain ⟨c, hcγ, hcB⟩ := hmaps n hn γ hγ
      refine ⟨cOf γ, ?_, rfl⟩
      have hsame : sameCoefficientBlock cb (localizedComplexIntegerRing ideal) (cOf γ) c :=
        (sameCoefficientBlock_iff_centralCharacterResidueHom_eq cb ideal _ _).mpr
          ((hcOf γ).symm.trans hcγ)
      rw [brauer_eq_of_same ideal 2 (Subgroup.zpowers t) htp _ le_rfl
        (Subgroup.centralizer_le_normalizer _) cb hsame]
      exact hcB
  have hcardeq := card_image_eq_of_iff (Finset.univ.filter fun γ => ∃ (n : G)
    (hn : n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)),
      LabelTransport wb wb (fiberConj hSC hWC n hn) β₀ γ)
    (fun γ => coefficientBlock cb (localizedComplexIntegerRing ideal) (cOf γ))
    (coefficientBlock wb (localizedComplexIntegerRing ideal)) (fun x _ y _ => by
      rw [coefficientBlock_eq_iff, coefficientBlock_eq_iff,
        sameCoefficientBlock_iff_centralCharacterResidueHom_eq, ← hcOf x, ← hcOf y]
      exact ⟨hinj x y (hWdef x) (hWdef y), fun h => brauer_eq_of_same ideal 2 _ hSCp _ le_rfl
        (Subgroup.centralizer_le_normalizer _) wb h⟩)
  have hdvd := card_orbit_blocks_dvd hSC hWC wb ideal β₀
  rw [hF, hcardeq]
  rcases index_centralizer_eq S hS with h1 | h3
  · left
    have h1' : (Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 1 := h1
    rw [h1'] at hdvd
    exact Nat.dvd_one.mp hdvd
  · have h3' : (Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((S : Subgroup G) : Set G)) = 3 := h3
    rw [h3'] at hdvd
    exact (Nat.dvd_prime Nat.prime_three).mp hdvd

end CFSG.Semidihedral.Principal
