module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2FusedCenterFourImage
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCenterFourSevenGenerated

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement Pointwise

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem exists_odd_local_elementary_of_le_twoLocalOddRank [Finite G] {n : ℕ} (hn : 1 ≤ n)
    (he : n ≤ CFSG.twoLocalOddRank G) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ (B : Subgroup G) (r : ℕ), IsElemAbelian p B ∧
      Nat.card B = p ^ r ∧ n ≤ r ∧ ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧
        B ≤ normalizer (T : Set G) := by
  have hbridge : ∀ (q : ℕ) (K : Subgroup G), CFSG.pRank q K = CFSG.Open.pRank q K :=
    fun q K => (CFSG.SectionRank.pRank_eq_open_pRank_top q K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hbdd : BddAbove {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨K, -, q, hq, -, -, rfl⟩
    rw [hbridge]
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
    have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    omega
  have hne : {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : CFSG.twoLocalOddRank G = 0 := by
      rw [CFSG.twoLocalOddRank, h]
      exact csSup_empty
    omega
  obtain ⟨K, ⟨T, hT1, hT2, rfl⟩, p, hp, hp2, -, hrank⟩ := Nat.sSup_mem hne hbdd
  rw [hbridge] at hrank
  obtain ⟨E, hEK, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (T : Set G))
  refine ⟨p, hp, hp2, E, _, hE, hEcard, ?_, T, hT1, hT2, hEK⟩
  have h1 : CFSG.twoLocalOddRank G = CFSG.Open.pRank p (normalizer (T : Set G)) := hrank
  omega

theorem exists_two_subgroup_large_frattini
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 4 ≤ CFSG.twoLocalOddRank G) :
    ∃ Q₀ : Subgroup G, IsPGroup 2 Q₀ ∧ 2 ^ 8 ≤ Nat.card (Q₀ ⧸ frattini Q₀) := by
  obtain ⟨p, hp, hp2, B, r, hB, hBr, hr, T, hT1, hT2, hBT⟩ :=
    exists_odd_local_elementary_of_le_twoLocalOddRank (n := 4) (by norm_num) he
  obtain ⟨-, -, hlocal, -⟩ := large_local_rank_core_and_component_reduction hchar (by omega)
  obtain ⟨⟨d, hd, hdr⟩, -, -⟩ := hlocal p hp hp2 B r hB hBr (by omega) T hT1 hT2 hBT
  have := Fact.mk hp
  have hf := CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
  refine ⟨CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)), CFSG.pCore_isPGroup.map _, ?_⟩
  rw [hd]
  exact Nat.pow_le_pow_right (by norm_num) ((Nat.mul_le_mul hf hr).trans hdr)

theorem map_commutator_mulEquiv {A C : Type*} [Group A] [Group C] (e : A ≃* C) :
    (commutator A).map e.toMonoidHom = commutator C := by
  rw [commutator_def, commutator_def, map_commutator, map_top_of_surjective _ e.surjective]

theorem core_section_bound_of_card_sixty_four [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) (hQ64 : Nat.card Q = 64)
    (hZcyc : IsCyclic (center Q)) (hZcard : Nat.card (center Q) = 4) {z : G}
    (hzZ : z ∈ (center Q).map Q.subtype) (hzord : orderOf z = 2) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hΦ : (frattini Q).map Q.subtype = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hρ : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hker : ρ.ker = CFSG.pCore 2 M) :
    ∀ P : Subgroup M, IsPGroup 2 P → ∀ (N : Subgroup P) [N.Normal],
      CFSG.IsElementaryAbelian 2 (P ⧸ N) → Nat.card (P ⧸ N) ≤ 2 ^ 7 := by
  obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective, fun _ => rfl⟩
  have hzQ : z ∈ Q := map_subtype_le _ hzZ
  have hcard : Nat.card (CFSG.pCore 2 M) = 64 := by rw [Nat.card_congr e.toEquiv, hQ64]
  have hcyc₀ : IsCyclic (center (CFSG.pCore 2 M)) :=
    isCyclic_of_surjective (Subgroup.centerCongr e).symm.toMonoidHom (MulEquiv.surjective _)
  have hZ₀ : Nat.card (center (CFSG.pCore 2 M)) = 4 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hZcard]
  have hz₀Z : e.symm ⟨z, hzQ⟩ ∈ center (CFSG.pCore 2 M) := by
    obtain ⟨c, hc, hcz⟩ := hzZ
    have hc' : (⟨z, hzQ⟩ : Q) = c := Subtype.ext hcz.symm
    rw [hc', ← map_center_eq e.symm]
    exact mem_map_of_mem _ hc
  have hz₀ord : orderOf (e.symm ⟨z, hzQ⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hzord
  have hzpow : zpowers (⟨z, hzQ⟩ : Q) = (zpowers z).comap Q.subtype := by
    apply map_injective Q.subtype_injective
    rw [MonoidHom.map_zpowers, map_comap_eq, range_subtype, inf_eq_right.mpr]
    · rfl
    · exact zpowers_le.mpr hzQ
  have hcomm₀ : commutator (CFSG.pCore 2 M) = zpowers (e.symm ⟨z, hzQ⟩) := by
    have h1 : commutator Q = zpowers (⟨z, hzQ⟩ : Q) := by
      apply map_injective Q.subtype_injective
      rw [map_subtype_commutator, hQ', MonoidHom.map_zpowers]
      rfl
    rw [← map_commutator_mulEquiv e.symm, h1, MonoidHom.map_zpowers]
    rfl
  have hfrat₀ : frattini (CFSG.pCore 2 M) = zpowers (e.symm ⟨z, hzQ⟩) := by
    have h1 : frattini Q = zpowers (⟨z, hzQ⟩ : Q) := by
      apply map_injective Q.subtype_injective
      rw [hΦ, MonoidHom.map_zpowers]
      rfl
    rw [← map_frattini_mulEquiv e.symm, h1, MonoidHom.map_zpowers]
    rfl
  have hker' : ∀ h : M, (∀ q : CFSG.pCore 2 M, (q : M)⁻¹ * (h * q * h⁻¹) ∈
      (center (CFSG.pCore 2 M)).map (CFSG.pCore 2 M).subtype) ↔ h ∈ CFSG.pCore 2 M := by
    intro h
    have hmem : h ∈ CFSG.pCore 2 M ↔ ρ h = 1 := by rw [← MonoidHom.mem_ker, hker]
    rw [hmem]
    constructor
    · intro hq
      apply Units.ext
      apply LinearMap.ext
      intro w
      obtain ⟨w', rfl⟩ := Additive.ofMul.surjective w
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w'
      have hy : h * (q : M) * h⁻¹ ∈ CFSG.pCore 2 M := (CFSG.pCore_normal).conj_mem _ q.2 h
      rw [hρ h q ⟨_, hy⟩ rfl, Units.val_one, Module.End.one_apply]
      congr 1
      rw [eq_comm, QuotientGroup.eq]
      obtain ⟨c, hc, hceq⟩ := hq q
      have hc' : q⁻¹ * (⟨_, hy⟩ : CFSG.pCore 2 M) = c := Subtype.ext hceq.symm
      rw [hc']
      exact hc
    · intro h1 q
      have hy : h * (q : M) * h⁻¹ ∈ CFSG.pCore 2 M := (CFSG.pCore_normal).conj_mem _ q.2 h
      have h2 := hρ h q ⟨_, hy⟩ rfl
      rw [h1, Units.val_one, Module.End.one_apply] at h2
      exact ⟨_, QuotientGroup.eq.mp (Additive.ofMul.injective h2), rfl⟩
  exact (center_four_order_sixty_four_extension_seven_generated (H := M) (Q := CFSG.pCore 2 M)
    hcard hcyc₀ hZ₀ hz₀Z hz₀ord hcomm₀ hfrat₀ hker').2

theorem frattini_card_le_of_sylow_section_bound [Finite G] {M : Subgroup G}
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤)
    (hbound : ∀ P : Subgroup M, IsPGroup 2 P → ∀ (N : Subgroup P) [N.Normal],
      CFSG.IsElementaryAbelian 2 (P ⧸ N) → Nat.card (P ⧸ N) ≤ 2 ^ 7)
    {Q₀ : Subgroup G} (hQ₀ : IsPGroup 2 Q₀) : Nat.card (Q₀ ⧸ frattini Q₀) ≤ 2 ^ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 M) := inferInstance
  obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl _ ⟨T₀, rfl⟩)
  rw [relIndex_top_right] at hSidx
  obtain ⟨P', hP'⟩ := hQ₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hS2.toSylow hSidx) P'
  have hRM : CFSG.conjugate Q₀ g ≤ M := by
    intro x hx
    rw [mem_conjugate_iff_conj_mem] at hx
    have h1 := hP' hx
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
      IsPGroup.toSylow_coe] at h1
    have h2 : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
      rw [inv_smul_eq_iff, MulAut.smul_def, MulAut.conj_apply]
    rw [h2] at h1
    exact map_subtype_le _ h1
  let e : Q₀ ≃* (CFSG.conjugate Q₀ g).subgroupOf M :=
    ((MulAut.conj g⁻¹).subgroupMap Q₀).trans (subgroupOfEquivOfLe hRM).symm
  have hP2 : IsPGroup 2 ((CFSG.conjugate Q₀ g).subgroupOf M) := hQ₀.of_equiv e
  have hEl := (CFSG.GroupTheory.frattini_elementary_quotient hP2).2.2.2.1
  have hb := hbound _ hP2 (frattini _) hEl
  rwa [← Nat.card_congr (QuotientGroup.congr _ _ e (map_frattini_mulEquiv e)).toEquiv] at hb

end SteinbergCH

open SteinbergCH

theorem gf2_center_four_width_at_least_three_at_rank_four
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    IsCyclic (center Q) ∧ Nat.card (center Q) = 4 ∧
    ⁅Q, Q⁆ = (frattini Q).map Q.subtype ∧ Nat.card (⁅Q, Q⁆ : Subgroup G) = 2 ∧
    256 ≤ Nat.card Q ∧
    ∃ (_ : CFSG.IsElementaryAbelian 2 (Q ⧸ center Q)),
      ∃! v : ℕ, 3 ≤ v ∧ Nat.card Q = 2 ^ (2 * v + 2) ∧
        Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 * v := by
  have he3 : 3 ≤ CFSG.twoLocalOddRank G := le_trans (by norm_num) he
  obtain ⟨hcharM, hBodd, hZcyc, hZcard, hVel, ⟨w, hQcard, hVcard⟩, z, hzZ, hzord, -, hMC,
    -, -, hSyl, hQ'G, hΦ, -, -, -⟩ := fused_base_package hchar he3 hM hsym hB hBM hQ hnex hexp
  obtain ⟨hVel₀, hdim, b, -, -, -, -, ρ, hρ, hker, -, ⟨ι, hιinj, -⟩, -⟩ :=
    core_symplectic_transport hBM hcharM hBodd hQ hZcyc hVel hzZ hzord hQ'G
  obtain ⟨v, ⟨hv2, hQv, -⟩, -⟩ := width_package hchar he3 hQ hSyl ι hιinj hdim hQcard hVcard
  have hwv : w = v := by
    have := Nat.pow_right_injective (le_refl 2) (hQcard.symm.trans hQv)
    omega
  subst hwv
  have hv3 : 3 ≤ w := by
    by_contra hlt
    obtain rfl : w = 2 := by omega
    have hbound := core_section_bound_of_card_sixty_four hQ (by rw [hQcard]; norm_num) hZcyc
      hZcard hzZ hzord hQ'G hΦ hρ hker
    obtain ⟨Q₀, hQ₀, h8⟩ := exists_two_subgroup_large_frattini hchar he
    have h7 := frattini_card_le_of_sylow_section_bound hSyl hbound hQ₀
    have : (2 : ℕ) ^ 8 ≤ 2 ^ 7 := h8.trans h7
    norm_num at this
  have hfin : Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 * w := by
    have h1 := natCard_eq_two_pow_finrank (Additive (Q ⧸ center Q))
    rw [Nat.card_congr Additive.toMul, hVcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  refine ⟨hZcyc, hZcard, hQ'G.trans hΦ.symm, ?_, ?_, hVel, w, ⟨hv3, hQcard, hfin⟩,
    fun v' hv' => ?_⟩
  · rw [hQ'G, Nat.card_zpowers, hzord]
  · rw [hQcard]
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (2 * w + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have := Nat.pow_right_injective (le_refl 2) (hv'.2.1.symm.trans hQcard)
    omega

end CFSG.LocalAnalysis.GorensteinLyons
