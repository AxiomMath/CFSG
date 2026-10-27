module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2ExtraspecialWidthThree
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGElevenGeneratorPrimeThree

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative

namespace SteinbergBK

theorem extraspecial_width_three_two_subgroups_ten_generated {H : Type*} [Group H] [Finite H]
    (hH : CFSG.IsCharacteristicP 2 H) (hQ : IsExtraspecialPGroup 2 (CFSG.pCore 2 H))
    (hQ128 : Nat.card (CFSG.pCore 2 H) = 128) (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ S : Finset P, S.card ≤ 10 ∧ closure (S : Set P) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := SteinbergCG.exists_center_eq_zpowers hQ.2.2.2
  have HQ := commPairHyp_of_extraspecial hQ hz
  have := HQ.isElementaryAbelian_quotient
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hVcard : Nat.card (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) = 64 := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (center (CFSG.pCore 2 H))
    rw [hQ128, hQ.2.2.2] at h1
    change Nat.card (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 64
    omega
  set Y : Subgroup H := (center (CFSG.pCore 2 H)).map (CFSG.pCore 2 H).subtype with hYdef
  have hYD : Y ≤ CFSG.pCore 2 H := map_subtype_le _
  have hYc : IsCyclic Y := by
    have hY2 : Nat.card Y = 2 := by
      rw [hYdef, card_map_of_injective (Subgroup.subtype_injective _), hQ.2.2.2]
    exact isCyclic_of_prime_card hY2
  let π : CFSG.pCore 2 H →* Multiplicative (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (x : CFSG.pCore 2 H ⧸
        center (CFSG.pCore 2 H)))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : Function.Surjective π := fun v => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Multiplicative.toAdd v).toMul
    refine ⟨x, ?_⟩
    change Multiplicative.ofAdd (Additive.ofMul (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) = v
    rw [hx]
    rfl
  have hπker : π.ker = Y.subgroupOf (CFSG.pCore 2 H) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change Multiplicative.ofAdd (Additive.ofMul
      (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) = Multiplicative.ofAdd (Additive.ofMul 1) ↔ _
    refine ((Multiplicative.ofAdd.injective.comp Additive.ofMul.injective).eq_iff).trans ?_
    refine (QuotientGroup.eq_one_iff _).trans ?_
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨c, hc, hceq⟩
      obtain rfl : c = x := Subtype.ext hceq
      exact hc
  have hcomm : ∀ (σ : MulAut (CFSG.pCore 2 H)) (u v : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)),
      commVal z (centerQuotientHom _ σ u) (centerQuotientHom _ σ v) = commVal z u v := by
    intro σ u v
    have h1 := HQ.sqVal_mul hz (centerQuotientHom _ σ u) (centerQuotientHom _ σ v)
    have h2 := HQ.sqVal_mul hz u v
    rw [← map_mul, CFSG.RankThree.GroupTheory.SteinbergBY.sqVal_centerQuotientHom HQ hz,
      CFSG.RankThree.GroupTheory.SteinbergBY.sqVal_centerQuotientHom HQ hz,
      CFSG.RankThree.GroupTheory.SteinbergBY.sqVal_centerQuotientHom HQ hz, h2] at h1
    exact (add_left_cancel h1).symm
  let ρ₀ : H →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).symm.toMonoidHom.comp
      (CFSG.RankThree.GroupTheory.SteinbergBY.autLinHom.comp MulAut.conjNormal)
  have hρ₀ : ∀ (h : H) (w : Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))),
      (ρ₀ h).val w =
      Additive.ofMul (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h) w.toMul) :=
    fun _ _ => rfl
  have hρmem : ∀ h : H, ρ₀ h ∈ bilinIsometryGroup HQ.commForm := by
    intro h x y
    rw [hρ₀, hρ₀, HQ.commForm_apply, HQ.commForm_apply, toMul_ofMul, toMul_ofMul, hcomm]
  let ρ : H →* bilinIsometryGroup HQ.commForm := ρ₀.codRestrict _ hρmem
  have hρ : ∀ (h : H) (d d' : CFSG.pCore 2 H), (d' : H) = h * d * h⁻¹ →
      Multiplicative.toAdd (π d') = (ρ h).val.val (Multiplicative.toAdd (π d)) := by
    intro h d d' hd
    change Additive.ofMul (d' : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) =
      Additive.ofMul (centerQuotientHom (CFSG.pCore 2 H) (MulAut.conjNormal h)
        (d : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))
    rw [CFSG.ComponentClassification.CentralCover.centerQuotientHom_apply_mk]
    congr 2
    exact Subtype.ext (by rw [hd, MulAut.conjNormal_apply])
  have hρ₀core : ∀ h : H, ρ₀ h = (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
      (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))).symm
        (SteinbergCG.coreOrth HQ hz h).val := fun _ => rfl
  have hρker : ρ.ker = CFSG.pCore 2 H := by
    refine Eq.trans ?_ (SteinbergCG.ker_coreOrth hH hQ HQ hz)
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : ρ₀ h = 1 := congrArg Subtype.val h1
      rw [hρ₀core, MulEquiv.symm_apply_eq, map_one] at h2
      exact Subtype.ext h2
    · intro h1
      apply Subtype.ext
      change ρ₀ h = 1
      rw [hρ₀core, h1, OneMemClass.coe_one, map_one]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h10⟩ :=
    cyclic_layer_symplectic_six_extension_eleven_generated (Y := Y) (D := CFSG.pCore 2 H)
      (Q := CFSG.pCore 2 H) hYD le_rfl hQ2 hYc (by rw [relIndex_self]; norm_num) hVcard π hπ
      hπker HQ.commForm_isAlt HQ.commForm_nondegenerate ρ hρ hρker P hP _ rfl _ rfl _ _ rfl rfl
  exact (h10 rfl).2

theorem two_subgroups_generated_of_sylow_le {G : Type*} [Group G] [Finite G] {S M : Subgroup G}
    (hSM : S ≤ M) (hS : IsSylowOf 2 S ⊤) {n : ℕ}
    (hgen : ∀ P : Subgroup M, IsPGroup 2 P → ∃ T : Finset P, T.card ≤ n ∧ closure (T : Set P) = ⊤)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ T : Finset G, T.card ≤ n ∧ closure (T : Set G) = P := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_le_of_isSylowOf_top hS hP
  set X₀ := P.map (MulAut.conj g).toMonoidHom with hX₀
  have hX₀M : X₀ ≤ M := hg.trans hSM
  set X := X₀.subgroupOf M with hX
  have hX2 : IsPGroup 2 X :=
    (hP.map (MulAut.conj g).toMonoidHom).of_equiv (subgroupOfEquivOfLe hX₀M).symm
  obtain ⟨T, hT, hTc⟩ := hgen X hX2
  let f : X →* G := (MulAut.conj g⁻¹).toMonoidHom.comp (M.subtype.comp X.subtype)
  have hfrange : f.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, hX,
      map_subgroupOf_eq_of_le hX₀M, hX₀, Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨T.image f, Finset.card_image_le.trans hT, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hTc, ← MonoidHom.range_eq_map, hfrange]

end SteinbergBK

open SteinbergBK

theorem gf2_extraspecial_width_at_least_four_at_rank_four
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hQe : IsExtraspecialPGroup 2 Q) {r : ℕ} (hr : r = GLATwoLocalRank 3 G) :
    ∃ w : ℕ, 4 ≤ w ∧ Nat.card Q = 2 ^ (1 + 2 * w) ∧
      (∀ w' : ℕ, Nat.card Q = 2 ^ (1 + 2 * w') → w' = w) ∧ Nat.card B = 3 ^ r ∧ r ≤ w ∧
      512 ≤ Nat.card Q := by
  have := Fact.mk Nat.prime_two
  obtain ⟨w, hw3, hQcard, huniq, hBcard, hrw⟩ :=
    gf2_extraspecial_width_at_least_three hchar (by omega) hM hsym hB hBM hQ hQe hr
  have hw4 : 4 ≤ w := by
    by_contra hw4
    have hw : w = 3 := by omega
    subst hw
    have hcharM : CFSG.IsCharacteristicP 2 M := hchar M hM.1
    have eQ : CFSG.pCore 2 M ≃* Q := by
      rw [hQ]
      exact (CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
    have hQ₀e : IsExtraspecialPGroup 2 (CFSG.pCore 2 M) :=
      isExtraspecialPGroup_congr_mulEquiv eQ.symm hQe
    have hQ₀card : Nat.card (CFSG.pCore 2 M) = 128 :=
      (Nat.card_congr eQ.toEquiv).trans (hQcard.trans (by norm_num))
    obtain ⟨⟨z, -, -, -, -, -, -, hSyl⟩, -⟩ :=
      gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
    have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
    have hgen : ∀ P : Subgroup G, IsPGroup 2 P →
        ∃ T : Finset G, T.card ≤ 11 ∧ closure (T : Set G) = P := by
      intro P hP
      obtain ⟨T, hT, hTc⟩ := two_subgroups_generated_of_sylow_le (map_subtype_le _) (hSyl _ hSM).1
        (fun X hX => extraspecial_width_three_two_subgroups_ten_generated hcharM hQ₀e hQ₀card X hX)
        P hP
      exact ⟨T, by omega, hTc⟩
    obtain ⟨-, -, h4⟩ :=
      eleven_generator_two_subgroups_force_large_odd_local_prime_three hchar he hgen
    rw [← hr] at h4
    omega
  refine ⟨w, hw4, hQcard, huniq, hBcard, hrw, ?_⟩
  rw [hQcard]
  calc 512 = 2 ^ (1 + 2 * 4) := by norm_num
    _ ≤ 2 ^ (1 + 2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GorensteinLyons
