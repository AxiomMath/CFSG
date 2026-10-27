module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourWidthThreeRankFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCGElevenGeneratorPrimeThree

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative Pointwise

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem symplectic_six_core_two_subgroups_ten_generated {H : Type*} [Group H] [Finite H]
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))]
    (hcyc : IsCyclic (center (CFSG.pCore 2 H)))
    (hV : Nat.card (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) = 64)
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))}
    (hb : b.IsAlt) (hnd : b.Nondegenerate)
    {ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))}
    (hρ : ∀ (h : H) (x y : CFSG.pCore 2 H), (y : H) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))))
          (Additive.ofMul (x : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) =
        Additive.ofMul (y : CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))
    (hker : ρ.ker = CFSG.pCore 2 H) (hiso : ∀ h, ρ h ∈ bilinIsometryGroup b)
    (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ S : Finset P, S.card ≤ 10 ∧ closure (S : Set P) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (CFSG.pCore 2 H) := CFSG.pCore_isPGroup
  have hVcard : Nat.card (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) = 64 := hV
  set Y : Subgroup H := (center (CFSG.pCore 2 H)).map (CFSG.pCore 2 H).subtype with hYdef
  have hYD : Y ≤ CFSG.pCore 2 H := map_subtype_le _
  have hYc : IsCyclic Y :=
    isCyclic_of_surjective ((center (CFSG.pCore 2 H)).equivMapOfInjective _
      (Subgroup.subtype_injective _)).toMonoidHom (MulEquiv.surjective _)
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
  let ρ' : H →* bilinIsometryGroup b := ρ.codRestrict _ hiso
  have hρ' : ∀ (h : H) (d d' : CFSG.pCore 2 H), (d' : H) = h * d * h⁻¹ →
      Multiplicative.toAdd (π d') = ((ρ' h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)))) :
          Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H)) →ₗ[ZMod 2]
            Additive (CFSG.pCore 2 H ⧸ center (CFSG.pCore 2 H))) (Multiplicative.toAdd (π d)) :=
    fun h d d' hd => (hρ h d d' hd).symm
  have hρ'ker : ρ'.ker = CFSG.pCore 2 H := by rw [MonoidHom.ker_codRestrict, hker]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h10⟩ :=
    cyclic_layer_symplectic_six_extension_eleven_generated (Y := Y) (D := CFSG.pCore 2 H)
      (Q := CFSG.pCore 2 H) hYD le_rfl hQ2 hYc (by rw [relIndex_self]; norm_num) hVcard π hπ
      hπker hb hnd ρ' hρ' hρ'ker P hP _ rfl _ rfl _ _ rfl rfl
  exact (h10 rfl).2

theorem exists_conjugate_le_of_sylow [Finite G] {M : Subgroup G}
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤) {P : Subgroup G}
    (hP : IsPGroup 2 P) : ∃ g : G, CFSG.conjugate P g ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 M) := inferInstance
  obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl _ ⟨T₀, rfl⟩)
  rw [relIndex_top_right] at hSidx
  obtain ⟨P', hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hS2.toSylow hSidx) P'
  refine ⟨g, fun x hx => ?_⟩
  rw [mem_conjugate_iff_conj_mem] at hx
  have h1 := hP' hx
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe] at h1
  have h2 : (MulAut.conj g)⁻¹ • (g * x * g⁻¹) = x := by
    rw [inv_smul_eq_iff, MulAut.smul_def, MulAut.conj_apply]
  rw [h2] at h1
  exact map_subtype_le _ h1

theorem two_subgroup_generated_of_sylow [Finite G] {M : Subgroup G}
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤) {n : ℕ}
    (hgen : ∀ P : Subgroup M, IsPGroup 2 P →
      ∃ T : Finset P, T.card ≤ n ∧ closure (T : Set P) = ⊤)
    {P : Subgroup G} (hP : IsPGroup 2 P) :
    ∃ T : Finset G, T.card ≤ n ∧ closure (T : Set G) = P := by
  classical
  obtain ⟨g, hg⟩ := exists_conjugate_le_of_sylow hSyl hP
  let e : P ≃* (CFSG.conjugate P g).subgroupOf M :=
    ((MulAut.conj g⁻¹).subgroupMap P).trans (subgroupOfEquivOfLe hg).symm
  obtain ⟨T, hT, hTc⟩ := hgen _ (hP.of_equiv e)
  let f : (CFSG.conjugate P g).subgroupOf M →* G :=
    (MulAut.conj g).toMonoidHom.comp (M.subtype.comp (Subgroup.subtype _))
  have hf : f.range = P := by
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      have hy := y.2
      rw [mem_subgroupOf, mem_conjugate_iff_conj_mem] at hy
      exact hy
    · intro hx
      have h1 : g⁻¹ * x * g ∈ CFSG.conjugate P g := inv_mul_mul_mem_conjugate hx
      refine ⟨⟨⟨_, hg h1⟩, mem_subgroupOf.mpr h1⟩, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  refine ⟨T.image f, Finset.card_image_le.trans hT, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hTc, ← MonoidHom.range_eq_map, hf]

theorem local_rank_le_core_width
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {v : ℕ}
    (hQv : Nat.card Q = 2 ^ (2 * v + 2)) : GLATwoLocalRank 3 G ≤ v := by
  obtain ⟨-, -, z, hzZ, hzord, -⟩ :=
    gf2_center_four_symplectic_embedding_and_fusion hchar he hM hsym hB hBM hQ hnex hexp
  obtain ⟨⟨D, hD⟩, hBK⟩ := gf2_critical_center_and_exponent_four_reduction hchar he hM hsym hB hBM
    hQ hzZ hzord rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcase⟩ := hBK D hD _ rfl _ rfl
  have hnotB : ¬ (8 ≤ Nat.card ((center D).map D.subtype) ∧ ∃ x : Q, 8 ≤ orderOf x) := by
    rintro ⟨-, x, hx⟩
    have h1 : x ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp x x.2)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega
  obtain ⟨-, -, -, -, w, -, -, -, -, hQcard, -, -, -, -, hrw⟩ :=
    (hcase hnex).elim (fun h => h.1) fun h => absurd h.1 hnotB
  have hwv : w = v := by
    have := Nat.pow_right_injective (le_refl 2) (hQcard.symm.trans hQv)
    omega
  exact hwv ▸ hrw

theorem two_subgroups_ten_generated_of_card_core
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) (hQ256 : Nat.card Q = 256)
    (P : Subgroup G) (hP : IsPGroup 2 P) :
    ∃ T : Finset G, T.card ≤ 10 ∧ closure (T : Set G) = P := by
  obtain ⟨hZcyc, hZcard, z, -, -, -, -, -, ⟨hVel₀, -, b, -, -, hb, hnd, ρ, hρ, hker, hiso, -, -⟩,
    -, hSyl, -⟩ :=
    gf2_center_four_symplectic_embedding_and_fusion hchar he hM hsym hB hBM hQ hnex hexp
  have e : CFSG.pCore 2 M ≃* Q := by
    subst hQ
    exact (CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have hcyc₀ : IsCyclic (center (CFSG.pCore 2 M)) :=
    isCyclic_of_surjective (Subgroup.centerCongr e).symm.toMonoidHom (MulEquiv.surjective _)
  have hV : Nat.card (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)) = 64 := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (center (CFSG.pCore 2 M))
    rw [Nat.card_congr e.toEquiv, hQ256, Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      hZcard] at h1
    omega
  exact two_subgroup_generated_of_sylow hSyl
    (fun X hX => symplectic_six_core_two_subgroups_ten_generated hcyc₀ hV hb hnd hρ hker hiso X hX)
    hP

end SteinbergCH

open SteinbergCH

theorem gf2_center_four_width_at_least_four_at_rank_four
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) :
    IsCyclic (center Q) ∧ Nat.card (center Q) = 4 ∧
    ⁅Q, Q⁆ = (frattini Q).map Q.subtype ∧ Nat.card (⁅Q, Q⁆ : Subgroup G) = 2 ∧
    1024 ≤ Nat.card Q ∧
    ∃ (_ : CFSG.IsElementaryAbelian 2 (Q ⧸ center Q)),
      ∃ v : ℕ, 4 ≤ v ∧ Nat.card Q = 2 ^ (2 * v + 2) ∧
        Module.finrank (ZMod 2) (Additive (Q ⧸ center Q)) = 2 * v ∧
        (∀ v' : ℕ, Nat.card Q = 2 ^ (2 * v' + 2) → v' = v) ∧ r ≤ v := by
  have he3 : 3 ≤ CFSG.twoLocalOddRank G := le_trans (by norm_num) he
  obtain ⟨hZcyc, hZcard, hQ'Φ, hQ'card, -, hVel, v, ⟨hv3, hQv, hfin⟩, -⟩ :=
    gf2_center_four_width_at_least_three_at_rank_four hchar he hM hsym hB hBM hQ hnex hexp
  have hrv : r ≤ v := by
    rw [hr]
    exact local_rank_le_core_width hchar he3 hM hsym hB hBM hQ hnex hexp hQv
  have hv4 : 4 ≤ v := by
    by_contra hlt
    obtain rfl : v = 3 := by omega
    have hgen := two_subgroups_ten_generated_of_card_core hchar he3 hM hsym hB hBM hQ hnex hexp
      (hQv.trans (by norm_num))
    obtain ⟨-, -, h4⟩ := eleven_generator_two_subgroups_force_large_odd_local_prime_three hchar he
      fun P hP => (hgen P hP).imp fun T hT => ⟨by omega, hT.2⟩
    omega
  refine ⟨hZcyc, hZcard, hQ'Φ, hQ'card, ?_, hVel, v, hv4, hQv, hfin, fun v' hv' => ?_, hrv⟩
  · rw [hQv]
    calc 1024 = 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (2 * v + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have := Nat.pow_right_injective (le_refl 2) (hv'.symm.trans hQv)
    omega

end CFSG.LocalAnalysis.GorensteinLyons
