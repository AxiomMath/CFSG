module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CriticalCenterExponentFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2ExtraspecialWidthThree
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCriticalSymplectic
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCGeneratorBound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators)
open scoped IsMulCommutative commutatorElement

namespace SteinbergBK

theorem isThompsonCritical_map_mulEquiv {A A' : Type*} [Group A] [Group A'] (e : A ≃* A')
    {C : Subgroup A} (hC : CFSG.SectionRank.Ccomm.IsThompsonCritical C) :
    CFSG.SectionRank.Ccomm.IsThompsonCritical (C.map e.toMonoidHom) := by
  obtain ⟨hchar, hfrat, hcomm, hcent⟩ := hC
  have hcen : (centralizer (C : Set A)).map e.toMonoidHom =
      centralizer ((C.map e.toMonoidHom : Subgroup A') : Set A') := by
    ext y
    rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · rintro h _ ⟨c, hc, rfl⟩
      apply e.symm.injective
      rw [map_mul, map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      exact h c hc
    · intro h c hc
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h (e c) ⟨c, hc, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [characteristic_iff_comap_eq] at hchar ⊢
    intro ψ
    ext x
    have h := SetLike.ext_iff.mp (hchar ((e.trans ψ).trans e.symm)) (e.symm x)
    rw [mem_comap] at h
    rw [mem_comap, mem_map_equiv, mem_map_equiv]
    simpa [MulEquiv.trans_apply] using h
  · let e' : C ≃* C.map e.toMonoidHom := C.equivMapOfInjective e.toMonoidHom e.injective
    have hf : (frattini C).map e'.toMonoidHom = frattini (C.map e.toMonoidHom) :=
      OrderIso.map_radical (MulEquiv.mapSubgroup e')
    have hcomp : (C.map e.toMonoidHom).subtype.comp e'.toMonoidHom =
        e.toMonoidHom.comp C.subtype :=
      MonoidHom.ext fun _ => rfl
    rw [← hf, map_map, hcomp, ← map_map, ← hcen, ← map_inf_eq _ _ _ e.injective]
    exact map_mono hfrat
  · have h := map_mono (f := e.toMonoidHom) hcomm
    rwa [map_commutator, map_top_of_surjective _ e.surjective, map_inf_eq _ _ _ e.injective,
      hcen] at h
  · rw [← hcen, ← map_inf_eq _ _ _ e.injective, ← hcent]

theorem isElementaryAbelian_transfer_mulEquiv {p : ℕ} {X X' : Type*} [Group X] [Group X']
    (e : X ≃* X') [h : CFSG.IsElementaryAbelian p X] : CFSG.IsElementaryAbelian p X' := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.toIsMulCommutative.is_comm.comm _ _
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_
    apply e.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p X) _

theorem card_generalLinearGroup_dvd_six {X : Type*} [Group X] [Finite X]
    [IsElementaryAbelian 2 X] {w : ℕ} (hV : Module.finrank (ZMod 2) (Additive X) = 2 * w)
    (hw : w ≤ 1) : Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive X)) ∣ 6 := by
  obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
  · rw [mul_zero] at hV
    let bas := Module.finBasisOfFinrankEq (ZMod 2) (Additive X) hV
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' bas).toEquiv, Matrix.card_GL_field]
    simp
  · rw [mul_one] at hV
    let bas := Module.finBasisOfFinrankEq (ZMod 2) (Additive X) hV
    rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' bas).toEquiv, Matrix.card_GL_field,
      Fin.prod_univ_two, ZMod.card]
    norm_num

theorem natCard_eq_two_pow_finrank {X : Type*} [Group X] [Finite X]
    [IsElementaryAbelian 2 X] : Nat.card X = 2 ^ Module.finrank (ZMod 2) (Additive X) := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  rw [Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at h1
  exact h1

theorem two_mul_le_finrank_of_faithful_three {X : Type*} [Group X] [Finite X]
    [IsElementaryAbelian 2 X] {H : Type*} [Group H] [Finite H] {B : Subgroup H}
    (hB : IsElemAbelian 3 B)
    {r : ℕ} (hBcard : Nat.card B = 3 ^ r)
    (ρ : B →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive X)) (hρ : Function.Injective ρ) :
    2 * r ≤ Module.finrank (ZMod 2) (Additive X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hBcomm, hBpow⟩ := hB
  let _ : CommGroup B := IsMulCommutative.instCommGroup
  exact CFSG.PreuniquenessRankFour.Helpers.faithful_binary_elementary_linear_action_dimension_bound
    (acting := B) (space := Additive X) 3 r (by norm_num) hBcard
    (fun x => Subtype.ext (by simpa using hBpow x x.2))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp ρ)
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).injective.comp hρ)

theorem exists_two_subgroup_eight_le_pGeneratorRank
    {G : Type*} [Group G] [Finite G]
    (hchar : CFSG.IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) :
    ∃ Q₀ : Subgroup G, IsPGroup 2 Q₀ ∧ 8 ≤ pGeneratorRank 2 Q₀ := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, -, hlocal, -⟩ := large_local_rank_core_and_component_reduction hchar (by omega)
  have hbridge : ∀ (q : ℕ) (K : Subgroup G), CFSG.pRank q K = CFSG.Open.pRank q K :=
    fun q K => (CFSG.SectionRank.pRank_eq_open_pRank_top q K).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have hbddE : BddAbove {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨K, -, q, hq, -, -, rfl⟩
    rw [hbridge]
    obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
    have h1 : CFSG.Open.pRank q K < q ^ CFSG.Open.pRank q K := Nat.lt_pow_self hq.one_lt
    have h2 : Nat.card E ≤ Nat.card G := card_le_card_group E
    omega
  have hneE : {r : ℕ | ∃ K : Subgroup G, CFSG.IsPLocal 2 K ∧
      ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ Nat.card G ∧ r = CFSG.pRank q K}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : CFSG.twoLocalOddRank G = 0 := by
      rw [CFSG.twoLocalOddRank, h]
      exact csSup_empty
    omega
  obtain ⟨K, ⟨T, hT1, hT2, rfl⟩, p, hp, hp2, -, hrank⟩ := Nat.sSup_mem hneE hbddE
  have he' : CFSG.twoLocalOddRank G = CFSG.Open.pRank p (normalizer (T : Set G)) := by
    rw [← hbridge]
    exact hrank
  have := Fact.mk hp
  obtain ⟨A, hAK, hA, hAcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (normalizer (T : Set G))
  obtain ⟨⟨d, hd, hfd⟩, -, -⟩ :=
    hlocal p hp hp2 A _ hA hAcard (by omega) T hT1 hT2 hAK
  have hf2 := CFSG.PreuniquenessRankFour.Helpers.binary_prime_order_at_least_two p hp2
  refine ⟨CFSG.inSubgroup (CFSG.pCore 2) (normalizer (T : Set G)), CFSG.pCore_isPGroup.map _, ?_⟩
  rw [pGeneratorRank, hd, Nat.log_pow (by norm_num)]
  have h8 := Nat.mul_le_mul hf2 (show 4 ≤ CFSG.Open.pRank p (normalizer (T : Set G)) by omega)
  omega

theorem critical_subgroup_transport_to_core {G : Type*} [Group G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {D : Subgroup Q} (hD : ThompsonCritical D) :
    (D.map Q.subtype).subgroupOf M ≤ CFSG.pCore 2 M ∧
      ThompsonCritical (((D.map Q.subtype).subgroupOf M).subgroupOf (CFSG.pCore 2 M)) ∧
      Nonempty (D ≃* (D.map Q.subtype).subgroupOf M) := by
  set P := CFSG.pCore 2 M with hPdef
  have hQP : Q = P.map M.subtype := hQ
  have hQM : Q ≤ M := by
    rw [hQP]
    exact map_subtype_le _
  obtain ⟨φQ, hφQ⟩ : ∃ e : P ≃* Q, ∀ p : P, ((e p : Q) : G) = ((p : M) : G) :=
    ⟨(P.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hQP.symm), fun _ => rfl⟩
  set D' := (D.map Q.subtype).subgroupOf M with hD'def
  have hDP : D' ≤ P := by
    intro m hm
    have h1 : (m : G) ∈ Q := map_subtype_le D (mem_subgroupOf.mp hm)
    rw [hQP] at h1
    exact (mem_map_iff_mem M.subtype_injective).mp h1
  have hsub : D'.subgroupOf P = D.comap φQ.toMonoidHom := by
    ext p
    rw [mem_subgroupOf, mem_subgroupOf, mem_comap]
    constructor
    · rintro ⟨q, hq, hqe⟩
      have h1 : φQ p = q := Subtype.ext (by rw [hφQ]; exact hqe.symm)
      rw [MulEquiv.coe_toMonoidHom, h1]
      exact hq
    · intro h
      exact ⟨φQ p, h, hφQ p⟩
  have hcrit : ThompsonCritical (D'.subgroupOf P) := by
    have h1 := map_equiv_eq_comap_symm' φQ.symm D
    rw [MulEquiv.symm_symm] at h1
    rw [hsub, ← h1]
    exact isThompsonCritical_map_mulEquiv φQ.symm hD
  have hDGM : D.map Q.subtype ≤ M := (map_subtype_le D).trans hQM
  exact ⟨hDP, hcrit, ⟨(D.equivMapOfInjective Q.subtype Q.subtype_injective).trans
    (subgroupOfEquivOfLe hDGM).symm⟩⟩

theorem critical_subgroups_generated {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ2 : IsPGroup 2 Q) {D : Subgroup Q} (hD : ThompsonCritical D)
    (hZ0 : (center D).map D.subtype ≠ ⊥) (hcyc : IsCyclic ((center D).map D.subtype))
    (hZchar : ((center D).map D.subtype).Characteristic)
    {φ : Q →* MulAut ((center D).map D.subtype)} (hφ : φ.ker = D) {D' : Type*} [Group D']
    (eD : D ≃* D') [IsElementaryAbelian 2 (D' ⧸ center D')] {w : ℕ}
    (hcard : Nat.card (D' ⧸ center D') = 2 ^ (2 * w)) (K : Subgroup Q) :
    ∃ S : Finset Q, S.card ≤ 2 * w + 3 ∧ closure (S : Set Q) = K := by
  have hDn : D.Normal := @Subgroup.normal_of_characteristic _ _ D hD.1
  have hZn : ((center D).map D.subtype).Normal :=
    @Subgroup.normal_of_characteristic _ _ _ hZchar
  have hZsub : ((center D).map D.subtype).subgroupOf D = center D :=
    comap_map_eq_self_of_injective D.subtype_injective _
  have hZmap : (((center D).map D.subtype).subgroupOf D).map eD = center D' := by
    rw [hZsub]
    exact map_center_eq eD
  obtain ⟨eQ⟩ : Nonempty (D ⧸ ((center D).map D.subtype).subgroupOf D ≃* D' ⧸ center D') :=
    ⟨QuotientGroup.congr _ _ eD hZmap⟩
  have : IsElementaryAbelian 2 (D ⧸ ((center D).map D.subtype).subgroupOf D) :=
    isElementaryAbelian_transfer_mulEquiv eQ.symm
  have hDZcard : Nat.card (D ⧸ ((center D).map D.subtype).subgroupOf D) = 2 ^ (2 * w) :=
    (Nat.card_congr eQ.toEquiv).trans hcard
  have hPD : ∃ A : Subgroup (MulAut ((center D).map D.subtype)), Nonempty (Q ⧸ D ≃* A) :=
    ⟨φ.range, ⟨(QuotientGroup.quotientMulEquivOfEq hφ.symm).trans
      (QuotientGroup.quotientKerEquivRange φ)⟩⟩
  exact cyclic_central_layer_automorphism_extension_generator_bound hQ2 (D := D)
    (Y := (center D).map D.subtype) le_rfl hZ0 hDZcard hPD K

theorem seven_le_of_core_generators_of_small_image
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M Q S : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) (hSM : S ≤ M) (hS : IsSylowOf 2 S ⊤)
    {Γ : Type*} [Group Γ] [Finite Γ] (hΓ : Nat.card Γ ∣ 6) (ρ : M →* Γ)
    (hρ : ρ.ker ≤ CFSG.pCore 2 M) {n : ℕ}
    (hgen : ∀ K : Subgroup Q, ∃ T : Finset Q, T.card ≤ n ∧ closure (T : Set Q) = K) :
    7 ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact CFSG.pCore_isPGroup.map _
  set P := CFSG.pCore 2 M with hPdef
  have hQP : Q = P.map M.subtype := hQ
  obtain ⟨φQ, -⟩ : ∃ e : P ≃* Q, ∀ p : P, ((e p : Q) : G) = ((p : M) : G) :=
    ⟨(P.equivMapOfInjective M.subtype M.subtype_injective).trans
      (MulEquiv.subgroupCongr hQP.symm), fun _ => rfl⟩
  obtain ⟨Q₀, hQ₀2, hQ₀d⟩ := exists_two_subgroup_eight_le_pGeneratorRank hchar he
  obtain ⟨g, hg⟩ := exists_conj_le_of_isSylowOf_top hS hQ₀2
  have hX₀M : Q₀.map (MulAut.conj g).toMonoidHom ≤ M := hg.trans hSM
  obtain ⟨X, hX⟩ : ∃ X : Subgroup M, X = (Q₀.map (MulAut.conj g).toMonoidHom).subgroupOf M :=
    ⟨_, rfl⟩
  have eX : X ≃* Q₀ := (MulEquiv.subgroupCongr hX).trans ((subgroupOfEquivOfLe hX₀M).trans
    (Q₀.equivMapOfInjective _ (MulAut.conj g).injective).symm)
  have hX2 : IsPGroup 2 X := hQ₀2.of_equiv eX.symm
  let θ := ρ.comp X.subtype
  have hθ2 : IsPGroup 2 θ.range := hX2.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  obtain ⟨j, hj⟩ := hθ2.exists_card_eq
  have hj1 : j ≤ 1 := by
    by_contra hj1
    push Not at hj1
    have h1 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 hj1
    rw [← hj] at h1
    have h2 := h1.trans ((card_subgroup_dvd_card θ.range).trans hΓ)
    norm_num at h2
  have hquot : pGeneratorRank 2 (X ⧸ θ.ker) ≤ 1 := by
    have h1 := SymplecticSixLayer.pGeneratorRank_le_log_card 2 (X := X ⧸ θ.ker)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv, hj,
      Nat.log_pow (by norm_num)] at h1
    omega
  have hkerP : ∀ k : θ.ker, (X.subtype.comp θ.ker.subtype) k ∈ P := fun k =>
    hρ (show X.subtype (k : X) ∈ ρ.ker from k.2)
  let κ : θ.ker →* Q :=
    φQ.toMonoidHom.comp ((X.subtype.comp θ.ker.subtype).codRestrict P hkerP)
  have hκ : Function.Injective κ := by
    intro a b hab
    have h1 := congrArg Subtype.val (φQ.injective hab)
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨S₀, hS₀, hS₀cl⟩ := hgen κ.range
  obtain ⟨T, hT, hTcard⟩ := exists_finset_closure_eq_top_of_closure_eq hS₀cl
  have hK' := pGeneratorRank_le_generators Nat.prime_two (hQ2.to_subgroup κ.range) T hT
  have hker : pGeneratorRank 2 θ.ker ≤ n := by
    rw [SymplecticSixLayer.pGeneratorRank_congr (MonoidHom.ofInjective hκ)]
    omega
  have hsum := SymplecticSixLayer.pGeneratorRank_le_quotient_add Nat.prime_two hX2 θ.ker
  rw [SymplecticSixLayer.pGeneratorRank_congr eX] at hsum
  omega

end SteinbergBK

open SteinbergBK

theorem gf2_critical_quotient_and_width_at_rank_four
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) :
    (∃ D : Subgroup Q, ThompsonCritical D) ∧
    ∀ D : Subgroup Q, ThompsonCritical D → ∀ D' : Subgroup M,
      D' = (D.map Q.subtype).subgroupOf M →
      center D' ≠ ⊥ ∧ IsCyclic (center D') ∧
      ∃ z : D', z ∈ center D' ∧ orderOf z = 2 ∧ (∀ z' ∈ center D', orderOf z' = 2 → z' = z) ∧
      ∃ _ : IsElementaryAbelian 2 (D' ⧸ center D'),
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (D' ⧸ center D')),
        (∀ x y : D', ⁅x, y⁆ = z ^ (b (Additive.ofMul (x : D' ⧸ center D'))
          (Additive.ofMul (y : D' ⧸ center D'))).val) ∧
        (∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (D' ⧸ center D')),
          (∀ x y : D', ⁅x, y⁆ = z ^ (b' (Additive.ofMul (x : D' ⧸ center D'))
            (Additive.ofMul (y : D' ⧸ center D'))).val) → b' = b) ∧
        b.IsAlt ∧ b.Nondegenerate ∧
        ∃ w : ℕ, 2 ≤ w ∧ Module.finrank (ZMod 2) (Additive (D' ⧸ center D')) = 2 * w ∧
          (∀ w' : ℕ, Module.finrank (ZMod 2) (Additive (D' ⧸ center D')) = 2 * w' → w' = w) ∧
          (∃ ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D' ⧸ center D')),
            (∀ (m : M) (x y : D'), (y : M) = m * x * m⁻¹ →
              ((ρ m : LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D' ⧸ center D'))) :
                Module.End (ZMod 2) (Additive (D' ⧸ center D')))
                  (Additive.ofMul (x : D' ⧸ center D')) = Additive.ofMul (y : D' ⧸ center D')) ∧
            ρ.ker = CFSG.pCore 2 M ∧ (∀ m, ρ m ∈ bilinIsometryGroup b) ∧
            (∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
              ∀ m : M, ((ι (m : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D' ⧸ center D'))) = ρ m) ∧
            Function.Injective (ρ.comp (inclusion hBM))) ∧
          Nat.card B = 3 ^ r ∧ r ≤ w ∧
          (∀ K : Subgroup Q, ∃ S : Finset Q, S.card ≤ 2 * w + 3 ∧ closure (S : Set Q) = K) ∧
          ¬ IsCyclic D := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z₁, hz₁Q, hz₁, -, -, -, -, hSyl⟩, -, hQne, hBcard, -, -, -, -, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
  have hcc := gf2_critical_center_and_exponent_four_reduction hchar (by omega) hM hsym hB hBM hQ
    hz₁Q hz₁ hr
  refine ⟨hcc.1, fun D hD D' hD' => ?_⟩
  subst hD'
  obtain ⟨⟨E, R, -, -, -, -, -, -, -, -, ⟨φ, -, hφker⟩, -⟩, hZ0, hcyc, hZchar, -⟩ :=
    hcc.2 D hD _ rfl _ rfl
  have hcharM : CFSG.IsCharacteristicP 2 M := hchar M hM.1
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact CFSG.pCore_isPGroup.map _
  obtain ⟨hDP, hcrit, ⟨eD⟩⟩ := critical_subgroup_transport_to_core hQ hD
  have hP0 : CFSG.pCore 2 M ≠ ⊥ := by
    intro h
    apply hQne
    rw [hQ]
    change (CFSG.pCore 2 M).map M.subtype = ⊥
    rw [h, Subgroup.map_bot]
  have hYcyc : IsCyclic (center ((D.map Q.subtype).subgroupOf M)) := by
    have hZD : IsCyclic (center D) := by
      let e : (center D).map D.subtype ≃* center D :=
        ((center D).equivMapOfInjective D.subtype D.subtype_injective).symm
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    exact isCyclic_of_surjective (Subgroup.centerCongr eD).toMonoidHom
      (Subgroup.centerCongr eD).surjective
  have hcycDD' : IsCyclic D → IsCyclic ((D.map Q.subtype).subgroupOf M) := fun _ =>
    isCyclic_of_surjective eD.toMonoidHom eD.surjective
  have hCC := critical_cyclic_center_faithful_symplectic_action hcharM hP0 hDP hcrit
  obtain ⟨hY0, z, hzc, hz2, huniq, hrest⟩ := hCC
  obtain ⟨hEA, hrest⟩ := hrest
  obtain ⟨b, hbform, hbuniq, hbalt, hbnd, hwex, hρex⟩ := hrest
  obtain ⟨w, hw, hwuniq, hw0, -⟩ := hwex
  obtain ⟨ρ, hρ, hρker, hρSp, hιex, hodd⟩ := hρex
  have hgen := critical_subgroups_generated hQ2 hD hZ0 hcyc hZchar hφker eD
    (by rw [natCard_eq_two_pow_finrank, hw])
  have hw2 : 2 ≤ w := by
    by_contra hw2
    push Not at hw2
    have hGL := card_generalLinearGroup_dvd_six hw (by omega)
    have hGLfin := Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero (by norm_num) hGL)
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
    have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
    have h7 := seven_le_of_core_generators_of_small_image hchar he hQ (map_subtype_le _)
      (hSyl _ hSM).1 hGL ρ hρker.le hgen
    omega
  have hBinj : Function.Injective (ρ.comp (inclusion hBM)) := by
    have hBodd : Odd (Nat.card (B.subgroupOf M)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv, hBcard]
      exact Odd.pow ⟨1, rfl⟩
    have h1 := hodd _ hBodd
    intro b₁ b₂ h
    have h2 := @h1 ⟨inclusion hBM b₁, mem_subgroupOf.mpr b₁.2⟩
      ⟨inclusion hBM b₂, mem_subgroupOf.mpr b₂.2⟩ h
    exact inclusion_injective hBM (congrArg Subtype.val h2)
  have hrw : r ≤ w := by
    have h := two_mul_le_finrank_of_faithful_three hB.1 hBcard _ hBinj
    rw [hw] at h
    omega
  have hncyc : ¬ IsCyclic D := by
    intro hc
    have h2 := hw0.mpr (hcycDD' hc)
    omega
  exact ⟨hY0, hYcyc, z, hzc, hz2, huniq, hEA, b, hbform, hbuniq, hbalt, hbnd, w, hw2, hw,
    hwuniq, ⟨ρ, hρ, hρker, hρSp, hιex, hBinj⟩, hBcard, hrw, hgen, hncyc⟩

end CFSG.LocalAnalysis.GorensteinLyons
