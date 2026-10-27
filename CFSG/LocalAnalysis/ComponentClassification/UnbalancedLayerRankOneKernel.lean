module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneTwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalClassical
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {K : Type*} [Group K] [Finite K]

theorem rank_one_pComponent_facts {a : K} (ha : orderOf a = 2) (haZ : a ∈ center K)
    {X : Subgroup K} (hX : IsPComponent 2 X) (haX : a ∈ X) (hrank : pRank 2 X ≤ 1) :
    (∀ T : Sylow 2 X, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      (∀ x ∈ X, orderOf x = 2 → x = a) ∧ ∀ T : Sylow 2 X, (⟨a, haX⟩ : X) ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CatalogueBHeldSmallCore.pComponent_perfect 2 X hX
  have hA := CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 X hX
  have heven : Even (Nat.card X) := by
    have : IsSimpleGroup ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) := hA.2.1
    have h1 := (SimpleEvenOrder.nonabelian_simple_even hA.2.2).1
    exact even_iff_two_dvd.mpr ((even_iff_two_dvd.mp h1).trans
      ((card_quotient_dvd_card _).trans (card_quotient_dvd_card _)))
  have hquat : ∀ T : Sylow 2 X, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2))) :=
    fun T => LocalAnalysis.ComponentInitial.perfect_rank_one_Sylow_quaternion heven hrank T
  set a' : X := ⟨a, haX⟩ with ha'def
  have ha'2 : orderOf a' = 2 := by rw [ha'def, Subgroup.orderOf_mk, ha]
  have ha'Z : ∀ y : X, Commute y a' := fun y => Subtype.ext (mem_center_iff.mp haZ y)
  have hAn : (zpowers a').Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [((ha'Z g).zpow_right k).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers a') k⟩
  have hA2 : IsPGroup 2 (zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha'2, pow_one])
  have haT : ∀ T : Sylow 2 X, a' ∈ T := fun T => hA2.le_sylow_of_normal T (mem_zpowers a')
  refine ⟨hquat, fun x hx hx2 => ?_, haT⟩
  set x' : X := ⟨x, hx⟩ with hx'def
  have hx'2 : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk, hx2]
  have hV : IsPGroup 2 (zpowers x' ⊔ zpowers a' : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2, pow_one])) hA2
  obtain ⟨T, hVT⟩ := hV.exists_le_sylow
  obtain ⟨r, hr, ⟨eT⟩⟩ := hquat T
  have hm : 0 < 2 ^ (r - 2) := Nat.two_pow_pos _
  have hxT : x' ∈ T := hVT (mem_sup_left (mem_zpowers x'))
  have h1 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm
    (eT ⟨x', hxT⟩)).1 (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx'2])
  have h2 := (CFSG.Semidihedral.QuaternionAutomorphismLifting.unique_involution _ hm
    (eT ⟨a', haT T⟩)).1 (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ha'2])
  have h3 : (⟨x', hxT⟩ : T) = ⟨a', haT T⟩ := eT.injective (h1.trans h2.symm)
  exact congrArg Subtype.val (congrArg Subtype.val h3)

theorem le_pRank_of_le_map_odd {O Q : Subgroup K} [O.Normal] (hO : Odd (Nat.card O))
    {E : Subgroup (K ⧸ O)} (hEQ : E ≤ Q.map (QuotientGroup.mk' O)) [IsElementaryAbelian 2 E]
    {k : ℕ} (hE : Nat.card E = 2 ^ k) : k ≤ pRank 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : Q →* K ⧸ O := (QuotientGroup.mk' O).comp Q.subtype
  have hker : O.subgroupOf Q = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact (QuotientGroup.eq_one_iff _).symm
  have hrange : φ.range = Q.map (QuotientGroup.mk' O) := by
    rw [MonoidHom.range_comp, range_subtype]
  let e : Q ⧸ O.subgroupOf Q ≃* Q.map (QuotientGroup.mk' O) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))
  have : (O.subgroupOf Q).Normal := Normal.subgroupOf inferInstance Q
  have hodd : ¬ 2 ∣ Nat.card (O.subgroupOf Q) := by
    have hdvd : Nat.card (O.subgroupOf Q) ∣ Nat.card O := by
      rw [← card_map_of_injective Q.subtype_injective, subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    exact fun h2 => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h2.trans hdvd))
  have h1 : pRank 2 Q = pRank 2 (Q.map (QuotientGroup.mk' O)) := by
    rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top,
      ← SectionRank.pRank_quotient_eq (O.subgroupOf Q) hodd]
    exact SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e
  rw [h1, SectionRank.pRank_eq_open_pRank_top]
  have hcomm : ∀ x y : E, x * y = y * x := fun x y => mul_comm' x y
  have hpow : ∀ x : E, x ^ 2 = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow, elemPow_eq_one_of_isElementaryAbelian _ x.2,
      Subgroup.coe_one])
  exact SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hE (inclusion hEQ)
    (inclusion_injective hEQ) le_top

theorem le_coreActionKernel {J X : Subgroup K} (hJ : IsPComponent 2 J) (hX : IsPComponent 2 X)
    (hXJ : X ≠ J) : X ≤ coreActionKernel J := by
  intro g hg
  obtain ⟨-, hrest⟩ :=
    CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two J X hJ hX
  obtain ⟨hXN, -, hcore, -⟩ := hrest (Ne.symm hXJ)
  refine ⟨hXN hg, fun j hj => ?_⟩
  have hmem : j⁻¹ * g⁻¹ * j * g ∈ ⁅J, X⁆ := by
    rw [show j⁻¹ * g⁻¹ * j * g = ⁅j⁻¹, g⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
    exact commutator_mem_commutator (inv_mem hj) (inv_mem hg)
  exact (mem_inf.mp (hcore hmem)).1

omit [Finite K] in
theorem mem_normalizer_iff_conjugate_eq {J : Subgroup K} {g : K} :
    g ∈ normalizer (J : Set K) ↔ conjugate J g = J := by
  constructor
  · exact conjugate_eq_of_mem_normalizer
  · intro h
    rw [mem_normalizer_iff]
    intro x
    rw [← mem_conjugate_iff, h]

theorem conjugate_eq_of_ne_of_ne {a : K} (ha : orderOf a = 2) (haZ : a ∈ center K)
    {J : Subgroup K} (hJ : IsPComponent 2 J) (haJ : a ∈ J) (hJrank : pRank 2 J ≤ 1)
    (hQrank : pRank 2 (coreActionKernel J) ≤ 2) {h₁ h₂ : K} (h₁J : conjugate J h₁ ≠ J)
    (h₂J : conjugate J h₂ ≠ J) : conjugate J h₁ = conjugate J h₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h12
  have hconj : ∀ h : K, IsPComponent 2 (conjugate J h) ∧ a ∈ conjugate J h ∧
      pRank 2 (conjugate J h) ≤ 1 := by
    intro h
    refine ⟨isPComponent_conjugate hJ h, ?_, ?_⟩
    · have hmem := conj_mem_conjugate haJ h
      rwa [mul_assoc, ← mem_center_iff.mp haZ h, inv_mul_cancel_left] at hmem
    · unfold conjugate
      rw [← pRank_eq_of_mulEquiv (by norm_num)
        (J.equivMapOfInjective _ (MulAut.conj h⁻¹).injective)]
      exact hJrank
  obtain ⟨hX₁, haX₁, hr₁⟩ := hconj h₁
  obtain ⟨hX₂, haX₂, hr₂⟩ := hconj h₂
  have hQ₁ := le_coreActionKernel hJ hX₁ h₁J
  have hQ₂ := le_coreActionKernel hJ hX₂ h₂J
  have hOodd : Odd (Nat.card (pPrimeCore 2 K)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have himage : ∀ X : Subgroup K, IsPComponent 2 X → a ∈ X → pRank 2 X ≤ 1 →
      ∃ U : Subgroup (K ⧸ pPrimeCore 2 K), U ≤ X.map (QuotientGroup.mk' (pPrimeCore 2 K)) ∧
        QuotientGroup.mk' (pPrimeCore 2 K) a ∈ U ∧
        ∃ r : ℕ, 3 ≤ r ∧ Nonempty (U ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro X hX haX hrX
    obtain ⟨hquat, -, haT⟩ := rank_one_pComponent_facts ha haZ hX haX hrX
    let T : Sylow 2 X := default
    obtain ⟨r, hr, ⟨eT⟩⟩ := hquat T
    let ψ : (T : Subgroup X) →* K ⧸ pPrimeCore 2 K :=
      ((QuotientGroup.mk' (pPrimeCore 2 K)).comp X.subtype).comp (T : Subgroup X).subtype
    have hψ : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro t ht
      have h1 : ((t : X) : K) ∈ pPrimeCore 2 K :=
        (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp ht)
      have hbot := eq_bot_of_le_two_group_of_le_odd (T.isPGroup'.map X.subtype) hOodd
        (X := (T : Subgroup X).map X.subtype ⊓ pPrimeCore 2 K) inf_le_left inf_le_right
      have hmem : ((t : X) : K) ∈ (T : Subgroup X).map X.subtype ⊓ pPrimeCore 2 K :=
        mem_inf.mpr ⟨⟨t, t.2, rfl⟩, h1⟩
      rw [hbot, mem_bot] at hmem
      exact (mem_bot).mpr (Subtype.ext (Subtype.ext hmem))
    refine ⟨ψ.range, ?_, ⟨⟨⟨a, haX⟩, haT T⟩, rfl⟩, r, hr,
      ⟨(MonoidHom.ofInjective hψ).symm.trans eT⟩⟩
    rintro _ ⟨t, rfl⟩
    exact ⟨((t : X) : K), (t : X).2, rfl⟩
  obtain ⟨U₁, hU₁X, haU₁, r₁, hr₁', hU₁⟩ := himage _ hX₁ haX₁ hr₁
  obtain ⟨U₂, hU₂X, haU₂, r₂, hr₂', hU₂⟩ := himage _ hX₂ haX₂ hr₂
  obtain ⟨Kc₁, hKc₁, -, hX₁K, -⟩ := id hX₁
  obtain ⟨Kc₂, hKc₂, -, hX₂K, -⟩ := id hX₂
  have hne : Kc₁ ≠ Kc₂ := fun h =>
    h12 (pComponent_eq_of_map_eq hX₁ hX₂ (hX₁K.trans (h.trans hX₂K.symm)))
  have hcomm : ⁅Kc₁, Kc₂⁆ = ⊥ := (distinct_components_commute hKc₁ hKc₂).resolve_left hne
  have hUV : ∀ u ∈ U₁, ∀ v ∈ U₂, u * v = v * u := by
    intro u hu v hv
    have hu' : u ∈ Kc₁ := hX₁K ▸ hU₁X hu
    have hv' : v ∈ Kc₂ := hX₂K ▸ hU₂X hv
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hu') v hv').symm
  obtain ⟨-, ⟨E, hEUV, hE, hEcard, -⟩, -⟩ :=
    SmallLocal.commuting_quaternion_pair_common_involution_rank_three hUV hr₁' hr₂' hU₁ hU₂
      (orderOf_mk_eq_two hOodd ha) haU₁ haU₂
  have hEQ : E ≤ (coreActionKernel J).map (QuotientGroup.mk' (pPrimeCore 2 K)) :=
    hEUV.trans (sup_le (hU₁X.trans (map_mono hQ₁)) (hU₂X.trans (map_mono hQ₂)))
  have h3 := le_pRank_of_le_map_odd hOodd hEQ (k := 3) (by rw [hEcard]; norm_num)
  omega

omit [Finite K] in
theorem mem_normalizer_inf {A B : Subgroup K} {g : K} (hA : g ∈ normalizer (A : Set K))
    (hB : g ∈ normalizer (B : Set K)) : g ∈ normalizer ((A ⊓ B : Subgroup K) : Set K) := by
  rw [mem_normalizer_iff]
  intro x
  rw [mem_inf, mem_inf]
  exact and_congr (mem_normalizer_iff.mp hA x) (mem_normalizer_iff.mp hB x)

theorem rank_one_small_kernel_core {a : K} (ha : orderOf a = 2) (haZ : a ∈ center K)
    {J : Subgroup K} (hJ : IsPComponent 2 J) (haJ : a ∈ J) (hJrank : pRank 2 J ≤ 1)
    (hQrank : pRank 2 (coreActionKernel J) ≤ 2) :
    (∀ x ∈ J, orderOf x = 2 → x = a) ∧
    (∀ T : Sylow 2 J, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
    {X : Subgroup K | ∃ h, X = conjugate J h}.ncard ≤ 2 ∧
    (¬ J.Normal → ∃ L : Subgroup K,
      ((∃ h, L = conjugate J h) ∧ L ≠ J) ∧
      (∀ L' : Subgroup K, (∃ h, L' = conjugate J h) → L' ≠ J → L' = L) ∧
      (normalizer (J : Set K)).index = 2 ∧ (normalizer (J : Set K)).Normal ∧
      (J.subgroupOf (normalizer (J : Set K))).Normal ∧
      (L.subgroupOf (normalizer (J : Set K))).Normal ∧
      IsPComponent 2 L ∧ a ∈ L ∧ L ≤ coreActionKernel J ∧
      ∀ S : Subgroup K, S ≤ normalizer (J : Set K) →
        (∃ T : Sylow 2 (normalizer (J : Set K)),
          (T : Subgroup _) = S.subgroupOf (normalizer (J : Set K))) →
        ((S ⊓ L).subgroupOf S).Normal ∧
        (∃ T : Sylow 2 L, (T : Subgroup L) = (S ⊓ L).subgroupOf L) ∧
        (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S ⊓ L : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
        (a ∈ S ⊓ L ∧ ∀ x ∈ S ⊓ L, orderOf x = 2 → x = a) ∧
        S ⊓ L ≤ S ⊓ coreActionKernel J ∧
        (((∃ n : ℕ, 3 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup K) ≃* DihedralGroup (2 ^ (n - 1)))) ∨
          (∃ n : ℕ, 4 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup K) ≃* Open.SemidihedralGroup n))) →
          ∃ n : ℕ, 4 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup K) ≃* Open.SemidihedralGroup n) ∧
            (S ⊓ L).relIndex (S ⊓ coreActionKernel J) = 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hquat, huniq, -⟩ := rank_one_pComponent_facts ha haZ hJ haJ hJrank
  have hconjfacts : ∀ h : K, IsPComponent 2 (conjugate J h) ∧ a ∈ conjugate J h ∧
      pRank 2 (conjugate J h) ≤ 1 := by
    intro h
    refine ⟨isPComponent_conjugate hJ h, ?_, ?_⟩
    · have hmem := conj_mem_conjugate haJ h
      rwa [mul_assoc, ← mem_center_iff.mp haZ h, inv_mul_cancel_left] at hmem
    · unfold conjugate
      rw [← pRank_eq_of_mulEquiv (by norm_num)
        (J.equivMapOfInjective _ (MulAut.conj h⁻¹).injective)]
      exact hJrank
  have horbit : ∀ h₁ h₂ : K, conjugate J h₁ ≠ J → conjugate J h₂ ≠ J →
      conjugate J h₁ = conjugate J h₂ := fun _ _ =>
    conjugate_eq_of_ne_of_ne ha haZ hJ haJ hJrank hQrank
  have h3 : {X : Subgroup K | ∃ h, X = conjugate J h}.ncard ≤ 2 := by
    by_cases hall : ∀ h : K, conjugate J h = J
    · have hsub : {X : Subgroup K | ∃ h, X = conjugate J h} ⊆ {J} := by
        rintro X ⟨h, rfl⟩
        exact hall h
      calc _ ≤ ({J} : Set (Subgroup K)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by rw [Set.ncard_singleton]; norm_num
    · push Not at hall
      obtain ⟨h₀, hh₀⟩ := hall
      have hsub : {X : Subgroup K | ∃ h, X = conjugate J h} ⊆ {J, conjugate J h₀} := by
        rintro X ⟨h, rfl⟩
        by_cases hJh : conjugate J h = J
        · exact Or.inl hJh
        · exact Or.inr (horbit h h₀ hJh hh₀)
      calc _ ≤ ({J, conjugate J h₀} : Set (Subgroup K)).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({conjugate J h₀} : Set (Subgroup K)).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
  refine ⟨huniq, hquat, h3, fun hJn => ?_⟩
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : K, conjugate J h₀ ≠ J := by
    by_contra hall
    push Not at hall
    apply hJn
    refine ⟨fun n hn g => mem_conjugate_iff.mp ?_⟩
    rw [hall g]
    exact hn
  set L := conjugate J h₀ with hLdef
  have huniqL : ∀ L' : Subgroup K, (∃ h, L' = conjugate J h) → L' ≠ J → L' = L := by
    rintro L' ⟨h, rfl⟩ hne
    exact horbit h h₀ hne hh₀
  obtain ⟨hL, haL, hLrank⟩ := hconjfacts h₀
  have hLQ := le_coreActionKernel hJ hL hh₀
  set N := normalizer (J : Set K) with hNdef
  have hLN : L ≤ N := fun x hx => (hLQ hx).1
  have hconjN : ∀ g : K, g ∈ N ↔ conjugate J g = J := fun g => mem_normalizer_iff_conjugate_eq
  have hnotN : ∀ g : K, g ∉ N → conjugate J g = L := fun g hg =>
    huniqL _ ⟨g, rfl⟩ (fun h => hg ((hconjN g).mpr h))
  have hLh₀ : conjugate L h₀ = J := by
    by_contra hne
    have h := huniqL (conjugate L h₀) ⟨h₀ * h₀, by rw [hLdef, conjugate_conjugate]⟩ hne
    exact hh₀ (conjugate_injective (h.trans hLdef))
  have hidx : N.index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨h₀, fun b => ?_⟩
    by_cases hb : b ∈ N
    · have hbh : b * h₀ ∉ N := by
        rw [hconjN, ← conjugate_conjugate, (hconjN b).mp hb]
        exact hh₀
      simp [hb, hbh]
    · have hbh : b * h₀ ∈ N := by
        rw [hconjN, ← conjugate_conjugate, hnotN b hb]
        exact hLh₀
      simp [hb, hbh]
  have hNn : N.Normal := normal_of_index_eq_two hidx
  have hJN : (J.subgroupOf N).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
  have hNL : N ≤ normalizer (L : Set K) := by
    intro n hn
    rw [mem_normalizer_iff_conjugate_eq]
    by_contra hne
    have hLn : conjugate L n = J := by
      by_contra hne'
      exact hne (huniqL _ ⟨h₀ * n, by rw [hLdef, conjugate_conjugate]⟩ hne')
    apply hh₀
    have h₀n : h₀ * n ∈ N :=
      (hconjN _).mpr (by rw [← conjugate_conjugate, ← hLdef]; exact hLn)
    have h₀N := (hconjN _).mp (mul_mem h₀n (inv_mem hn))
    rwa [mul_inv_cancel_right] at h₀N
  have hLNn : (L.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  refine ⟨L, ⟨⟨h₀, rfl⟩, hh₀⟩, huniqL, hidx, hNn, hJN, hLNn, hL, haL, hLQ,
    fun S hSN hSsyl => ?_⟩
  obtain ⟨Lquat, Luniq, -⟩ := rank_one_pComponent_facts ha haZ hL haL hLrank
  have hSL : S ≤ normalizer (L : Set K) := hSN.trans hNL
  have hD1 : ((S ⊓ L).subgroupOf S).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact fun s hs => mem_normalizer_inf (le_normalizer hs) (hSL hs)
  obtain ⟨S', hS'⟩ := hSsyl
  obtain ⟨P₀, hP₀⟩ := Glauberman.sylow_inf_normal S' (N := L.subgroupOf N)
  let e : L.subgroupOf N ≃* L := subgroupOfEquivOfLe hLN
  have hD2 : ∃ T : Sylow 2 L, (T : Subgroup L) = (S ⊓ L).subgroupOf L := by
    have he : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨P₀.mapSurjective he, ?_⟩
    rw [Sylow.coe_mapSurjective, hP₀, hS']
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ (S.subgroupOf N ⊓ L.subgroupOf N).subgroupOf (L.subgroupOf N) := hy
      rw [mem_subgroupOf, mem_inf, mem_subgroupOf, mem_subgroupOf] at hy'
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hy'.1, hy'.2⟩)
    · intro hx
      rw [mem_subgroupOf] at hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      show e.symm x ∈ (S.subgroupOf N ⊓ L.subgroupOf N).subgroupOf (L.subgroupOf N)
      rw [mem_subgroupOf, mem_inf, mem_subgroupOf, mem_subgroupOf]
      exact ⟨(mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  obtain ⟨TD, hTD⟩ := hD2
  have hD3 : ∃ r : ℕ, 3 ≤ r ∧
      Nonempty ((S ⊓ L : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    obtain ⟨r, hr, ⟨eT⟩⟩ := Lquat TD
    exact ⟨r, hr, ⟨(subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).symm.trans
      ((MulEquiv.subgroupCongr hTD).symm.trans eT)⟩⟩
  have haN : a ∈ N := le_normalizer haJ
  have haS : a ∈ S := by
    set a'' : N := ⟨a, haN⟩ with ha''def
    have hc : ∀ g : N, Commute g a'' := fun g =>
      Subtype.ext (mem_center_iff.mp haZ (g : K))
    have hn : (zpowers a'').Normal := ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
      rw [((hc g).zpow_right k).eq, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers a'') k⟩
    have h2 : IsPGroup 2 (zpowers a'') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha''def, Subgroup.orderOf_mk, ha,
        pow_one])
    have hmem := h2.le_sylow_of_normal S' (mem_zpowers a'')
    rw [hS'] at hmem
    exact hmem
  have haD : a ∈ S ⊓ L := mem_inf.mpr ⟨haS, haL⟩
  have hD5 : S ⊓ L ≤ S ⊓ coreActionKernel J := inf_le_inf_left S hLQ
  refine ⟨hD1, ⟨TD, hTD⟩, hD3, ⟨haD, fun x hx => Luniq x (mem_inf.mp hx).2⟩, hD5,
    fun hshape => ?_⟩
  have hDPn : ((S ⊓ L).subgroupOf (S ⊓ coreActionKernel J)).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hD5]
    exact inf_le_left.trans ((normal_subgroupOf_iff_le_normalizer inf_le_left).mp hD1)
  have hDnc : ¬ IsMulCommutative ((S ⊓ L).subgroupOf (S ⊓ coreActionKernel J)) := by
    obtain ⟨r, hr, ⟨eD⟩⟩ := hD3
    exact not_isMulCommutative_of_quaternion hr ((subgroupOfEquivOfLe hD5).trans eD)
  have haP : a ∈ S ⊓ coreActionKernel J := hD5 haD
  have haPZ : (⟨a, haP⟩ : (S ⊓ coreActionKernel J : Subgroup K)) ∈ center _ := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp haZ g)
  have haP2 : orderOf (⟨a, haP⟩ : (S ⊓ coreActionKernel J : Subgroup K)) = 2 := by
    rw [Subgroup.orderOf_mk, ha]
  have hPuniq : ∀ x ∈ (S ⊓ L).subgroupOf (S ⊓ coreActionKernel J), orderOf x = 2 →
      x = ⟨a, haP⟩ := by
    intro x hx hx2
    rw [mem_subgroupOf] at hx
    apply Subtype.ext
    exact Luniq _ (mem_inf.mp hx).2 (by rw [Subgroup.orderOf_coe]; exact hx2)
  rcases hshape with ⟨n, hn, ⟨φ⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exfalso
    have hm : 3 ≤ 2 ^ (n - 1) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact false_of_dihedral_of_unique_central_involution hm φ hDnc haPZ hPuniq
  · exact ⟨n, hn, ⟨f⟩, index_eq_two_of_semidihedral hn f.symm hDPn hDnc haPZ haP2 hPuniq⟩

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_small_kernel_normal_or_two_conjugates {a : G} (ha : orderOf a = 2)
    {J : Subgroup (centralizer ({a} : Set G))} (hJ : IsPComponent 2 J)
    (haJ : a ∈ J.map (centralizer ({a} : Set G)).subtype) (hJrank : pRank 2 J ≤ 1)
    (hQrank : pRank 2 (coreActionKernel J) ≤ 2) :
    (∀ x ∈ J, orderOf (x : G) = 2 → (x : G) = a) ∧
    (∀ T : Sylow 2 J, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
    {X : Subgroup (centralizer ({a} : Set G)) | ∃ h, X = conjugate J h}.ncard ≤ 2 ∧
    (J.Normal →
      SmallLocal.IsClassicalInvolutionWitness a (J.map (centralizer ({a} : Set G)).subtype) ∧
        SmallLocal.ClassicalInvolution a) ∧
    (¬ J.Normal → ∃ L : Subgroup (centralizer ({a} : Set G)),
      ((∃ h, L = conjugate J h) ∧ L ≠ J) ∧
      (∀ L' : Subgroup (centralizer ({a} : Set G)), (∃ h, L' = conjugate J h) → L' ≠ J →
        L' = L) ∧
      (normalizer (J : Set (centralizer ({a} : Set G)))).index = 2 ∧
      (normalizer (J : Set (centralizer ({a} : Set G)))).Normal ∧
      (J.subgroupOf (normalizer (J : Set (centralizer ({a} : Set G))))).Normal ∧
      (L.subgroupOf (normalizer (J : Set (centralizer ({a} : Set G))))).Normal ∧
      IsPComponent 2 L ∧ a ∈ L.map (centralizer ({a} : Set G)).subtype ∧
      L ≤ coreActionKernel J ∧
      ∀ S : Subgroup (centralizer ({a} : Set G)),
        S ≤ normalizer (J : Set (centralizer ({a} : Set G))) →
        (∃ T : Sylow 2 (normalizer (J : Set (centralizer ({a} : Set G)))),
          (T : Subgroup _) = S.subgroupOf (normalizer (J : Set (centralizer ({a} : Set G))))) →
        ((S ⊓ L).subgroupOf S).Normal ∧
        (∃ T : Sylow 2 L, (T : Subgroup L) = (S ⊓ L).subgroupOf L) ∧
        (∃ r : ℕ, 3 ≤ r ∧
          Nonempty ((S ⊓ L : Subgroup (centralizer ({a} : Set G))) ≃*
            QuaternionGroup (2 ^ (r - 2)))) ∧
        (a ∈ (S ⊓ L).map (centralizer ({a} : Set G)).subtype ∧
          ∀ x ∈ S ⊓ L, orderOf (x : G) = 2 → (x : G) = a) ∧
        S ⊓ L ≤ S ⊓ coreActionKernel J ∧
        (((∃ n : ℕ, 3 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup (centralizer ({a} : Set G))) ≃*
              DihedralGroup (2 ^ (n - 1)))) ∨
          (∃ n : ℕ, 4 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup (centralizer ({a} : Set G))) ≃*
              Open.SemidihedralGroup n))) →
          ∃ n : ℕ, 4 ≤ n ∧
            Nonempty ((S ⊓ coreActionKernel J : Subgroup (centralizer ({a} : Set G))) ≃*
              Open.SemidihedralGroup n) ∧
            (S ⊓ L).relIndex (S ⊓ coreActionKernel J) = 2)) := by
  have haC : a ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have ha' : orderOf (⟨a, haC⟩ : centralizer ({a} : Set G)) = 2 := by
    rw [Subgroup.orderOf_mk, ha]
  have ha'Z : (⟨a, haC⟩ : centralizer ({a} : Set G)) ∈ center (centralizer ({a} : Set G)) := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have haJ' : (⟨a, haC⟩ : centralizer ({a} : Set G)) ∈ J := by
    obtain ⟨x, hx, hxa⟩ := mem_map.mp haJ
    rwa [show x = ⟨a, haC⟩ from Subtype.ext hxa] at hx
  obtain ⟨c1, c2, c3, c5⟩ := rank_one_small_kernel_core ha' ha'Z hJ haJ' hJrank hQrank
  have h1 : ∀ x ∈ J, orderOf (x : G) = 2 → (x : G) = a := fun x hx hx2 => by
    rw [Subgroup.orderOf_coe] at hx2
    rw [c1 x hx hx2]
  refine ⟨h1, c2, c3, fun hJn => ?_, fun hJn => ?_⟩
  ·
    have hsub : (J.map (centralizer ({a} : Set G)).subtype).subgroupOf
        (centralizer ({a} : Set G)) = J :=
      comap_map_eq_self_of_injective (centralizer ({a} : Set G)).subtype_injective J
    refine SmallLocal.normal_unique_involution_classical ha (map_subtype_le J)
      (by rw [hsub]; exact hJn) haJ ?_ ?_
    · intro x hx hx2
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact h1 y hy hx2
    · intro P
      obtain ⟨r, hr, ⟨eP⟩⟩ := sylow_quaternion_of_mulEquiv
        (J.equivMapOfInjective _ (centralizer ({a} : Set G)).subtype_injective) c2 P
      exact not_isMulCommutative_of_quaternion hr eP
  ·
    obtain ⟨L, hL1, hL2, hL3, hL4, hL5, hL6, hL7, haL, hL8, hS⟩ := c5 hJn
    refine ⟨L, hL1, hL2, hL3, hL4, hL5, hL6, hL7, mem_map.mpr ⟨_, haL, rfl⟩, hL8,
      fun S hSN hSsyl => ?_⟩
    obtain ⟨d1, d2, d3, ⟨haD, hDu⟩, d5, d6⟩ := hS S hSN hSsyl
    refine ⟨d1, d2, d3, ⟨mem_map.mpr ⟨_, haD, rfl⟩, fun x hx hx2 => ?_⟩, d5, d6⟩
    rw [Subgroup.orderOf_coe] at hx2
    rw [hDu x hx hx2]

end CFSG.ComponentClassification.UnbalancedLayer
