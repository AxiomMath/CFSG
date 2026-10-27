module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueBasic
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeBasic
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_fusionZStar_of_mem {T : Subgroup Y} {w : Y} (hwT : w ∈ T)
    (hw : w ∈ Open.fusionZStar Y) : (⟨w, hwT⟩ : ↥T) ∈ Open.fusionZStar ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (pPrimeCore 2 Y).comap T.subtype ≤ pPrimeCore 2 ↥T :=
    le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right
      (card_comap_dvd_of_injective _ _ T.subtype_injective) pPrimeCore_coprime_card⟩
  rw [Sol78.fusionZStar_eq_comap, mem_comap, mem_center_iff] at hw ⊢
  intro g
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have h := hw (QuotientGroup.mk' _ (t : Y))
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  exact hle (mem_subgroupOf.mpr (by simpa using h))

theorem map_eq_top_of_index_eq {T : Subgroup Y}
    (h : (pPrimeCore 2 ↥T).index = (pPrimeCore 2 Y).index) :
    T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥T →* Y ⧸ pPrimeCore 2 Y := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp T.subtype
  have hk : φ.ker = (pPrimeCore 2 Y).comap T.subtype := by
    ext x
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
  have hker : φ.ker ≤ pPrimeCore 2 ↥T := by
    rw [hk]
    exact le_sSup ⟨inferInstance, Nat.Coprime.coprime_dvd_right
      (card_comap_dvd_of_injective _ _ T.subtype_injective) pPrimeCore_coprime_card⟩
  have hrange : φ.range = T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) := by
    rw [MonoidHom.range_comp, range_subtype]
  rw [← hrange]
  refine Subgroup.eq_top_of_le_card _ ?_
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, ← index_eq_card,
    ← index_eq_card, ← h]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hker)

theorem nonempty_quot_equiv_of_map_eq_top {T : Subgroup Y}
    (h : T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = ⊤) :
    Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃* Y ⧸ pPrimeCore 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥T →* Y ⧸ pPrimeCore 2 Y := (QuotientGroup.mk' (pPrimeCore 2 Y)).comp T.subtype
  have hφ : Function.Surjective φ := by
    intro y
    have hy : y ∈ T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) := h ▸ mem_top y
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hodd : Odd (Nat.card φ.ker) := by
    have hk : φ.ker = (pPrimeCore 2 Y).comap T.subtype := by
      ext x
      simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rw [hk]
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat
      (card_comap_dvd_of_injective _ _ T.subtype_injective)
  obtain ⟨e⟩ := DPrime.nonempty_coreQuotEquiv_of_surjective φ hφ hodd
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq
    (GH74.GLS.pPrimeCore_quotient_eq_bot Y)).trans QuotientGroup.quotientBot)⟩

theorem map_eq_top_of_surjective (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y)) {F : Subgroup Y}
    (hF : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 Y)).comp F.subtype))
    {T : Subgroup Y} (hTF : T ≤ F) (hT : IsPComponent 2 (T.subgroupOf F)) :
    T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let qC : ↥F →* Y ⧸ O := (QuotientGroup.mk' O).comp F.subtype
  have hqCodd : Odd (Nat.card qC.ker) := by
    have hk : qC.ker = O.comap F.subtype := by
      ext x
      simp [qC, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, mem_subgroupOf]
    rw [hk]
    exact hOodd.of_dvd_nat (card_comap_dvd_of_injective _ _ F.subtype_injective)
  have hT2 : TwoComponents.IsTwoComponent (T.subgroupOf F) :=
    (CatalogueBAlternating.pComponent_two_iff _).mp hT
  have himg := OddKernelTwoComponents.image qC hF hqCodd _ hT2
  have heq : (T.subgroupOf F).map qC = T.map (QuotientGroup.mk' O) := by
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hTF]
  rw [heq] at himg
  have hcomp := TwoComponents.ordinary_of_corefree GH74.GLS.TwoThin.oddCore_barQ himg
  have hYo : Open.IsQuasisimple (Y ⧸ O) := ⟨hYq.1.commutator_eq_top, hYq.2.1⟩
  rcases Quasisimple.subnormal_le_center_or_eq_top hYo _ hcomp.2.1 with h | h
  · exfalso
    have hperf : ⁅T, T⁆ = T := GH74.GLS.TwoThin.commutator_self_of_isTwoComponent hTF hT2
    have hne := GH74.GLS.TwoThin.map_barMk_ne_bot_of_perfect hperf
      (GH74.GLS.TwoThin.ne_bot_of_isTwoComponent hT2)
    have : Group.IsPerfect ↥(T.map (QuotientGroup.mk' O)) := by
      rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hperf]
    exact hne (Quasisimple.perfect_le_center_eq_bot _ h)
  · exact h

theorem map_eq_top_of_forall_inv_mul_mem (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y))
    (β : MulAut Y) (hβ : ∀ y, β (β y) = y) (htriv : ∀ y : Y, y⁻¹ * β y ∈ pPrimeCore 2 Y)
    {T : Subgroup Y} (hTC : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) :
    T.map (QuotientGroup.mk' (pPrimeCore 2 Y)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  have hOmap : O.map β.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp inferInstance β
  have hβO : ∀ n ∈ O, β n ∈ O := fun n hn => hOmap ▸ mem_map_of_mem β.toMonoidHom hn
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  refine map_eq_top_of_surjective hYq (fun y => ?_) hTC hT
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
  obtain ⟨n, hn, hfix⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem β hβ hβO hOodd (htriv x)
  refine ⟨⟨x * n, hfix⟩, ?_⟩
  change QuotientGroup.mk' O (x * n) = QuotientGroup.mk' O x
  have hn1 : QuotientGroup.mk' O n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
  rw [map_mul, hn1, mul_one]

theorem typL16_of_fixed
    (hP11 : L34CentralSLTwoFact) (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y))
    (hL : GH74.GLS.IsL34Quotient (Y ⧸ pPrimeCore 2 Y))
    (hZ : ¬ IsElementaryAbelian 2 ↥(center (Y ⧸ pPrimeCore 2 Y)))
    (β : MulAut Y) (hβ : ∀ y, β (β y) = y) {T : Subgroup Y} (hTC : T ≤ fixedSubgroup β)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup β))) {q₀ : ℕ}
    (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ)) (hTQ : TypQ q₀ ↥T) {w : Y} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwZ : w ∈ Open.fusionZStar Y) : TypL16 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTtype, hTdvd⟩ := hTQ
  set O := pPrimeCore 2 Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hYO : pPrimeCore 2 (Y ⧸ O) = ⊥ := GH74.GLS.pPrimeCore_quotient_eq_bot Y
  have hTq : IsQuasisimple (↥T ⧸ pPrimeCore 2 ↥T) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hTC)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hT)
  have hwT2 : orderOf (⟨w, hwT⟩ : ↥T) = 2 := by rw [Subgroup.orderOf_mk]; exact hw
  obtain ⟨hwc, hw1⟩ := mk_mem_center_ne_one (mem_fusionZStar_of_mem hwT hwZ) hwT2
  have hle : (pPrimeCore 2 ↥T).index ≤ (pPrimeCore 2 Y).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.le_of_dvd Nat.card_pos (card_quot_dvd T)
  rcases hle.lt_or_eq with hlt | heq
  swap
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_quot_equiv_of_map_eq_top (map_eq_top_of_index_eq heq)
    rcases hTtype with hodd | ⟨n, -, h2A⟩
    · have hY : Blueprint.OddLieType ((Y ⧸ O) ⧸ center (Y ⧸ O)) :=
        oddLieType_of_mulEquiv ((Sol78.coreQuotientCenterEquiv ↥T).symm.trans
          (Sol78.centerQuotCongr e)) hodd
      exact not_oddLieType_of_l34 hL hY
    · obtain ⟨-, h2, -⟩ := isDoubleCoverOfAlt_of_mulEquiv e h2A
      have h3 := Group.exponent_dvd_nat_card (G := ↥(center (Y ⧸ O)))
      rw [h2] at h3
      exact hZ ⟨h3⟩
  obtain ⟨σ, -, hσ, hPF, hP, hPne, ⟨eP⟩⟩ :=
    GrSLit.exists_simple_fixed_component_image hYq β hβ hTC hT hlt
  have hS : IsSimpleGroup ((Y ⧸ O) ⧸ center (Y ⧸ O)) := hYq.2.1
  have hl2 := GrSLit.simpleFixedComponents_l34 _ hS hYq.2.2 hL σ hσ _ hPF hP hPne
  obtain ⟨q, hq, hLie⟩ : ∃ q : ℕ, (q = 5 ∨ q = 7) ∧
      Blueprint.LieModel ((↥T ⧸ pPrimeCore 2 ↥T) ⧸ center (↥T ⧸ pPrimeCore 2 ↥T)) .PSL 2 q 1 := by
    rcases hl2 with h | h
    · exact ⟨5, Or.inl rfl, Blueprint.LieModel.of_mulEquiv
        (eP.symm.trans (Sol78.coreQuotientCenterEquiv ↥T).symm) h⟩
    · exact ⟨7, Or.inr rfl, Blueprint.LieModel.of_mulEquiv
        (eP.symm.trans (Sol78.coreQuotientCenterEquiv ↥T).symm) h⟩
  have hqp : q.Prime := by rcases hq with rfl | rfl <;> norm_num
  have hq2 : q ≠ 2 := by rcases hq with rfl | rfl <;> norm_num
  have hTO : pPrimeCore 2 (↥T ⧸ pPrimeCore 2 ↥T) = ⊥ := GH74.GLS.pPrimeCore_quotient_eq_bot ↥T
  have hSL : HarrisLit.IsSLTwoOver q (↥T ⧸ pPrimeCore 2 ↥T) := by
    rcases GH74.Generic.BProg.B2.l2_cover_cases hTq hqp hq2 hLie with
      ⟨z, hz1, hzc, hzo⟩ | ⟨hZbot, -⟩ | ⟨-, K, _, _, hK, ⟨eK⟩⟩
    · exfalso
      have hzO : zpowers z ≤ pPrimeCore 2 (↥T ⧸ pPrimeCore 2 ↥T) := by
        refine le_sSup ⟨?_, ?_⟩
        · exact Subgroup.normal_of_le_center
            (zpowers_le.mpr (mem_center_iff.mpr fun g => hzc g))
        · rw [Nat.card_zpowers]
          exact Nat.coprime_two_left.mpr hzo
      rw [hTO, le_bot_iff, zpowers_eq_bot] at hzO
      exact hz1 hzO
    · rw [hZbot, mem_bot] at hwc
      exact absurd hwc hw1
    · let _ : Fintype K := Fintype.ofFinite K
      exact ⟨K, inferInstance, inferInstance, by rw [← Nat.card_eq_fintype_card, hK, pow_one],
        ⟨eK⟩⟩
  have hqq : q₀ = q := by
    have h1 := card_of_isSLTwoOver hSL
    rw [h1] at hTdvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq with rfl | rfl <;> rcases hq₀ with rfl | rfl | rfl <;>
      first | rfl | exact absurd hTdvd (by decide)
  subst hqq
  have hOmap : O.map β.toMonoidHom = O := Subgroup.characteristic_iff_map_eq.mp inferInstance β
  set σY : MulAut (Y ⧸ O) := QuotientGroup.congr O O β hOmap with hσYdef
  have hσYmk : ∀ y : Y, σY (π y) = π (β y) := fun y => rfl
  have hσY : ∀ y, σY (σY y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [hσYmk, hσYmk, hβ]
  have hσY1 : σY ≠ 1 := by
    intro h1
    have htriv : ∀ y : Y, y⁻¹ * β y ∈ O := by
      intro y
      have h2 : σY (π y) = π y := by rw [h1]; rfl
      rw [hσYmk] at h2
      exact (QuotientGroup.eq (s := O)).mp h2.symm
    have htop := map_eq_top_of_forall_inv_mul_mem hYq β hβ htriv hTC hT
    exact absurd (GrSLit.index_pPrimeCore_le_of_map_eq_top htop) (not_le.mpr hlt)
  set N := T.map π with hN
  have hNC : N ≤ fixedSubgroup σY := by
    rintro _ ⟨t, ht, rfl⟩
    change σY (π t) = π t
    rw [hσYmk, show β t = t from hTC ht]
  let πT : ↥T →* ↥N := (π.comp T.subtype).codRestrict N fun t => ⟨t, t.2, rfl⟩
  have hπT : Function.Surjective πT := by
    rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hπTodd : Odd (Nat.card πT.ker) := by
    have hk : πT.ker = (π.domRestrict T).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk]
    exact OddKernel.odd_card_restriction_kernel π
      (by rw [QuotientGroup.ker_mk']; exact Nat.coprime_two_left.mp pPrimeCore_coprime_card) T
  obtain ⟨eN⟩ := DPrime.nonempty_coreQuotEquiv_of_surjective πT hπT hπTodd
  have hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) :=
    DPrime.isSLTwoOver_of_coreEquiv eN hSL
  have hwZ' : π w ∈ center (Y ⧸ O) := by
    rw [Sol78.fusionZStar_eq_comap] at hwZ
    exact hwZ
  have hw2 : orderOf (π w) = 2 := GH74.GLS.TwoThin.orderOf_barMk hw
  obtain ⟨-, h16⟩ := hP11 (Y ⧸ O) hYq (Sol78.center_isPGroup_two hYO) hL σY hσY hσY1 N hNC q₀
    hq₀ hNSL (π w) hw2 ⟨w, hwT, rfl⟩ hwZ'
  exact ⟨hL, h16⟩

end CFSG.ComponentClassification.GS82PumpInputs.Residue
