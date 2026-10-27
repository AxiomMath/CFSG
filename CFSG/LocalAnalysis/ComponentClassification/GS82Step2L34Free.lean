module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3Thm8
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3Psi
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3G
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CI3Rows
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIUCl3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIU3Spor
public import CFSG.LocalAnalysis.ComponentClassification.GS82HMain
public import CFSG.LocalAnalysis.ComponentClassification.GS82HLargeInputs
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrime
public import CFSG.LocalAnalysis.ComponentClassification.GS82CIInputsHarris
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.GS82Step2Assembly
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Final
public import CFSG.LocalAnalysis.ComponentClassification.GS82PC
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P11
public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueL34Free
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigNormExport
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34FixedSqrt
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34Lift
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigAmbient

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.Residue

open CFSG Subgroup CFSG.Semidihedral.Principal
open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_seven_of_twoGroup_l34
    (hP11 : L34CentralSLTwoFact) (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y))
    (hL : GH74.GLS.IsL34Quotient (Y ⧸ pPrimeCore 2 Y)) {A : Type} [Group A] [Finite A]
    (hA : IsPGroup 2 A) (α : A →* MulAut Y) {F : Subgroup Y}
    (hF : ∀ y, y ∈ F ↔ ∀ a, α a y = y) {T : Subgroup Y} (hTF : T ≤ F)
    (hT : IsPComponent 2 (T.subgroupOf F)) {q₀ : ℕ} (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ))
    (hSL : HarrisLit.IsSLTwoOver q₀ (↥T ⧸ pPrimeCore 2 ↥T)) {w : Y} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwZ : w ∈ Open.fusionZStar Y) : q₀ = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hYO : pPrimeCore 2 (Y ⧸ O) = ⊥ := GH74.GLS.pPrimeCore_quotient_eq_bot Y
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hαO : ∀ a : A, ∀ n ∈ O, α a n ∈ O := by
    intro a n hn
    have hOmap : O.map (α a).toMonoidHom = O :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance (α a)
    exact hOmap ▸ mem_map_of_mem _ hn
  set ρ := CoprimeFixedPoint.quotientAction α O hαO with hρ
  have hρmk : ∀ a y, ρ a (π y) = π (α a y) := fun a y => rfl
  by_cases htriv : ∀ a : A, ρ a = 1
  ·
    exfalso
    have hcov := coprime_fixed_point_lifting 2 hA α O hαO
      (fun h => Nat.not_even_iff_odd.mpr hOodd (even_iff_two_dvd.mpr h))
    have hsurj : Function.Surjective (π.comp F.subtype) := by
      intro y
      have hy : y ∈ {q : Y ⧸ O | ∀ a : A, CoprimeFixedPoint.quotientAction α O hαO a q = q} :=
        fun a => by rw [← hρ, htriv a, MulAut.one_apply]
      rw [hcov] at hy
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨⟨c, (hF c).mpr hc⟩, rfl⟩
    obtain ⟨e⟩ := nonempty_quot_equiv_of_map_eq_top (map_eq_top_of_surjective hYq hsurj hTF hT)
    have h1 : Nat.card (Y ⧸ O) = q₀ * (q₀ ^ 2 - 1) := by
      rw [← Nat.card_congr e.toEquiv]
      exact card_of_isSLTwoOver hSL
    have h2 : 20160 ∣ Nat.card (Y ⧸ O) := by
      rw [← card_of_l34 hL, Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Y ⧸ O))]
      exact dvd_mul_right _ _
    rw [h1] at h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq₀
    rcases hq₀ with rfl | rfl | rfl <;> exact absurd h2 (by decide)
  obtain ⟨a, ha⟩ := not_forall.mp htriv
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hA) a
  have hdvd : orderOf (ρ a) ∣ 2 ^ m := hm ▸ orderOf_map_dvd ρ a
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact ha hj
  have h2 : 2 ∣ orderOf (ρ a) := hj ▸ dvd_pow_self 2 hj0
  set k := orderOf (ρ a) / 2 with hk
  set σ := ρ (a ^ k) with hσdef
  have hσ2 : orderOf σ = 2 := by
    rw [hσdef, map_pow]
    exact orderOf_pow_orderOf_div (by rw [hj]; positivity) h2
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y
    have h1 := pow_orderOf_eq_one σ
    rw [hσ2] at h1
    rw [← MulAut.mul_apply, ← pow_two, h1, MulAut.one_apply]
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ2
    exact absurd hσ2 (by norm_num)
  set N := T.map π with hN
  have hNC : N ≤ FixedCommutingProduct.fixedSubgroup σ := by
    rintro _ ⟨t, ht, rfl⟩
    change σ (π t) = π t
    rw [hσdef, hρmk, (hF t).mp (hTF ht)]
  let πT : ↥T →* ↥N := (π.comp T.subtype).codRestrict N fun t => ⟨t, t.2, rfl⟩
  have hπT : Function.Surjective πT := by
    rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hπTodd : Odd (Nat.card πT.ker) := by
    have hk' : πT.ker = (π.domRestrict T).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk']
    exact OddKernel.odd_card_restriction_kernel π (by rw [QuotientGroup.ker_mk']; exact hOodd) T
  obtain ⟨eN⟩ := DPrime.nonempty_coreQuotEquiv_of_surjective πT hπT hπTodd
  have hNSL : HarrisLit.IsSLTwoOver q₀ (↥N ⧸ pPrimeCore 2 ↥N) :=
    DPrime.isSLTwoOver_of_coreEquiv eN hSL
  have hwZ' : π w ∈ center (Y ⧸ O) := by
    rw [Sol78.fusionZStar_eq_comap] at hwZ
    exact hwZ
  have hw2 : orderOf (π w) = 2 := GH74.GLS.TwoThin.orderOf_barMk hw
  exact (hP11 (Y ⧸ O) hYq (Sol78.center_isPGroup_two hYO) hL σ hσσ hσ1 N hNC q₀ hq₀ hNSL (π w)
    hw2 ⟨w, hwT, rfl⟩ hwZ').1

theorem exists_sqrt_mod_of_twoGroup_l34
    (hYq : IsQuasisimple (Y ⧸ pPrimeCore 2 Y)) (hL : GH74.GLS.IsL34Quotient (Y ⧸ pPrimeCore 2 Y))
    (hZ : Nat.card ↥(center (Y ⧸ pPrimeCore 2 Y)) = 16) {A : Type} [Group A] [Finite A]
    (hA : IsPGroup 2 A) (α : A →* MulAut Y) {T : Subgroup Y} (hTA : ∀ a, ∀ y ∈ T, α a y = y)
    (hSL : HarrisLit.IsSLTwoOver 7 (↥T ⧸ pPrimeCore 2 ↥T)) {w : Y} (hw : orderOf w = 2)
    (hwT : w ∈ T) (hwZ : w ∈ Open.fusionZStar Y) :
    ∃ ω : Y, (∀ y : Y, ω⁻¹ * (y⁻¹ * ω * y) ∈ pPrimeCore 2 Y) ∧
      (∀ a, ω⁻¹ * α a ω ∈ pPrimeCore 2 Y) ∧ (ω * ω)⁻¹ * w ∈ pPrimeCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hαO : ∀ a : A, ∀ n ∈ O, α a n ∈ O := by
    intro a n hn
    have hOmap : O.map (α a).toMonoidHom = O :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance (α a)
    exact hOmap ▸ mem_map_of_mem _ hn
  set ρ := CoprimeFixedPoint.quotientAction α O hαO with hρ
  have hρmk : ∀ a y, ρ a (π y) = π (α a y) := fun a y => rfl
  set N := T.map π with hN
  have hNA : ∀ β ∈ ρ.range, ∀ y ∈ N, β y = y := by
    rintro _ ⟨a, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [hρmk, hTA a t ht]
  let πT : ↥T →* ↥N := (π.comp T.subtype).codRestrict N fun t => ⟨t, t.2, rfl⟩
  have hπT : Function.Surjective πT := by
    rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hπTodd : Odd (Nat.card πT.ker) := by
    have hk' : πT.ker = (π.domRestrict T).ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk']
    exact OddKernel.odd_card_restriction_kernel π (by rw [QuotientGroup.ker_mk']; exact hOodd) T
  obtain ⟨eN⟩ := DPrime.nonempty_coreQuotEquiv_of_surjective πT hπT hπTodd
  obtain ⟨Fq, _, _, hFq, ⟨eT⟩⟩ := DPrime.isSLTwoOver_of_coreEquiv eN hSL
  have hwZ' : π w ∈ center (Y ⧸ O) := by
    rw [Sol78.fusionZStar_eq_comap] at hwZ
    exact hwZ
  have hw' : w ^ 2 = 1 := by
    rw [← hw]
    exact pow_orderOf_eq_one w
  have hw2 : π w ^ 2 = 1 := by rw [← map_pow, hw', map_one]
  have hAρ : IsPGroup 2 ρ.range := hA.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  obtain ⟨ωb, hωZ, hωA, hω2⟩ := TBLit.L34P.exists_fixed_central_sqrt hYq hL hZ ρ.range hAρ N
    hNA (by rw [Nat.card_eq_fintype_card, hFq]) eT hw2 ⟨w, hwT, rfl⟩ hwZ'
  obtain ⟨ω, rfl⟩ := QuotientGroup.mk'_surjective O ωb
  refine ⟨ω, fun y => ?_, fun a => ?_, ?_⟩
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    change π (ω⁻¹ * (y⁻¹ * ω * y)) = 1
    simp only [map_mul, map_inv]
    rw [mul_assoc (π y)⁻¹, ← mem_center_iff.mp hωZ (π y), inv_mul_cancel_left, inv_mul_cancel]
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    change π (ω⁻¹ * α a ω) = 1
    rw [map_mul, map_inv, ← hρmk, hωA (ρ a) ⟨a, rfl⟩, inv_mul_cancel]
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    change π ((ω * ω)⁻¹ * w) = 1
    rw [map_mul, map_inv, map_mul, ← sq, hω2, inv_mul_cancel]

end CFSG.ComponentClassification.GS82PumpInputs.Residue

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup
open scoped MatrixGroups

variable {X : Type} [Group X] [Finite X]

theorem eq_seven_of_gs82HConfig_l16
    (hP11 : GS82PumpInputs.L34CentralSLTwoFact) {q₀ : ℕ} (hq₀ : q₀ ∈ ({5, 7, 9} : Finset ℕ))
    {t : X} {K R T : Subgroup X} {w : X} (h : GS82HConfig q₀ t K R T w)
    (hK16 : GH74.GLS.IsL34Quotient (GH74.GLS.kBar K) ∧
      Nat.card ↥(center (GH74.GLS.kBar K)) = 16) : q₀ = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hKt, hKc, hR2, hRt, hRK, hTKR, hTc, hSL, hw, hwT, hwK⟩ := h
  have hTK : T ≤ K := hTKR.trans inf_le_left
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKt)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hKc)
  let α : ↥R →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hRK)
  have hα : ∀ (a : ↥R) (y : ↥K), ((α a y : ↥K) : X) = a * y * (a : X)⁻¹ := fun a y => rfl
  set F := (K ⊓ centralizer (R : Set X)).subgroupOf K with hFdef
  have hF : ∀ y : ↥K, y ∈ F ↔ ∀ a : ↥R, α a y = y := by
    intro y
    rw [mem_subgroupOf, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨-, hy⟩ a
      apply Subtype.ext
      rw [hα]
      calc (a : X) * y * (a : X)⁻¹ = y * a * (a : X)⁻¹ := by rw [hy a a.2]
        _ = y := by group
    · intro hy
      refine ⟨y.2, fun r hr => ?_⟩
      have h1 := congrArg Subtype.val (hy ⟨r, hr⟩)
      rw [hα] at h1
      calc r * (y : X) = r * y * r⁻¹ * r := by group
        _ = y * r := by rw [h1]
  have hTF : T.subgroupOf K ≤ F := fun y hy => mem_subgroupOf.mpr (hTKR (mem_subgroupOf.mp hy))
  have hTF' : IsPComponent 2 ((T.subgroupOf K).subgroupOf F) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTc
  have hSLK : HarrisLit.IsSLTwoOver q₀ (↥(T.subgroupOf K) ⧸ pPrimeCore 2 ↥(T.subgroupOf K)) :=
    GS82PumpInputs.DPrime.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hTK).symm hSL
  obtain ⟨k, hk, hkw⟩ := hwK
  have hk2 : orderOf k = 2 := by
    rw [← hw, ← hkw]
    exact (Subgroup.orderOf_coe k).symm
  have hkT : k ∈ T.subgroupOf K := mem_subgroupOf.mpr (by rw [← hkw] at hwT; exact hwT)
  exact GS82PumpInputs.Residue.eq_seven_of_twoGroup_l34 hP11 hKq hK16.1 hR2 α hF hTF hTF' hq₀
    hSLK hk2 hkT hk

theorem Eight2.CtxA0.exists_gs82HConfig'
    (c : Eight2.CtxA0 X)
    (hA : ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)))
    (hq3 : ¬ (c.s.p = 3 ∧ c.s.f = 1)) :
    ∃ (r e : ℕ) (t : X) (K R T : Subgroup X) (w : X), r.Prime ∧ r ≠ 2 ∧ 1 ≤ e ∧
      GS82HConfig (r ^ e) t K R T w ∧
      t ∈ GH74.GLS.pLayerOf 2 (centralizer ({t} : Set X)) ∧
      (r ^ e = 7 → ¬ (GH74.GLS.IsL34Quotient (GH74.GLS.kBar K) ∧
        Nat.card ↥(center (GH74.GLS.kBar K)) = 16)) := by
  obtain ⟨r, e, K, R, T, w, hr, hr2, he, h, hq, htL, hnorm⟩ := c.exists_gs82HConfig_norm hA hq3
  refine ⟨r, e, _, K, R, T, w, hr, hr2, he, h, htL, fun h7 hK16 => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq7 : c.s.p ^ c.s.f = 7 := hq.symm.trans h7
  obtain ⟨ht, hKt, hKc, hR2, hRt, hRK, hTKR, hTc, hSL, hw, hwT, hwK⟩ := h
  rw [h7] at hSL
  have hTK : T ≤ K := hTKR.trans inf_le_left
  have hKq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) :=
    CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hKt)
      (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hKc)
  let α : ↥R →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hRK)
  have hα : ∀ (a : ↥R) (y : ↥K), ((α a y : ↥K) : X) = a * y * (a : X)⁻¹ := fun a y => rfl
  have hTA : ∀ a : ↥R, ∀ y ∈ T.subgroupOf K, α a y = y := by
    intro a y hy
    apply Subtype.ext
    rw [hα]
    have hyR := (hTKR (mem_subgroupOf.mp hy)).2
    calc (a : X) * y * (a : X)⁻¹ = y * a * (a : X)⁻¹ := by
          rw [(mem_centralizer_iff.mp hyR a a.2).symm]
      _ = y := by group
  have hSLK : HarrisLit.IsSLTwoOver 7 (↥(T.subgroupOf K) ⧸ pPrimeCore 2 ↥(T.subgroupOf K)) :=
    GS82PumpInputs.DPrime.isSLTwoOver_of_mulEquiv (subgroupOfEquivOfLe hTK).symm hSL
  obtain ⟨k, hk, hkw⟩ := hwK
  have hk2 : orderOf k = 2 := by
    rw [← hw, ← hkw]
    exact (Subgroup.orderOf_coe k).symm
  have hkT : k ∈ T.subgroupOf K := mem_subgroupOf.mpr (by rw [← hkw] at hwT; exact hwT)
  obtain ⟨ω, hωc, hωR, hω2⟩ := GS82PumpInputs.Residue.exists_sqrt_mod_of_twoGroup_l34 hKq
    hK16.1 hK16.2 hR2 α hTA hSLK hk2 hkT hk
  obtain ⟨Ω, hΩt, hΩB, hΩ2, hΩe, hΩc⟩ := hnorm ω ω.2
    (fun k' hk' => ⟨_, hωc ⟨k', hk'⟩, rfl⟩) (fun r' hr' => ⟨_, hωR ⟨r', hr'⟩, rfl⟩)
    (by rw [← hkw]; exact ⟨_, hω2, rfl⟩)
  exact c.false_of_fixed_sqrt_mod hA hq7 Ω hΩt hΩB hΩ2 hΩe hΩc

theorem gs82TheoremH' (hL : GS82LargeStatement) (hR : GS82ResidueStatement')
    (hP11 : GS82PumpInputs.L34CentralSLTwoFact)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) :
    ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
      ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
      ¬ (c.s.p = 3 ∧ c.s.f = 1) → False := by
  intro X _ _ c hA hq3
  obtain ⟨r, e, t, K, R, T, w, hr, hr2, he, h, htL, h7⟩ := c.exists_gs82HConfig' hA hq3
  have hamb := c.gs82HAmbient hUc
  by_cases h3 : r ^ e = 3
  · rw [h3] at h
    exact not_gs82HConfig_three h
  by_cases hmem : r ^ e ∈ ({5, 7, 9} : Finset ℕ)
  · exact hR X hamb (r ^ e) hmem t K R T w h htL fun hK16 =>
      h7 (eq_seven_of_gs82HConfig_l16 hP11 hmem h hK16) hK16
  · refine hL X hamb r e hr hr2 he ?_ t K R T w h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    tauto

theorem gs82Step2FuseStatementK_of_ci
    (hCI : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models) :
    GS82Step2FuseStatementK :=
  gs82Step2FuseStatementK_of_cases (gs82Step2FuseQ3_of_psi
      RankThree.PartOne.SPOR.schreierFor_catalog
      (gs82LemmaPsi_of_l43 RankThree.PartOne.SPOR.schreierFor_catalog
          (cfQPUJ6Three_of_classical_spor cfQPUJ6ThreeClassical_holds cfQPUJ6ThreeSpor_holds)
          l43FixedA6Input_holds))
    (gs82TheoremH' (gs82LargeStatement_of_inputs GS82PumpInputs.theoremDPrime_holds
        (harris82Theorem1KProper_of_ci hCI) GS82PumpInputs.chevOddCentralPumpInput_holds
        (GS82PumpInputs.kgSLTwoInput_of_inputs GS82PumpInputs.chevOddPumpLeaf_holds
            GS82PumpInputs.fixedTwoComponentLocation_holds CatLeafProof.lieOrderFormulasInput) GS82PumpInputs.mTypeOfSLTwoSection_holds)
      (GS82PumpInputs.Residue.gs82ResidueStatement'_of_typPump GS82PumpInputs.typPumpInput_holds
        GS82PumpInputs.l34CentralSLTwoFact_holds (harris82Theorem1KProper_of_ci hCI)
        (OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
          @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
        hCI FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds)
      GS82PumpInputs.l34CentralSLTwoFact_holds FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds)

theorem gs82Step2FuseStatementK_holds :
    GS82Step2FuseStatementK :=
  gs82Step2FuseStatementK_of_ci @CFSG.Milestones.cl_lit_classical_involution_theorem_models

end CFSG.ComponentClassification.GSThmB
