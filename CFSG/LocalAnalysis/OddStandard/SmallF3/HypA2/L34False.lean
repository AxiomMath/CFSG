module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.L34Trivial
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SectionCard
public import CFSG.GH74.GLS.TwoThin.Struct
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigCore
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem isSLTwoOver_of_iso {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : HarrisLit.IsSLTwoOver q A) : HarrisLit.IsSLTwoOver q B := by
  obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i₁, i₂, hF, ⟨e.symm.trans eF⟩⟩

private theorem card_of_isSLTwoOver' {q : ℕ} {A : Type} [Group A]
    (h : HarrisLit.IsSLTwoOver q A) : Nat.card A = q * (q ^ 2 - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    Nat.card_eq_fintype_card, hF]

private theorem nonempty_coreQuotEquiv_of_surjective {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (f : A →* B) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker)) :
    Nonempty (A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : (pPrimeCore 2 B).comap f = pPrimeCore 2 A :=
    (CFSG.prime_complement_kernel_core_preimage f hf
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))).1
  let g : A →* B ⧸ pPrimeCore 2 B := (QuotientGroup.mk' _).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hker : g.ker = pPrimeCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hc]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem false_of_l34_outcome (hP11 : GS82PumpInputs.L34CentralSLTwoFact) {H : Type} [Group H]
    [Finite H] {M : Subgroup H} {x : H} {T : Subgroup H} {w : H} (h : VCSetting M x T w)
    (hSL : HarrisLit.IsSLTwoOver 9 (↥T ⧸ pPrimeCore 2 ↥T))
    (hL34 : GH74.GLS.IsL34Quotient (↥M ⧸ pPrimeCore 2 ↥M)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 ↥M with hO
  set Mb := ↥M ⧸ O with hMb
  set π := QuotientGroup.mk' O with hπ
  have hMbq : IsQuasisimple Mb :=
    ((HarrisLit.isTwoComponent_iff_isPComponent M).mpr h.hM).2.2
  have hYO : pPrimeCore 2 Mb = ⊥ := GH74.GLS.pPrimeCore_quotient_eq_bot ↥M
  have hZ2 : IsPGroup 2 ↥(center Mb) := Sol78.center_isPGroup_two hYO
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hx' : M.map (MulAut.conj x).toMonoidHom = M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h.hxM
  let φ : MulAut ↥M := conjAut M x hx'
  have hx2 : x * x = 1 := by
    have hh := pow_orderOf_eq_one x
    rwa [h.ox, pow_two] at hh
  have hxinv2 : x⁻¹ * x⁻¹ = 1 := by
    rw [← mul_inv_rev, hx2, inv_one]
  have hφφ : ∀ k : ↥M, φ (φ k) = k := by
    intro k
    apply Subtype.ext
    rw [coe_conjAut_apply, coe_conjAut_apply]
    calc x * (x * (k : H) * x⁻¹) * x⁻¹ = (x * x) * (k : H) * (x⁻¹ * x⁻¹) := by group
      _ = (k : H) := by rw [hx2, hxinv2]; simp
  have hOmap : O.map (φ : ↥M ≃* ↥M).toMonoidHom = O :=
    CFSG.pPrimeCore_map_iso 2 (φ : ↥M ≃* ↥M)
  let σ : MulAut Mb := QuotientGroup.congr O O (φ : ↥M ≃* ↥M) hOmap
  have hσmk : ∀ k : ↥M, σ (π k) = π (φ k) := fun k =>
    QuotientGroup.congr_apply O O (φ : ↥M ≃* ↥M) hOmap k
  have hσσ : ∀ y : Mb, σ (σ y) = y := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [hσmk k, hσmk (φ k), hφφ k]
  set T' := T.subgroupOf M with hT'
  set N := T'.map π with hN
  let πT : ↥T' →* ↥N := (π.comp T'.subtype).codRestrict N fun t => ⟨t, t.2, rfl⟩
  have hπT : Function.Surjective πT := by
    rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩
  have hπTodd : Odd (Nat.card πT.ker) := by
    have hk' : πT.ker = (π.domRestrict T').ker := MonoidHom.ker_codRestrict _ _ _
    rw [hk']
    exact OddKernel.odd_card_restriction_kernel π (by rw [QuotientGroup.ker_mk']; exact hOodd) T'
  obtain ⟨eN⟩ := nonempty_coreQuotEquiv_of_surjective πT hπT hπTodd
  have hSL' : HarrisLit.IsSLTwoOver 9 (↥T' ⧸ pPrimeCore 2 ↥T') :=
    GSThmB.HConfig.isSLTwoOver_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.hTM).symm hSL
  have hNSL : HarrisLit.IsSLTwoOver 9 (↥N ⧸ pPrimeCore 2 ↥N) :=
    isSLTwoOver_of_iso eN hSL'
  have hNfix : N ≤ FixedCommutingProduct.fixedSubgroup σ := by
    rintro _ ⟨t, ht, rfl⟩
    change σ (π t) = π t
    have hφt : φ t = t := by
      apply Subtype.ext
      rw [coe_conjAut_apply]
      have htx : (t : H) * x = x * (t : H) :=
        mem_centralizer_singleton_iff.mp (h.hTx (Subgroup.mem_subgroupOf.mp ht))
      calc x * (t : H) * x⁻¹ = (t : H) * x * x⁻¹ := by rw [← htx]
        _ = (t : H) := by group
    rw [hσmk t, hφt]
  set wM : ↥M := ⟨w, h.hTM h.hwT⟩ with hwM
  set c : Mb := π wM with hc
  have hwM2 : orderOf wM = 2 := by rw [Subgroup.orderOf_mk]; exact h.ow
  have hc2 : orderOf c = 2 := GH74.GLS.TwoThin.orderOf_barMk (Y := ↥M) hwM2
  have hcN : c ∈ N := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr h.hwT)
  have hcZ : c ∈ center Mb := by
    obtain ⟨m, hm, hmw⟩ := h.hwZ
    have hwMfz : wM ∈ Open.fusionZStar ↥M := by
      rw [show wM = m from Subtype.ext hmw.symm]
      exact hm
    rw [Sol78.fusionZStar_eq_comap] at hwMfz
    exact hwMfz
  by_cases hσ1 : σ = 1
  ·
    exfalso
    have htriv : ∀ m ∈ M, x * m * x⁻¹ * m⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
      intro m hm
      have hmem : (φ ⟨m, hm⟩) * ⟨m, hm⟩⁻¹ ∈ O := by
        have h1 : π ((φ ⟨m, hm⟩) * ⟨m, hm⟩⁻¹) = 1 := by
          rw [map_mul, map_inv, ← hσmk ⟨m, hm⟩, hσ1]
          simp
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hval : M.subtype ((φ ⟨m, hm⟩) * ⟨m, hm⟩⁻¹) = x * m * x⁻¹ * m⁻¹ := by
        rw [map_mul, map_inv]
        change ((φ ⟨m, hm⟩ : ↥M) : H) * (((⟨m, hm⟩ : ↥M)) : H)⁻¹ = x * m * x⁻¹ * m⁻¹
        have hcoe : ((φ ⟨m, hm⟩ : ↥M) : H) = x * m * x⁻¹ := by
          change ((conjAut M x hx' ⟨m, hm⟩ : ↥M) : H) = x * m * x⁻¹
          rw [coe_conjAut_apply]
        rw [hcoe]
      have h2 := Subgroup.mem_map_of_mem M.subtype hmem
      rwa [hval] at h2
    have hsup := sup_pPrimeCore_eq_of_trivial_action h htriv
    have htopmap : (⊤ : Subgroup ↥M).map M.subtype = M := by
      simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup H) M
    have hsup' : T' ⊔ O = ⊤ := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.hTM, htopmap]
      exact hsup
    have hOmap_bot : O.map π = ⊥ :=
      (Subgroup.map_eq_bot_iff (f := π) O).mpr (le_of_eq (QuotientGroup.ker_mk' O).symm)
    have hNtop : N = ⊤ := by
      calc N = T'.map π ⊔ O.map π := by rw [hOmap_bot, sup_bot_eq]
        _ = (T' ⊔ O).map π := (Subgroup.map_sup T' O π).symm
        _ = (⊤ : Subgroup ↥M).map π := by rw [hsup']
        _ = ⊤ := Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)
    have hMbSL : HarrisLit.IsSLTwoOver 9 (Mb ⧸ pPrimeCore 2 Mb) := by
      rw [hNtop] at hNSL
      exact GSThmB.HConfig.isSLTwoOver_of_mulEquiv Subgroup.topEquiv hNSL
    have hcard : Nat.card (Mb ⧸ pPrimeCore 2 Mb) = 720 := by
      simpa using card_of_isSLTwoOver' hMbSL
    have hcardMb : Nat.card Mb = 720 := by
      have e : Mb ⧸ pPrimeCore 2 Mb ≃* Mb :=
        (QuotientGroup.quotientMulEquivOfEq hYO).trans QuotientGroup.quotientBot
      rw [← Nat.card_congr e.toEquiv]
      exact hcard
    have hL34' : LieModel (Mb ⧸ center Mb) .PSL 3 2 2 := hL34
    have h20160 : 20160 ∣ Nat.card Mb := by
      rw [← card_lieModel_psl_three_two_two hL34',
        Subgroup.card_eq_card_quotient_mul_card_subgroup (center Mb)]
      exact dvd_mul_right _ _
    exact absurd h20160 (by rw [hcardMb]; decide)
  ·
    have hL34' : LieModel (Mb ⧸ center Mb) .PSL 3 2 2 := hL34
    have hconcl := hP11 Mb hMbq hZ2 hL34' σ hσσ hσ1 N hNfix 9 (by decide) hNSL c hc2 hcN hcZ
    exact absurd hconcl.1 (by decide)

end CFSG.OddStandard.SmallF3.HypA2
