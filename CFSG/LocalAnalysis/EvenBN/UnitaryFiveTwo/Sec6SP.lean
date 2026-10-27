module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6K
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6P
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsL44
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPstd

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer L44Sylow
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd (pstd sigmaSL msigma)
open scoped commutatorElement MatrixGroups

section SylowTools

variable {G : Type} [Group G] [Finite G]

theorem factorization_two_25920 : (25920 : ℕ).factorization 2 = 6 := by
  rw [show (25920 : ℕ) = 2 ^ 6 * 405 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem isSylowOf_of_card_ge {K T : Subgroup G} (hTK : T ≤ K) (hT : IsPGroup 2 ↥T)
    (hK : Nat.card ↥K = 25920) (hc : 2 ^ 6 ≤ Nat.card ↥T) :
    CFSG.ABGLocalTools.IsSylowOf 2 T K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  have hTdvd : Nat.card ↥T ∣ 25920 := hK ▸ Subgroup.card_dvd_of_le hTK
  have hn6 : n ≤ 6 := by
    by_contra hlt
    have h7 : 2 ^ 7 ∣ 25920 := (pow_dvd_pow 2 (by omega : 7 ≤ n)).trans (hn ▸ hTdvd)
    norm_num at h7
  have hle6 : Nat.card ↥T ≤ 2 ^ 6 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) hn6
  refine CFSG.ABGLocalTools.isSylowOf_of_card hTK ?_
  rw [hK, factorization_two_25920]
  exact le_antisymm hle6 hc

theorem exists_conj_le_sylow_two {K P E : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hEK : E ≤ K) (hE : IsPGroup 2 ↥E) : ∃ k ∈ K, ∀ x ∈ E, k * x * k⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : IsPGroup 2 ↥(E.subgroupOf K) :=
    hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hQK : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup ↥K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQK.exists_mem_conj hP
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [hconj]
  have : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [this]
  exact ⟨⟨x, hEK hx⟩, hQ hx, rfl⟩

end SylowTools

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem card_M_sup_Y (h : d.Hyp) (hK : d.KLinear) : Nat.card ↥(d.M ⊔ d.Y) = 2 ^ 12 := by
  have hKY := h.M_le_normalizer_Y_linear hK
  have e := PGrp.card_sup_mul_card_inf (A := d.M) (B := d.Y) (fun m hm => hKY m hm)
  rw [h.M_inf_Y, h.card_V₂, h.card_M, h.card_Y'] at e
  have hpos : 0 < 2 ^ 6 := by norm_num
  have : Nat.card ↥(d.M ⊔ d.Y) * 2 ^ 6 = 2 ^ 12 * 2 ^ 6 := by rw [e]; norm_num [pow_add]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem isSylowOf_M_sup_Y (h : d.Hyp) (hK : d.KLinear) :
    CFSG.ABGLocalTools.IsSylowOf 2 (d.M ⊔ d.Y) d.K := by
  obtain ⟨φ, -⟩ := hK.graphField
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₃ : d.K₃ ≤ d.K := by
    rw [← hK.centralizer_eq]
    exact inf_le_left
  have hYK : d.Y ≤ d.K := h.Y_le_K hK₃ (Data.Lev_le_zpowers_sup_K₃ d)
  have hMK : d.M ≤ d.K := h.M_le_K hYK hK₃
  have hKY := h.M_le_normalizer_Y_linear hK
  have hM2 : IsPGroup 2 ↥d.M := (IsPGroup.of_card (n := 14) h.card_D₁).to_le M_le_D₁
  have hY2 : IsPGroup 2 ↥d.Y := IsPGroup.of_card (n := 8) h.card_Y'
  have hMY2 : IsPGroup 2 ↥(d.M ⊔ d.Y) :=
    PGrp.isPGroup_sup_of_le_normalizer hM2 hY2 (fun m hm => hKY m hm)
  obtain ⟨χ, hinj, hsurj, hKm, hAQ⟩ := exists_chi_of_pGroup φ hMY2 (sup_le hMK hYK)
  have hcardQ : Nat.card ↥(PK.map χ) = 2 ^ 12 := by
    rw [Subgroup.card_map_of_injective hinj, card_PK]
  have hEq : d.M ⊔ d.Y = PK.map χ :=
    Subgroup.eq_of_le_of_card_ge hAQ (by rw [h.card_M_sup_Y hK, hcardQ])
  rw [hEq]
  exact isSylowOf_map_PK hinj hsurj hKm

theorem exists_standard_position (h : d.Hyp) (hK : d.KLinear) :
    ∃ φ' : SL(4, F4) →* G, Function.Injective φ' ∧
      φ'.range = d.K ∧ (∀ A, d.t * φ' A * d.t⁻¹ = φ' (sigmaSL F4 A)) ∧
      (pstd F4).map φ' = d.M ⊔ d.Y := by
  obtain ⟨φ, hφ⟩ := hK.graphField
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := h.isSylowOf_M_sup_Y hK
  have hK₃ : d.K₃ ≤ d.K := by
    rw [← hK.centralizer_eq]
    exact inf_le_left
  have hcard3 : Nat.card ↥(d.K ⊓ centralizer ({d.t} : Set G)) = 25920 := by
    have := card_K₃ hK
    rwa [← hK.centralizer_eq] at this
  set K₃' : Subgroup G := d.K ⊓ centralizer ({d.t} : Set G) with hK₃'
  set ψ₀ : SL(4, F4) →* G := d.K.subtype.comp φ.toMonoidHom with hψ₀
  have hψ₀inj : Function.Injective ψ₀ := d.K.subtype_injective.comp φ.injective
  have hψ₀t : ∀ A, d.t * ψ₀ A * d.t⁻¹ = ψ₀ (sigmaSL F4 A) := fun A => hφ A
  have hmemC : ∀ A : msigma F4, ψ₀ (A : SL(4, F4)) ∈ K₃' := by
    intro A
    refine ⟨(φ (A : SL(4, F4))).2, mem_centralizer_singleton_iff.2 ?_⟩
    have hA : sigmaSL F4 (A : SL(4, F4)) = A := A.2
    have := hψ₀t (A : SL(4, F4))
    rw [hA] at this
    calc ψ₀ (A : SL(4, F4)) * d.t
        = d.t * ψ₀ (A : SL(4, F4)) * d.t⁻¹ * d.t := by
          rw [this]
      _ = d.t * ψ₀ (A : SL(4, F4)) := by group
  let χ₁ : msigma F4 →* ↥K₃' :=
    (ψ₀.comp (msigma F4).subtype).codRestrict K₃' hmemC
  have hχ₁ : Function.Bijective χ₁ := by
    refine ⟨fun A B hAB => ?_, ?_⟩
    · have h0 := congrArg Subtype.val hAB
      have h1 : ψ₀ (A : SL(4, F4)) = ψ₀ (B : SL(4, F4)) := h0
      exact Subtype.ext (hψ₀inj h1)
    rintro ⟨g, hgK, hgC⟩
    set A : SL(4, F4) := φ.symm ⟨g, hgK⟩ with hA
    have hgA : ψ₀ A = g := by simp [ψ₀, hA]
    have hgt : d.t * g * d.t⁻¹ = g := by
      have := mem_centralizer_singleton_iff.1 hgC
      calc d.t * g * d.t⁻¹ = g * d.t * d.t⁻¹ := by rw [this]
        _ = g := by group
    have hσ : sigmaSL F4 A = A := by
      apply hψ₀inj
      rw [← hψ₀t, hgA, hgt]
    exact ⟨⟨A, hσ⟩, Subtype.ext hgA⟩
  let χ₀ : msigma F4 ≃* ↥K₃' := MulEquiv.ofBijective χ₁ hχ₁
  have hχ₀ : ∀ A : msigma F4, ((χ₀ A : ↥K₃') : G) = ψ₀ (A : SL(4, F4)) :=
    fun A => rfl
  have hT₁S : IsPGroup 2 ↥(d.X₂ ⊔ d.F) :=
    (IsPGroup.of_card (n := 10) d.card_S).to_le d.X₂_sup_F_le_S
  have hT₁K : d.X₂ ⊔ d.F ≤ K₃' := by
    intro x hx
    have := d.X₂_sup_F_le_K₃ hx
    rw [← hK.centralizer_eq] at this
    exact this
  have hT₁syl : CFSG.ABGLocalTools.IsSylowOf 2 (d.X₂ ⊔ d.F) K₃' :=
    isSylowOf_of_card_ge hT₁K hT₁S hcard3 d.card_X₂_sup_F
  set E : Subgroup G := (msigma F4 ⊓ pstd F4).map ψ₀ with hE
  have hEK : E ≤ K₃' := by
    rintro _ ⟨A, hA, rfl⟩
    exact hmemC ⟨A, hA.1⟩
  have hEcard : Nat.card ↥E = 2 ^ 6 := by
    rw [hE, Subgroup.card_map_of_injective hψ₀inj,
      CFSG.EvenSmallLie.UnitarySix.YamadaPar.card_msigma_inf_pstd
        CFSG.EvenSmallLie.UnitarySix.YamadaPar.natCard_F4]
  have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card hEcard
  obtain ⟨k, hkK, hk⟩ := exists_conj_le_sylow_two hT₁syl hEK hE2
  let χ : msigma F4 ≃* ↥K₃' := χ₀.trans (MulAut.conj (⟨k, hkK⟩ : ↥K₃'))
  have hχ : ∀ A : msigma F4, ((χ A : ↥K₃') : G) =
      k * ψ₀ (A : SL(4, F4)) * k⁻¹ := fun A => rfl
  have hT₁MY : d.X₂ ⊔ d.F ≤ d.M ⊔ d.Y := by
    refine sup_le (fun x hx => mem_sup_left ?_) (fun x hx => mem_sup_right (h.F_le_Y hx))
    exact (Subgroup.mem_inf.2 ⟨h.A₁_le_D₁ (X₂_le_A₁ hx), mem_centralizer_singleton_iff.2
      (X₂_comm_e₂ hx)⟩)
  have hχP : ∀ A : msigma F4, (A : SL(4, F4)) ∈ pstd F4 →
      ((χ A : ↥K₃') : G) ∈ d.M ⊔ d.Y := by
    intro A hA
    rw [hχ]
    exact hT₁MY (hk _ ⟨A, ⟨A.2, hA⟩, rfl⟩)
  have hker : φ.toMonoidHom.ker ≤ center SL(4, F4) := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective]
    exact bot_le
  obtain ⟨φ', hφ'inj, hφ'range, -, hφ't, hφ'P⟩ :=
    CFSG.EvenSmallLie.UnitarySix.YamadaInputs.l44Input F4 CFSG.EvenSmallLie.UnitarySix.YamadaPar.natCard_F4 G d.K
      φ.toMonoidHom φ.surjective hker d.t h.t_mul_t h.t_mem_normalizer_K χ (d.M ⊔ d.Y) hsyl hχP
  exact ⟨φ', hφ'inj, hφ'range, hφ't, hφ'P⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
