module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallAutComm
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallAutSmallQ
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylowModel

public section

namespace CFSG.ComponentClassification.CatFactsSmall

open CFSG Subgroup CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank GorensteinWalter
  CatalogueSchreierLinearTwo AutL2Facts
open scoped commutatorElement

theorem hasOuterSign_psl2 {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hpo : Odd p)
    (hcard : Nat.card F = p ^ f) (hf : Odd f) : HasOuterSign (PSL2 F) := by
  have hF' : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpo, hf.pos, hcard⟩
  have hincl : ∀ y : PSL2 F, (semilinearEquivAut F).symm (MulAut.conj y) = incl F y := by
    intro y
    rw [MulEquiv.symm_apply_eq]
    exact (semilinearAction_incl F y).symm
  refine ⟨(deltaPGL hF').comp (semilinearEquivAut F).symm.toMonoidHom, fun y => ?_,
    fun σ hσ hψ => ?_⟩
  · simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, hincl]
    rw [incl_apply, deltaPGL_inl, (chiPGL_eq_one_iff hF' _).2 ⟨y, rfl⟩]
  · obtain ⟨k, hk⟩ := hσ
    set g := (semilinearEquivAut F).symm σ with hg
    have hgk : g ^ 2 ^ k = 1 := by rw [hg, ← map_pow, hk, map_one]
    have hrk : g.right ^ 2 ^ k = 1 := by
      rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, hgk, map_one]
    have hgl : g = SemidirectProduct.inl g.left :=
      SemidirectProduct.ext rfl (eq_one_of_two_power_ringAut hp hcard hf _ k hrk)
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, ← hg] at hψ
    rw [hgl, deltaPGL_inl, chiPGL_eq_one_iff] at hψ
    obtain ⟨y, hy⟩ := hψ
    refine ⟨y, (semilinearEquivAut F).symm.injective ?_⟩
    rw [hincl, ← hg, hgl, incl_apply, hy]

theorem odd_of_card_sylow_eq_four {Y : Type*} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (e : Y ≃* PSL2 F) {p f : ℕ} (hp : p.Prime) (hpo : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (T : Sylow 2 Y) (hT : Nat.card (T : Subgroup Y) = 4) :
    Odd f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  obtain ⟨g, rfl⟩ := Nat.not_odd_iff_even.1 hev
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, g + g, hp, hpo, hf, hcard⟩
  obtain ⟨k, hk⟩ : Odd (p ^ g) := hpo.pow
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hsq : Nat.card F = 8 * j + 1 := by
    rw [hcard, ← two_mul, mul_comm, pow_mul, hk]
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this, hj]
    ring
  have hq1 : Nat.card F - 1 ≠ 0 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  have h8 : 2 ^ 3 ∣ Nat.card F - 1 := ⟨j, by omega⟩
  have h3 : 3 ≤ twoVal F := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hq1).1 h8
  have hT' : Nat.card (T : Subgroup Y) = 2 ^ twoVal F := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv,
      psl2_factorization_two hodd (by omega)]
  have : 2 ^ 3 ≤ 2 ^ twoVal F := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem sylowCond_psl2 {Y : Type*} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (e : Y ≃* PSL2 F) {p f : ℕ} (hp : p.Prime) (hpo : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (T : Sylow 2 Y) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty ((T : Subgroup Y) ≃* DihedralGroup (2 ^ n))) ∨
      (Nat.card (T : Subgroup Y) = 4 ∧ HasOuterSign Y) := by
  obtain ⟨m, hm, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv e ⟨p, f, hp, hpo, hf, hcard⟩ T
  by_cases h2 : 2 ≤ m
  · exact Or.inl ⟨m, h2, ⟨φ⟩⟩
  obtain rfl : m = 1 := by omega
  have h4 : Nat.card (T : Subgroup Y) = 4 := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
    norm_num
  exact Or.inr ⟨h4, HasOuterSign.of_mulEquiv e
    (hasOuterSign_psl2 hp hpo hcard (odd_of_card_sylow_eq_four e hp hpo hf hcard T h4))⟩

theorem hasCommProp_of_small {Y : Type} [Group Y] [Finite Y] (h : IsSmallAltOrL2 Y)
    (hZ : center Y = ⊥) : HasCommProp Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hasCommProp_of hZ (hasOuterChar_of_small h) ?_
  rcases h with ⟨n, hn, ⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · rcases hn with rfl | rfl | rfl
    · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_five_of_alternating_five Y ⟨e⟩
      exact sylowCond_psl2 (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
        Nat.prime_five (by decide) le_rfl hK
    · obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
        LocalAnalysis.ComponentInitial.statedClassicalModel_psl_two_nine_of_alternating_six Y ⟨e⟩
      exact sylowCond_psl2 (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
        Nat.prime_three (by decide) (by norm_num) hK
    · intro T
      obtain ⟨m, hm, ⟨φ⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_of_mulEquiv e
        hasDihedralSylowTwo_alternatingGroupSeven T
      refine Or.inl ⟨m, ?_, ⟨φ⟩⟩
      by_contra hm2
      obtain rfl : m = 1 := by omega
      have h4 : Nat.card (T : Subgroup Y) = 4 := by
        rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card]
        norm_num
      have h8 : 2 ^ 3 ∣ Nat.card Y := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      have h8T : 2 ^ 3 ∣ Nat.card (T : Subgroup Y) := T.pow_dvd_card_of_pow_dvd_card h8
      rw [h4] at h8T
      exact absurd h8T (by decide)
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
    exact sylowCond_psl2 e hp (hp.odd_of_ne_two hp2) hf hF

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem sAct_mem_map_conj (s : h.S) (hs : (s : H) ∈ h.D ⊔ h.P) :
    sAct h s ∈ ((h.D.subgroupOf h.J).map (QuotientGroup.mk' (pPrimeCore 2 h.J))).map
      (MulAut.conj : OddBar h.J →* MulAut (OddBar h.J)) := by
  have hDS : h.D ≤ h.S := inf_le_left
  have hPS : h.P ≤ h.S := inf_le_left
  have hle : (h.D ⊔ h.P).subgroupOf h.S ≤
      (((h.D.subgroupOf h.J).map (QuotientGroup.mk' (pPrimeCore 2 h.J))).map
        (MulAut.conj : OddBar h.J →* MulAut (OddBar h.J))).comap (sAct h) := by
    rw [subgroupOf_sup hDS hPS]
    refine sup_le (fun d hd => ?_) (fun p hp => ?_)
    · rw [mem_subgroupOf] at hd
      rw [mem_comap, sAct_of_mem_J h d hd.2]
      exact ⟨_, ⟨⟨d, hd.2⟩, mem_subgroupOf.2 hd, rfl⟩, rfl⟩
    · rw [mem_subgroupOf] at hp
      rw [mem_comap, (sAct_eq_one_iff h p).2 hp]
      exact one_mem _
  exact hle (mem_subgroupOf.2 hs)

omit [Finite H] in
theorem eq_one_of_mem_pPrimeCore {L : Subgroup H} [Finite L] {g : L} (hg : g ∈ pPrimeCore 2 L)
    {k : ℕ} (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (orderOf g) := by
    rw [← Subgroup.orderOf_mk g hg]
    exact (pPrimeCore_coprime_card (p := 2) (G := L)).coprime_dvd_right (orderOf_dvd_natCard _)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hcop)
    (orderOf_dvd_of_pow_eq_one hk) dvd_rfl)

theorem cfAutSmallCommutator : CFAutSmallCommutator := by
  intro H _ _ h hsmall hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Tb, hTb⟩ := exists_sylow_Dbar h
  have hX2 : IsPGroup 2 (sAct h).range :=
    (isPGroup_S h).of_surjective (sAct h).rangeRestrict (sAct h).rangeRestrict_surjective
  have hinnX : ∀ σ ∈ (sAct h).range,
      σ ∈ (MulAut.conj : OddBar h.J →* MulAut (OddBar h.J)).range →
        ∃ t ∈ (Tb : Subgroup (OddBar h.J)), σ = MulAut.conj t := by
    rintro _ ⟨s, rfl⟩ hinn
    obtain ⟨x, hx, hxe⟩ := sAct_mem_map_conj h s ((mem_D_sup_P_iff_inner h hZ s).1 hinn)
    exact ⟨x, by rw [hTb]; exact hx, hxe.symm⟩
  have hTX : ∀ t ∈ (Tb : Subgroup (OddBar h.J)), MulAut.conj t ∈ (sAct h).range := by
    intro t ht
    rw [hTb] at ht
    obtain ⟨d, hd, rfl⟩ := mem_map.1 ht
    rw [mem_subgroupOf] at hd
    exact ⟨⟨d, hd.1⟩, sAct_of_mem_J h ⟨d, hd.1⟩ d.2⟩
  obtain ⟨t, ht, hσt, hcomm⟩ := hasCommProp_of_small hsmall hZ Tb _ hX2 hinnX hTX
  rw [hTb] at ht
  obtain ⟨d₀, hd₀, rfl⟩ := mem_map.1 ht
  rw [mem_subgroupOf] at hd₀
  have hdS : (d₀ : H) ∈ h.S := hd₀.1
  refine ⟨d₀, hd₀, fun s hs => ?_, ?_⟩
  ·
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hσt (sAct h ⟨s, hs⟩) ⟨⟨s, hs⟩, rfl⟩)
    have hsd : s * d₀ * s⁻¹ ∈ h.J := (mem_normalizer_iff.1 (hyp_S_le_N h hs) d₀).1 d₀.2
    have hk' : QuotientGroup.mk' (pPrimeCore 2 h.J) (d₀ ^ k) =
        QuotientGroup.mk' (pPrimeCore 2 h.J) ⟨s * d₀ * s⁻¹, hsd⟩ := by
      rw [map_zpow, hk]
      rfl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
    have hwS : (((d₀ ^ k)⁻¹ * ⟨s * d₀ * s⁻¹, hsd⟩ : h.J) : H) ∈ h.S := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      exact h.S.mul_mem (h.S.inv_mem (h.S.zpow_mem hdS k))
        (h.S.mul_mem (h.S.mul_mem hs hdS) (h.S.inv_mem hs))
    obtain ⟨n, hn⟩ := isPGroup_S h ⟨_, hwS⟩
    have hn' : ((d₀ ^ k)⁻¹ * ⟨s * d₀ * s⁻¹, hsd⟩ : h.J) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact this
    have h1 := eq_one_of_mem_pPrimeCore hk' hn'
    have h2 : (⟨s * d₀ * s⁻¹, hsd⟩ : h.J) = d₀ ^ k := (inv_mul_eq_one.1 h1).symm
    have h3 : s * d₀ * s⁻¹ = (d₀ : H) ^ k := by
      have := congrArg Subtype.val h2
      rwa [Subgroup.coe_zpow] at this
    rw [h3]
    exact zpow_mem (mem_zpowers _) k
  ·
    rw [commutator_le]
    intro s₁ h₁ s₂ h₂
    have hc := hcomm (sAct h ⟨s₁, h₁⟩) ⟨_, rfl⟩ (sAct h ⟨s₂, h₂⟩) ⟨_, rfl⟩
    rw [← map_commutatorElement] at hc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hc
    have h1 : sAct h (⟨d₀, hdS⟩ ^ k) =
        MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 h.J) d₀) ^ k :=
      (map_zpow (sAct h) _ k).trans (congrArg (· ^ k) (sAct_of_mem_J h ⟨d₀, hdS⟩ d₀.2))
    have h2 : sAct h ((⟨d₀, hdS⟩ ^ k)⁻¹ * ⁅(⟨s₁, h₁⟩ : h.S), ⟨s₂, h₂⟩⁆) = 1 := by
      rw [map_mul, map_inv, h1, hk, inv_mul_cancel]
    have hP := (sAct_eq_one_iff h _).1 h2
    have hcoe : ((((⟨d₀, hdS⟩ : h.S) ^ k)⁻¹ * ⁅(⟨s₁, h₁⟩ : h.S), ⟨s₂, h₂⟩⁆ : h.S) : H) =
        ((d₀ : H) ^ k)⁻¹ * ⁅s₁, s₂⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    have heq : ⁅s₁, s₂⁆ = (d₀ : H) ^ k *
        ((((⟨d₀, hdS⟩ : h.S) ^ k)⁻¹ * ⁅(⟨s₁, h₁⟩ : h.S), ⟨s₂, h₂⟩⁆ : h.S) : H) := by
      rw [hcoe, mul_inv_cancel_left]
    rw [heq]
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) k)) (mem_sup_right hP)

end CFSG.ComponentClassification.CatFactsSmall
