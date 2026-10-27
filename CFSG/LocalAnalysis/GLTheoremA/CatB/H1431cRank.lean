module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY rank_le_twoLocal_of_normalizes_pre)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Pre mem_c25Pre c25_mem_normalizer_pre
  c25_isElemAbelian_sup_zpowers c25_exists_elemAbelian_lift_hom c25_isPGroup_of_elemAbelian
  c25_isElemAbelian_map fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.LocalAnalysis.GLTheoremA (pQuotHom map_fixSubgroup_pQuotHom fixSubgroup_normalizerMonoidHom
  chev_barAut_eq_one_iff_centMod i1431_isElemAbelian_zpowers coprime_card_inf_ker_pQuotHom
  chev_coe_normalizerMonoidHom)

variable {G : Type} [Group G] [Finite G]

theorem fixSubgroup_one_eq_top {Y : Type} [Group Y] : fixSubgroup (1 : MulAut Y) = ⊤ := by
  ext y
  simp [mem_fixSubgroup]

theorem map_fixSubgroup_eq_top {K : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G))
    (hcK : CentMod 3 K c) (hc3 : IsPGroup 3 (Subgroup.zpowers c)) :
    (fixSubgroup (K.normalizerMonoidHom ⟨c, hc⟩)).map (pQuotHom 3 K) = ⊤ := by
  rw [map_fixSubgroup_pQuotHom Nat.prime_three hc hc3,
    (chev_barAut_eq_one_iff_centMod (p := 3) hc).2 hcK, fixSubgroup_one_eq_top]

theorem mk_conj_eq {K : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G))
    (hcK : CentMod 3 K c) (x : ↥K) :
    (QuotientGroup.mk (K.normalizerMonoidHom ⟨c, hc⟩ x) : PQuot 3 K) = QuotientGroup.mk x := by
  have h1 := barAut_mk 3 K ⟨c, hc⟩ x
  rw [(chev_barAut_eq_one_iff_centMod (p := 3) hc).2 hcK, MulAut.one_apply] at h1
  exact h1.symm

theorem subgroupOf_map_subtype_eq {K : Subgroup G} (S₁ : Subgroup ↥K) :
    (S₁.map K.subtype).subgroupOf K = S₁ := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  · intro hx
    exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩

theorem exists_lift_centralized {K : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (K : Set G))
    (hcK : CentMod 3 K c) (hc3 : c ^ 3 = 1) {E : Subgroup (PQuot 3 K)} (hE : IsElemAbelian 3 E) :
    ∃ S : Subgroup G, S ≤ K ∧ S ≤ Subgroup.centralizer ({c} : Set G) ∧ IsElemAbelian 3 S ∧
      Nat.card S = Nat.card E ∧ (S.subgroupOf K).map (pQuotHom 3 K) = E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : IsPGroup 3 (Subgroup.zpowers c) :=
    c25_isPGroup_of_elemAbelian (i1431_isElemAbelian_zpowers hc3)
  set F : Subgroup K := fixSubgroup (K.normalizerMonoidHom ⟨c, hc⟩) with hF
  set f : ↥F →* PQuot 3 K := (pQuotHom 3 K).comp F.subtype with hf
  have hsurj : Function.Surjective f := by
    intro q
    have hq : q ∈ F.map (pQuotHom 3 K) := by
      rw [map_fixSubgroup_eq_top hc hcK hc3']
      exact Subgroup.mem_top q
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    have h1 : Nat.card (f.ker.map F.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective F.subtype_injective
    have h2 : f.ker.map F.subtype = F ⊓ (pQuotHom 3 K).ker := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, by simpa [hf] using hy⟩
      · rintro ⟨hxF, hxk⟩
        exact ⟨⟨x, hxF⟩, by simpa [hf] using hxk, rfl⟩
    have h3 := coprime_card_inf_ker_pQuotHom Nat.prime_three K F
    rw [← h1, h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 h3
  obtain ⟨S', hS'el, hS'map, hS'card⟩ := c25_exists_elemAbelian_lift_hom f hsurj hker hE
  set S₁ : Subgroup K := S'.map F.subtype with hS₁
  set S : Subgroup G := S₁.map K.subtype with hS
  have hS₁el : IsElemAbelian 3 S₁ := c25_isElemAbelian_map F.subtype hS'el
  have hSel : IsElemAbelian 3 S := c25_isElemAbelian_map K.subtype hS₁el
  refine ⟨S, ?_, ?_, hSel, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have h2 : (y : K) ∈ (K ⊓ Subgroup.centralizer ({c} : Set G)).subgroupOf K := by
      rw [← fixSubgroup_normalizerMonoidHom hc]
      exact y.2
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 h2)).2
  · rw [hS, Subgroup.card_map_of_injective K.subtype_injective, hS₁,
      Subgroup.card_map_of_injective F.subtype_injective, hS'card]
  · rw [subgroupOf_map_subtype_eq, hS₁, Subgroup.map_map]
    exact hS'map

theorem rkY_of_centMod {K B : Subgroup G} (hrk : GLATwoLocalRank 3 ↥(K ⊔ B) ≤ 4)
    (hB : IsElemAbelian 3 B) {c : G} (hcB : c ∈ B) (hc1 : c ≠ 1) (hcK : CentMod 3 K c) :
    RkY (PQuot 3 K) := by
  intro U hU hU2 E hEN hE
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hcN : c ∈ Subgroup.normalizer (K : Set G) := hcK.1
  obtain ⟨S, hSK, hSC, hSel, hScard, hSmap⟩ := exists_lift_centralized hcN hcK hc3 hE
  have hmemE : ∀ s (hs : s ∈ S), (QuotientGroup.mk ⟨s, hSK hs⟩ : PQuot 3 K) ∈ E := by
    intro s hs
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem (pQuotHom 3 K) (Subgroup.mem_subgroupOf.2 hs)
  have hcS : c ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hSC hs
    rw [Subgroup.mem_centralizer_iff] at h1
    exact (h1 c (Set.mem_singleton c)).symm
  have hTel : IsElemAbelian 3 (Subgroup.zpowers c ⊔ S) := c25_isElemAbelian_sup_zpowers hSel hc3 hcS
  obtain ⟨j, hj⟩ := (c25_isPGroup_of_elemAbelian hTel).exists_card_eq
  have hTX : Subgroup.zpowers c ⊔ S ≤ K ⊔ B :=
    sup_le (by rw [Subgroup.zpowers_le]; exact (le_sup_right : B ≤ K ⊔ B) hcB)
      (hSK.trans le_sup_left)
  have hconj : ∀ x : ↥K, ((K.normalizerMonoidHom ⟨c, hcN⟩ x : ↥K) : G) = c * (x : G) * c⁻¹ :=
    fun x => chev_coe_normalizerMonoidHom ⟨c, hcN⟩ x
  have hPc : c ∈ Subgroup.normalizer (c25Pre K U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨hgK, hgU⟩ := mem_c25Pre.1 hg
      have hy : c * g * c⁻¹ ∈ K := by
        have h0 := (K.normalizerMonoidHom ⟨c, hcN⟩ ⟨g, hgK⟩).2
        rw [hconj] at h0
        exact h0
      refine mem_c25Pre.2 ⟨hy, ?_⟩
      have h1 := mk_conj_eq hcN hcK ⟨g, hgK⟩
      have h3 : (QuotientGroup.mk ⟨c * g * c⁻¹, hy⟩ : PQuot 3 K) =
          QuotientGroup.mk (K.normalizerMonoidHom ⟨c, hcN⟩ ⟨g, hgK⟩) :=
        congrArg QuotientGroup.mk (Subtype.ext (hconj ⟨g, hgK⟩).symm)
      rw [h3, h1]
      exact hgU
    · intro hg
      obtain ⟨hcgK, hcgU⟩ := mem_c25Pre.1 hg
      have hgK : g ∈ K := (Subgroup.mem_normalizer_iff.1 hcN g).2 hcgK
      refine mem_c25Pre.2 ⟨hgK, ?_⟩
      have h1 := mk_conj_eq hcN hcK ⟨g, hgK⟩
      have h3 : K.normalizerMonoidHom ⟨c, hcN⟩ ⟨g, hgK⟩ = ⟨c * g * c⁻¹, hcgK⟩ :=
        Subtype.ext (hconj _)
      rw [← h1, h3]
      exact hcgU
  have hTN : Subgroup.zpowers c ⊔ S ≤ Subgroup.normalizer (c25Pre K U : Set G) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact hPc
    · intro s hs
      exact c25_mem_normalizer_pre (hSK hs) (hEN (hmemE s hs))
  have hj4 : j ≤ 4 :=
    (rank_le_twoLocal_of_normalizes_pre (le_sup_left : K ≤ K ⊔ B) hU hU2 hTel hTX hTN hj).trans hrk
  obtain ⟨m, hm⟩ := (c25_isPGroup_of_elemAbelian hSel).exists_card_eq
  have hmj : m ≤ j := by
    have h1 := Subgroup.card_dvd_of_le (le_sup_right : S ≤ Subgroup.zpowers c ⊔ S)
    rw [hm, hj] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h1
  refine ⟨?_, fun hEZ => ?_⟩
  · rw [← hScard, hm]
    exact Nat.pow_le_pow_right (by norm_num) (hmj.trans hj4)
  ·
    have hcS' : c ∉ S := by
      intro hcSG
      have hcK' : c ∈ K := hSK hcSG
      set cK : ↥K := ⟨c, hcK'⟩ with hcKdef
      have hmcE : (QuotientGroup.mk cK : PQuot 3 K) ∈ E := hmemE c hcSG
      have hcomm : ∀ x : ↥K, (QuotientGroup.mk cK : PQuot 3 K) * QuotientGroup.mk x =
          QuotientGroup.mk x * QuotientGroup.mk cK := by
        intro x
        have h1 := mk_conj_eq hcN hcK x
        have h2 : (QuotientGroup.mk (cK * x * cK⁻¹ : ↥K) : PQuot 3 K) =
            QuotientGroup.mk (K.normalizerMonoidHom ⟨c, hcN⟩ x) :=
          congrArg QuotientGroup.mk (Subtype.ext (by rw [hconj x]; simp [hcKdef, mul_assoc]))
        have h3 : (QuotientGroup.mk (cK * x * cK⁻¹ : ↥K) : PQuot 3 K) =
            QuotientGroup.mk cK * QuotientGroup.mk x * (QuotientGroup.mk cK)⁻¹ := by
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [h3, h1] at h2
        calc (QuotientGroup.mk cK : PQuot 3 K) * QuotientGroup.mk x
            = (QuotientGroup.mk cK * QuotientGroup.mk x * (QuotientGroup.mk cK)⁻¹) *
                QuotientGroup.mk cK := by group
          _ = QuotientGroup.mk x * QuotientGroup.mk cK := by rw [h2]
      have hmcZ : (QuotientGroup.mk cK : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
        exact (hcomm x).symm
      have hz : (QuotientGroup.mk cK : PQuot 3 K) ∈ E ⊓ Subgroup.center (PQuot 3 K) :=
        ⟨hmcE, hmcZ⟩
      rw [hEZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz
      have hcop : Nat.Coprime 3 (orderOf cK) := by
        have hle : Subgroup.zpowers cK ≤ GLAPPrimeCore 3 ↥K := Subgroup.zpowers_le.2 hz
        have hd : Nat.card (Subgroup.zpowers cK) ∣ Nat.card (GLAPPrimeCore 3 ↥K) :=
          Subgroup.card_dvd_of_le hle
        rw [Nat.card_zpowers] at hd
        exact Nat.Coprime.coprime_dvd_right hd (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K))
      have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have hoc : orderOf cK = orderOf c := (Subgroup.orderOf_coe cK).symm.trans rfl
      rw [← hoc] at hord
      rcases (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hord) with h1 | h1
      · exact hc1 (orderOf_eq_one_iff.1 (by rw [← hoc]; exact h1))
      · rw [h1] at hcop
        exact absurd hcop (by norm_num)
    have hST : S < Subgroup.zpowers c ⊔ S := by
      refine lt_of_le_of_ne le_sup_right ?_
      intro h
      exact hcS' (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
    have hlt := Subgroup.card_lt_of_lt hST
    rw [hm, hj] at hlt
    have hmj' : m < j := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
    rw [← hScard, hm]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
