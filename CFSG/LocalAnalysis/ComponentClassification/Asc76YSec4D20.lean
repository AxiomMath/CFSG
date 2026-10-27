module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D19
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D18

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_isBarOf (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K L T₁ T₂ : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) (h₁ : IsSylowOf 2 T₁ K)
    (h₂ : IsSylowOf 2 T₂ L) (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G))
    (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G)) {d : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d) (hd₂ : IsBarOf (sec4W Ω S) T₂ d) : K = L := by
  by_contra hKL
  rcases eq_or_dAdj_of_commute H hS hK hL h₁ h₂ hT₁W hT₂W hd₁ hd₂ rfl with h | ⟨-, -, hLK, hKL'⟩
  · exact hKL h
  set W := sec4W Ω S with hWdef
  obtain ⟨U₁, hU₁, r, hrT, hrU, hrd⟩ := hd₁
  obtain ⟨U₂, -, r', hr'T, -, hr'd⟩ := hd₂
  have hU₁W : U₁ ≤ W := rot_le_sec4W H.hΩ hS hK h₁ hU₁ hT₁W
  have hc : (r : G)⁻¹ * r' ∈ centralizer (W : Set G) := by
    have h1 : (r : NBar W) = (r' : NBar W) := hrd.symm.trans hr'd
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    simpa using h1
  have hbot : (L ⊓ K) ⊓ W = ⊥ :=
    eq_bot_of_isPGroup_of_odd ((sec4W_isPGroup hS).to_le inf_le_right)
      ((H.hΩ.inter L hL K hK (Ne.symm hKL)).of_dvd_nat (card_dvd_of_le inf_le_left))
  have hcent : ∀ u ∈ U₁, (r' : G) * u * (r' : G)⁻¹ = u := by
    intro u hu
    have huK : u ∈ K := h₁.le (hU₁.le hu)
    have h1 := L26.commutatorElement_mem_inf (h₂.le hr'T) huK (hLK (h₂.le hr'T)) (hKL' huK)
    have h2 : (r' : G) * u * (r' : G)⁻¹ * u⁻¹ ∈ W :=
      mul_mem ((mem_normalizer_iff.mp r'.2 u).mp (hU₁W hu)) (inv_mem (hU₁W hu))
    have h3 := mem_inf.mpr ⟨h1, h2⟩
    rw [hbot, mem_bot] at h3
    calc (r' : G) * u * (r' : G)⁻¹ = (r' : G) * u * (r' : G)⁻¹ * u⁻¹ * u := by group
      _ = u := by rw [h3, one_mul]
  obtain ⟨ρ, hρ, hρo⟩ := hU₁.exists_gen
  have hρU : ρ ∈ U₁ := hρ ▸ mem_zpowers ρ
  apply hU₁.gen_mul_self_ne_one hρo
  set c := (r : G)⁻¹ * r' with hcdef
  have hcρ : ρ * c = c * ρ := mem_centralizer_iff.mp hc ρ (hU₁W hρU)
  have h1 : (r' : G) * ρ * (r' : G)⁻¹ = ρ⁻¹ := by
    have e : (r' : G) = r * c := by rw [hcdef]; group
    have hcρ' : c * ρ * c⁻¹ = ρ := by rw [← hcρ]; group
    calc (r' : G) * ρ * (r' : G)⁻¹ = r * (c * ρ * c⁻¹) * (r : G)⁻¹ := by rw [e]; group
      _ = ρ⁻¹ := by rw [hcρ', hU₁.conj_eq r hrT hrU ρ hρU]
  have h2 : ρ⁻¹ = ρ := h1.symm.trans (hcent ρ hρU)
  calc ρ * ρ = ρ * ρ⁻¹ := by rw [h2]
    _ = 1 := mul_inv_cancel ρ

theorem MinCounter.mem_dComp_iff (h22 : Asc76Lemma22) {S : Subgroup G} (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hRW : R ≤ normalizer (sec4W Ω S : Set G))
    {r : NBar (sec4W Ω S)} (hr : IsBarOf (sec4W Ω S) R r) {L : Subgroup G} :
    L ∈ dComp Ω K ↔ L ∈ Ω ∧ ∃ T : Subgroup G, ∃ d : NBar (sec4W Ω S), IsSylowOf 2 T L ∧
      T ≤ normalizer (sec4W Ω S : Set G) ∧ IsBarOf (sec4W Ω S) T d ∧ r * d = d * r := by
  have H : Sec4Hyp Ω := ⟨h22, hM.assumption, hM.twoNil⟩
  have hS := hM.sylow
  have hΩne : Ω.Nonempty := ⟨K, hK⟩
  have hrD := IsBarOf.mem_dBar (⟨⟨K, hK, hR⟩, hRW⟩ : R ∈ DSet Ω (sec4W Ω S)) hr
  constructor
  · intro hL
    induction hL with
    | refl => exact ⟨hK, R, r, hR, hRW, hr, rfl⟩
    | @tail b c _ hab ih =>
      obtain ⟨hbΩ, T, d, hT, hTW, hd, hrd⟩ := ih
      have hcΩ := hab.2.1
      obtain ⟨-, T', hT', hT'W⟩ := hM.mem_omegaD_of_le_normalizer ⟨hbΩ, T, hT, hTW⟩ hcΩ hab.2.2.1
      have hT'D : T' ∈ DSet Ω (sec4W Ω S) := ⟨⟨c, hcΩ, hT'⟩, hT'W⟩
      obtain ⟨d', hd'⟩ := IsBarOf.exists_of_mem H.hΩ hT'D
      refine ⟨hcΩ, T', d', hT', hT'W, hd', ?_⟩
      have hdd' : d * d' = d' * d := by
        by_cases hbc : b = c
        · subst hbc
          rw [bar_eq_of_same H hS hbΩ hT hT' hTW hT'W hd hd']
        · exact bar_commute_of_sylow H hS hbΩ hcΩ hbc hT hT' hTW hab.2.2.1 hab.2.2.2 hd hd'
      have hdD := IsBarOf.mem_dBar (⟨⟨b, hbΩ, hT⟩, hTW⟩ : T ∈ DSet Ω (sec4W Ω S)) hd
      exact DBar.commute_trans H hS hΩne hdis hrD hdD (IsBarOf.mem_dBar hT'D hd') hrd hdd'
  · rintro ⟨hLΩ, T, d, hT, hTW, hd, hrd⟩
    rcases eq_or_dAdj_of_commute H hS hK hLΩ hR hT hRW hTW hr hd hrd with h | h
    · rw [← h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h

theorem MinCounter.eq_or_dAdj_of_mem_dComp (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hRW : R ≤ normalizer (sec4W Ω S : Set G)) {L L' : Subgroup G} (hL : L ∈ dComp Ω K)
    (hL' : L' ∈ dComp Ω K) : L = L' ∨ DAdj Ω L L' := by
  have H : Sec4Hyp Ω := ⟨h22, hM.assumption, hM.twoNil⟩
  have hRD : R ∈ DSet Ω (sec4W Ω S) := ⟨⟨K, hK, hR⟩, hRW⟩
  obtain ⟨r, hr⟩ := IsBarOf.exists_of_mem H.hΩ hRD
  obtain ⟨hLΩ, T, d, hT, hTW, hd, hrd⟩ := (hM.mem_dComp_iff h22 hdis hK hR hRW hr).mp hL
  obtain ⟨hL'Ω, T', d', hT', hT'W, hd', hrd'⟩ := (hM.mem_dComp_iff h22 hdis hK hR hRW hr).mp hL'
  have hdd' : d * d' = d' * d :=
    DBar.commute_trans H hM.sylow ⟨K, hK⟩ hdis
      (IsBarOf.mem_dBar (⟨⟨L, hLΩ, hT⟩, hTW⟩ : T ∈ DSet Ω (sec4W Ω S)) hd)
      (IsBarOf.mem_dBar hRD hr)
      (IsBarOf.mem_dBar (⟨⟨L', hL'Ω, hT'⟩, hT'W⟩ : T' ∈ DSet Ω (sec4W Ω S)) hd') hrd.symm hrd'
  exact eq_or_dAdj_of_commute H hM.sylow hLΩ hL'Ω hT hT' hTW hT'W hd hd' hdd'

theorem exists_oddCoreIn_eq_rightConjugate {K R R' : Subgroup G} (hR : IsSylowOf 2 R K)
    (hR' : IsSylowOf 2 R' K) (hnil : IsTwoNil K R') :
    ∃ o ∈ oddCoreIn K, R = AschbacherTightEmbedding.rightConjugate R' o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkR⟩ := L26.IsSylowOf.exists_conj_mem hR' hR
  obtain ⟨o, ho, r, hr, rfl⟩ := hnil k hk
  refine ⟨o⁻¹, inv_mem ho, ?_⟩
  ext x
  rw [hkR, mem_rightConjugate_iff, inv_inv]
  constructor
  · intro h
    have := mul_mem (mul_mem hr h) (inv_mem hr)
    have e : r * ((o * r)⁻¹ * x * (o * r)) * r⁻¹ = o⁻¹ * x * o := by group
    rwa [e] at this
  · intro h
    have := mul_mem (mul_mem (inv_mem hr) h) hr
    have e : r⁻¹ * (o⁻¹ * x * o) * r = (o * r)⁻¹ * x * (o * r) := by group
    rwa [e] at this

theorem conj_rightConjugate_of_normalizes {K R' : Subgroup G} (hR' : IsSylowOf 2 R' K) {o t : G}
    (ho : o ∈ oddCoreIn K) (htK : t ∈ normalizer (K : Set G))
    (htR' : t ∈ normalizer (R' : Set G))
    (htR : t ∈ normalizer (AschbacherTightEmbedding.rightConjugate R' o : Set G)) {u : G}
    (hu : u ∈ R') (htu : t * u * t⁻¹ = u) : t * (o⁻¹ * u * o) * t⁻¹ = o⁻¹ * u * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := o * t * o⁻¹ * t⁻¹ with hcdef
  have hcO : c ∈ oddCoreIn K := by
    have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreIn K :=
      (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn K htK) _).mp (inv_mem ho)
    have e : c = o * (t * o⁻¹ * t⁻¹) := by rw [hcdef]; group
    rw [e]
    exact mul_mem ho h1
  have hcR : ∀ y ∈ R', c * y * c⁻¹ ∈ R' := by
    intro y hy
    have h1 : t⁻¹ * y * t⁻¹⁻¹ ∈ R' := (mem_normalizer_iff.mp (inv_mem htR') y).mp hy
    have h2 : o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o ∈ AschbacherTightEmbedding.rightConjugate R' o := by
      rw [mem_rightConjugate_iff]
      have e : o * (o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o) * o⁻¹ = t⁻¹ * y * t⁻¹⁻¹ := by group
      rw [e]
      exact h1
    have h3 := (mem_normalizer_iff.mp htR _).mp h2
    rw [mem_rightConjugate_iff] at h3
    have e : o * (t * (o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o) * t⁻¹) * o⁻¹ = c * y * c⁻¹ := by
      rw [hcdef]; group
    rwa [e] at h3
  have hbot : R' ⊓ oddCoreIn K = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hR'.isPGroup.to_le inf_le_left)
      ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_right))
  have hcu : c * u = u * c := by
    have h1 : c * u * c⁻¹ * u⁻¹ ∈ R' ⊓ oddCoreIn K := by
      refine mem_inf.mpr ⟨mul_mem (hcR u hu) (inv_mem hu), ?_⟩
      have h2 : u * c⁻¹ * u⁻¹ ∈ oddCoreIn K :=
        (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K (hR'.le hu)) _).mp (inv_mem hcO)
      have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [e]
      exact mul_mem hcO h2
    rw [hbot, mem_bot] at h1
    calc c * u = c * u * c⁻¹ * u⁻¹ * (u * c) := by group
      _ = u * c := by rw [h1, one_mul]
  calc t * (o⁻¹ * u * o) * t⁻¹ = o⁻¹ * c * (t * u * t⁻¹) * c⁻¹ * o := by rw [hcdef]; group
    _ = o⁻¹ * (c * u) * c⁻¹ * o := by rw [htu]; group
    _ = o⁻¹ * u * o := by rw [hcu]; group

theorem exists_oddCoreIn_conj_eq_of_isDihedralRot {K T₀ V₀ T V : Subgroup G}
    (hT₀ : IsSylowOf 2 T₀ K) (hV₀ : IsDihedralRot V₀ T₀) (hT : IsSylowOf 2 T K)
    (hV : IsDihedralRot V T) (hnil : IsTwoNil K T) {t z : G} (htV : t ∈ V₀) (ht1 : t ≠ 1)
    (htt : t * t = 1) (hzV : z ∈ V) (hz1 : z ≠ 1) (hzz : z * z = 1) :
    ∃ o ∈ oddCoreIn K, t = o⁻¹ * z * o := by
  obtain ⟨o, ho, hT₀eq⟩ := exists_oddCoreIn_eq_rightConjugate hT₀ hT hnil
  refine ⟨o, ho, ?_⟩
  have hV' := hV.rightConjugate o
  rw [← hT₀eq] at hV'
  have hVeq : AschbacherTightEmbedding.rightConjugate V o = V₀ :=
    hV₀.eq_of_isCyclic hV'.le hV'.isCyclic hV'.relIndex_eq
  obtain ⟨z₀, -, -, -, huniq, -⟩ := hV₀.exists_involution
  have h1 : o⁻¹ * z * o ∈ V₀ := hVeq ▸ conj_mem_rightConjugate hzV o
  have h2 : o⁻¹ * z * o * (o⁻¹ * z * o) = 1 := by
    calc o⁻¹ * z * o * (o⁻¹ * z * o) = o⁻¹ * (z * z) * o := by group
      _ = 1 := by rw [hzz]; group
  have h3 : o⁻¹ * z * o ≠ 1 := by
    intro h
    apply hz1
    calc z = o * (o⁻¹ * z * o) * o⁻¹ := by group
      _ = 1 := by rw [h]; group
  rw [(huniq t htV htt).resolve_left ht1, (huniq _ h1 h2).resolve_left h3]

omit [Finite G] in
theorem exists_conj_eq_mul_of_odd {c y : G} (hyy : y * y = 1) (hc : Odd (orderOf c))
    (hcy : c * y * (c * y) = 1) : ∃ d : G, d * y * d⁻¹ = c * y := by
  obtain ⟨m, hm⟩ := hc
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyc : y * c * y⁻¹ = c⁻¹ := by
    rw [hyinv]
    calc y * c * y = c⁻¹ * (c * y * (c * y)) := by group
      _ = c⁻¹ := by rw [hcy, mul_one]
  set d := c ^ (m + 1) with hddef
  have hyd : y * d * y⁻¹ = d⁻¹ := by
    rw [hddef, ← conj_pow, hyc, inv_pow]
  have hdd : d * d = c := by
    rw [hddef, ← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  refine ⟨d, ?_⟩
  have hyd' : y * d⁻¹ * y⁻¹ = d := by
    have : y * d⁻¹ * y⁻¹ = (y * d * y⁻¹)⁻¹ := by group
    rw [this, hyd, inv_inv]
  calc d * y * d⁻¹ = d * (y * d⁻¹ * y⁻¹) * y := by group
    _ = d * d * y := by rw [hyd']
    _ = c * y := by rw [hdd]

end CFSG.ComponentClassification.Asc76.Sec4
