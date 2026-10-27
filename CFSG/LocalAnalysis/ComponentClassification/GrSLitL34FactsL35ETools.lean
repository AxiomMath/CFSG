module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ESL2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECArith
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts
open scoped commutatorElement

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

@[expose] noncomputable def theta (h : Config G p w v L K) : ↥L →* ↥K ⧸ pPrimeCore 2 ↥K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion h.L_le)

theorem theta_apply (h : Config G p w v L K) (x : ↥L) :
    h.theta x = QuotientGroup.mk (⟨x, h.L_le x.2⟩ : ↥K) := rfl

theorem tau_theta (h : Config G p w v L K) (x : ↥L) : h.tau (h.theta x) = h.theta x := by
  have hxv : (x : G) * v = v * x := mem_centralizer_singleton_iff.mp (h.compL.1 x.2).2
  rw [theta_apply]
  change oddAut h.beta (QuotientGroup.mk _) = _
  rw [oddAut_mk]
  congr 1
  apply Subtype.ext
  rw [h.beta_apply]
  calc v * (x : G) * v⁻¹ = (x : G) * v * v⁻¹ := by rw [hxv]
    _ = x := by group

theorem mem_pPrimeCore_of_theta (h : Config G p w v L K) {x : ↥L} (hx : h.theta x = 1) :
    x ∈ pPrimeCore 2 ↥L := by
  set N : Subgroup ↥L := (pPrimeCore 2 ↥K).comap (Subgroup.inclusion h.L_le) with hN
  have hNn : N.Normal := (inferInstance : (pPrimeCore 2 ↥K).Normal).comap _
  have hcop : Nat.Coprime 2 (Nat.card N) :=
    Nat.Coprime.coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective h.L_le))
      pPrimeCore_coprime_card
  refine le_pPrimeCore_of_normal_coprime hNn hcop ?_
  rw [hN, mem_comap]
  exact (QuotientGroup.eq_one_iff _).mp hx

theorem even_false_of_commute (h : Config G p w v L K) {k : ℕ} (hk : 1 ≤ k) (hs5 : 5 ≤ p ^ k)
    (hLsl : IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)) (Φ : ↥L →* Equiv.Perm (Fin 42))
    {C : Subgroup (Equiv.Perm (Fin 42))} (hCs : IsSimpleGroup C) (hC2 : 2 ∣ Nat.card C)
    (hrange : Φ.range = C) (hcardC : Nat.card C * 2 = p ^ k * ((p ^ k) ^ 2 - 1))
    {xL yL : ↥L} (hx2 : Φ xL * Φ xL = 1) (hy2 : Φ yL * Φ yL = 1) (hx1 : Φ xL ≠ 1)
    (hy1 : Φ yL ≠ 1) (hxy : Φ xL ≠ Φ yL) (hcomm : xL * yL * xL⁻¹ * yL⁻¹ ∈ pPrimeCore 2 ↥L) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hCs
  obtain ⟨hQq, hQZ, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  have hO : pPrimeCore 2 ↥L ≤ Φ.ker := by
    set M := (pPrimeCore 2 ↥L).map Φ with hM
    have hMC : M ≤ C := hrange ▸ map_le_range Φ _
    have hMn : (M.subgroupOf C).Normal := ⟨fun m hm c => by
      rw [mem_subgroupOf] at hm ⊢
      obtain ⟨o, ho, hoe⟩ := hm
      have hc : (c : Equiv.Perm (Fin 42)) ∈ Φ.range := hrange ▸ c.2
      obtain ⟨x, hx⟩ := hc
      refine ⟨x * o * x⁻¹, (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem o ho x, ?_⟩
      simp only [map_mul, map_inv, hx, hoe, Subgroup.coe_mul, Subgroup.coe_inv]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf C) with h0 | h1
    · rw [← Subgroup.map_eq_bot_iff]
      rw [subgroupOf_eq_bot] at h0
      exact eq_bot_iff.mpr fun m hm => (h0.le_bot ⟨hm, hMC hm⟩)
    · exfalso
      have hCM : C ≤ M := fun c hc => by
        have : (⟨c, hc⟩ : ↥C) ∈ M.subgroupOf C := h1 ▸ mem_top _
        exact this
      have hd : 2 ∣ Nat.card (pPrimeCore 2 ↥L) :=
        (hC2.trans (Subgroup.card_dvd_of_le hCM)).trans (Subgroup.card_map_dvd _ _)
      have := Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card hd
      omega
  set ψ := QuotientGroup.lift (pPrimeCore 2 ↥L) Φ hO with hψ
  have hψmk : ∀ x : ↥L, ψ (QuotientGroup.mk x) = Φ x := fun x => QuotientGroup.lift_mk _ _ _
  have hψrange : ψ.range = C := by
    rw [← hrange]
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      exact ⟨x, (hψmk x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, hψmk x⟩
  have hAcard : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = Nat.card C * 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥L ⧸ pPrimeCore 2 ↥L)), hQZ,
      EvenCover.card_mul_two_of_psl2 h.ne_two hQm, hcardC]
  have hQo : Open.IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    (AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQq)
  have hle : ψ.ker ≤ center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases Quasisimple.normal_le_center_or_eq_top hQo ψ.ker with hc | ht
    · exact hc
    · exfalso
      apply hx1
      rw [← hψmk]
      have : (QuotientGroup.mk xL : ↥L ⧸ pPrimeCore 2 ↥L) ∈ ψ.ker := ht ▸ mem_top _
      exact this
  have hkcard : Nat.card ψ.ker = 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hψrange, hAcard] at h1
    have hpos : 0 < Nat.card C := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm
  have hkeq : ψ.ker = center (↥L ⧸ pPrimeCore 2 ↥L) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQZ, hkcard])
  have hker : ∀ c, c ∈ center (↥L ⧸ pPrimeCore 2 ↥L) ↔ ψ c = 1 := fun c => by
    rw [← hkeq, MonoidHom.mem_ker]
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hLsl
  have hFodd : Odd (Fintype.card F) := hF ▸ (h.prime.odd_of_ne_two h.ne_two).pow
  have hinv : ∀ c : ↥L ⧸ pPrimeCore 2 ↥L, c ^ 2 = 1 → c ∈ center _ := fun c hc =>
    sl2_sq_eq_one_mem_center hFodd e hc
  refine false_of_commute_lifts hQZ hinv ψ hker (a := QuotientGroup.mk xL)
    (b := QuotientGroup.mk yL) (by rw [hψmk]; exact hx2) (by rw [hψmk]; exact hy2)
    (by rw [hψmk]; exact hx1) (by rw [hψmk]; exact hy1) (by rw [hψmk, hψmk]; exact hxy) ?_
  have h1 := (QuotientGroup.eq_one_iff (xL * yL * xL⁻¹ * yL⁻¹)).mpr hcomm
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  calc (QuotientGroup.mk xL : ↥L ⧸ pPrimeCore 2 ↥L) * QuotientGroup.mk yL
      = QuotientGroup.mk xL * QuotientGroup.mk yL * (QuotientGroup.mk xL)⁻¹ *
          (QuotientGroup.mk yL)⁻¹ * (QuotientGroup.mk yL * QuotientGroup.mk xL) := by group
    _ = QuotientGroup.mk yL * QuotientGroup.mk xL := by rw [h1, one_mul]

end Config

theorem commutatorElement_eq_of_map {Y : Type*} [Group Y]
    {q : Y →* Equiv.Perm (Fin 42)} (hqker : q.ker ≤ center Y)
    {l : LieType.Multipliers.L34.Cover →* Y}
    (hql : q.comp l = sigma) {y₁ y₂ : Y} {c₁ c₂ : LieType.Multipliers.L34.Cover}
    (h₁ : q y₁ = sigma c₁) (h₂ : q y₂ = sigma c₂) : ⁅y₁, y₂⁆ = l ⁅c₁, c₂⁆ := by
  have hlq : ∀ c, q (l c) = sigma c := fun c => by rw [← MonoidHom.comp_apply, hql]
  have hz : ∀ {y c}, q y = sigma c → (l c)⁻¹ * y ∈ center Y := fun {y c} hy =>
    hqker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hlq, hy, inv_mul_cancel])
  rw [show y₁ = l c₁ * ((l c₁)⁻¹ * y₁) by group, show y₂ = l c₂ * ((l c₂)⁻¹ * y₂) by group,
    CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hz h₁) (hz h₂),
    ← map_commutatorElement]

end CFSG.ComponentClassification.HarrisLit.L35
