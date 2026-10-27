module

public import CFSG.LocalAnalysis.ABGTheoremB.Statements
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.QuasiDihedralFusion.Transport
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open scoped Pointwise

universe u

section Thompson

variable {A B : Type*} [Group A] [Group B] (f : A →* B)

private theorem thompsonCenter_map_of_injective (hf : Function.Injective f) (P : Subgroup A) :
    (CFSG.thompsonCenter P).map f = CFSG.thompsonCenter (P.map f) :=
  CFSG.map_thompsonCenter_of_injective f P (hf.comp P.subtype_injective)

end Thompson

section General

variable {G : Type u} [Group G]

private theorem normalizer_le_normalizer_thompsonCenter_v2 (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (CFSG.thompsonCenter P : Set G) :=
  CFSG.normalizer_le_normalizer_thompsonCenter_of_bounded P

private theorem normalizer_le_normalizer_centralizer_v2 (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc r hr
    have hrn : n⁻¹ * r * n ∈ R := by
      have h := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (R : Set G)).inv_mem hn)
        r).mp hr
      simpa using h
    have h := hc _ hrn
    calc r * (n * c * n⁻¹) = n * ((n⁻¹ * r * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * r * n)) * n⁻¹ := by rw [h]
      _ = n * c * n⁻¹ * r := by group
  · intro hc r hr
    have hrn : n * r * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn r).mp hr
    have h := hc _ hrn
    calc r * c = n⁻¹ * ((n * r * n⁻¹) * (n * c * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * c * n⁻¹) * (n * r * n⁻¹)) * n := by rw [h]
      _ = c * r := by group

private theorem normalizer_le_normalizer_oddCoreIn_v2 [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : (oddCoreIn H).map (MulAut.conj g).toMonoidHom ≤ oddCoreIn H := by
    apply le_oddCoreIn
    · exact (Subgroup.map_mono (oddCoreIn_le H)).trans hg.le
    · rw [← Subgroup.map_equiv_normalizer_eq]
      exact hg.ge.trans (Subgroup.map_mono (le_normalizer_oddCoreIn H))
    · rw [Subgroup.card_map_of_injective hinj]
      exact odd_card_oddCoreIn H
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective hinj).ge

private theorem exists_isSylowOf_ge_v2 {p : ℕ} {Q K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K) : IsPGroup p (Q.subgroupOf K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, ?_⟩
  intro q hq
  exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.subgroupOf K from hq), rfl⟩

private theorem odd_card_of_isPGroup_v2 [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hX : IsPGroup r X) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem le_normalizer_pPrimeCoreIn_sup_thompsonCenter [Finite G] {r : ℕ}
    [Fact r.Prime] (hr2 : r ≠ 2) {H P : Subgroup G} (hcon : IsPConstrained r H)
    (hst : IsPStable r H) (hP : IsSylowOf r P H) :
    H ≤ Subgroup.normalizer ((pPrimeCoreIn r H ⊔ CFSG.thompsonCenter P : Subgroup G) :
      Set G) := by
  obtain ⟨Q, rfl⟩ := hP
  have hzj := zj_factorization hr2 hcon hst Q
  set K : Subgroup H := CFSG.pPrimeCore r H
  set Z : Subgroup H := CFSG.thompsonCenter (Q : Subgroup H)
  have hK : K.Normal := CFSG.pPrimeCore_normal
  have hnorm : (K ⊔ Z).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hzj]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) ?_
    have hle : Subgroup.normalizer (Z : Set H) ≤ Subgroup.normalizer (K : Set H) := by
      rw [Subgroup.normalizer_eq_top K]
      exact le_top
    exact (le_inf hle le_rfl).trans (normalizer_inf_normalizer_le_normalizer_sup K Z)
  have hmap : (K ⊔ Z).map H.subtype =
      pPrimeCoreIn r H ⊔ CFSG.thompsonCenter ((Q : Subgroup H).map H.subtype) := by
    rw [Subgroup.map_sup, thompsonCenter_map_of_injective H.subtype H.subtype_injective]
    rfl
  rw [← hmap]
  exact le_normalizer_map_subtype H (K ⊔ Z)

private theorem exists_sylow_normalizer_thompsonCenter_mem [Finite G] {r : ℕ} [Fact r.Prime]
    {𝓕 : Set (Subgroup G)} (hne : 𝓕.Nonempty)
    (hstep : ∀ H ∈ 𝓕, ∃ P : Subgroup G, IsSylowOf r P H ∧
      Subgroup.normalizer (CFSG.thompsonCenter P : Set G) ∈ 𝓕) :
    ∃ P : Sylow r G, Subgroup.normalizer (CFSG.thompsonCenter (P : Subgroup G) : Set G) ∈ 𝓕 := by
  have hr : r.Prime := Fact.out
  set s : Set (Subgroup G) := {X | IsPGroup r X ∧ ∃ H ∈ 𝓕, X ≤ H}
  obtain ⟨H₀, hH₀⟩ := hne
  have hsne : s.Nonempty := ⟨⊥, IsPGroup.of_bot, H₀, hH₀, bot_le⟩
  obtain ⟨X₀, ⟨hX₀p, H, hH, hX₀H⟩, hmax⟩ :=
    Set.exists_max_image s (fun X => Nat.card X) (Set.toFinite s) hsne
  obtain ⟨P, hP, hPF⟩ := hstep H hH
  have hX₀P : Nat.card X₀ ≤ Nat.card P := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX₀p
    rw [hP.card_eq, hk]
    apply Nat.pow_le_pow_right hr.pos
    have hdvd : r ^ k ∣ Nat.card H := hk ▸ Subgroup.card_dvd_of_le hX₀H
    exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP.isPGroup
  have hidx : ¬ r ∣ P.index := by
    intro hdvd
    have hG : r ^ (n + 1) ∣ Nat.card G := by
      rw [← Subgroup.card_mul_index P, hn, pow_succ]
      exact Nat.mul_dvd_mul_left _ hdvd
    obtain ⟨Y, hY⟩ :=
      Sylow.exists_subgroup_card_pow_prime r (Sylow.prime_pow_dvd_card_normalizer hG hn)
    have hYcard : Nat.card (Y.map (Subgroup.normalizer (P : Set G)).subtype) = r ^ (n + 1) := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hY]
    have hYs : Y.map (Subgroup.normalizer (P : Set G)).subtype ∈ s :=
      ⟨IsPGroup.of_card hYcard, _, hPF,
        (Subgroup.map_subtype_le Y).trans (normalizer_le_normalizer_thompsonCenter_v2 P)⟩
    have h1 := hmax _ hYs
    rw [hYcard] at h1
    exact absurd (h1.trans (hX₀P.trans hn.le))
      (not_le.mpr (Nat.pow_lt_pow_right hr.one_lt n.lt_succ_self))
  refine ⟨hP.isPGroup.toSylow hidx, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact hPF

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem exists_sylow_C_normalized (h_C : σ.C ≤ oddCoreIn σ.C ⊔ σ.D) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ P : Subgroup G, IsSylowOf r P σ.C ∧ σ.D ≤ Subgroup.normalizer (P : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hDC : σ.D ≤ Subgroup.normalizer (σ.C : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_centralizer_v2 σ.T)
  have hDO : σ.D ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
    hDC.trans (normalizer_le_normalizer_oddCoreIn_v2 σ.C)
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_normalized_of_odd hr hD2 hDO (odd_card_oddCoreIn σ.C)
  refine ⟨P, isSylowOf_iff.mpr ⟨hP.le.trans (oddCoreIn_le σ.C), hP.isPGroup, ?_⟩, hDP⟩
  have hidx : ¬ r ∣ (oddCoreIn σ.C).relIndex σ.C := by
    intro hdvd
    have h1 : (oddCoreIn σ.C).relIndex σ.C ∣ (oddCoreIn σ.C).relIndex σ.D := by
      have h := Subgroup.relIndex_mul_relIndex (oddCoreIn σ.C) σ.C (oddCoreIn σ.C ⊔ σ.D)
        (oddCoreIn_le σ.C) h_C
      rw [sup_comm, relIndex_sup_right_of_le_normalizer hDO] at h
      exact Dvd.intro _ h
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD2
    have h2 : r ∣ 2 ^ k :=
      (hdvd.trans h1).trans (hk ▸ Subgroup.relIndex_dvd_card (oddCoreIn σ.C) σ.D)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
  rw [← Subgroup.relIndex_mul_relIndex P (oddCoreIn σ.C) σ.C hP.le (oddCoreIn_le σ.C)]
  exact hr.not_dvd_mul (isSylowOf_iff.mp hP).2.2 hidx

theorem exists_sylow_ON_normalized (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P : Subgroup G} (hPC : P ≤ σ.C) (hPr : IsPGroup r P)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) :
    ∃ R : Subgroup G, IsSylowOf r R σ.ON ∧ σ.D ≤ Subgroup.normalizer (R : Set G) ∧
      P ≤ Subgroup.normalizer (R : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hPON : P ≤ Subgroup.normalizer (σ.ON : Set G) :=
    hPC.trans (σ.C_le_N.trans σ.N_le_normalizer_ON)
  have hDON : σ.D ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (σ.D_le_N hσ).trans σ.N_le_normalizer_ON
  have hYodd : Odd (Nat.card (σ.ON ⊔ P : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hPON σ.odd_card_ON (odd_card_of_isPGroup_v2 hr hr2 hPr)
  have hDY : σ.D ≤ Subgroup.normalizer ((σ.ON ⊔ P : Subgroup G) : Set G) :=
    (le_inf hDON hPD).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R, hR, hPR, hDR⟩ :=
    exists_isSylowOf_normalized_ge_of_odd hr hD2 hDY hYodd le_sup_right hPr hPD
  have hYN : σ.ON ⊔ P ≤ Subgroup.normalizer (σ.ON : Set G) := sup_le Subgroup.le_normalizer hPON
  refine ⟨R ⊓ σ.ON, hR.inf_of_le_normalizer le_sup_left hYN, ?_, ?_⟩
  · exact (le_inf hDR hDON).trans Subgroup.inf_normalizer_le_normalizer_inf
  · exact (le_inf (hPR.trans Subgroup.le_normalizer) hPON).trans
      Subgroup.inf_normalizer_le_normalizer_inf

theorem lemmaV21 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h81 : σ.LemmaIV81)
    (h83 : σ.LemmaIV83) (hc81 : σ.CorIV81) (h91 : σ.PropIV91)
    (h_II61D : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pCore r H ≠ ⊥ →
        CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H)
    {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) :
    ∃ P : Sylow r G, Subgroup.normalizer (CFSG.thompsonCenter (P : Subgroup G) : Set G) ∈
      d.familyM := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  refine exists_sylow_normalizer_thompsonCenter_mem ⟨_, h81 r hr d⟩ fun H hH => ?_
  obtain ⟨hDwrt, hodd, -⟩ := h83 r hr d H hH
  have hcon : PConstrainedWithin r H (CFSG.oddCore H) :=
    h91 r hr H ⟨hH.1, hH.2.1, hDwrt, hodd⟩
  have hst : IsPStable r H := h_II61D hσ hII H hH.2.1 hDwrt r hr.prime hr2
    hH.1.pCore_ne_bot (pPrimeCore_le_Op_p'p.trans hcon.1)
  obtain ⟨P₁, hP₁⟩ := exists_isSylowOf r H
  exact hc81 r hr d H hH P₁ hP₁ (le_normalizer_pPrimeCoreIn_sup_thompsonCenter hr2 hcon.2 hst hP₁)

theorem lemmaV22_of_familyL (hσ : σ.IsValid) (h32 : σ.LemmaIV32)
    (h61 : σ.PropIV61) (hc61 : σ.CorIV61)
    (h_II61Q : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H)
    {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    (hexc : σ.Exceptional r) (hrp : r ≠ σ.p) :
    ∃ P : Sylow r G, Subgroup.normalizer (CFSG.thompsonCenter (P : Subgroup G) : Set G) ∈
      σ.familyL r := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr hdiv
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  obtain ⟨R, hR, hDR⟩ := exists_isSylowOf_normalized_of_odd hr hD2
    ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON) σ.odd_card_ON
  refine exists_sylow_normalizer_thompsonCenter_mem ⟨_, (h32 r hr hdiv hexc R hR hDR).1⟩
    fun H hH => ?_
  have hDH : σ.D ≤ H := hH.2.2.1
  have hcon : PConstrainedWithin r H (CFSG.solvableRadical H) := h61 r hr hdiv hexc H hH
  have hst : IsPStable r H := h_II61Q r hr hdiv hrp H hH (pPrimeCore_le_Op_p'p.trans hcon.1)
  obtain ⟨R₀, hR₀, hDR₀⟩ := exists_isSylowOf_normalized_of_odd hr hD2
    (hDH.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H)
  obtain ⟨Rs, hRs, hR₀Rs⟩ := exists_isSylowOf_ge_v2 (hR₀.le.trans (oddCoreIn_le H)) hR₀.isPGroup
  have hinf : Rs ⊓ oddCoreIn H = R₀ :=
    hR₀.eq_of_le (le_inf hR₀Rs hR₀.le) inf_le_right hRs.isPGroup.to_inf_left
  refine ⟨Rs, hRs, hc61 r hr hdiv hexc H hH Rs hRs (by rw [hinf]; exact hDR₀) ?_⟩
  exact le_normalizer_pPrimeCoreIn_sup_thompsonCenter hr2 hcon.2 hst hRs

theorem II61Q_familyL (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h_II61Q : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      (∃ S₁ : Sylow 2 G, (S₁ : Subgroup G) ≤ H) → HasQCharPower H σ.q → ∀ r : ℕ, r.Prime →
        r ≠ 2 → r ≠ σ.p → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H →
          IsPStable r H) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H := by
  intro r hr hdiv hrp H hH hO
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hQ, -, -, ⟨S₁, hS₁⟩, -, -⟩ := σ.familyL_properties hσ hII hr hdiv hH
  exact h_II61Q hσ hII H hH.2.2.1 ⟨S₁, hS₁.trans inf_le_left⟩ hQ r hr
    (σ.prime_ne_two_of_dvd_ON hr hdiv) hrp hH.1.pCore_ne_bot hO

theorem lemmaV22 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h32 : σ.LemmaIV32)
    (h61 : σ.PropIV61) (hc61 : σ.CorIV61)
    (h_II61Q : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      (∃ S₁ : Sylow 2 G, (S₁ : Subgroup G) ≤ H) → HasQCharPower H σ.q → ∀ r : ℕ, r.Prime →
        r ≠ 2 → r ≠ σ.p → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H →
          IsPStable r H)
    {r : ℕ} (hr : r.Prime) (hdiv : r ∣ Nat.card σ.ON)
    (hexc : σ.Exceptional r) (hrp : r ≠ σ.p) :
    ∃ P : Sylow r G, Subgroup.normalizer (CFSG.thompsonCenter (P : Subgroup G) : Set G) ∈
      σ.familyL r :=
  σ.lemmaV22_of_familyL hσ h32 h61 hc61 (σ.II61Q_familyL hσ hII h_II61Q) hr hdiv hexc hrp

theorem propV21_of_familyL (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h32 : σ.LemmaIV32)
    (h61 : σ.PropIV61) (hc61 : σ.CorIV61) (h71 : σ.PropIV71) (h81 : σ.LemmaIV81)
    (h83 : σ.LemmaIV83) (hc81 : σ.CorIV81) (h91 : σ.PropIV91)
    (h_II61D : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pCore r H ≠ ⊥ →
        CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H)
    (h_II61Q : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → r ≠ σ.p → ∀ H ∈ σ.familyL r,
      CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H → IsPStable r H)
    (h_II4C : σ.C ≤ oddCoreIn σ.C ⊔ σ.D) {r : ℕ} (hr : σ.HypIV7 r) :
    r = σ.p := by
  by_contra hrp
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  obtain ⟨P, hP, hPD⟩ := σ.exists_sylow_C_normalized h_II4C hr.prime hr2
  obtain ⟨R, hR, hRD, hRP⟩ := σ.exists_sylow_ON_normalized hσ hr.prime hr2 hP.le hP.isPGroup hPD
  obtain ⟨d, -, -⟩ := h71 r hr P R hP hPD hR hRD hRP
  obtain ⟨P₁, hP₁⟩ := σ.lemmaV21 hσ hII h81 h83 hc81 h91 h_II61D hr d
  obtain ⟨P₂, hP₂⟩ :=
    σ.lemmaV22_of_familyL hσ h32 h61 hc61 h_II61Q hr.prime hr.dvd_ON hr.exceptional hrp
  have hD := (h83 r hr d _ hP₁).1.1
  have hQ := (σ.familyL_properties hσ hII hr.prime hr.dvd_ON hP₂).1.1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P₂
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hconj : (P₂ : Subgroup G) = (P₁ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hH : Subgroup.normalizer (CFSG.thompsonCenter (P₂ : Subgroup G) : Set G) =
      (Subgroup.normalizer (CFSG.thompsonCenter (P₁ : Subgroup G) : Set G)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hconj, ← thompsonCenter_map_of_injective _ hinj, Subgroup.map_equiv_normalizer_eq]
  have hD₂ : IsDGroup (Subgroup.normalizer (CFSG.thompsonCenter (P₂ : Subgroup G) : Set G)) := by
    rw [hH]
    exact IsDGroup.of_mulEquiv (Subgroup.equivMapOfInjective _ _ hinj) hD
  exact (hII.fusion_disjoint _).2.2.2.1 hQ hD₂

theorem propV21 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (h32 : σ.LemmaIV32)
    (h61 : σ.PropIV61) (hc61 : σ.CorIV61) (h71 : σ.PropIV71) (h81 : σ.LemmaIV81)
    (h83 : σ.LemmaIV83) (hc81 : σ.CorIV81) (h91 : σ.PropIV91)
    (h_II61D : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      IsDGroupWrt (σ.T.subgroupOf H) → ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pCore r H ≠ ⊥ →
        CFSG.pPrimeCore r H ≤ CFSG.oddCore H → IsPStable r H)
    (h_II61Q : σ.IsValid → σ.ChapterIIFacts → ∀ H : Subgroup G, σ.D ≤ H →
      (∃ S₁ : Sylow 2 G, (S₁ : Subgroup G) ≤ H) → HasQCharPower H σ.q → ∀ r : ℕ, r.Prime →
        r ≠ 2 → r ≠ σ.p → CFSG.pCore r H ≠ ⊥ → CFSG.pPrimeCore r H ≤ CFSG.solvableRadical H →
          IsPStable r H)
    (h_II4C : σ.C ≤ oddCoreIn σ.C ⊔ σ.D) {r : ℕ} (hr : σ.HypIV7 r) :
    r = σ.p :=
  σ.propV21_of_familyL hσ hII h32 h61 hc61 h71 h81 h83 hc81 h91 h_II61D
    (σ.II61Q_familyL hσ hII h_II61Q) h_II4C hr

end Setting

end CFSG.ABGTheoremB
