module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Families
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

section PRank

variable {G : Type*} [Group G] [Finite G]

theorem le_pRank_of_elem {p : ℕ} (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

theorem exists_elem_of_pRank {p : ℕ} (hp : 1 < p) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ CFSG.Open.pRank p H := CFSG.SectionRank.exists_pRank hp H

theorem one_le_pRank_of_le {p : ℕ} (hp : 1 < p) {R₁ R₀ : Subgroup G} (h : R₁ ≤ R₀)
    (h1 : 1 ≤ CFSG.Open.pRank p R₁) : 1 ≤ CFSG.Open.pRank p R₀ := by
  obtain ⟨E, hE, hEa, hEc⟩ := exists_elem_of_pRank hp R₁
  exact h1.trans (le_pRank_of_elem hp (hE.trans h) hEa hEc)

theorem pRank_le_pRank_map {p : ℕ} (hp : 1 < p) {G' : Type*} [Group G'] [Finite G']
    (f : G →* G') (hf : Function.Injective f) (Q : Subgroup G) :
    CFSG.Open.pRank p Q ≤ CFSG.Open.pRank p (Q.map f) := by
  obtain ⟨E, hE, hEa, hEc⟩ := exists_elem_of_pRank hp Q
  refine le_pRank_of_elem hp (Subgroup.map_mono hE) ⟨?_, ?_⟩ ?_
  · have := hEa.1
    infer_instance
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hEa.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective hf, hEc]

end PRank

section Main

theorem gammaCore_eq_top_of_glbCore {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    [Nontrivial ↥K] (hK : ∀ T : Sylow 3 ↥K, CFSG.Open.GLBCore 3 1 (T : Subgroup ↥K) = ⊤)
    (P : Sylow 3 X) : gammaCore 3 1 ⊤ (P : Subgroup X) = ⊤ := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h13 : 1 < 3 := by norm_num
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  set H : Subgroup X := gammaCore 3 1 ⊤ (P : Subgroup X) with hH
  have hTP : ∀ q : ↥K, q ∈ (T : Subgroup ↥K) → (q : X) ∈ (P : Subgroup X) := by
    intro q hq
    rw [hT] at hq
    exact (Subgroup.mem_subgroupOf.mp hq).1
  have hKH : CFSG.Open.GLBCore 3 1 (T : Subgroup ↥K) ≤ H.comap K.subtype := by
    unfold CFSG.Open.GLBCore
    refine sSup_le ?_
    rintro N ⟨Q, hQT, hQr, rfl⟩ n hn
    show (n : X) ∈ H
    have hR : Q.map K.subtype ≤ (P : Subgroup X) := by
      rintro _ ⟨q, hq, rfl⟩
      exact hTP q (hQT hq)
    have hrk : 1 ≤ CFSG.Open.pRank 3 (Q.map K.subtype) :=
      hQr.trans (pRank_le_pRank_map h13 K.subtype K.subtype_injective Q)
    refine Subgroup.subset_closure ⟨Subgroup.mem_top _, Q.map K.subtype, hR, hrk, ?_⟩
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro r
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨n * q * n⁻¹, (hn q).mp hq, rfl⟩
    · rintro ⟨q, hq, hqr⟩
      refine ⟨n⁻¹ * q * n, (hn _).mpr (by rw [show n * (n⁻¹ * q * n) * n⁻¹ = q by group]; exact hq), ?_⟩
      have h1 : (q : X) = (n : X) * r * (n : X)⁻¹ := hqr
      calc ((n⁻¹ * q * n : ↥K) : X) = (n : X)⁻¹ * (q : X) * (n : X) := rfl
        _ = r := by rw [h1]; group
  have hKtop : H.comap K.subtype = ⊤ := top_le_iff.mp (by rw [← hK T]; exact hKH)
  have hKleH : K ≤ H := fun k hk => by
    have := (Subgroup.eq_top_iff' _).mp hKtop ⟨k, hk⟩
    exact this
  have hne : ∃ Q : Subgroup ↥K, Q ≤ (T : Subgroup ↥K) ∧ 1 ≤ CFSG.Open.pRank 3 Q := by
    by_contra hcon
    push Not at hcon
    have hbot : CFSG.Open.GLBCore 3 1 (T : Subgroup ↥K) = ⊥ := by
      unfold CFSG.Open.GLBCore
      apply le_bot_iff.mp
      refine sSup_le ?_
      rintro N ⟨Q, hQT, hQr, rfl⟩
      exact absurd hQr (not_le.mpr (hcon Q hQT))
    rw [hK T] at hbot
    exact absurd hbot top_ne_bot
  obtain ⟨Q, hQT, hQr⟩ := hne
  have hrk0 : 1 ≤ CFSG.Open.pRank 3 ((P : Subgroup X) ⊓ K) := by
    refine one_le_pRank_of_le h13 (R₁ := Q.map K.subtype) ?_
      (hQr.trans (pRank_le_pRank_map h13 K.subtype K.subtype_injective Q))
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨hTP q (hQT hq), q.2⟩
  have hNH : Subgroup.normalizer ((((P : Subgroup X) ⊓ K : Subgroup X)) : Set X) ≤ H :=
    fun x hx => Subgroup.subset_closure ⟨Subgroup.mem_top _, _, inf_le_left, hrk0, hx⟩
  have hfr := Sylow.normalizer_sup_eq_top (N := K) T
  have hmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr inf_le_right
  rw [eq_top_iff, ← hfr]
  refine sup_le ?_ hKleH
  rw [hmap]
  exact hNH

theorem gls3PlusCase_of_glbCore (i : TauCeti.CFSGIndex)
    (h : ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
      Nonempty (K ≃* i.Group) → ∀ T : Sylow 3 K, CFSG.Open.GLBCore 3 1 (T : Subgroup K) = ⊤) :
    Gls3PlusCase i := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP hΓ
  exfalso
  have := hKn
  obtain ⟨a, b, hab⟩ := hnc
  have hnt : Nontrivial ↥K := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hK := h ↥K hKs ⟨a, b, hab⟩ hiso
  rw [gammaCore_eq_top_of_glbCore hK P] at hΓ
  exact lt_irrefl _ hΓ

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
