module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GT3

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem exists_sylow_ge {G : Type} [Group G] [Finite G] {N M : Subgroup G} (hMN : M ≤ N)
    (hM : IsPGroup 2 M) : ∃ T : Subgroup G, M ≤ T ∧ IsSylow2Of T N := by
  have hM2 : IsPGroup 2 (M.subgroupOf N) := hM.comap_subtype
  obtain ⟨P, hMP⟩ := hM2.exists_le_sylow
  refine ⟨(P : Subgroup ↥N).map N.subtype, ?_, isSylow2Of_map_sylow P⟩
  calc M = (M.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hMN).symm
    _ ≤ (P : Subgroup ↥N).map N.subtype := map_mono hMP

private theorem s888b2g_isPGroup_twoCoreIn {G : Type} [Group G] (X : Subgroup G) :
    IsPGroup 2 (twoCoreIn X) := by
  unfold twoCoreIn CFSG.inSubgroup
  exact (CFSG.pCore_isPGroup (G := ↥X) (p := 2)).map X.subtype

theorem mem_Qsub_of_sq_mem (h516a : Asc82Lemma516a) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    (hNz : normalizer (Qsub K₁ K₂ h : Set G) ≤ centralizer ({z} : Set G)) :
    ∀ s ∈ normalizer (Qsub K₁ K₂ h : Set G), s * s ∈ Qsub K₁ K₂ h →
      (∀ q ∈ Qsub K₁ K₂ h, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Qsub K₁ K₂ h := by
  intro s hsN hs2 hcomm
  have hQ2 : IsPGroup 2 (Qsub K₁ K₂ h) := by
    unfold Qsub
    exact s888b2g_isPGroup_twoCoreIn _
  obtain ⟨n, hn⟩ := hQ2 ⟨s * s, hs2⟩
  have hs_pow : s ^ (2 ^ (n + 1)) = 1 := by
    have h1 : (s * s) ^ (2 ^ n) = 1 := by
      have := congrArg (Subgroup.subtype (Qsub K₁ K₂ h)) hn
      simpa using this
    have h2 : (s ^ 2) ^ (2 ^ n) = 1 := by simpa [sq] using h1
    rw [pow_succ', pow_mul]
    exact h2
  have hM : IsPGroup 2 (zpowers s) := by
    refine IsPGroup.of_card_dvd_pow (p := 2) (n := n + 1) ?_
    rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]
    exact hs_pow
  have hMN : zpowers s ≤ normalizer (Qsub K₁ K₂ h : Set G) :=
    Subgroup.zpowers_le.mpr hsN
  obtain ⟨T, hMT, hTN⟩ := exists_sylow_ge hMN hM
  exact centS_of_516a h516a c hTN hNz s (hMT (Subgroup.mem_zpowers s)) hcomm

end CFSG.OddStandard.SmallF3.Omega
