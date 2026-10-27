module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBlockCentrality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Main

variable {G : Type*} [Group G] [Finite G]

theorem minimal_parabolic_subgroup_over_normal_Sylow_part {p : ℕ} [Fact p.Prime]
    {X T M N R : Subgroup G} (hT : IsSylowIn p T X) (hMX : M < X) (hTM : T ≤ M)
    (hM : ∀ Y : Subgroup G, T ≤ Y → Y < X → Y ≤ M)
    (hNX : N ≤ X) (hNn : X ≤ normalizer (N : Set G)) (hXNT : N ⊔ T = X)
    (hNno : NoPQuotient p N) (hR1 : R ≠ ⊥) (hRT : R ≤ T)
    (hRTn : T ≤ normalizer (R : Set G)) (hRsyl : IsSylowIn p R (N ⊔ R))
    (hchar : NoCharNormal R X) :
    ∃ P : Subgroup G, P ≤ N ⊔ R ∧ R < P ∧ ¬ P ≤ M ∧ IsSylowIn p R P ∧
      ¬ P ≤ normalizer (R : Set G) ∧
      (P ⊓ M < P ∧ R ≤ P ⊓ M ∧ ∀ Y : Subgroup G, R ≤ Y → Y < P → Y ≤ P ⊓ M) ∧
      P ⊔ T = X ∧ conjJoin T P = N ⊔ R ∧ NoCharNormal R P := by
  classical
  set NR : Subgroup G := N ⊔ R with hNR
  have hTX : T ≤ X := hT.le
  have hT2 : IsPGroup p T := hT.isPGroup
  have hRX : R ≤ X := hRT.trans hTX
  have hNNR : N ≤ NR := le_sup_left
  have hRNR : R ≤ NR := le_sup_right
  have hNRX : NR ≤ X := sup_le hNX hRX
  have hTN : T ≤ normalizer (N : Set G) := fun t ht => hNn (hTX ht)
  have hTNR : T ≤ normalizer (NR : Set G) := fun t ht =>
    C1.mem_normalizer_sup (hTN ht) (hRTn ht)
  have hXNR : X ≤ normalizer (NR : Set G) := by
    rw [← hXNT]
    exact sup_le (fun n hn => Subgroup.le_normalizer (hNNR hn)) hTNR
  have hNRM : ¬ NR ≤ M := by
    intro h
    have hXM : X ≤ M := by
      rw [← hXNT]
      exact sup_le (hNNR.trans h) hTM
    exact lt_irrefl _ (lt_of_lt_of_le hMX hXM)
  have hfin : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  obtain ⟨P, ⟨hPNR, hRP, hPM⟩, hmin⟩ :=
    wellFounded_lt.has_min {P : Subgroup G | P ≤ NR ∧ R ≤ P ∧ ¬ P ≤ M} ⟨NR, le_rfl, hRNR, hNRM⟩
  have hmin' : ∀ Y : Subgroup G, R ≤ Y → Y < P → Y ≤ M := by
    intro Y hRY hYP
    by_contra hYM
    exact hmin Y ⟨hYP.le.trans hPNR, hRY, hYM⟩ hYP
  have hRPlt : R < P := by
    refine lt_of_le_of_ne hRP fun h => hPM ?_
    rw [← h]
    exact hRT.trans hTM
  have hPX : P ≤ X := hPNR.trans hNRX
  have hPT : P ⊔ T = X := by
    have hle : P ⊔ T ≤ X := sup_le hPX hTX
    rcases eq_or_lt_of_le hle with h | h
    · exact h
    · exact absurd (le_sup_left.trans (hM (P ⊔ T) le_sup_right h)) hPM
  have hPsyl : IsSylowIn p R P := by
    refine ⟨hRP, hRsyl.isPGroup, fun hdvd => hRsyl.not_dvd_relIndex ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex R P NR hRP hPNR]
    exact hdvd.mul_right _
  have hPnn : ¬ P ≤ normalizer (R : Set G) := by
    intro h
    refine hchar R le_rfl hR1 (by rw [Subgroup.subgroupOf_self]; infer_instance) ?_
    rw [← hPT]
    exact sup_le h hRTn
  have hDP : conjJoin T P = NR := by
    have hPD : P ≤ conjJoin T P := by
      intro y hy
      refine Subgroup.mem_iSup_of_mem (⟨1, T.one_mem⟩ : T) ⟨y, hy, ?_⟩
      simp
    refine le_antisymm ?_ ?_
    · refine iSup_le fun t x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      have := (Subgroup.mem_normalizer_iff.mp (hXNR (hTX t.2)) y).mp (hPNR hy)
      simpa using this
    · have hTD : T ≤ normalizer (conjJoin T P : Set G) := fun t ht => mem_normalizer_conjJoin ht
      have hXD : X ≤ conjJoin T P ⊔ T := by
        rw [← hPT]
        exact sup_le (hPD.trans le_sup_left) le_sup_right
      have hND : N ≤ conjJoin T P := le_of_noPQuotient hNno
        (fun n hn => exists_pow_mem_of_mem_sup_pGroup hT2 hTD (hXD (hNX hn)))
      exact sup_le hND (hRP.trans hPD)
  have hPchar : NoCharNormal R P := by
    intro C hCR hC0 hCchar hPC
    refine hchar C hCR hC0 hCchar ?_
    rw [← hPT]
    exact sup_le hPC (fun t ht => mem_normalizer_of_characteristic hCchar hCR (hRTn ht))
  have hPMlt : P ⊓ M < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hPM ?_
    rw [← h]
    exact inf_le_right
  exact ⟨P, hPNR, hRPlt, hPM, hPsyl, hPnn,
    ⟨hPMlt, le_inf hRP (hRT.trans hTM), fun Y hRY hYP => le_inf hYP.le (hmin' Y hRY hYP)⟩,
    hPT, hDP, hPchar⟩

end Main

end CFSG.QuasithinUnique.Setup.Campbell
