module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroup
public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem normalizer_le_glaWeakCore_of_three_le {r : ℕ} (hr : 1 < r) {P Q : Subgroup G}
    (hQP : Q ≤ P) (h3 : 3 ≤ CFSG.Open.pRank r Q) :
    Subgroup.normalizer (Q : Set G) ≤ GLAWeakCore r P :=
  le_sSup ⟨Q, hQP, by omega,
    h3.trans (CFSG.SectionRank.pRank_mono hr le_sup_left), rfl⟩

theorem exists_twoLocal_covering (hS : GLStanding G m p) {B X L L₂ : Subgroup G}
    (hBp : IsPGroup p B) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hXp : ¬ p ∣ Nat.card X) (hLX : L ≤ X) (hL₂L : L₂ ≤ L)
    (hOL₂ : GLAPPrimeCoreOf 2 X ≤ L₂) (hL₂n : (L₂.subgroupOf L).Normal)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (_hrp : r ≠ p)
    (h1 : m + 1 ≤ GLATwoLocalRank r ↥L) (h2 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥L))
    (h3 : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥L₂)) :
    ∃ H : Subgroup G, IsTwoLocal H ∧ B ≤ H ∧
      ∀ j ∈ X, (∀ t ∈ L₂, j * t * j⁻¹ * t⁻¹ ∈ GLAPPrimeCoreOf 2 X) →
        j ∈ (H ⊓ X) ⊔ GLAPPrimeCoreOf 2 X := by
  have hp : p.Prime := hS.beta.1
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr1 : 1 < r := hr.one_lt
  have h2' : 3 ≤ CFSG.Open.pRank r L := by
    rwa [CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype hr1 L]
  have h3' : 3 ≤ CFSG.Open.pRank r L₂ := by
    rwa [CFSG.LocalAnalysis.GLTheoremB.pRank_eq_pRank_top_subtype hr1 L₂]
  have hrL : r ∣ Nat.card L := dvd_card_of_one_le_pRank hr (by omega)
  have hrG : r ∣ Nat.card G := hrL.trans (Subgroup.card_subgroup_dvd_card L)
  have hβ : r ∈ GLABeta (m + 1) G :=
    ⟨hr, hr2, hrG, h1.trans (glaTwoLocalRank_subgroup_le hr1 L)⟩
  have hcop : ¬ p ∣ Nat.card L := fun h => hXp (h.trans (Subgroup.card_dvd_of_le hLX))
  obtain ⟨R₀, hR₀L, hR₀p, hR₀max, hBR₀⟩ :=
    exists_sylow_normalized_of_not_dvd (p := p) (q := r) L B hBp hBL hcop
  obtain ⟨P, hP⟩ := hR₀p.exists_le_sylow
  obtain ⟨H, hH, hWH⟩ := (hS.weakCoreLocal r hβ).2 P
  have hR₀rank : 3 ≤ CFSG.Open.pRank r R₀ :=
    h2'.trans (pRank_le_of_sylow hR₀L hR₀p hR₀max)
  have hBH : B ≤ H :=
    hBR₀.trans ((normalizer_le_glaWeakCore_of_three_le hr1 hP hR₀rank).trans hWH)
  have hTp : IsPGroup r ↥(R₀ ⊓ L₂) := hR₀p.to_le inf_le_left
  have hTsyl := sylow_inf_of_normal hL₂L hL₂n hR₀L hR₀p hR₀max
  have hTrank : 3 ≤ CFSG.Open.pRank r (R₀ ⊓ L₂) :=
    h3'.trans (pRank_le_of_sylow inf_le_right hTp hTsyl)
  have hTH : Subgroup.normalizer ((R₀ ⊓ L₂ : Subgroup G) : Set G) ≤ H :=
    (normalizer_le_glaWeakCore_of_three_le hr1 (inf_le_left.trans hP) hTrank).trans hWH
  refine ⟨H, hH, hBH, fun j hj hjc => ?_⟩
  have hOX : GLAPPrimeCoreOf 2 X ≤ X := Subgroup.map_subtype_le _
  have hTn : R₀ ⊓ L₂ ≤ Subgroup.normalizer (GLAPPrimeCoreOf 2 X : Set G) :=
    inf_le_right.trans (hL₂L.trans (hLX.trans (le_normalizer_glaPPrimeCoreOf 2 X)))
  have hsyl : ∀ n : ℕ, r ^ n ∣ Nat.card ↥((R₀ ⊓ L₂) ⊔ GLAPPrimeCoreOf 2 X) →
      r ^ n ∣ Nat.card ↥(R₀ ⊓ L₂) := fun n hn =>
    hTsyl n (hn.trans (Subgroup.card_dvd_of_le (sup_le inf_le_right hOL₂)))
  obtain ⟨o, ho, hoj⟩ := exists_mem_normalizer_of_sylow hTp hTn hsyl
    (fun t ht => hjc t ht.2)
  have hjX : o⁻¹ * j ∈ X := mul_mem (inv_mem (hOX ho)) hj
  have : j = o * (o⁻¹ * j) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right ho) (Subgroup.mem_sup_left ⟨hTH hoj, hjX⟩)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
