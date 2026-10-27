module

public import CFSG.Open.RankThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_9End2
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowContainment

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gen49e_inf_le {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {M T R : Subgroup G} {x : G}
    (hT2 : IsPGroup 2 T) (hNT : normalizer (T : Set G) = M) (hRM : R ≤ M) (hRp : IsPGroup p R)
    (hxR : x ∈ R) (hfpf : ∀ t ∈ T, t * x = x * t → t = 1)
    {Y : Subgroup G} (hY0 : Y ≠ ⊥) (hY2 : IsPGroup 2 Y) (hRY : R ≤ normalizer (Y : Set G))
    (hmax : ∀ Y' : Subgroup G, Y' ≠ ⊥ → IsPGroup 2 Y' → R ≤ normalizer (Y' : Set G) →
      ¬ normalizer (Y' : Set G) ≤ M → Nat.card Y' ≤ Nat.card Y)
    (hDM : rankThreePrimeCore p (normalizer (Y : Set G)) ≤ M)
    {X : Subgroup G} (hXH : X ≤ normalizer (Y : Set G))
    (hXn : normalizer (Y : Set G) ≤ normalizer (X : Set G))
    (hXc : ∀ h ∈ X, h * x * h⁻¹ * x⁻¹ ∈ rankThreePrimeCore p (normalizer (Y : Set G)))
    (hXM : ¬ X ≤ M) :
    T ⊓ normalizer (Y : Set G) ≤ Y := by
  set H := normalizer (Y : Set G) with hH
  set D := rankThreePrimeCore p H with hD
  obtain ⟨hDH, hHD, hDcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p H
  set W := T ⊓ H with hW
  have hWH : W ≤ H := inf_le_right
  have hW2 : IsPGroup 2 W := hT2.to_le inf_le_left
  have hWM : W ≤ M := inf_le_left.trans (hNT ▸ le_normalizer)
  have hRT : R ≤ normalizer (T : Set G) := hNT ▸ hRM
  have hWD : W ≤ normalizer (D : Set G) := hWH.trans hHD
  have hRW : R ≤ normalizer (W : Set G) := by
    refine le_normalizer_iff.mpr fun r hr w hw => ⟨le_normalizer_iff.mp hRT r hr w hw.1, ?_⟩
    exact H.mul_mem (H.mul_mem (hRY hr) hw.2) (H.inv_mem (hRY hr))
  have hYD : Y ≤ D := gen49e_le_primeCore le_normalizer le_rfl
    (gen49e_coprime_card_two Fact.out hp hY2)
  have hxH : x ∈ H := hRY hxR
  have hcomm : ∀ w ∈ W, ∀ k ∈ X, k * w * k⁻¹ * w⁻¹ ∈ D :=
    gen49e_commutator_mem hHD hXn hxH hXc hWH
      (gen49e_exists_comm (hRW hxR) fun w hw hc => hfpf w hw.1 hc)
  set N := D ⊔ W with hN
  have hXN : X ≤ normalizer (N : Set G) := gen49e_le_normalizer_sup hHD hXH hcomm
  have hNcop : Nat.Coprime p (Nat.card N) :=
    CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer hWD hDcop
      (gen49e_coprime_card_two Fact.out hp hW2)
  have hRN : R ≤ normalizer (N : Set G) :=
    (le_inf (hRY.trans hHD) hRW).trans (inf_normalizer_le_normalizer_sup D W)
  have hNM : N ≤ M := sup_le hDM hWM
  have hYWN : Y ⊔ W ≤ N := sup_le (hYD.trans le_sup_left) le_sup_right
  have hYW2 : IsPGroup 2 (Y ⊔ W : Subgroup G) := hY2.to_sup_of_normal_left' hW2 hWH
  have hRYW : R ≤ normalizer ((Y ⊔ W : Subgroup G) : Set G) :=
    (le_inf hRY hRW).trans (inf_normalizer_le_normalizer_sup Y W)
  obtain ⟨S, hYWS, hRS⟩ := CFSG.SignalizerFunctor.Helpers.normalized_pgroup_actor_sylow_containing
    p 2 Fact.out Nat.prime_two R N (Y ⊔ W) hRp hRN hNcop hYWN hYW2 hRYW
  set S' : Subgroup G := (S : Subgroup N).map N.subtype with hS'
  have hfr : X ≤ N ⊔ normalizer (S' : Set G) :=
    le_sup_normalizer_of_isSylowOf hXN ⟨S, rfl⟩
  have hS'M : ¬ normalizer (S' : Set G) ≤ M := fun h => hXM (hfr.trans (sup_le hNM h))
  have hYS' : Y ≤ S' := le_sup_left.trans hYWS
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map N.subtype
  have hS'0 : S' ≠ ⊥ := fun h => hY0 (le_bot_iff.mp (h ▸ hYS'))
  have hcard := hmax S' hS'0 hS'2 hRS hS'M
  have hSY : Y = S' := eq_of_le_of_card_ge hYS' hcard
  exact le_sup_right.trans (hYWS.trans hSY.ge)

end CFSG.LocalAnalysis.RankThreeTheoremC
