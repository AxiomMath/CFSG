module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviInputs
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactor
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChevMap
import CFSG.GroupTheory.SubgroupOfQuotientMap
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup

private lemma gomiChevLevi_single_max {G : Type*} [Group G] {B K A P : Subgroup G}
    (hmax : ∀ Q : Subgroup G, B ⊓ K < Q → Q ≤ K → Q = K)
    (hBA : B ≤ A) (hAK : ¬ A ⊓ K ≤ B) (hAP : A < P) (hPBK : P ≤ B ⊔ K) : False := by
  have hlt : B ⊓ K < A ⊓ K :=
    lt_of_le_of_ne (inf_le_inf_right K hBA) fun h => hAK (h ▸ inf_le_left)
  have hKle : K ≤ A := (hmax (A ⊓ K) hlt inf_le_right) ▸ inf_le_left
  exact (not_lt_of_ge (hPBK.trans (sup_le hBA hKle))) hAP

private lemma gomiChevLevi_single_TQ {G Γ : Type*} [Group G] [Finite G] [Group Γ]
    {L U P H D K A : Subgroup G} {ψ : ↥(P ⊔ H) →* Γ}
    (hψ : Function.Surjective ψ) (hker : ψ.ker = D.subgroupOf (P ⊔ H))
    (hU : IsSylowOf 2 U L) (hDB : D ≤ L ⊓ normalizer (U : Set G)) (hDK : D ≤ K)
    (hKP : K ≤ P) (hPD : P ≤ normalizer (D : Set G)) (hUK : U ≤ K)
    (hPL : P ≤ L) (hBA : L ⊓ normalizer (U : Set G) ≤ A)
    (hAK : ¬ A ⊓ K ≤ L ⊓ normalizer (U : Set G)) :
    (K.subgroupOf (P ⊔ H)).map ψ ⊓
        normalizer (((U.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ) : Set Γ) <
      ((A ⊓ K).subgroupOf (P ⊔ H)).map ψ := by
  have hKX : K ≤ P ⊔ H := hKP.trans le_sup_left
  have hUX : U ≤ P ⊔ H := hUK.trans hKX
  have hDX : D ≤ P ⊔ H := hDK.trans hKX
  have hDL : D ≤ L := hDB.trans inf_le_left
  have hDU : U ≤ normalizer (D : Set G) := hUK.trans (hKP.trans hPD)
  have hoddU : ¬ 2 ∣ U.relIndex D := by
    have hnot : ¬ 2 ∣ U.relIndex (U ⊔ D) :=
      (isSylowOf_iff.mp (hU.of_le le_sup_left (sup_le hU.le hDL))).2.2
    rw [← Subgroup.inf_relIndex_right (H := U) (K := D),
      ← (relIndex_sup_eq_relIndex_inf_of_le_normalizer hDU).1]
    exact hnot
  have hnorm := normalizer_map_subgroupOf hψ hker hDX hUX hU.isPGroup hoddU
  have hDXn : D ≤ (P ⊔ H) ⊓ normalizer (U : Set G) := le_inf hDX (hDB.trans inf_le_right)
  have hinf := map_subgroupOf_inf hker K (K' := (P ⊔ H) ⊓ normalizer (U : Set G)) hDXn
  have hEq : (K.subgroupOf (P ⊔ H)).map ψ ⊓
      normalizer (((U.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ) : Set Γ) =
      ((K ⊓ ((P ⊔ H) ⊓ normalizer (U : Set G))).subgroupOf (P ⊔ H)).map ψ := by
    rw [hnorm, ← hinf]
  have hBK : K ⊓ ((P ⊔ H) ⊓ normalizer (U : Set G)) =
      (L ⊓ normalizer (U : Set G)) ⊓ K := by
    apply le_antisymm
    · rintro x ⟨hxK, _, hxN⟩
      exact ⟨⟨hKP.trans hPL hxK, hxN⟩, hxK⟩
    · rintro x ⟨⟨hxL, hxN⟩, hxK⟩
      exact ⟨hxK, hKX hxK, hxN⟩
  rw [hEq, hBK]
  have hAKX : A ⊓ K ≤ P ⊔ H := inf_le_right.trans hKX
  have hBKX : (L ⊓ normalizer (U : Set G)) ⊓ K ≤ P ⊔ H := inf_le_right.trans hKX
  have hD_AK : D ≤ A ⊓ K := le_inf (hDB.trans hBA) hDK
  have hD_BK : D ≤ (L ⊓ normalizer (U : Set G)) ⊓ K := le_inf hDB hDK
  have hle : (((L ⊓ normalizer (U : Set G)) ⊓ K).subgroupOf (P ⊔ H)).map ψ ≤
      ((A ⊓ K).subgroupOf (P ⊔ H)).map ψ :=
    (map_subgroupOf_le_map_subgroupOf_iff hker hBKX hD_AK).2 (inf_le_inf_right K hBA)
  refine lt_of_le_of_ne hle fun heq => ?_
  have hAB : A ⊓ K ≤ (L ⊓ normalizer (U : Set G)) ⊓ K :=
    (map_subgroupOf_le_map_subgroupOf_iff hker hAKX hD_BK).1 (le_of_eq heq.symm)
  exact hAK (hAB.trans inf_le_left)

private lemma gomiChevLevi_single_QA {G Γ : Type*} [Group G] [Group Γ]
    {L U P H D K A : Subgroup G} {ψ : ↥(P ⊔ H) →* Γ}
    (hker : ψ.ker = D.subgroupOf (P ⊔ H)) (hKP : K ≤ P)
    (hDB : D ≤ L ⊓ normalizer (U : Set G)) (hDK : D ≤ K)
    (hBA : L ⊓ normalizer (U : Set G) ≤ A) (hAP : A < P)
    (hPBK : P ≤ L ⊓ normalizer (U : Set G) ⊔ K) :
    ((A ⊓ K).subgroupOf (P ⊔ H)).map ψ < (K.subgroupOf (P ⊔ H)).map ψ := by
  have hKX : K ≤ P ⊔ H := hKP.trans le_sup_left
  have hD_AK : D ≤ A ⊓ K := le_inf (hDB.trans hBA) hDK
  refine lt_of_le_of_ne
    ((map_subgroupOf_le_map_subgroupOf_iff hker (inf_le_right.trans hKX) hDK).2
      inf_le_right) fun heq => ?_
  have hKA : K ≤ A ⊓ K :=
    (map_subgroupOf_le_map_subgroupOf_iff hker hKX hD_AK).1 (le_of_eq heq.symm)
  exact (not_lt_of_ge (hPBK.trans (sup_le hBA (hKA.trans inf_le_left)))) hAP

theorem gomiChevLevi_false_of_single_factor (hIso : GomiChevIsolated)
    (hR1 : GomiChevRankOneOvergroups) (hR2 : GomiFact36Overgroups) {G : Type} [Group G]
    [Finite G] {L U H P D K A : Subgroup G} (hU : IsSylowOf 2 U L) (hH : IsPGroup 2 H)
    (hHU : H ≤ normalizer (U : Set G)) (hHK : H ≤ normalizer (K : Set G))
    (hHA : H ≤ normalizer (A : Set G)) (hPL : P ≤ L) (hBA : L ⊓ normalizer (U : Set G) ≤ A)
    (hAP : A < P) (hAK : ¬ A ⊓ K ≤ L ⊓ normalizer (U : Set G))
    (hDB : D ≤ L ⊓ normalizer (U : Set G)) (hDK : D ≤ K) (hKP : K ≤ P)
    (hPD : P ≤ normalizer (D : Set G)) (hUK : U ≤ K)
    (hPBK : P ≤ L ⊓ normalizer (U : Set G) ⊔ K)
    (hfac : ∀ [(D.subgroupOf K).Normal], IsGomiChevTwo (↥K ⧸ D.subgroupOf K) ∨
      Nonempty ((↥K ⧸ D.subgroupOf K) ≃* Equiv.Perm (Fin 6)) ∨
      ∀ Q : Subgroup G, L ⊓ normalizer (U : Set G) ⊓ K < Q → Q ≤ K → Q = K)
    {Γ : Type} [Group Γ] [Finite Γ] {ψ : ↥(P ⊔ H) →* Γ} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = D.subgroupOf (P ⊔ H))
    (hiso : IsPIsolatedOver 2 ((K.subgroupOf (P ⊔ H)).map ψ ⊓
      centralizer (((H.subgroupOf (P ⊔ H)).map ψ : Subgroup Γ) : Set Γ)) ⊥) :
    False := by
  have hinst : (D.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDK).2 (hKP.trans hPD)
  have hKX : K ≤ P ⊔ H := hKP.trans le_sup_left
  have hHAK : H ≤ normalizer (A ⊓ K : Subgroup G) :=
    (le_inf hHA hHK).trans Subgroup.inf_normalizer_le_normalizer_inf
  rcases hfac with hchev | hS6 | hmax
  · obtain ⟨e⟩ := nonempty_mulEquiv_map_subgroupOf hker hKX
    obtain ⟨a, haV, haN⟩ := GomiChevIsolated.exists_not_mem_normalizer hIso hR1 hR2
      (Or.inl (IsGomiChevTwo.of_mulEquiv e.symm hchev)) (hH.comap_subtype.map ψ)
      (map_subgroupOf_le_normalizer ψ hHK)
      (isSylowOf_map_subgroupOf hKX (hU.of_le hUK (hKP.trans hPL)))
      (map_subgroupOf_le_normalizer ψ hHU) hiso
      (gomiChevLevi_single_TQ hψ hker hU hDB hDK hKP hPD hUK hPL hBA hAK)
      (gomiChevLevi_single_QA hker hKP hDB hDK hBA hAP hPBK)
    exact haN (map_subgroupOf_le_normalizer ψ hHAK haV)
  · obtain ⟨f⟩ := hS6
    obtain ⟨e⟩ := nonempty_mulEquiv_map_subgroupOf hker hKX
    obtain ⟨a, haV, haN⟩ := GomiChevIsolated.exists_not_mem_normalizer hIso hR1 hR2
      (Or.inr ⟨e.trans f⟩) (hH.comap_subtype.map ψ)
      (map_subgroupOf_le_normalizer ψ hHK)
      (isSylowOf_map_subgroupOf hKX (hU.of_le hUK (hKP.trans hPL)))
      (map_subgroupOf_le_normalizer ψ hHU) hiso
      (gomiChevLevi_single_TQ hψ hker hU hDB hDK hKP hPD hUK hPL hBA hAK)
      (gomiChevLevi_single_QA hker hKP hDB hDK hBA hAP hPBK)
    exact haN (map_subgroupOf_le_normalizer ψ hHAK haV)
  · exact gomiChevLevi_single_max hmax hBA hAK hAP hPBK

end CFSG.GroupTheory
