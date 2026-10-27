module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTenBridge
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.NineSettingOfHypC
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section


namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem exists_isSylowOf_ge [Fact p.Prime] {K : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩,
    fun q hq => ⟨⟨q, hQK hq⟩, hS (Subgroup.mem_comap.mpr hq), rfl⟩⟩

theorem le_kSub_of_isElemAbelian [Fact p.Prime] {E : Subgroup G} (hL : pLayerIn p H ≤ M)
    (hE : IsElemAbelian p E) (hEH : E ≤ H) : E ≤ kSub p M H := by
  intro x hx
  rw [kSub_of_le hL]
  by_cases h1 : x = 1
  · rw [h1]
    exact one_mem _
  have hord : orderOf x = p := orderOf_eq_prime (hE.2 x hx) h1
  exact le_sSup (show zpowers x ∈ {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p} from
    ⟨zpowers_le.mpr (hEH hx), by rw [Nat.card_zpowers, hord]⟩) (mem_zpowers x)

theorem le_kSub_sup_inf (h : TwelveCtx G M p Q H) (hI : NineNineOneInput)
    (hL : pLayerIn p H ≤ M) : H ≤ kSub p M H ⊔ (H ⊓ M) := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c, hΓ⟩ := h.exists_E_sq
  have hd := h.hypCGen hE₀Q hE₀ hE₀c hΓ
  have hU : NineNineOne M p := hI G M E₀ H E₀ p hd.toNineSettingGen hd.not_mem_sigmaM
  have hKH : kSub p M H ≤ H := kSub_le p M H
  have hHN : H ≤ normalizer (kSub p M H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp (kSub_normal_of_le hL)
  obtain ⟨P, hP, hQP⟩ := exists_isSylowOf_ge (le_inf h.Q_le_H h.Q_le_M) h.Q_isPGroup
  have hPH :=
    (isSylowOf_of_NineNineOne h.maxLocal h.mem_QSet h.Q_le_H hd.not_mem_sigmaM hU hP).1
  have hPK := hPH.inf_of_le_normalizer hKH hHN
  have hE₀K := le_kSub_of_isElemAbelian hL hE₀ (hE₀Q.trans h.Q_le_H)
  have hN : normalizer ((P ⊓ kSub p M H : Subgroup G) : Set G) ≤ M :=
    hU.normalizer_le h.maxLocal (hE₀Q.trans h.Q_le_M) hE₀ hE₀c hΓ
      (le_inf (hE₀Q.trans hQP) hE₀K) (inf_le_left.trans (hP.le.trans inf_le_right))
  exact (CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf hKH hHN hPK).le.trans
    (sup_le_sup_left (inf_le_inf_left H hN) _)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
