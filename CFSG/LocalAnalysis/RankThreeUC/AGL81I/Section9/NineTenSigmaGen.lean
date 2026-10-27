module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenQuotGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenSigma

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {Q H E : Subgroup G} {k : ℕ}

namespace NineSettingGen

theorem isPSLType_oPPrimeHull_quotKer_of_hom_perm_four (h : NineSettingGen G M 3 Q H E k)
    (hp : 3 ∉ sigmaM G M) (hU : NineNineOne M 3) {X Γ : Type} [Group X] [Group Γ]
    (σ : X →* Equiv.Perm (Fin 4)) (π : X →* QuotKer M H) (hπ : Function.Surjective π)
    (ρ : X →* Γ) (hρ : ρ.ker ≤ π.ker) (hσ : ∀ x, σ x = 1 → ρ x ∈ Subgroup.center Γ) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) := by
  have hker : σ.ker ≤ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    exact map_eq_one_of_map_mem_center ρ π hπ hρ (h.center_quotKer_eq_bot hp hU) (hσ x hx)
  obtain ⟨e⟩ := nonempty_mulEquiv_oPPrimeHull_of_hom (alternatingGroup (Fin 4))
    card_alternatingGroup_four
    (fun x hx => mem_alternatingGroup_of_odd_orderOf x
      (hx.elim fun k hk => hk ▸ Odd.pow (by decide))) σ π hπ hker
    (h.dvd_card_quotKer hp hU) (h.pCore_quotKer_eq_bot hp hU)
  exact isPSLType_two_three_of_mulEquiv_alternatingGroup e

theorem isPSLType_oPPrimeHull_quotKer_of_lines (h : NineSettingGen G M 3 Q H E k)
    (hp : 3 ∉ sigmaM G M) (hU : NineNineOne M 3) {V : Type} [Group V] [Finite V]
    (hVc : ∀ a b : V, a * b = b * a) (hV3 : ∀ v : V, v ^ 3 = 1) (hV : Nat.card V = 27)
    (D : Fin 3 → Subgroup V) (hD : ∀ i, Nat.card (D i) = 3) (hDV : (⨆ i, D i) = ⊤)
    {X : Type} [Group X] (ρ : X →* MulAut V)
    (hρ : ∀ x i, ∃ j, (D i).map (ρ x).toMonoidHom = D j) (π : X →* QuotKer M H)
    (hπ : Function.Surjective π) (hρπ : ρ.ker ≤ π.ker) :
    IsPSLType 2 (ZMod 3) ↥(oPPrimeHull 3 (⊤ : Subgroup (QuotKer M H))) := by
  obtain ⟨σ, hσ⟩ := exists_hom_perm_four_of_lines hVc hV3 hV D hD hDV ρ hρ
  exact h.isPSLType_oPPrimeHull_quotKer_of_hom_perm_four hp hU σ π hπ ρ hρπ
    (fun x hx => (hσ x hx).elim (fun h1 => by rw [h1]; exact Subgroup.one_mem _)
      fun hinv => mem_center_mulAut_of_forall_eq_inv hinv)

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
