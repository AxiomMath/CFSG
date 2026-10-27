module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Components
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ReduceHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.RuAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23InputsHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputsHered

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

theorem ruBalanceHered_of_full_aut (hC : CatalogNoRuFull) (hA : RuAutInner) :
    RuBalanceHered := by
  intro H _ _ hH N hN hidx hK M v hv hMC hM hSyl
  have hnot : ¬ CFSG.Blueprint.Catalog ↥N := fun hcat => hC H N hN hidx hcat M v hv hMC hM
  have hO : CFSG.oddCore ↥(centralizer ({v} : Set H)) = ⊥ := by
    by_contra hne
    exact hnot (catalog_of_unbalanced_of_uhered hH hN hidx hK hv hne)
  have hvC : v ∈ centralizer ({v} : Set H) := mem_centralizer_singleton_iff.2 rfl
  have hMle : M ≤ centralizer ({v} : Set H) := hMC.1
  have h4M : 4 ∣ Nat.card M := four_dvd_card_of_isQuasisimple hM.1
  have h4 : ¬ 4 ∣ Nat.card (centralizer (M : Set H)) := not_four_dvd_card_of_sylow hSyl
  have hnorm : ∀ c ∈ centralizer ({v} : Set H), ∀ m ∈ M, c * m * c⁻¹ ∈ M :=
    fun c hc m hm => isCompIn_conj_mem hMC h4M h4 hc hm
  have hvM : v ∈ centralizer (M : Set H) := by
    rw [mem_centralizer_iff]
    intro m hm
    exact mem_centralizer_singleton_iff.1 (hMle hm)
  have hD := centralizer_inf_eq_zpowers hO hvC hv hnorm hvM h4
  have : Group.IsPerfect ↥M := hM.1.1
  have hOut : ∀ φ : MulAut (↥M ⧸ center ↥M), ∃ y, φ = MulAut.conj y := by
    obtain ⟨e⟩ := hM.2.2
    exact fun φ => mulAut_inner_of_mulEquiv e hA φ
  exact le_antisymm (centralizer_le_sup_zpowers hMle hnorm hOut hD)
    (sup_le hMle (zpowers_le.2 hvC))

theorem fi23BalanceHered_of_full (hC : CatalogFi23HostFull) : Fi23BalanceHered := by
  intro H _ _ hH N L hN hidx hK hstd hL hSyl t htL ht2
  have htC : t ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 rfl
  have hLC : L ≤ centralizer ({t} : Set H) := fun x hx =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htL x hx)
  have hCt : centralizer ({t} : Set H) ≤ normalizer (L : Set H) :=
    centralizer_le_normalizer_of_stdBare hstd.stdBare ht2 htL
  have hLnorm : ∀ c ∈ centralizer ({t} : Set H), ∀ l ∈ L, c * l * c⁻¹ ∈ L :=
    fun c hc l hl => (mem_normalizer_iff.1 (hCt hc) l).1 hl
  have hcomp : IsCompIn L (centralizer ({t} : Set H)) :=
    isCompIn_of_normal hLC hL.1 ((Subgroup.normal_subgroupOf_iff_le_normalizer hLC).2 hCt)
  by_cases h2 : N.index = 2
  · obtain ⟨-, hcent⟩ := hC H N hN hidx (catalog_of_index_two hN h2 hK) L t ht2 hcomp hL
    rw [hcent]
    exact inf_eq_left.2 (zpowers_le.2 htC)
  · have hNtop : N = ⊤ := eq_top_of_index_ne_two hidx h2
    have hO : CFSG.oddCore ↥(centralizer ({t} : Set H)) = ⊥ := by
      by_contra hne
      have hcat := catalog_of_unbalanced_of_uhered hH hN hidx hK ht2 hne
      exact (hC H N hN hidx hcat L t ht2 hcomp hL).1 (hNtop ▸ mem_top t)
    exact centralizer_inf_eq_zpowers hO htC ht2 hLnorm htL (not_four_dvd_card_of_sylow hSyl)

end CFSG.EvenSporadicStandard.Induction.Balance
