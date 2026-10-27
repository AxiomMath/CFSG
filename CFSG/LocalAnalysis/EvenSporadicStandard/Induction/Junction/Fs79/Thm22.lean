module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.TwoRank
import CFSG.GroupTheory.OddOverlap

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem LtF.toLt {K L : Subgroup H} (h : LtF K L) : Lt K L := by
  obtain ⟨s, t, hs, ht, hst, hK, hL, hKL⟩ := h
  have hcs : centralizer ((zpowers s : Subgroup H) : Set H) = centralizer ({s} : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hct : centralizer ((zpowers t : Subgroup H) : Set H) = centralizer ({t} : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have ht1 : t ≠ 1 := by rintro rfl; simp at ht
  refine ⟨zpowers s, zpowers t, (zpowers_ne_bot).2 hs1, (zpowers_ne_bot).2 ht1,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs]; norm_num),
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num), ?_, hcs ▸ hK, hct ▸ hL,
    ?_⟩
  · have hcomm : ⁅zpowers s, zpowers t⁆ = ⊥ := by
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rw [hct]
      exact (centralizer ({t} : Set H)).zpow_mem (mem_centralizer_singleton_iff.2 hst) k
    rw [hcomm]
    exact bot_le
  · refine hKL.trans (sup_le ?_ ?_)
    · have := le_iSup₂ (f := fun g (_ : g ∈ zpowers s) => L.map (MulAut.conj g).toMonoidHom) 1
        (one_mem _)
      have h1 : L.map (MulAut.conj (1 : H)).toMonoidHom = L := by
        ext y
        simp
      rw [h1] at this
      exact this
    · exact le_iSup₂ (f := fun g (_ : g ∈ zpowers s) => L.map (MulAut.conj g).toMonoidHom) s
        (mem_zpowers s)

variable [Finite H]

omit [Finite H] in
theorem mem_normalizer_of_stdBare_of_involution {L : Subgroup H} (hL : StdBare L) {t g : H}
    (ht : orderOf t = 2) (htL : t ∈ centralizer (L : Set H)) (hg : g * t = t * g) :
    g ∈ normalizer (L : Set H) :=
  StandardSubgroupAPI.mem_of_odd_inf_map_conj_of_commute hL.2 htL ht hg

theorem eq_of_ltF_of_stdBare {K L : Subgroup H} (hL : StdBare L) (h : LtF K L)
    (hcq : cqOrd K = cqOrd L) : K = L := by
  obtain ⟨s, t, hs, ht, hst, hK, hLc, hKL⟩ := h
  have htL : t ∈ centralizer (L : Set H) :=
    mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hLc.1 hl)
  have hsN := mem_normalizer_of_stdBare_of_involution hL ht htL hst
  have hKL' : K ≤ L := by
    refine hKL.trans (sup_le le_rfl ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact ((Subgroup.mem_normalizer_iff.1 hsN) x).1 hx
  exact eq_of_le_of_cqOrd_eq hKL' hK.isQuasisimple hLc.isQuasisimple hcq

end CFSG.EvenSporadicStandard.Induction

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup Relation CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus

theorem sol78Thm22At_of_balance {H : Type} [Group H] [Finite H] (h13 : FS79Thm13UseAt H)
    (hbal : LayerBalanceKAt H) (hQ : Sol78RankOne) : Sol78Thm22At H := by
  intro hkp N hN hidx A hA hrank
  obtain ⟨⟨T₀, hT₀ne, hT₀, hAT⟩, hmax⟩ := hA
  have hAq : CFSG.IsQuasisimple ↥A := hAT.isQuasisimple
  obtain ⟨t, ht2, htmem, htc⟩ := exists_involution_center hT₀ hT₀ne
  have hts : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht2
  have hT : zpowers t ≠ ⊥ := fun h => by
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht2
    omega
  have hWT : T₀ ≤ normalizer ((zpowers t : Subgroup H) : Set H) := fun x hx =>
    mem_normalizer_zpowers_of_commute (htc x hx)
  have hK' : IsCompIn A (centralizer ((T₀ ⊔ zpowers t : Subgroup H) : Set H)) := by
    rw [sup_eq_left.2 (zpowers_le.2 htmem)]
    exact hAT
  have hO : CFSG.oddCore H = ⊥ := hN.oddCore_eq_bot
  have hAL : A ≤ layerIn (centralizer ((zpowers t : Subgroup H) : Set H)) :=
    hbal hkp hO T₀ t hT₀ ht2 htmem htc A hAT
  obtain ⟨M, hM, hAM⟩ := exists_isCompIn_le_conjClosure hWT hK' hAL
  have hM' : IsCompIn M (centralizer ({t} : Set H)) := by
    rw [← centralizer_zpowers_eq]
    exact hM
  have hcomm : ⁅T₀, zpowers t⁆ ≤ T₀ ⊓ zpowers t := by
    have : ⁅T₀, zpowers t⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => by
      rw [centralizer_zpowers_eq]
      exact mem_centralizer_singleton_iff.2 (htc x hx)
    rw [this]
    exact bot_le
  have hLtAM : Lt A M := ⟨T₀, zpowers t, hT₀ne, hT, hT₀, hts, hcomm, hAT, hM, hAM⟩
  obtain ⟨L, hML, hLmax, -⟩ := exists_maximalF_above (⟨t, ht2, hM'⟩ : InLF M)
  have hreach : ∀ X, ReflTransGen LtF M X → TransGen Lt A X := by
    intro X hX
    induction hX with
    | refl => exact TransGen.single hLtAM
    | tail _ hstep ih => exact ih.tail hstep.toLt
  have hcq : ∀ X, ReflTransGen LtF M X → cqOrd A = cqOrd X := fun X hX => by
    obtain ⟨e⟩ := hmax X (hreach X hX)
    exact Nat.card_congr e.toEquiv
  have hLreach : ReflTransGen LtF M L := by
    rcases hML with rfl | h
    · exact ReflTransGen.refl
    · exact h.to_reflTransGen
  have hLq : CFSG.IsQuasisimple ↥L := hLmax.1.isQuasisimple
  have hstdL : StdBare L := by
    refine h13 hkp N hN (perfect_subgroups_le_of_index_le_two hN.normal hidx) L hLmax
      fun hr1 => ?_
    have hexc : ExcType ↥L := hQ ↥L hLq hr1
    obtain ⟨e⟩ := hmax L (hreach L hLreach)
    have hA3 := pRank_two_le_two_of_excType hAq (ExcType.of_cqEquiv e hexc)
    omega
  have hcollapse : ∀ X, ReflTransGen LtF X L → ReflTransGen LtF M X → X = L := by
    intro X hXL
    induction hXL using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ => rfl
    | head hXY hYL ih =>
      rename_i X Y
      intro hMX
      have hMY : ReflTransGen LtF M Y := hMX.tail hXY
      have hY : Y = L := ih hMY
      subst hY
      exact eq_of_ltF_of_stdBare hstdL hXY ((hcq X hMX).symm.trans (hcq Y hMY))
  have hMeq : M = L := hcollapse M hLreach ReflTransGen.refl
  have hLc : IsCompIn L (centralizer ({t} : Set H)) := hMeq ▸ hM'
  have hAM' : A ≤ conjClosure L T₀ := hMeq ▸ hAM
  have htL : t ∈ centralizer (L : Set H) :=
    mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (hLc.1 hl)
  have hT₀N : T₀ ≤ normalizer (L : Set H) := fun g hg =>
    mem_normalizer_of_stdBare_of_involution hstdL ht2 htL (htc g hg)
  have hAle : A ≤ L := hAM'.trans (conjClosure_le_of_le_normalizer le_rfl hT₀N)
  have hAeq : A = L := eq_of_le_of_cqOrd_eq hAle hAq hLq (hcq L hLreach)
  rw [hAeq]
  exact hstdL

end CFSG.EvenSporadicStandard.Induction.Junction
