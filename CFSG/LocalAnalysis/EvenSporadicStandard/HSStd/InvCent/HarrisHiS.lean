module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Defs
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.AutInn
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Derived
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HiS.CaseA
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HiS.Centralizer
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HiS.Odd
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.HiS.SwapFifteen
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.InnEquiv
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.NormalClosure
import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.SolomonRed

theorem orderOf_mul_of_orders_three_five {M : Type*} [Group M] {a b : M} (ha : orderOf a = 3)
    (hb : orderOf b = 5) (hab : a * b = b * a) : orderOf (a * b) = 15 := by
  rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (show Commute a b from hab)
    (by rw [ha, hb]; norm_num), ha, hb]

theorem natCard_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem false_of_equiv_alternatingGroup_six_le_centralizer {G : Type*} [Group G] [Finite G]
    {g : G}
    (f : ↥(centralizer ({g} : Set G)) ⧸ CFSG.Open.fusionOddCore ↥(centralizer ({g} : Set G)) ≃*
      Equiv.Perm (Fin 5))
    {X : Subgroup G} (hX : X ≤ centralizer ({g} : Set G))
    (ψ : ↥X ≃* alternatingGroup (Fin 6)) : False := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥X := ψ.isSimpleGroup
  exact false_of_simple_le_centralizer f hX inferInstance
    ((Nat.card_congr ψ.toEquiv).trans natCard_alternatingGroup_six)

theorem harris311HiS_of_cat (h : CatHarrisAS) (h15 : NoFifteen) (hout : OutNoOdd) :
    Harris311HiS := by
  intro G _ _ hK hO t ht ⟨e⟩ g hg ⟨f⟩
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hnab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a :=
    exists_noncommute_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
  have hR := rhyp_mulAut hnab
  have hL : centralizerDerived t =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map
        (embA e) := by
    rw [centralizerDerived_eq_map e, commutator_mulAut_alt6]
  obtain ⟨hiso⟩ := nonempty_mulEquiv_range_conj hnab
  let ι : ↥((MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map
      (embA e)) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.equivMapOfInjective _ (embA e) (embA_injective e)).symm.trans hiso
  obtain ⟨k, hk5, hgk⟩ := exists_order_five_commute f
  have hx15 : orderOf (g * k) = 15 := orderOf_mul_of_orders_three_five hg hk5 hgk
  rcases lemmaR hR hO ht e with htc | ⟨hS, hswap | ⟨S, hF, hle⟩⟩
  ·
    exfalso
    have hcent : centralizer ({t} : Set G) = ⊤ := by
      ext x
      simp only [mem_centralizer_singleton_iff, Subgroup.mem_top, iff_true]
      exact Subgroup.mem_center_iff.mp htc x
    let e' : G ≃* Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)) :=
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hcent.symm)).trans e
    exact false_of_order_fifteen_z2_mulAut e' (g * k) hx15
  ·
    exfalso
    obtain ⟨S₁, S₂, hs⟩ := hswap
    let ψ₁ : ↥S₁ ≃* alternatingGroup (Fin 6) := hs.iso.some.trans ι
    obtain ⟨ν⟩ := swapData_equiv_S₂ hs
    let ψ₂ : ↥S₂ ≃* alternatingGroup (Fin 6) := ν.symm.trans ψ₁
    have h₁ : OddInner ↥S₁ := OddInner.of_mulEquiv ψ₁.symm oddInner_alternatingGroup_six
    have h₂ : OddInner ↥S₂ := OddInner.of_mulEquiv ψ₂.symm oddInner_alternatingGroup_six
    have hno₁ : ∀ a : ↥S₁, orderOf a ≠ 15 := fun a ha =>
      no_order_fifteen_alternatingGroup_six (ψ₁ a) (by rw [MulEquiv.orderOf_eq]; exact ha)
    have hno₂ : ∀ a : ↥S₂, orderOf a ≠ 15 := fun a ha =>
      no_order_fifteen_alternatingGroup_six (ψ₂ a) (by rw [MulEquiv.orderOf_eq]; exact ha)
    have hgE : g ∈ layer G := odd_mem_layer_of_swapData hS hs h₁ h₂ g (by rw [hg]; decide)
    have hkE : k ∈ layer G := odd_mem_layer_of_swapData hS hs h₁ h₂ k (by rw [hk5]; decide)
    rcases swap_order_three_five hS hs hno₁ hno₂ hg hk5 hgk hgE hkE with ⟨hg1, -⟩ | ⟨hg2, -⟩
    · refine false_of_equiv_alternatingGroup_six_le_centralizer f (X := S₂) (fun b hb => ?_) ψ₂
      exact mem_centralizer_singleton_iff.2 (hs.commute g hg1 b hb).symm
    · refine false_of_equiv_alternatingGroup_six_le_centralizer f (X := S₁) (fun a ha => ?_) ψ₁
      exact mem_centralizer_singleton_iff.2 (hs.commute a ha g hg2)
  ·
    haveI := hF.simple
    have hBne : (MulAut.conj :
        alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range.map (embA e) ≠ ⊥ := by
      intro hbot
      obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
      rw [hbot, Subgroup.mem_bot] at ha hb
      exact hab (by rw [ha, hb])
    have hcat : Catalog ↥S :=
      CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK S (MonoidHom.id ↥S)
        Function.surjective_id
    have key : (LieModel ↥S .PSU 4 3 1 ∨ LieModel ↥S .PSL 3 3 2 ∨ LieModel ↥S .PSL 4 3 1) →
        False := by
      intro hlie
      have hodd : OddInner ↥S := hout ↥S hlie
      have hgS : g ∈ S := odd_mem_of_fixedData hF hodd g (by rw [hg]; decide)
      have hkS : k ∈ S := odd_mem_of_fixedData hF hodd k (by rw [hk5]; decide)
      have hord : orderOf ((⟨g, hgS⟩ : ↥S) * ⟨k, hkS⟩) = 15 :=
        orderOf_mul_of_orders_three_five (by rw [Subgroup.orderOf_mk]; exact hg)
          (by rw [Subgroup.orderOf_mk]; exact hk5) (Subtype.ext hgk)
      exact h15 ↥S hlie _ hord
    obtain ⟨a, ha, b, hb, hab⟩ := hF.nonab
    rcases h G S hF.normal hF.simple
      ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h' => hab (congrArg Subtype.val h')⟩ hcat hF.cent t ht ⟨e⟩
      with h1 | h1 | h1 | h1
    · exact (key (Or.inl h1)).elim
    · rw [hL, normalClosureOf_eq_of_le_simple hF.normal hF.simple hle hBne]
      exact h1
    · exact (key (Or.inr (Or.inl h1))).elim
    · exact (key (Or.inr (Or.inr h1))).elim

end CFSG.EvenSporadicStandard.HSStd.InvCent
