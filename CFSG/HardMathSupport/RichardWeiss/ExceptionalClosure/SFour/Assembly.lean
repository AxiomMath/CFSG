module

public import CFSG.HardMathSupport.RichardWeiss.Coordinator.SFourClosure
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.CoreGen
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.EOffenderS4
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.SFour.Offender

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Open
  CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.RichardWeiss.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s_four_false_assembled {S L : Subgroup G}
    (hA : Asc81bHyp (L ⊔ S) S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    {r d : ℕ} (hr : r = 3 ∨ 5 ≤ r) (e : Fin d ≃ OmegaE r 4)
    (π : ↥⁅blockV S L, L⁆ →* Multiplicative (altHeart d)) (θ : ↥(L ⊔ S) →* Perm (Fin d))
    (hπ : Function.Surjective π)
    (hker : π.ker =
      (⁅blockV S L, L⁆ ⊓ Subgroup.centralizer (L : Set G)).subgroupOf ⁅blockV S L, L⁆)
    (hAlt : ∀ σ ∈ alternatingGroup (Fin d),
      ∃ l : ↥L, θ ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ = σ)
    (hequiv : SectionEquiv ⁅blockV S L, L⁆ (L ⊔ S) π θ)
    (hθV : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ Subgroup.centralizer (blockV S L : Set G))
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hW : ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) = Wr r 4)
    (hperf : ⁅L, L⁆ = L) : False := by
  have hD := eOffenderData_of_section hA e π θ hπ hequiv hθV hW.le
  have hd : d = 2 * r + 4 := by
    have h1 : d = Fintype.card (OmegaE r 4) := by
      rw [← Fintype.card_congr e]; simp
    simp only [OmegaE, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool] at h1
    omega
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.1 (hMV ((le_sup_left : L ≤ L ⊔ S) hl)) v⁻¹).1
      ((blockV S L).inv_mem hv)
    simpa [mul_assoc] using (blockV S L).mul_mem hv this
  have hcen : ∀ m : ↥(L ⊔ S), (m : G) ∈ Subgroup.centralizer (blockV S L : Set G) → θ m = 1 :=
    fun m hm => (theta_eq_one_iff (by omega) hπ hequiv hUV hθV m).2 hm
  have hVJ : blockV S L ≤ thompsonJ S :=
    blockV_le_thompsonJ_of_offender hA e π θ hπ hequiv hθV hMV hW.le
  have hAlt' : ∀ σ ∈ alternatingGroup (Fin d), ∃ m : ↥(L ⊔ S), θ m = σ := fun σ hσ => by
    obtain ⟨l, hl⟩ := hAlt σ hσ
    exact ⟨_, hl⟩
  obtain ⟨t, htJ, ht⟩ : ∃ t : ↥(L ⊔ S), (t : G) ∈ thompsonJ S ∧ (θ t).IsSwap := by
    have hk : 0 < r := by omega
    have hmem : swap (Sum.inl (⟨0, hk⟩, false) : OmegaE r 4) (Sum.inl (⟨0, hk⟩, true)) ∈
        ((thompsonJ S).subgroupOf (L ⊔ S)).map (e.permCongrHom.toMonoidHom.comp θ) :=
      hW ▸ swap_mem_Wr r 4 ⟨0, hk⟩
    obtain ⟨t, ht, hθt⟩ := hmem
    refine ⟨t, Subgroup.mem_subgroupOf.1 ht, e.symm (Sum.inl (⟨0, hk⟩, false)),
      e.symm (Sum.inl (⟨0, hk⟩, true)), by simp, ?_⟩
    apply e.permCongr.injective
    rw [permCongr_swap']
    simpa using hθt
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hZL := commutator_mem_blockV_of_mem_omegaOneCenter hS2 hperf θ hθS hcen hAlt' hD t ht htJ
  have hXL := commute_commutator_of_mem_omegaOneCenter hS2 hperf θ hθS hθV hcen hAlt' hD t ht htJ
  have hZC : ∀ z ∈ omegaOneCenterOf (thompsonJ S), ∀ v ∈ blockV S L, z * v = v * z := by
    intro z hz v hv
    exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf _ hz).2 v (hVJ hv)).symm
  have hne := commutator_ne_bot_of_offender hA hSL hr e π θ hπ hAlt hequiv hθV hθS hW
  exact s_four_false_of_centralizes hA hSL hr e π θ hker hAlt hequiv hθS hW hZC
    (fun z hz l hl => by rw [commutatorElement_def]; exact hZL z hz l hl) hXL hne

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
