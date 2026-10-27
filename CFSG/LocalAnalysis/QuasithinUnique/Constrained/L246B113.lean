module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Three
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Cited
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

section Stable

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_offender_of_ffJP {G T K : Subgroup (MulAut V)} {Pst : Set (Subgroup (MulAut V))}
    (hst : IsStableFF G Pst) (hK : CFSG.Open.IsQuasisimple ↥K ∨ Nat.card ↥K = 3)
    (hKJ : ⁅K, ffJP Pst T⁆ = K) : ∃ A, IsFFStarOffender G A ∧ A ≤ T ∧ ⁅K, A⁆ = K := by
  have hJN : ffJP Pst T ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    le_normalizer_of_commutator_eq hKJ
  have hK0 : K ≠ ⊥ := B113.ne_bot_of_quasisimple_or_card_three hK
  obtain ⟨A, hAP, hAT, hAc⟩ : ∃ A ∈ Pst, A ≤ T ∧
      ¬ A ≤ Subgroup.centralizer (K : Set (MulAut V)) := by
    by_contra hcon
    push Not at hcon
    apply hK0
    have hle : ffJP Pst T ≤ Subgroup.centralizer (K : Set (MulAut V)) :=
      iSup₂_le fun A hA => iSup_le fun hAT => hcon A hA hAT
    have h1 : ⁅K, ffJP Pst T⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    rwa [hKJ] at h1
  have hAJ : A ≤ ffJP Pst T := le_iSup₂_of_le A hAP (le_iSup_of_le hAT le_rfl)
  have hAX : ∀ b ∈ A, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
    (Subgroup.mem_normalizer_iff.mp (hJN (hAJ hb)) k).mp hk
  refine ⟨A, hst.2.1 A hAP, hAT, ?_⟩
  rcases B1Red.commutator_eq_or_commute hK hAX with h | h
  · exact h
  · exact absurd (fun b hb => Subgroup.mem_centralizer_iff.2 fun k hk => (h b hb k hk).symm) hAc

theorem ffJ_le_normalizer_of_stable (hP4 : AsB15Part4) (hV : ∀ v : V, v ^ 2 = 1)
    {G T K : Subgroup (MulAut V)} {Pst : Set (Subgroup (MulAut V))}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hst : IsStableFF G Pst)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hsub : IsSubnormal K (K ⊔ T))
    (hKJ : ⁅K, ffJP Pst T⁆ = K) : ffJ T ≤ Subgroup.normalizer (K : Set (MulAut V)) := by
  rcases hK with hq | h3
  · refine iSup₂_le fun A hA => ?_
    have hAH : IsFFStarOffender (K ⊔ T) A := ⟨hA.1.trans le_sup_right, hA.2.1, hA.2.2.1, hA.2.2.2⟩
    have hcomp : CFSG.Open.IsComponentOf K (K ⊔ T) :=
      ⟨le_sup_left, hsub, B1Red.isQuasisimple_to_open hq⟩
    exact hP4 V hV (K ⊔ T) A hAH K hcomp
  · obtain ⟨A, hAG, hAT, hAK⟩ := exists_offender_of_ffJP hst (Or.inr h3) hKJ
    have hsub' : IsSubnormal K (T ⊔ K) := by rwa [sup_comm] at hsub
    have hAT' : IsFFStarOffender T A := ⟨hAT, hAG.2.1, hAG.2.2.1, hAG.2.2.2⟩
    exact B1Red.ffJ_le_normalizer_of_card_three hV hT.2.1 h3 hsub' hAT' hAK

theorem commutator_ffJ_eq_of_stable (hP4 : AsB15Part4) (hV : ∀ v : V, v ^ 2 = 1)
    {G T K : Subgroup (MulAut V)} {Pst : Set (Subgroup (MulAut V))}
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T G) (hst : IsStableFF G Pst)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) (hsub : IsSubnormal K (K ⊔ T))
    (hKJ : ⁅K, ffJP Pst T⁆ = K) : ⁅K, ffJP {A | IsFFStarOffender G A} T⁆ = K := by
  rw [B113.ffJP_eq_ffJ hT.1]
  apply le_antisymm
  · exact commutator_le_of_normalizes (ffJ_le_normalizer_of_stable hP4 hV hT hst hK hsub hKJ)
  · refine le_trans (le_of_eq hKJ.symm) (Subgroup.commutator_mono le_rfl ?_)
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    exact B6.le_ffJ ⟨hAT, (hst.2.1 A hA).2.1, (hst.2.1 A hA).2.2.1, (hst.2.1 A hA).2.2.2⟩

end Stable

section Translate

theorem nonempty_sl3_of_isPSL {K : Type} [Group K] (h : IsPSL 3 2 1 K) :
    Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
    (by rw [hcard]; norm_num))⟩

variable {V : Type} [CommGroup V]

theorem b113Concl_of_conclusion {G K : Subgroup (MulAut V)} (h : B113Conclusion G K) :
    B113Concl G K := by
  rcases h with ⟨h3, hF, hC⟩ | ⟨hcomp, -⟩ | ⟨L, hL, hKL, m, hm, hrest⟩
  · exact Or.inl ⟨h3, le_inf hF hC⟩
  · exact Or.inr (Or.inl hcomp)
  · refine Or.inr (Or.inr ⟨L, hL, hKL, m, hm, ?_⟩)
    rcases hrest with ⟨n, hn, hK⟩ | ⟨hK, hm7⟩
    · exact Or.inl ⟨n, hn, hK⟩
    · exact Or.inr ⟨nonempty_sl3_of_isPSL hK, hm7⟩

end Translate

theorem asB113With_of_inputs (KP : ∀ (Y : Type) [Group Y], Prop)
    (hI : AsB113InputsList (IsSQTKQuotient KP)) : AsB113With KP := by
  intro V _ _ hV G T K Pst hSQ hO2 hT hst hKG hK hsub hKJ
  have hKJ' := commutator_ffJ_eq_of_stable hI.timmesfeld hV hT hst hK hsub hKJ
  exact b113Concl_of_conclusion (B1_13_list hV hI hSQ hO2 hT hKG hK hsub hKJ')

end CFSG.QuasithinUnique.Bridge
