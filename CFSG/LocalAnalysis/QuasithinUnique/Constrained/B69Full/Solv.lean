module

public import CFSG.Quasithin.Background.B69SolvStruct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B69

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}

theorem structConclP_of_solvable (hV : ∀ v : V, v ^ 2 = 1) (h : MinParabolic X T M)
    (hO : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) (hsolv : Group.IsSolvable ↥X) :
    ∃ 𝓗 : Finset (Subgroup (MulAut V)), StructConcl X T M 𝓗 ∧
      (∀ g ∈ X, ∀ H ∈ 𝓗, B6.conjSub g H ∈ 𝓗) ∧
      ∀ H ∈ 𝓗, ∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e ∧
        M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) := by
  have hO' := normal_two_subgroups_trivial_of_pCoreOf_eq_bot hO
  have hJX := B1.closure_transvectionsIn_le X
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO'
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X))) =
      Subgroup.closure (transvectionsIn X) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  have hffJ : ffJ X = ⨆ H ∈ 𝓗, H := hb.ffJ_eq hV hsolv hO'
  have hJ' : ffJ X = Subgroup.closure (transvectionsIn X) := hffJ.trans hb.iSup_eq
  have hnat : ∀ H ∈ 𝓗, ∃ e : ℕ, 1 ≤ e ∧
      BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e ∧
        M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V)) := by
    intro H hH
    refine ⟨1, le_rfl, ?_, ?_⟩
    · have hHJ : H ≤ ffJ X :=
        hffJ ▸ le_iSup₂ (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => K) H hH
      have hZ : commV H ⊓ fixV (ffJ X) = ⊥ := by
        refine le_bot_iff.1 ?_
        calc commV H ⊓ fixV (ffJ X) ≤ commV H ⊓ fixV H := inf_le_inf_left _ (fixV_anti hHJ)
          _ = ⊥ := by
            rw [inf_comm, commV_eq_commSub]
            exact IsTransvectionBlocks.fixV_inf_commSub hV hb hH
      have hnat := FFC.binaryNaturalSL_two_of_s3 hV (hb.card_eq H hH) (U := commV H) (C := ⊥)
        (by rw [commV_eq_commSub]; exact hb.card_comm H hH)
        (by rw [commV_eq_commSub]; exact hb.stab H hH)
        (fun g hg hgu => by
          have hmem : g ∈ H ⊓ centSub (commSub (⊤ : Subgroup V) H) :=
            ⟨hg, fun u hu => hgu u (by rwa [commV_eq_commSub])⟩
          rw [hb.inf_centSub hH, Subgroup.mem_bot] at hmem
          exact hmem)
        (fun g _ c hc => by
          rw [Subgroup.mem_bot] at hc
          rw [hc, map_one]
          exact Subgroup.one_mem _)
        (inf_bot_eq _)
      rw [sup_bot_eq] at hnat
      rw [hZ]
      exact hnat
    · rw [inf_M_eq hV h hO hFF hb hffJ hH, inf_normalizer_eq_of_card (hb.card_eq H hH) inf_le_right
        (card_inf_eq_two hV h hO hFF hb hffJ hH) (exists_two_involutions hV hb hH)]
  refine ⟨𝓗, ⟨fun H hH => (hb.le_J hH).trans hJX, hffJ, hb.comm,
    fun H hH => hb.inf_biSup_ne_eq_bot hH, ?_, fun H hH => ?_, ?_,
    fun H hH H' hH' => exists_conjSub_of_blocks hV h hO hFF hb hffJ hH hH',
    h.eq_sup_ffJ hO hFF, fun H hH => Or.inl (hnat H hH)⟩,
    fun g hg H hH => conjSub_mem_of_blocks hV hb hffJ hg hH, hnat⟩
  · rw [hJ', commV_iSup_eq hb]
  · rw [hJ']
    exact commSub_sup_fixV_inf hV hb hH
  · intro H hH H' hH' hne
    rw [commSub_eq_bot_iff]
    intro u hu g hg
    rw [commV_eq_commSub] at hu
    exact hb.triv H' hH' H hH (Ne.symm hne) g hg u hu

end B69

end CFSG.Quasithin
