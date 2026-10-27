module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertM12
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertU33
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.CertG23
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S3.RowFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.AEmpty

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.Blueprint
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A

section Group

variable {Y : Type} [Group Y] [Finite Y]

theorem le_centralizer_of_inf_eq_bot {A B : Subgroup Y} [A.Normal] [B.Normal] (h : A ⊓ B = ⊥) :
    A ≤ Subgroup.centralizer (B : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 := Subgroup.commutator_le_inf A B (Subgroup.commutator_mem_commutator hx hb)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem inf_eq_bot_or_le {N H : Subgroup Y} [N.Normal] [H.Normal] (hs : IsSimpleGroup ↥N) :
    H ⊓ N = ⊥ ∨ N ≤ H := by
  have hn : ((H ⊓ N).subgroupOf N).Normal := Subgroup.Normal.subgroupOf inferInstance N
  haveI := hs
  rcases hn.eq_bot_or_eq_top with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥N) ∈ (H ⊓ N).subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · right
    intro x hx
    have : (⟨x, hx⟩ : ↥N) ∈ (H ⊓ N).subgroupOf N := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem oddCore_eq_bot_of_normal {N : Subgroup Y} [N.Normal] (hs : IsSimpleGroup ↥N) {t : Y}
    (htN : t ∈ N) (ht : t * t = 1) (ht1 : t ≠ 1) (hC : Subgroup.centralizer (N : Set Y) = ⊥) :
    classicalInvolutionOddCore Y = ⊥ := by
  rcases inf_eq_bot_or_le (H := classicalInvolutionOddCore Y) hs with h | h
  · rw [eq_bot_iff, ← hC]
    exact le_centralizer_of_inf_eq_bot h
  · exfalso
    have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
    have h2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) ht1
    have hdvd : orderOf t ∣ Nat.card (classicalInvolutionOddCore Y) := by
      rw [← Subgroup.orderOf_mk t (h htN)]
      exact orderOf_dvd_natCard _
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem omegaGen_q8Fam_eq_top {N : Subgroup Y} [N.Normal] (hs : IsSimpleGroup ↥N)
    (hC : Subgroup.centralizer (N : Set Y) = ⊥) (hidx : N = ⊤ ∨ N.index = 2) {T : Subgroup Y}
    (hT : T ∈ q8Fam Y) (hTN : N.index = 2 → ¬ T ≤ N) : omegaGen (q8Fam Y) = ⊤ := by
  haveI : (omegaGen (q8Fam Y)).Normal := omegaGen_normal conjInvariant_q8Fam
  have hTH : T ≤ omegaGen (q8Fam Y) := le_omegaGen hT
  rcases inf_eq_bot_or_le (H := omegaGen (q8Fam Y)) hs with h | h
  · exfalso
    have h1 := le_centralizer_of_inf_eq_bot h
    rw [hC] at h1
    have hT8 := card_eq_eight hT
    have hTb : T = ⊥ := le_bot_iff.mp (hTH.trans h1)
    rw [hTb, Subgroup.card_bot] at hT8
    norm_num at hT8
  · rcases hidx with htop | hidx
    · rw [htop] at h
      exact top_le_iff.mp h
    · obtain ⟨t, htT, htN⟩ := Set.not_subset.mp (hTN hidx)
      rw [eq_top_iff]
      intro y _
      by_cases hy : y ∈ N
      · exact h hy
      · have h1 : y * t⁻¹ ∈ N := (Subgroup.mul_mem_iff_of_index_two hidx).mpr
          (iff_of_false hy fun h2 => htN (by simpa using N.inv_mem h2))
        have := Subgroup.mul_mem _ (h h1) (hTH htT)
        rwa [inv_mul_cancel_right] at this

end Group

@[expose] def RowClassAEmptyG23 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], classicalInvolutionOddCore X = ⊥ →
    CFSG.Blueprint.LieModel X .G2 0 3 1 →
    ∀ K : Subgroup X, TypeRHyp (CoreAssembly.conjClass K) → AEmpty (CoreAssembly.conjClass K) K

section Facts

theorem rowClassAEmpty_of_g23 (hG : RowClassAEmptyG23) : S7.RowClassAEmpty := by
  intro X _ _ hO h2 hmod K hK
  have hKm : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨z, hz⟩ := (hK.hyp.omega1 K hKm).1
  rcases hmod with hG23 | ⟨N, hN, hidx, hLie⟩ | hM12
  · exact hG X hO hG23 K hK
  · haveI := hN
    have hC := S5.centralizer_eq_bot_of_u33 hidx hLie h2
    obtain ⟨θ, -⟩ := S5.exists_u33_model hidx hLie hC
    obtain ⟨a, haK, haz⟩ := S3.exists_mul_self_eq hK hKm hz
    have hzN : z ∈ N := haz ▸ Subgroup.mul_self_mem_of_index_two hidx a
    have hzC := S3.oddCore_centralizer_eq_bot_of_index_two hidx hzN
      (S3.oddCore_centralizer_eq_bot_of_u33 hLie (Subtype.ext hz.sq)
        fun h => hz.ne_one (congrArg Subtype.val h))
    exact aEmpty_of_model θ hK (nonempty_q8_of_typeRHyp hK hz hzC) U33S7.aEmpty_q8
  · obtain ⟨θ₀⟩ := hM12
    let θ : X ≃* NativeSporadic.M12 := θ₀
    have hzC := S3.oddCore_centralizer_eq_bot_of_m12 ⟨θ₀⟩ hz.sq hz.ne_one
    exact aEmpty_of_model θ hK (nonempty_q8_of_typeRHyp hK hz hzC) M12S7.aEmpty_q8

theorem rowClassAEmptyG23_proved : RowClassAEmptyG23 := by
  intro X _ _ _ hG23 K hK
  have hKm : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨z, hz⟩ := (hK.hyp.omega1 K hKm).1
  obtain ⟨θ₀⟩ :=
    HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel hG23
  have hzC := S3.oddCore_centralizer_eq_bot_of_g23 hG23 hz.sq
  have hfin : Finite RankThree.PartTwo.Census.Carrier.G2Three.H3 :=
    Nat.finite_of_card_ne_zero (by rw [RankThree.PartTwo.Census.Carrier.G2Three.card_R3]; norm_num)
  exact @aEmpty_of_model RankThree.PartTwo.Census.Carrier.G2Three.H3 inferInstance hfin X _ _
    (θ₀.trans RankThree.PartTwo.Census.Carrier.G2Three.adjointEquivR3) K hK
    (nonempty_q8_of_typeRHyp hK hz hzC) G23S7.aEmpty_q8

theorem rowClassAEmpty_proved : S7.RowClassAEmpty :=
  rowClassAEmpty_of_g23 rowClassAEmptyG23_proved

theorem inspectionFacts_proved : S7.InspectionFacts := by
  intro Y _ _ hmod K hK
  rcases hmod with ⟨N, hN, hidx, hLie, hC⟩ | hM12
  · haveI := hN
    obtain ⟨θ, hθ⟩ := S5.exists_u33_model hidx hLie hC
    obtain ⟨hA, hV⟩ := U33S7.aStar_vStar θ K hK
    refine thm3RConclG_of_aStar_vStar hA hV ?_
    obtain ⟨h1, h2, -, hi1, -, hout⟩ := U33S7.basic_spec
    have hs := (PhilipHall.Frame.u33_isSimpleGroup hLie).1
    have hI1 := isUniqueInvolution_closure_pair h1
    have htN : θ.symm (U33S7.i1A * U33S7.i1A) ∈ N := by
      rw [← hθ, MulEquiv.apply_symm_apply]
      exact Subgroup.mul_mem _ hi1 hi1
    have hO : classicalInvolutionOddCore Y = ⊥ := oddCore_eq_bot_of_normal hs htN
      (by rw [← map_mul, hI1.sq, map_one]) (fun h => hI1.ne_one (θ.symm.injective
        (h.trans (map_one θ.symm).symm)))
      hC
    have hQ2 : U33S7.Q2.map θ.symm.toMonoidHom ∈ q8Fam Y :=
      map_mem_q8Fam θ.symm (nonempty_closure_pair_mulEquiv h2)
    have htop : omegaGen (q8Fam Y) = ⊤ := by
      refine omegaGen_q8Fam_eq_top hs hC (Or.inr hidx) hQ2 fun _ hle => hout ⟨?_, ?_⟩
      · have := hle (Subgroup.mem_map_of_mem _
          (Subgroup.subset_closure (Set.mem_insert U33S7.i2A _)))
        rw [← hθ] at this
        simpa using this
      · have := hle (Subgroup.mem_map_of_mem _
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton U33S7.j2A))))
        rw [← hθ] at this
        simpa using this
    rw [htop]
    set e := S5.secQuotTopEquiv' hO
    refine Or.inr (Or.inl ⟨N.map e.toMonoidHom, hN.map _ e.surjective,
      (Subgroup.index_map_equiv N e).trans hidx,
      CFSG.Blueprint.LieModel.of_mulEquiv (N.equivMapOfInjective e.toMonoidHom e.injective)
        hLie⟩)
  · obtain ⟨θ₀⟩ := hM12
    let θ : Y ≃* NativeSporadic.M12 := θ₀
    obtain ⟨hA, hV⟩ := M12S7.aStar_vStar θ K hK
    refine thm3RConclG_of_aStar_vStar hA hV ?_
    obtain ⟨h1, -, hz1, -, -⟩ := M12S7.basic_spec
    haveI : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    haveI : IsSimpleGroup Y := θ.isSimpleGroup
    have hs : IsSimpleGroup ↥(⊤ : Subgroup Y) := Subgroup.topEquiv.isSimpleGroup
    have hC : Subgroup.centralizer ((⊤ : Subgroup Y) : Set Y) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ, eq_bot_iff]
      intro x hx
      have h3 : θ x ∈ Subgroup.center NativeSporadic.M12 := by
        rw [Subgroup.mem_center_iff]
        intro m
        obtain ⟨y, rfl⟩ := θ.surjective m
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      rw [CFSG.Sporadic.Schreier.m12_center_eq_bot', Subgroup.mem_bot] at h3
      exact Subgroup.mem_bot.mpr (θ.injective (h3.trans (map_one θ).symm))
    have hI1 := isUniqueInvolution_closure_pair h1
    have hO : classicalInvolutionOddCore Y = ⊥ := oddCore_eq_bot_of_normal hs
      (Subgroup.mem_top (θ.symm (Certificates.S7M12.i1 * Certificates.S7M12.i1)))
      (by rw [← map_mul, hI1.sq, map_one])
      (fun h => hI1.ne_one (θ.symm.injective (h.trans (map_one θ.symm).symm))) hC
    have hQ1 : M12S7.Q1.map θ.symm.toMonoidHom ∈ q8Fam Y :=
      map_mem_q8Fam θ.symm (nonempty_closure_pair_mulEquiv h1)
    have htop : omegaGen (q8Fam Y) = ⊤ :=
      omegaGen_q8Fam_eq_top hs hC (Or.inl rfl) hQ1 fun h => by
        rw [Subgroup.index_top] at h
        exact absurd h (by norm_num)
    rw [htop]
    exact Or.inr (Or.inr (Or.inl ⟨(S5.secQuotTopEquiv' hO).symm.trans θ₀⟩))

end Facts

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
