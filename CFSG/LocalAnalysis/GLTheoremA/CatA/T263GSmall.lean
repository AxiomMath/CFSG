module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GVac
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bL27
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bL28
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bU33
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTits
import CFSG.GH74.GLS.LU.Local.FiveCbarF

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

theorem t263_n_eq_one_of_mark {lab : CFSG.Assembly.LargeEvenLabel}
    (hc : CFSG.StandardType.markChar lab = 2) (hd : CFSG.StandardType.markDeg lab = 1) : lab.n = 1 := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp [CFSG.StandardType.markChar, CFSG.StandardType.markDeg] at hc hd ⊢ <;>
    (try split_ifs at hd) <;> omega

theorem t263_not_sq_dvd_120 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 2 ∣ 120 := by
  intro hd
  have hpd : p ∣ 2 ^ 3 * 3 * 5 := (dvd_pow_self p two_ne_zero).trans hd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      subst this
      norm_num at hd
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).1 h
    subst this
    norm_num at hd

theorem t263_card_mulAut_alt8 : Nat.card (MulAut (alternatingGroup (Fin 8))) = 40320 := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num))]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem t263_marking_one_of_alt6 {X : Type} [Group X] (hX : commutator X = ⊤)
    [IsSimpleGroup (X ⧸ Subgroup.center X)] (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  have hK : Nat.card (ZMod 2) = 2 := by simp
  obtain ⟨e₆⟩ := CFSG.StandardType.nonempty_b2der_equiv_alternatingGroup hK
  have hnab := CFSG.StandardType.exists_mul_ne_mul_centerQuot_of_perfect hX inferInstance
  let θ := e.trans e₆.symm
  refine ⟨hX, ⟨.B2der, 0, 1⟩, ⟨le_rfl, rfl, rfl⟩, ZMod 2, inferInstance, inferInstance, hK, ?_⟩
  exact ⟨θ.symm.isSimpleGroup, CFSG.StandardType.nonabelian_of_mulEquiv θ hnab, θ, rfl⟩

section Marking


theorem t263_marking_one_of_alt8 {X : Type} [Group X] (hX : commutator X = ⊤)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 8)) :
    GLAMarking X (fun lab _ _ _ _ _ => lab.n = 1) := by
  have h := CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hX h)
  intro lab R _ I F θ hlab
  obtain ⟨-, -, hc, hd⟩ := hlab
  exact t263_n_eq_one_of_mark hc hd

theorem t263Vac_ambAlt : T263Vac t263GAmbAlt := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hQ hF2 hB h4 hT hC
  classical
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  obtain ⟨i, ⟨hamb, hnu⟩, ⟨e⟩⟩ := hQ
  rcases CFSG.StandardType.ChevTwo.ambiguousChev_two_cases hamb with
    ⟨h5, rfl⟩ | ⟨h6, rfl⟩ | ⟨h8, rfl⟩ | ⟨q, hv, hq, rfl⟩ | ⟨q, hv, hq, rfl⟩
  ·
    refine t263_false_of_not_sq_dvd hp hvh hC e ?_
    show ¬ p ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 5)))
    rw [CFSG.GH74.GLS.LU.Local.Five.nat_card_mulAut_alternatingGroup_five]
    exact t263_not_sq_dvd_120 hp hp2
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact hF2 rfl (t263_marking_one_of_alt6 hSq.1 e)
    · refine t263_false_of_not_sq_dvd hp hvh hC e ?_
      show ¬ p ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 6)))
      rw [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
      exact not_sq_dvd_of_dvd_smooth_mul (a := 5) (b := 2) (M := 5) hp hp2 hp3
        (by norm_num : Nat.Prime 5).squarefree (by norm_num)
  ·
    by_cases hp3 : p = 3
    · subst hp3
      exact hF2 rfl (t263_marking_one_of_alt8 hSq.1 e)
    · refine t263_false_of_not_sq_dvd hp hvh hC e ?_
      show ¬ p ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 8)))
      rw [t263_card_mulAut_alt8]
      exact not_sq_dvd_of_dvd_smooth_mul (a := 7) (b := 2) (M := 5 * 7) hp hp2 hp3
        (squarefree_prime_mul (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  ·
    have hc7 : catalogIs (↥S ⧸ Subgroup.center ↥S) fL27 := ⟨.lie ⟨.A 1 q, hv⟩, hq, ⟨e⟩⟩
    have hS : Nat.card (↥S ⧸ Subgroup.center ↥S) = 168 := card_fL27 hc7
    have hnab : ∃ a b : ↥S ⧸ Subgroup.center ↥S, a * b ≠ b * a :=
      exists_noncomm_of_simple_card hS (by norm_num)
    refine t263_false_of_not_sq_dvd hp hvh hC (MulEquiv.refl _) ?_
    by_cases hp3 : p = 3
    · subst hp3
      exact I1416Rows.not_sq_three_dvd_card_mulAut_of_card_168 hnab hS
    · exact not_sq_dvd_of_dvd_smooth_mul (a := 7) (b := 2) (M := 5 * 7) hp hp2 hp3
        (squarefree_prime_mul (by norm_num) (by norm_num) (by norm_num))
        ((card_mulAut_dvd_40320 hS).trans (by norm_num))
  ·
    exact absurd (show t263GAmbU33 (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩) from hq) hnu

end Marking

section U33


theorem t263Vac_ambU33 : T263Vac t263GAmbU33 := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hQ hF2 hB h4 hT hC
  classical
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  have hc : catalogIs (↥S ⧸ Subgroup.center ↥S) fU33 := S10.catalogIs_imp (fun i hi => hi) hQ
  have hm := statedClassicalModel_of_fU33 hc
  have hS : Nat.card (↥S ⧸ Subgroup.center ↥S) = 6048 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  have hZ : Subgroup.center (↥S ⧸ Subgroup.center ↥S) = ⊥ :=
    center_eq_bot_of_simple_nonprime hS (by norm_num)
  have hinj : Function.Injective
      (MulAut.conj : (↥S ⧸ Subgroup.center ↥S) →* MulAut (↥S ⧸ Subgroup.center ↥S)) :=
    conj_injective_of_center_eq_bot hZ
  have hOutle := CFSG.LargeExtraspecial.S63.card_outer_le_two_of_psu33 hinj (Or.inl ⟨by decide, hm⟩)
  have hOut : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (↥S ⧸ Subgroup.center ↥S)) := by
    intro hd
    have hpos : 0 < Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (↥S ⧸ Subgroup.center ↥S)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    have := hp.two_le
    omega
  refine t263_false_of_rank_bound hp hp2 hvh hC (MulEquiv.refl _) hZ
    (inner_of_pow_eq_one_of_not_dvd_outer hp hOut) ?_
  by_cases hp3 : p = 3
  · subst hp3
    exact rankBound_u33_three hc
  · exact rankBound_of_not_sq_dvd hp (by
      rw [hS]
      exact not_sq_dvd_of_dvd_smooth_mul (a := 5) (b := 3) (M := 7) hp hp2 hp3
        (by norm_num : Nat.Prime 7).squarefree (by norm_num))

end U33

section L28






theorem t263Vac_l28 : T263Vac t263GL28 := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hQ hF2 hB h4 hT hC
  classical
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  have hc : catalogIs (↥S ⧸ Subgroup.center ↥S) fL28 := S10.catalogIs_imp (fun i hi => hi) hQ
  have hm := statedClassicalModel_of_fL28 hc
  have hcard : Nat.card (↥S ⧸ Subgroup.center ↥S) = 504 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight hm
  have hAut := card_mulAut_fL28 hc
  by_cases hp3 : p = 3
  · subst hp3
    haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
    have hZ : Subgroup.center (↥S ⧸ Subgroup.center ↥S) = ⊥ :=
      center_eq_bot_of_simple_nonprime hcard (by norm_num)
    have hOutc : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥S ⧸ Subgroup.center ↥S)) = 3 := by
      have := card_mulAut_eq_mul_outer hcard (by norm_num)
      rw [hAut] at this
      omega
    exact t263_false_of_rank_bound' (m := 3) (r := 1) hp hp2 hvh hC (MulEquiv.refl _) hZ
      (fun P _ => by
        have := card_le_mul_card_inf_inner P
        rwa [hOutc] at this) (rankBound_l28_three hc) (by norm_num)
  · refine t263_false_of_not_sq_dvd hp hvh hC (MulEquiv.refl _) fun hdvd => ?_
    rw [hAut] at hdvd
    exact not_sq_dvd_of_dvd_smooth_mul (a := 3) (b := 3) (M := 7) hp hp2 hp3
      (by norm_num : Nat.Prime 7).squarefree (by norm_num) hdvd

end L28

section Tits


open CFSG.Sporadic.Schreier.Tits
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem t263Vac_tits : T263Vac t263GTits := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hQ hF2 hB h4 hT hC
  classical
  have hvh := t263VHyp_of_data hSn hSq hSp hB hp h4 hT
  have hc : catalogIs (↥S ⧸ Subgroup.center ↥S) fTits := S10.catalogIs_imp (fun i hi => hi) hQ
  obtain ⟨e⟩ := titsEquiv_of_catalog hc
  haveI : Finite (↥S ⧸ Subgroup.center ↥S) := inferInstance
  haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
  have hcardS : Nat.card (↥S ⧸ Subgroup.center ↥S) = 17971200 := by
    rw [Nat.card_congr e.toEquiv, card_titsD]
  haveI : IsSimpleGroup titsD := e.symm.isSimpleGroup
  have hZ : Subgroup.center titsD = ⊥ :=
    center_eq_bot_of_simple_nonprime (n := 17971200)
      (by rw [← Nat.card_congr e.toEquiv]; exact hcardS) (by norm_num)
  have hOutc : Nat.card (Outer titsD) = 2 := card_outer_titsD
  have hOut : ¬ p ∣ Nat.card (Outer titsD) := by
    rw [hOutc]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  refine t263_false_of_rank_bound hp hp2 hvh hC e hZ (inner_of_pow_eq_one_of_not_dvd_outer hp hOut) ?_
  by_cases hp3 : p = 3
  · subst hp3
    exact rankBound_titsD_three
  · have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      · exact Nat.not_prime_zero hp
      · exact Nat.not_prime_one hp
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    exact rankBound_of_localRank_le_one hp (localRank_titsD_le_one hp hp5)

end Tits

end CFSG.LocalAnalysis.GLTheoremA.T263

end
