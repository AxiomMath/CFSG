module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.TwoPart
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import Certificates.Certificate24431

public section

namespace CFSG.EvenSporadicStandard.HypOne.J3

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore (j3R j3u j3Rows j3OuterTbl j3CentTbl j3Sift j3PGTbls
  j3_groupData j3_primes j3_sylowOrder j3_centData
  ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  ctuc_j3_normalizing_involution_permutation_model
  ctuc_j3_full_automorphism_permutation_model j3_autModel j3_centralizer_eq_bot
  centData_spec tp rep_tp)

theorem class_data :
    tp 6156 t0 ∈ j3P ∧ orderOf (tp 6156 t0) = 2 ∧
      Nat.card ↥(centralizerIn j3P (tp 6156 t0)) = 1920 ∧
      tp 6156 t1 ∈ j3R ∧ tp 6156 t1 ∉ j3P ∧ orderOf (tp 6156 t1) = 2 ∧
      Nat.card ↥(centralizerIn j3P (tp 6156 t1)) = 2448 ∧
      ∀ v ∈ j3R, orderOf v = 2 →
        ∃ g ∈ j3P, v = g * tp 6156 t0 * g⁻¹ ∨ v = g * tp 6156 t1 * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, hrows, hcover, -⟩ :=
    j3_centData
  obtain ⟨h1, h2, h3, -, h5, -⟩ := hrows _ List.mem_cons_self
  obtain ⟨g1, g2, g3, -, g5, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h1 h2 h3 h5 g1 g2 g3 g5
  have hP0 : tp 6156 t0 ∈ j3P := by
    by_contra h
    exact Bool.false_ne_true (h3.2 h)
  have hP1 : tp 6156 t1 ∉ j3P := g3.1 rfl
  refine ⟨hP0, h2, h5, g1, hP1, g2, g5, fun v hv hv2 => ?_⟩
  obtain ⟨r, hr, g, hg, hv'⟩ := hcover v hv hv2
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr
  · exact ⟨g, hg, Or.inl (by rw [hv', hr])⟩
  · exact ⟨g, hg, Or.inr (by rw [hv', hr])⟩

theorem fourClassesLarge_rows :
    (∀ v ∈ j3P, orderOf v = 2 → FourClassesLarge (centralizerIn j3P v)) ∧
      ∀ v ∈ j3R, orderOf v = 2 → FourClassesLarge (centralizerIn j3R v) := by
  obtain ⟨hU2, -, hUP, hmap, -⟩ :=
    j3_centData
  obtain ⟨hP0, h20, hc0, hR1, hP1, h21, hc1, hcover⟩ := class_data
  have hUn : ∀ p ∈ j3P, tp 6156 j3OuterTbl * p * (tp 6156 j3OuterTbl)⁻¹ ∈ j3P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hsyl := Certificates.certificate24431.1
  simp only [sylowData, Bool.and_eq_true] at hsyl
  obtain ⟨⟨⟨⟨⟨⟨⟨hu, ht0⟩, ht1⟩, hs0⟩, hs1⟩, hs2⟩, hz0⟩, hz1⟩ := hsyl
  have rU := rep_tp hu
  have c0 : 2 ^ (Nat.card ↥(centralizerIn j3P (tp 6156 t0))).factorization 2 = 128 := by
    rw [hc0, two_pow_factorization_eq (k := 7) (b := 15) (by norm_num) (by norm_num)]
    norm_num
  have cR0 : Nat.card ↥(centralizerIn j3R (tp 6156 t0)) = 2 * 1920 := by
    rw [← hc0]
    exact card_centralizerIn_R_of_z j3_groupData rU hU2 hUn ht0 hz0
  have cR1 : Nat.card ↥(centralizerIn j3R (tp 6156 t1)) = 2 * 2448 := by
    rw [← hc1]
    exact card_centralizerIn_R_of_z j3_groupData rU hU2 hUn ht1 hz1
  have f0 : FourClassesLarge ↥(centralizerIn j3P (tp 6156 t0)) :=
    fourClassesLarge_row_P j3_groupData ht0 c0.symm hs0
  have fR0 : FourClassesLarge ↥(centralizerIn j3R (tp 6156 t0)) :=
    fourClassesLarge_row_R j3_groupData rU hU2 hUn ht0 (by
      rw [show centralizerIn (j3P ⊔ zpowers (tp 6156 j3OuterTbl)) (tp 6156 t0) =
        centralizerIn j3R (tp 6156 t0) from rfl, cR0,
        two_pow_factorization_eq (k := 8) (b := 15) (by norm_num) (by norm_num)]
      norm_num) hs1
  have fR1 : FourClassesLarge ↥(centralizerIn j3R (tp 6156 t1)) :=
    fourClassesLarge_row_R j3_groupData rU hU2 hUn ht1 (by
      rw [show centralizerIn (j3P ⊔ zpowers (tp 6156 j3OuterTbl)) (tp 6156 t1) =
        centralizerIn j3R (tp 6156 t1) from rfl, cR1,
        two_pow_factorization_eq (k := 5) (b := 153) (by norm_num) (by norm_num)]
      norm_num) hs2
  refine ⟨?_, ?_⟩
  · refine fourClassesLarge_centralizerIn_of_reps j3P [tp 6156 t0] (fun v hv h2 => ?_) ?_
    · obtain ⟨g, hg, hv'⟩ := hcover v (mem_sup_left hv) h2
      rcases hv' with hv' | hv'
      · exact ⟨tp 6156 t0, List.mem_singleton_self _, g, hg, hv'⟩
      · exfalso
        apply hP1
        have : tp 6156 t1 = g⁻¹ * v * g := by rw [hv']; group
        rw [this]
        exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hg) hv) hg
    · intro r hr
      rw [List.mem_singleton.1 hr]
      exact f0
  · refine fourClassesLarge_centralizerIn_of_reps j3R [tp 6156 t0, tp 6156 t1]
      (fun v hv h2 => ?_) ?_
    · obtain ⟨g, hg, hv'⟩ := hcover v hv h2
      rcases hv' with hv' | hv'
      · exact ⟨tp 6156 t0, by simp, g, mem_sup_left hg, hv'⟩
      · exact ⟨tp 6156 t1, by simp, g, mem_sup_left hg, hv'⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fR0
      · exact fR1

theorem center_j3P :
    Subgroup.center j3P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 6156)) ∈
      Subgroup.centralizer (j3P : Set (Equiv.Perm (Fin 6156))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [j3_centralizer_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.J3 := by
  obtain ⟨hP, hR⟩ := fourClassesLarge_rows
  obtain ⟨e, -, -, -, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hidx : Nat.card j3R ≤ 2 * Nat.card j3P := by
    rw [ctuc_j3_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1, card_j3P]
  exact hypothesisOne_of_outTwo j3PermEquiv center_j3P j3_autModel e hidx hodd hP hR

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.J3 :=
  HasElemAbelianEight.of_mulEquiv j3PermEquiv.symm
    (e8Rows_spec j3_groupData Certificates.certificate24431.2.1)

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.J3 := by
  obtain ⟨e, he, -, -, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨hP0, -, -, hR1, -, -, -, hcover⟩ := class_data
  obtain ⟨l, hl, hl2⟩ := foursWit_spec j3_groupData Certificates.certificate24431.2.2
  refine foursGroupCondition_of_outTwo j3PermEquiv center_j3P le_sup_left e he
    [⟨tp 6156 t1, hR1⟩] (fun τ hτ hτP => ?_) (fun ρ hρ => ?_)
  · obtain ⟨g, hg, hv⟩ := hcover τ τ.2 hτ
    rcases hv with hv | hv
    · exfalso
      apply hτP
      rw [hv]
      exact j3P.mul_mem (j3P.mul_mem hg hP0) (j3P.inv_mem hg)
    · exact ⟨⟨tp 6156 t1, hR1⟩, List.mem_singleton_self _, g, hg, hv⟩
  · rw [List.mem_singleton.1 hρ]
    exact ⟨l, hl, hl2⟩

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .J3) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne Y :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native
  exact rowData_of_hasElemAbelianEight hI
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .J3) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .J3) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.J3
