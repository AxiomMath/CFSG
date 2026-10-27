module

public import CFSG.Sporadic.SmallOddCore.McLAut
public import Certificates.Certificate24430

public section

namespace CFSG.EvenSporadicStandard.HypOne.McL

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Schreier
open CFSG.Sporadic.SmallOddCore (mclR mclU mclRows mclOuterTbl mclCentTbl mclSift mclPGTbls
  mcl_groupData mcl_primes mcl_sylowOrder mcl_centDataOK mcl_involution_centralizers
  mcl_normalizing_model mcl_full_automorphism_model mcl_autModel mcl_centralizer_eq_bot
  centData_spec tp rep_tp)

theorem class_data :
    tp 275 t0 ∈ mclP ∧ orderOf (tp 275 t0) = 2 ∧
      Nat.card ↥(centralizerIn mclP (tp 275 t0)) = 40320 ∧
      tp 275 t1 ∈ mclR ∧ tp 275 t1 ∉ mclP ∧ orderOf (tp 275 t1) = 2 ∧
      Nat.card ↥(centralizerIn mclP (tp 275 t1)) = 7920 ∧
      ∀ v ∈ mclR, orderOf v = 2 →
        ∃ g ∈ mclP, v = g * tp 275 t0 * g⁻¹ ∨ v = g * tp 275 t1 * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, hrows, hcover, -⟩ :=
    centData_spec mcl_groupData card_mclP mcl_primes mcl_sylowOrder mcl_centDataOK
  obtain ⟨h1, h2, h3, -, h5, -⟩ := hrows _ List.mem_cons_self
  obtain ⟨g1, g2, g3, -, g5, -⟩ := hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)
  dsimp only at h1 h2 h3 h5 g1 g2 g3 g5
  have hP0 : tp 275 t0 ∈ mclP := by
    by_contra h
    exact Bool.false_ne_true (h3.2 h)
  have hP1 : tp 275 t1 ∉ mclP := g3.1 rfl
  refine ⟨hP0, h2, h5, g1, hP1, g2, g5, fun v hv hv2 => ?_⟩
  obtain ⟨r, hr, g, hg, hv'⟩ := hcover v hv hv2
  simp only [mclRows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr
  · exact ⟨g, hg, Or.inl (by rw [hv', hr])⟩
  · exact ⟨g, hg, Or.inr (by rw [hv', hr])⟩

theorem fourClassesLarge_rows :
    (∀ v ∈ mclP, orderOf v = 2 → FourClassesLarge (centralizerIn mclP v)) ∧
      ∀ v ∈ mclR, orderOf v = 2 → FourClassesLarge (centralizerIn mclR v) := by
  obtain ⟨-, -, -, -, hP1, -, -, hcover⟩ := class_data
  obtain ⟨f0, fR0, fR1, -, -⟩ := Certificates.certificate24430
  refine ⟨?_, ?_⟩
  · refine fourClassesLarge_centralizerIn_of_reps mclP [tp 275 t0] (fun v hv h2 => ?_) ?_
    · obtain ⟨g, hg, hv'⟩ := hcover v (mem_sup_left hv) h2
      rcases hv' with hv' | hv'
      · exact ⟨tp 275 t0, List.mem_singleton_self _, g, hg, hv'⟩
      · exfalso
        apply hP1
        have : tp 275 t1 = g⁻¹ * v * g := by rw [hv']; group
        rw [this]
        exact mclP.mul_mem (mclP.mul_mem (mclP.inv_mem hg) hv) hg
    · intro r hr
      rw [List.mem_singleton.1 hr]
      exact f0
  · refine fourClassesLarge_centralizerIn_of_reps mclR [tp 275 t0, tp 275 t1]
      (fun v hv h2 => ?_) ?_
    · obtain ⟨g, hg, hv'⟩ := hcover v hv h2
      rcases hv' with hv' | hv'
      · exact ⟨tp 275 t0, by simp, g, mem_sup_left hg, hv'⟩
      · exact ⟨tp 275 t1, by simp, g, mem_sup_left hg, hv'⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact fR0
      · exact fR1

theorem center_mclP :
    Subgroup.center mclP = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have : (z : Equiv.Perm (Fin 275)) ∈
      Subgroup.centralizer (mclP : Set (Equiv.Perm (Fin 275))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
  rw [mcl_centralizer_eq_bot, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.McL := by
  obtain ⟨hP, hR⟩ := fourClassesLarge_rows
  obtain ⟨e, -, -, -, -⟩ := mcl_full_automorphism_model
  obtain ⟨-, -, -, -, -, -, -, hodd⟩ := mcl_involution_centralizers
  have hidx : Nat.card mclR ≤ 2 * Nat.card mclP := by
    rw [mcl_normalizing_model.2.2.2.2.2.2.2.2.1, card_mclP]
  exact hypothesisOne_of_outTwo mclPermEquiv center_mclP mcl_autModel e hidx hodd hP hR

theorem hasElemAbelianEight_native :
    HasElemAbelianEight NativeSporadic.McL :=
  HasElemAbelianEight.of_mulEquiv mclPermEquiv.symm Certificates.certificate24430.2.2.2.1

theorem foursGroupCondition_native :
    CFSG.EvenSmallLie.FoursGroupCondition NativeSporadic.McL := by
  obtain ⟨e, he, -, -, -⟩ := mcl_full_automorphism_model
  obtain ⟨hP0, -, -, hR1, -, -, -, hcover⟩ := class_data
  obtain ⟨l, hl, hl2⟩ := Certificates.certificate24430.2.2.2.2
  refine foursGroupCondition_of_outTwo mclPermEquiv center_mclP le_sup_left e he
    [⟨tp 275 t1, hR1⟩] (fun τ hτ hτP => ?_) (fun ρ hρ => ?_)
  · obtain ⟨g, hg, hv⟩ := hcover τ τ.2 hτ
    rcases hv with hv | hv
    · exfalso
      apply hτP
      rw [hv]
      exact mclP.mul_mem (mclP.mul_mem hg hP0) (mclP.inv_mem hg)
    · exact ⟨⟨tp 275 t1, hR1⟩, List.mem_singleton_self _, g, hg, hv⟩
  · rw [List.mem_singleton.1 hρ]
    exact ⟨l, hl, hl2⟩

theorem rowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .McL) : Finkelstein77.RowData Y := by
  obtain ⟨e⟩ := h
  have hI : HypothesisOne Y :=
    CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv e.symm hypothesisOne_native
  exact rowData_of_hasElemAbelianEight hI
    (HasElemAbelianEight.of_mulEquiv e.symm hasElemAbelianEight_native)

theorem foursGroupCondition_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .McL) : CFSG.EvenSmallLie.FoursGroupCondition Y := by
  obtain ⟨e⟩ := h
  exact CFSG.EvenSmallLie.FoursGroupCondition.of_mulEquiv e.symm foursGroupCondition_native

theorem fullRowData_of_isSporadic
    {Y : Type} [Group Y] [Finite Y] (h : IsSporadic Y .McL) : FullRowData Y :=
  ⟨rowData_of_isSporadic h, foursGroupCondition_of_isSporadic h⟩

end CFSG.EvenSporadicStandard.HypOne.McL
