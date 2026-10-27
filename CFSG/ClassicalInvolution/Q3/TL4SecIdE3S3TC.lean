module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TB
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3N
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZB
public import CFSG.ClassicalInvolution.Q3.TL4S289Exit

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Blueprint

namespace E3S3T

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem fstar_quot_simple (hm : EdgelessMember3 R S t) (hE2 : ¬ TightInO2 t) :
    IsSimpleGroup ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) ∧
      ∃ a b : ↥(genFittingFStar (Y ⧸ Subgroup.center Y)), a * b ≠ b * a := by
  have hN2 := E3S3Z.isPGroup_center (t := t) hm.cls
  have htN := E3S3Z.not_mem_center hm.cls hE2
  have hm' := E3S3Z.edgelessMember3_quot hm.datum hm.cls hE2 hm.edgeless
  have hcb := TwistQ.cls hm.datum le_rfl hN2 htN hm.cls
  have hE2b : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => hE2 (TwistQ.inO2_of hN2 h)
  have hZb := E3S3Z.center_quot_eq_bot hm.datum hm.cls hE2
  have hq : TightFStarQuasisimple (Y ⧸ Subgroup.center Y) := by
    rcases tightDichotomy_of hm'.datum hcb with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
    · exact absurd h hE2b
    · exact h
    · rw [hZb] at hFc
      exact absurd (hFc.trans bot_le) hFL
  have hZF : Subgroup.center ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) = ⊥ := by
    have h1 := TightDatum.center_genFittingFStar_le hm'.datum hcb hE2b
    rw [hZb, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
  exact isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZF

theorem fstar_quot_le_map (hm : EdgelessMember3 R S t) (hE2 : ¬ TightInO2 t) {L : Subgroup Y}
    (hLn : L.Normal) (hLnz : ¬ L ≤ Subgroup.center Y) :
    genFittingFStar (Y ⧸ Subgroup.center Y) ≤ L.map (QuotientGroup.mk' (Subgroup.center Y)) := by
  obtain ⟨hs, hnab⟩ := fstar_quot_simple hm hE2
  set N := genFittingFStar (Y ⧸ Subgroup.center Y) with hNdef
  set Lb := L.map (QuotientGroup.mk' (Subgroup.center Y)) with hLbdef
  have hNn : N.Normal := genFittingFStar_normal _
  have hLbn : Lb.Normal := hLn.map _ (QuotientGroup.mk'_surjective _)
  have hC : Subgroup.centralizer (N : Set (Y ⧸ Subgroup.center Y)) = ⊥ :=
    centralizer_genFittingFStar_eq_bot hnab
  have hLNn : ((Lb ⊓ N).subgroupOf N).Normal := Subgroup.Normal.subgroupOf inferInstance N
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Lb ⊓ N).subgroupOf N) with h | h
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h
    have hinf : Lb ⊓ N = ⊥ := by
      have h1 := disjoint_iff.mp h
      rwa [inf_assoc, inf_idem] at h1
    have hcomm : ⁅Lb, N⁆ = ⊥ := le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf Lb N)
    have hLbC : Lb ≤ Subgroup.centralizer (N : Set (Y ⧸ Subgroup.center Y)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    rw [hC, le_bot_iff] at hLbC
    apply hLnz
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center Y) x ∈ Lb := Subgroup.mem_map_of_mem _ hx
    rw [hLbC, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).mp h1
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact h.trans inf_le_left

theorem swap_of_quot (hm : EdgelessMember3 R S t) (hE2 : ¬ TightInO2 t)
    (h : TwSwap (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t)) : TwSwap R t := by
  have hN2 := E3S3Z.isPGroup_center (t := t) hm.cls
  have htN := E3S3Z.not_mem_center hm.cls hE2
  have hnt := E3S3Z.noTwin hm.datum hm.edgeless
  have hRN := TwistQ.inf_eq_bot hm.datum hN2 htN
  obtain ⟨gb, hgb, rb, hrb, hne⟩ := h
  rw [TwistQ.centralizer_mk_eq hnt] at hgb
  obtain ⟨g, hg, rfl⟩ := hgb
  obtain ⟨r, hr, rfl⟩ := hrb
  refine ⟨g, hg, r, hr, fun hmem => hne ?_⟩
  have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center Y)) hmem
  rwa [TwistQ.oddCoreImg_map hRN, map_pow, map_commutatorElement] at h1

theorem false_of_twisted_quot (hm : EdgelessMember3 R S t) (hE2 : ¬ TightInO2 t)
    (htw : TightTwisted Y t)
    (hk : (TightActs3 R t ∧ genFittingFStar (Y ⧸ Subgroup.center Y) = ⊤) ∨
      (((genFittingFStar (Y ⧸ Subgroup.center Y)).index = 2 ∨
          (genFittingFStar (Y ⧸ Subgroup.center Y)).index = 6) ∧
        TwSwap (R.map (QuotientGroup.mk' (Subgroup.center Y)))
          (QuotientGroup.mk' (Subgroup.center Y) t))) : False := by
  obtain ⟨L, -, hLn, -, -, ⟨x, hxL, hxt⟩, hFZ, hFL⟩ := htw
  have hZL : ¬ Subgroup.center Y ≤ L := fun h => hFL (hFZ.trans h)
  have hLnz : ¬ L ≤ Subgroup.center Y := fun h =>
    hxt (Subgroup.mem_center_iff.mp (h hxL) t).symm
  have hFle := fstar_quot_le_map hm hE2 hLn hLnz
  set F : Subgroup Y := (genFittingFStar (Y ⧸ Subgroup.center Y)).comap
    (QuotientGroup.mk' (Subgroup.center Y)) with hF
  have hFn : F.Normal := (genFittingFStar_normal _).comap _
  have hFLZ : F ≤ L ⊔ Subgroup.center Y := by
    have h1 := Subgroup.comap_mono (f := QuotientGroup.mk' (Subgroup.center Y)) hFle
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have hFL' := commutator_mem_of_le_sup_center hFLZ
  have hZF : Subgroup.center Y ≤ F := by
    intro z hz
    have h1 : QuotientGroup.mk' (Subgroup.center Y) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    show QuotientGroup.mk' (Subgroup.center Y) z ∈ genFittingFStar _
    rw [h1]
    exact one_mem _
  have hFi : F.index = (genFittingFStar (Y ⧸ Subgroup.center Y)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hZ2 := E3S3Z.isPGroup_center (t := t) hm.cls
  rcases hk with ⟨h3, htop⟩ | ⟨hi, hsw⟩
  · have hc := commutator_eq_top_of_acts3 hm.datum hm.cls.1 hm.cls.2.1 h3
    have hFtop : F = ⊤ := by rw [hF, htop, Subgroup.comap_top]
    exact false_of_top (fun f y => hFL' f (hFtop ▸ Subgroup.mem_top f) y) hZL hc
  · have hc := index_commutator_le_two hm.datum hm.cls.1 hm.cls.2.1 (swap_of_quot hm hE2 hsw)
    exact false_of_index hFL' hZF hZL hZ2 (hFi ▸ hi) hc

theorem eq_two_or_six {i : ℕ} (h2 : 2 ∣ i) (h6 : i ∣ 6) : i = 2 ∨ i = 6 := by
  have hle : i ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases i <;> omega

end E3S3T

theorem secIdE3S3NoTwist_of (hL2 : TwKindL2) (hL3 : TwKindL3) (hU3 : TwKindU3)
    (hM : ModelM12Acts3) : SecIdE3S3NoTwist := by
  intro Y _ _ R S t hm _ hE2 htw hx
  have hN2 := E3S3Z.isPGroup_center (t := t) hm.cls
  have htN := E3S3Z.not_mem_center hm.cls hE2
  have hnt := E3S3Z.noTwin hm.datum hm.edgeless
  have hm' := E3S3Z.edgelessMember3_quot hm.datum hm.cls hE2 hm.edgeless
  obtain ⟨hs, -⟩ := E3S3T.fstar_quot_simple hm hE2
  have hZb := E3S3Z.center_quot_eq_bot hm.datum hm.cls hE2
  have hlift : TightActs3 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
      (QuotientGroup.mk' (Subgroup.center Y) t) → TightActs3 R t :=
    E3S3Z.acts3_of_map hm.datum le_rfl hN2 htN hnt
  have hi0 : (genFittingFStar (Y ⧸ Subgroup.center Y)).index ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  rcases hx with ⟨h3, hX⟩ | he
  · have h3b : ¬ TightActs3 (R.map (QuotientGroup.mk' (Subgroup.center Y)))
        (QuotientGroup.mk' (Subgroup.center Y) t) := fun h => h3 (hlift h)
    obtain ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl | hl, hi6⟩⟩ | ⟨hm12, hi⟩ := hX
    · obtain ⟨h2, hsw⟩ := hL2 _ _ _ _ hm' hs h3b hi p f hp hp2 hf hl
      exact E3S3T.false_of_twisted_quot hm hE2 htw (Or.inr ⟨Or.inl (by omega), hsw⟩)
    · obtain ⟨h2, hsw⟩ := hL3 _ _ _ _ hm' hs h3b hi6 p f hp hp2 hl
      exact E3S3T.false_of_twisted_quot hm hE2 htw (Or.inr ⟨E3S3T.eq_two_or_six h2 hi6, hsw⟩)
    · obtain ⟨h2, hsw⟩ := hU3 _ _ _ _ hm' hs h3b hi6 p f hp hp2 hl
      exact E3S3T.false_of_twisted_quot hm hE2 htw (Or.inr ⟨E3S3T.eq_two_or_six h2 hi6, hsw⟩)
    · exact h3b (hM _ _ _ _ hm' hs hi hm12)
  · obtain ⟨e⟩ := he
    have hMs : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    have hYs : IsSimpleGroup (Y ⧸ Subgroup.center Y) := e.isSimpleGroup
    have htop : genFittingFStar (Y ⧸ Subgroup.center Y) = ⊤ := by
      have hFn : (genFittingFStar (Y ⧸ Subgroup.center Y)).Normal := genFittingFStar_normal _
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (genFittingFStar (Y ⧸ Subgroup.center Y)) with h | h
      · exfalso
        have hnt' := hs.toNontrivial
        rw [Subgroup.nontrivial_iff_ne_bot] at hnt'
        exact hnt' h
      · exact h
    have hi : (genFittingFStar (Y ⧸ Subgroup.center Y)).index ≤ 2 := by
      rw [htop, Subgroup.index_top]
      norm_num
    have hm12 : NativeSporadic.IsSporadic (FStarQuot (Y ⧸ Subgroup.center Y)) .M12 :=
      S289.isSporadic_fstarQuot_of_center_quot hs
        (((QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot).trans e)
    exact E3S3T.false_of_twisted_quot hm hE2 htw
      (Or.inl ⟨hlift (hM _ _ _ _ hm' hs hi hm12), htop⟩)

end CFSG.ClassicalInvolution.Q3.TL4
