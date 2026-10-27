module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporMathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporRestJ4
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kdSporRow_of_exact {name : TauCeti.SporadicName} {p : ℕ} {H : Type} [Group H] [Finite H]
    [IsSimpleGroup H] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : H ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hcard : ¬ (Nat.card H).Prime)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpc : ¬ p ^ 2 ∣ Nat.card H) : KDSporRow name p := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 inferInstance
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hcG : Nat.card G = Nat.card H := (Nat.card_congr b.toEquiv).symm
  have hnc : ∃ a c : G, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcG]; exact hcard)
  have hout := hOut G inferInstance hnc name ⟨MulEquiv.refl _⟩
  have hc : ∀ x : G, orderOf x = p → ∀ I : Subgroup G,
      GLAPComponent p (Subgroup.centralizer ({x} : Set G)) I → False := fun x hx I hI =>
    CFSG.HardMathSupport.Solomon.Coordinator.no_glaPComponent_of_exact hp hx (by rw [hcG]; exact hpc)
      hI
  exact ⟨fun h2 => downLe_of_centralizers hnc hout hp hp2 (kLevel_le_two ⟨_, h2, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).elim,
    fun h3 => downLe_of_centralizers hnc hout hp hp2 (kLevel_le_three ⟨_, h3, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).elim⟩

theorem kdSporRow_M12_eleven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .M12 11 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  haveI : IsSimpleGroup _ := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact kdSporRow_of_exact hOut b (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) (by norm_num)
    (by norm_num) (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)

theorem false_of_glaPComponent_of_pConstrained {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {C J : Subgroup X}
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p C)
    (hJ : GLAPComponent p C J) : False := by
  have hlay : GLAPLayer p C = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.glaPLayer_eq_bot_of_constrained
      hp le_rfl (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (CFSG.HardMathSupport.Dickson.I271.constraint_of_pConstrainedShape h)
  have hle : J ≤ GLAPLayer p C := le_sSup hJ
  rw [hlay] at hle
  exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ (eq_bot_iff.2 hle)

theorem kdSporRow_of_model {name : TauCeti.SporadicName} {p : ℕ} {H : Type} [Group H] [Finite H]
    [IsSimpleGroup H] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : H ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hcard : ¬ (Nat.card H).Prime)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hno : ∀ x : H, orderOf x = p → ∀ I : Subgroup H,
      GLAPComponent p (Subgroup.centralizer ({x} : Set H)) I → False) : KDSporRow name p := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 inferInstance
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hcG : Nat.card G = Nat.card H := (Nat.card_congr b.toEquiv).symm
  have hnc : ∃ a c : G, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcG]; exact hcard)
  have hout := hOut G inferInstance hnc name ⟨MulEquiv.refl _⟩
  have hc : ∀ x : G, orderOf x = p → ∀ I : Subgroup G,
      GLAPComponent p (Subgroup.centralizer ({x} : Set G)) I → False := by
    intro x hx I hI
    have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp b.symm hI
    rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv] at h
    exact hno _ (by rw [MulEquiv.orderOf_eq, hx]) _ h
  exact ⟨fun h2 => downLe_of_centralizers hnc hout hp hp2 (kLevel_le_two ⟨_, h2, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).elim,
    fun h3 => downLe_of_centralizers hnc hout hp hp2 (kLevel_le_three ⟨_, h3, ⟨MulEquiv.refl _⟩⟩)
      fun x hx I hI => (hc x hx I hI).elim⟩

theorem no_comp_of_conj {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) (h x : H)
    (hno : ∀ I : Subgroup H, GLAPComponent p (Subgroup.centralizer ({h⁻¹ * x * h} : Set H)) I →
      False) (I : Subgroup H) (hI : GLAPComponent p (Subgroup.centralizer ({x} : Set H)) I) :
    False := by
  have h' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp (MulAut.conj h⁻¹) hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv, MulAut.conj_apply,
    inv_inv] at h'
  exact hno _ h'

set_option maxRecDepth 100000 in
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.HardMathSupport.Timmesfeld.Tables.Census in
theorem kdSporRow_J4_eleven
    (hbr : SporadicBridges)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .J4 11 := by
  haveI hJs : IsSimpleGroup ↥J := isSimpleGroup_J j4Facts
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .J4).Group :=
    (seedEquiv j4Facts.mat).symm.trans (hbr .J4).some
  have h2 : 2 ∣ Nat.card ↥J := by
    rw [card_J_eq]
    exact Dvd.intro (2 ^ 20 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) (by ring)
  have hcard : ¬ (Nat.card ↥J).Prime := by
    intro hpr
    rcases hpr.eq_one_or_self_of_dvd 2 h2 with h | h
    · norm_num at h
    · rw [card_J_eq] at h
      norm_num at h
  refine @kdSporRow_of_model .J4 11 ↥J _ inferInstance hJs hOut b hcard (by norm_num) (by norm_num)
    fun x hx I hI => ?_
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_eleven_pow_four_dvd_card_J hx
  refine no_comp_of_conj (by norm_num) h x (fun I hI => ?_) I hI
  set u := h⁻¹ * x * h with hu
  have huo : orderOf u = 11 := by
    have := orderOf_conj_eq' h⁻¹ x
    rw [inv_inv] at this
    rw [hu, this, hx]
  by_cases hz : u ∈ Subgroup.zpowers qz
  · have hzp : Subgroup.zpowers u = Subgroup.zpowers qz :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_qz])
    rw [centralizer_singleton_eq_of_zpowers hzp] at hI
    refine false_of_glaPComponent_of_pConstrained (by norm_num) ?_ hI
    have hQC : Q11 ≤ Subgroup.centralizer ({qz} : Set ↥J) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem hq)
    refine ⟨Q11, hQC, fun g hg q hq => ?_, IsPGroup.of_card card_Q11,
      inf_le_right.trans centralizer_Q11_le⟩
    exact (Subgroup.mem_normalizer_iff.1 (centralizer_qz_le_normalizer_J4 hg) q).1 hq
  · obtain ⟨h121, h242⟩ := card_centralizer_noncentral_le hh hz
    refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
    obtain ⟨k, hk⟩ := h121
    have hk2 : k = 1 ∨ k = 2 := by
      have : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, mul_zero] at hk; exact absurd hk Nat.card_pos.ne'
        · exact h0
      omega
    haveI := Fintype.ofFinite ↥(Subgroup.centralizer ({u} : Set ↥J))
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 11) (q := 2) (a := 2) (b := k - 1) (by norm_num) (by norm_num) (by norm_num) ?_
    rw [Fintype.card_eq_nat_card, hk]
    rcases hk2 with rfl | rfl <;> norm_num

theorem isSolvable_of_card_eq {X : Type*} [Group X] [Finite X] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card X = p ^ a * q ^ b) : Group.IsSolvable X := by
  haveI := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [Fintype.card_eq_nat_card, h])

theorem not_prime_of_two_dvd {n : ℕ} (h2 : 2 ∣ n) (hn : n ≠ 2) : ¬ n.Prime := fun hpr => by
  rcases hpr.eq_one_or_self_of_dvd 2 h2 with h | h
  · norm_num at h
  · exact hn h.symm

set_option maxRecDepth 100000 in
theorem kdSporRow_ON_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KDSporRow .ONan 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  haveI hs : IsSimpleGroup ↥CFSG.ONSchreier.Pv :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ON.isSimpleGroup_ON CFSG.ONSchreier.onEquivPv.symm
  have hc : Nat.card ↥CFSG.ONSchreier.Pv = 460815505920 := CFSG.ONSchreier.card_Pv
  refine @kdSporRow_of_model .ONan 7 ↥CFSG.ONSchreier.Pv _ inferInstance hs hOut
    (CFSG.ONSchreier.onEquivPv.symm.trans b)
    (not_prime_of_two_dvd (by rw [hc]; norm_num) (by rw [hc]; norm_num)) (by norm_num)
    (by norm_num) fun x hx I hI => ?_
  refine false_of_glaPComponent_of_solvable (by norm_num) ?_ hI
  rcases CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.card_centralizer_seven_Pv
    hx with h | h
  · exact isSolvable_of_card_eq (p := 2) (q := 7) (a := 2) (b := 3) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)
  · exact isSolvable_of_card_eq (p := 7) (q := 2) (a := 2) (b := 0) (by norm_num) (by norm_num)
      (by norm_num) (by rw [h]; norm_num)

end CFSG.LocalAnalysis.GLTheoremA.KDSpor
