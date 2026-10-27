module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkL2
import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
import CFSG.Milestones.ASVolI.A2OddAut
import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
import CFSG.RankThree.PartTwo.Sec4.Ronan431CBridge
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196 (mem_innerAut_of_congr mem_innerAut_of_not_dvd
  mem_innerAut_of_isPGroup_outer psp43_model_of_twistedA ambiguousChev_lie_odd)

theorem t2021Layer_odd_orderOf {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut S} (hαp : α ^ p = 1) : Odd (orderOf α) :=
  Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hαp)

theorem t2021Layer_prime_pow_eq_eight {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (h : p ^ k = 8) :
    p = 2 ∧ k = 3 := by
  have h1 : p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact dvd_pow_self p (by omega)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
  subst hp2
  exact ⟨rfl, Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num))⟩

theorem t2021Layer_p_eq_two_of_card_eq_eight {q : TauCeti.PrimePower} (hq : q.card = 8) : q.p = 2 :=
  (t2021Layer_prime_pow_eq_eight q.prime_p q.exponent_pos
    ((TauCeti.PrimePower.card_def q).symm.trans hq)).1

theorem t2021Layer_inner_alt {S : Type} [Group S] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (e : S ≃* alternatingGroup (Fin n)) {α : MulAut S} (hαp : α ^ p = 1) :
    α ∈ (MulAut.conj : S →* MulAut S).range :=
  mem_innerAut_of_congr e (mem_innerAut_of_not_dvd hp
    (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn p hp hp2)
    (by rw [← map_pow, hαp, map_one]))

theorem t2021Layer_inner_l27 {S : Type} [Group S] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.A 1 q).Valid} (hq : q.card = 7)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group) {α : MulAut S} (hα : Odd (orderOf α)) :
    α ∈ (MulAut.conj : S →* MulAut S).range := by
  have hsc : StatedClassicalModel S .PSL 2 q.p q.exponent :=
    (CFSG.Models.lieModel_A 1 q hv e).2.resolve_right fun h => absurd h.1 (by norm_num)
  have hq7 : q.p ^ q.exponent = 7 := (TauCeti.PrimePower.card_def q).symm.trans hq
  haveI : Fact (Nat.Prime q.p) := ⟨q.prime_p⟩
  have hF : Nat.card (GaloisField 7 1) = q.p ^ q.exponent := by
    rw [GaloisField.card 7 1 (by norm_num), pow_one, hq7]
  obtain ⟨e7⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated q.p q.exponent
    (F := GaloisField 7 1) q.exponent_pos hF hsc
  obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.oddInner_transport e7
    CFSG.LocalAnalysis.GLTheoremA.oddInner_psl27 α hα
  exact ⟨g, hg.symm⟩

theorem t2021Layer_inner_u33 {S : Type} [Group S] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid} (hq : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) {α : MulAut S}
    (hα : Odd (orderOf α)) : α ∈ (MulAut.conj : S →* MulAut S).range := by
  have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def, hq]
  obtain ⟨hp, he⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).1 h3
  have hsc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hp, he] at hsc
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hsc
  exact CFSG.ASVolI.burnsideA26_u33 hK eK α hα

theorem t2021Layer_inner_psp43 {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : StatedClassicalModel S .PSp 2 3 1) {α : MulAut S} (hαp : α ^ p = 1) :
    α ∈ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm
  have hK3 : Nat.card K = 3 := by rw [hK, pow_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 3 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  have hout := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.isPGroup_outer_psp4
    (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.eq_zero_or_one_or_neg_one_of_card_three hK3) hodd
  exact mem_innerAut_of_congr eK (mem_innerAut_of_isPGroup_outer hp Nat.prime_two hp2 hout
    (by rw [← map_pow, hαp, map_one]))

theorem t2021Layer_inner_u42 {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {q : TauCeti.PrimePower} {hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid} (hq : q.card = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group) {α : MulAut S} (hαp : α ^ p = 1) :
    α ∈ (MulAut.conj : S →* MulAut S).range :=
  t2021Layer_inner_psp43 hp hp2 (psp43_model_of_twistedA hq e) hαp

theorem t2021Layer_inner_of_ambiguousChev_two {S : Type} [Group S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {i : TauCeti.CFSGIndex} (hi : ambiguousChev 2 i) (e : S ≃* i.Group)
    {α : MulAut S} (hαp : α ^ p = 1) : α ∈ (MulAut.conj : S →* MulAut S).range := by
  have hodd := t2021Layer_odd_orderOf hp hp2 hαp
  rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | ⟨d, hv⟩ | _
  · exact hi.elim
  · exact t2021Layer_inner_alt hp hp2 hn e hαp
  · rcases CFSG.LocalAnalysis.GLTheoremA.ambiguous_two_lie hv hi with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩
    · exact t2021Layer_inner_l27 hq e hodd
    · exact t2021Layer_inner_u33 hq e hodd
  · exact hi.elim

theorem t2021Layer_exists_le_card_eq {G : Type} [Group G] [Finite G] {p k : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) (hk : p ^ k ≤ Nat.card E) :
    ∃ E' ≤ E, IsElemAbelian p E' ∧ Nat.card E' = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE.isPGroup
  rw [hn] at hk
  have hdvd : p ^ k ∣ Nat.card E :=
    hn ▸ pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 hk)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine ⟨K.map E.subtype, Subgroup.map_subtype_le K, hE.mono (Subgroup.map_subtype_le K), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem t2021Layer_le_normalizer_map_conj {S : Type} [Group S] {E : Subgroup (MulAut S)}
    {Y : Subgroup S} (hEY : ∀ φ ∈ E, ∀ y ∈ Y, φ y ∈ Y) :
    E ≤ Subgroup.normalizer (Y.map (MulAut.conj : S →* MulAut S) : Set (MulAut S)) := by
  have key : ∀ φ ∈ E, ∀ c ∈ Y.map (MulAut.conj : S →* MulAut S),
      φ * c * φ⁻¹ ∈ Y.map (MulAut.conj : S →* MulAut S) := by
    rintro φ hφ _ ⟨y, hy, rfl⟩
    refine ⟨φ y, hEY φ hφ y hy, ?_⟩
    ext x
    simp [MulAut.conj_apply, MulAut.mul_apply]
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key φ hφ c, fun hc => ?_⟩
  have h := key φ⁻¹ (E.inv_mem hφ) _ hc
  simpa [mul_assoc] using h

section U38

theorem t2021Layer_exc_u38 {S : Type} [Group S] [Finite S] (eS : S ≃* CFSG.PGLModel.projSU 3 2 3)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hE3 : 3 ^ 3 ≤ Nat.card E)
    {Y : Subgroup S} (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hEY : ∀ φ ∈ E, ∀ y ∈ Y, φ y ∈ Y) :
    False := by
  haveI : Finite (MulAut S) := MulEquiv.finite_left
  obtain ⟨E', hE'E, hE', hE'27⟩ := t2021Layer_exists_le_card_eq Nat.prime_three hE hE3
  have hY3 : ¬ 3 ∣ Nat.card (Y.map (MulAut.conj : S →* MulAut S)) := by
    intro h3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hY2
    have h := h3.trans ((Subgroup.card_map_dvd Y MulAut.conj).trans hk.dvd)
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have hbot := CFSG.RankThree.PartTwo.Sec4.Item434U38.u38_K0_of_equiv ⟨eS⟩ E' hE'
    (by rw [hE'27]; norm_num) _ hY3 (hE'E.trans (t2021Layer_le_normalizer_map_conj hEY))
  have hZ : Subgroup.center (CFSG.PGLModel.projSU 3 2 3) = ⊥ :=
    (CFSG.RankThree.PartTwo.Sec13.isPerfect_center_projSU 2 3 (by norm_num) (by norm_num)
      (by norm_num)).2
  apply hY1
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hc : MulAut.conj y = 1 := by
    have h : MulAut.conj y ∈ Y.map (MulAut.conj : S →* MulAut S) := Subgroup.mem_map_of_mem _ hy
    rwa [hbot, Subgroup.mem_bot] at h
  have hyZ : eS y ∈ Subgroup.center (CFSG.PGLModel.projSU 3 2 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨s, rfl⟩ := eS.surjective g
    have h := DFunLike.congr_fun hc s
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    have hsy : s * y = y * s := by
      calc s * y = y * s * y⁻¹ * y := by rw [h]
        _ = y * s := by group
    rw [← map_mul, ← map_mul, hsy]
  rw [hZ, Subgroup.mem_bot] at hyZ
  exact eS.map_eq_one_iff.1 hyZ

end U38

theorem t2021Layer_exists_index {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut S} (hαp : α ^ p = 1) (hαi : α ∉ (MulAut.conj : S →* MulAut S).range)
    (hchev : IsChevSimple 2 S) :
    ∃ (d : TauCeti.LieTypeIndex) (hd : d.Valid), d.characteristic = 2 ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group) := by
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · rcases i with ⟨_, _⟩ | ⟨_, _⟩ | ⟨d, hd⟩ | _
    · exact hi.elim
    · exact hi.elim
    · exact ⟨d, hd, hi, ⟨e⟩⟩
    · exact hi.elim
  · exact absurd (t2021Layer_inner_of_ambiguousChev_two hp hp2 hi e hαp) hαi

section NotChev

theorem t2021Layer_inner_of_crossChar {S : Type} [Group S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.LieTypeIndex} {hd : d.Valid} (hd2 : d.characteristic = 2)
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group) {d' : TauCeti.LieTypeIndex} {hd' : d'.Valid}
    (hdp : d'.characteristic = p) (e : S ≃* (TauCeti.CFSGIndex.lie ⟨d', hd'⟩).Group)
    {α : MulAut S} (hαp : α ^ p = 1) : α ∈ (MulAut.conj : S →* MulAut S).range := by
  have hodd := t2021Layer_odd_orderOf hp hp2 hαp
  obtain ⟨t', n', p', f', hp', hM⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char ⟨d', hd'⟩
  have hB := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models
    (hM.of_mulEquiv e.symm)
  obtain rfl : p' = p := hp'.trans hdp
  have hOdd : CFSG.Blueprint.OddLieType S := ⟨t', n', p', f', hp, hp2, hB.admissible, hB⟩
  obtain ⟨t, n, f, hX⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid ⟨d, hd⟩ hd2 eS
  rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType' hX hOdd with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    obtain ⟨e4⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel 2 2 (F := GaloisField 2 2)
      (by norm_num) (GaloisField.card 2 2 (by norm_num)) hX
    obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.oddInner_transport e4
      (CFSG.ASVolI.burnsideA315x_psl2_odd_inner (K := GaloisField 2 2) Nat.prime_two
        (GaloisField.card 2 2 (by norm_num)) (Or.inr rfl)) α hodd
    exact ⟨g, hg.symm⟩
  ·
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨e7⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel 7 1 (F := GaloisField 7 1)
      (by norm_num) (GaloisField.card 7 1 (by norm_num))
      (CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism S hX)
    obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremA.oddInner_transport e7
      CFSG.LocalAnalysis.GLTheoremA.oddInner_psl27 α hodd
    exact ⟨g, hg.symm⟩
  ·
    exact t2021Layer_inner_psp43 hp hp2
      (CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two
        (hX.statedClassicalModel (by decide))) hαp

theorem t2021Layer_not_chev {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut S} (hαp : α ^ p = 1) (hαi : α ∉ (MulAut.conj : S →* MulAut S).range)
    (hchev : IsChevSimple 2 S)
    (hL2 : ¬ (p = 3 ∧ catalogIs S CFSG.LocalAnalysis.GLTheoremA.List93.l2Two)) :
    ¬ IsChevSimple p S := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  ·
    obtain ⟨d, hd, hd2, ⟨eS⟩⟩ := t2021Layer_exists_index hp hp2 hαp hαi hchev
    rcases i with ⟨_, _⟩ | ⟨_, _⟩ | ⟨d', hd'⟩ | _
    · exact hi.elim
    · exact hi.elim
    · exact hαi (t2021Layer_inner_of_crossChar hp hp2 hd2 eS hi e hαp)
    · exact hi.elim
  ·
    rcases i with ⟨_, _⟩ | ⟨n, hn⟩ | ⟨d', hd'⟩ | _
    · exact hi.elim
    · exact hαi (t2021Layer_inner_alt hp hp2 hn e hαp)
    · obtain ⟨rfl, ⟨q, hq, hq8⟩ | ⟨q, hq, hq2⟩⟩ := ambiguousChev_lie_odd hp2 hi
      · obtain rfl : d' = .A 1 q := hq
        exact hL2 ⟨rfl, ⟨.lie ⟨.A 1 q, hd'⟩, t2021Layer_p_eq_two_of_card_eq_eight hq8, ⟨e⟩⟩⟩
      · obtain rfl : d' = .twistedA 3 q := hq
        exact hαi (t2021Layer_inner_u42 hp hp2 hq2 e hαp)
    · exact hi.elim

end NotChev

section Exc

theorem t2021Layer_exc {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.LieTypeIndex} {hd : d.Valid}
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group))
    (hexc : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outerPLayerExc p d)
    (hD4 : ¬ (p = 3 ∧ catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)))
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    {Y : Subgroup S} (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hEY : ∀ φ ∈ E, ∀ y ∈ Y, φ y ∈ Y) :
    False := by
  obtain ⟨eS⟩ := he
  cases d with
  | A n q =>
    rcases n with _ | _ | n
    · exact hexc.elim
    ·
      obtain ⟨rfl, hq⟩ := hexc
      have h := CFSG.LocalAnalysis.GLTheoremA.List93.l2Two_holds S
        ⟨.lie ⟨.A 1 q, hd⟩, t2021Layer_p_eq_two_of_card_eq_eight hq, ⟨eS⟩⟩ E hE
      omega
    · exact hexc.elim
  | twistedA n q =>
    rcases n with _ | _ | _ | n
    · exact hexc.elim
    · exact hexc.elim
    ·
      obtain ⟨rfl, hq⟩ := hexc
      obtain ⟨r, k, hr, hk⟩ := q
      obtain ⟨rfl, rfl⟩ := t2021Layer_prime_pow_eq_eight hr hk
        ((TauCeti.PrimePower.card_def ⟨r, k, hr, hk⟩).symm.trans hq)
      obtain ⟨eU⟩ := CFSG.RankThree.PartTwo.Sec4.Ronan431C.nonempty_projSU_equiv_lieTwistedA
        (r := 2) (f := 3) hk hd
      exact t2021Layer_exc_u38 (eS.trans eU.symm) hE hE3 hY2 hY1 hEY
    · exact hexc.elim
  | suzuki k =>
    obtain ⟨rfl, rfl⟩ := hexc
    have h := CFSG.LocalAnalysis.RankFourTheoremC.autRankTwoAt_suzuki
      (d := ⟨.suzuki 2, hd⟩) rfl S ⟨eS⟩ E hE
    omega
  | trialityD4 q => exact hD4 ⟨hexc, ⟨.lie ⟨.trialityD4 q, hd⟩, trivial, ⟨eS⟩⟩⟩
  | _ => exact hexc.elim

end Exc

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
