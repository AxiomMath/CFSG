module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftLeaves
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowHyps
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.Mathlib.Arithmetic.TwoPowModThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD CFSG.LocalAnalysis.AGL81TheoremCD.Section15

section LiftData

variable {X : Type} [Group X] [Finite X]

theorem barO2_centralExt' {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) :
    ∃ f : ↥(barO2 L) →* ↥Ls,
      (∀ b : ↥(barO2 L), (f b : X ⧸ gnC T) = barToStar T (pCore_le_gnC hX) b) ∧
        Function.Surjective f ∧ f.ker ≤ Subgroup.center ↥(barO2 L) := by
  have hφ : ∀ A : Subgroup X,
      (barO2 A).map (barToStar T (pCore_le_gnC hX)) = A.map (toStar T) := by
    intro A
    unfold barO2
    rw [Subgroup.map_map]
    congr 1
  let f : ↥(barO2 L) →* ↥Ls := ((barToStar T (pCore_le_gnC hX)).comp (barO2 L).subtype).codRestrict Ls (by
    intro k
    have h : barToStar T (pCore_le_gnC hX) k ∈ (barO2 L).map (barToStar T (pCore_le_gnC hX)) :=
      ⟨k, k.2, rfl⟩
    rw [hφ, hL.2] at h
    exact h)
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    rw [← hL.2, ← hφ] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, hk⟩, rfl⟩
  have hcentral := (liftOf_central_ext hX hLs hL).1
  have hkerf : f.ker ≤ Subgroup.center ↥(barO2 L) := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := k.2
    have h1 : barToStar T (pCore_le_gnC hX) k = 1 := by
      have h0 : f k = 1 := MonoidHom.mem_ker.1 hk
      exact congrArg Subtype.val h0
    have h2 : l ∈ gnC T := by
      have h3 : toStar T l = 1 := by
        have : barToStar T (pCore_le_gnC hX) (QuotientGroup.mk' (CFSG.pCore 2 X) l) = toStar T l := rfl
        rw [← this, hlk]
        exact h1
      exact (QuotientGroup.eq_one_iff l).1 h3
    have h4 : (k : X ⧸ CFSG.pCore 2 X) ∈
        ((L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X))) :=
      ⟨l, ⟨hl, h2⟩, hlk⟩
    obtain ⟨z, hz, hzk⟩ := hcentral h4
    have : z = k := Subtype.ext hzk
    rwa [← this]
  exact ⟨f, fun b => rfl, hf, hkerf⟩

theorem rankDatum1512_of_ctx (hT : LieOddRankTable) {T T₁ T₂ : Subgroup X} {L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hshape : GNShape T T₁ T₂)
    (hLs : GNYComponent T T₁ T₂ Ls) (hL : LiftOf T L Ls)
    (h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3) : RankDatum1512 T L Ls :=
  rankDatum1512_of_rankDatum (rankDatum hT hX hshape hLs hL) h3

theorem rankDatum1512_of_pRank_three_eq_one {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hd : RankDatum T L Ls) (h1 : CFSG.Open.pRank 3 L = 1) : RankDatum1512 T L Ls := by
  rcases hd with ⟨d, hdr, e, hr⟩ | ⟨n, hn, e, hr⟩ | ⟨n, hn, e, hr⟩ | h4 | h5
  · have hval : mRankChev d.1 3 (Nat.card (Subgroup.center ↥(barO2 L))) = 1 :=
      (hr 3 Nat.prime_three (by norm_num)).symm.trans h1
    have hrank1 : RankOneList d.1 := ((mRank3_cases hdr _).1).1 hval
    obtain ⟨Q, hQ, -⟩ := rankOneList_cases hrank1
    have hQ2 : Q.p = 2 := by rw [hQ] at hdr; exact hdr.1
    exact Or.inl ⟨d, hdr, by rw [hQ]; exact hQ2, e, hr⟩
  · exact Or.inr (Or.inl ⟨n, hn, e, hr⟩)
  · exfalso
    have h := hr 3 Nat.prime_three (by norm_num)
    rcases hn with rfl | ⟨h8, -⟩ <;> omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))

@[expose] def KLiftA7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X), GNYComponent T T₁ T₂ Ls → LiftOf T L Ls →
      Nonempty (↥Ls ≃* alternatingGroup (Fin 7)) →
        Nonempty (↥(barO2 L) ≃* alternatingGroup (Fin 7))

end LiftData

section Row1515

variable {X : Type} [Group X] [Finite X]

theorem card_centerIn_s15 {Y : Type} [Group Y] (H : Subgroup Y) :
    Nat.card (KFactsPair.centerIn H) = Nat.card (Subgroup.center ↥H) := by
  unfold KFactsPair.centerIn
  exact Subgroup.card_map_of_injective H.subtype_injective

theorem card_centerIn_map_conj {Y : Type} [Group Y] (H : Subgroup Y) (z : Y) :
    Nat.card (KFactsPair.centerIn (H.map (MulAut.conj z).toMonoidHom)) = Nat.card (KFactsPair.centerIn H) := by
  rw [card_centerIn_s15, card_centerIn_s15]
  exact Nat.card_congr (Subgroup.centerCongr
    (H.equivMapOfInjective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective)).toEquiv.symm

theorem isAltSixCoverThree_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsAltSixCoverThree S') : IsAltSixCoverThree S := by
  obtain ⟨hq, hc, ⟨eq⟩⟩ := h
  refine ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e hq, ?_, ?_⟩
  · rw [← hc]
    exact Nat.card_congr (Subgroup.centerCongr e).toEquiv
  · exact ⟨(QuotientGroup.congr (Subgroup.center S) (Subgroup.center S') e
      (Subgroup.map_center_eq e)).trans eq⟩

theorem isAltSixCoverThree_barO2_conj {L : Subgroup X} (h : IsAltSixCoverThree ↥(barO2 L)) (x : X) :
    IsAltSixCoverThree ↥(barO2 (L.map (MulAut.conj x).toMonoidHom)) := by
  rw [barO2_map_conj]
  exact isAltSixCoverThree_of_mulEquiv
    ((barO2 L).equivMapOfInjective (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).toMonoidHom
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) x)).injective).symm h

theorem isCentralProdA6Z3_of_two_comps {Y : Type} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hA : IsAltSixCoverThree ↥A) (hB : IsAltSixCoverThree ↥B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hAB : KFactsPair.centerIn A = A ⊓ B)
    (hBA : KFactsPair.centerIn B = A ⊓ B) :
    IsCentralProdA6Z3 ↥(A ⊔ B) := by
  have hAC : A ≤ A ⊔ B := le_sup_left
  have hBC : B ≤ A ⊔ B := le_sup_right
  refine ⟨A.subgroupOf (A ⊔ B), B.subgroupOf (A ⊔ B),
    isAltSixCoverThree_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAC) hA,
    isAltSixCoverThree_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBC) hB, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hAC hBC]
    exact Subgroup.subgroupOf_self _
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (hc x hx y hy).symm
  · ext x
    show _ ↔ x ∈ CFSG.centerIn (A.subgroupOf (A ⊔ B))
    unfold CFSG.centerIn
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, fun g hg => ?_⟩
      have hxZ : (x : Y) ∈ KFactsPair.centerIn A := by rw [hAB]; exact ⟨hx1, hx2⟩
      exact Subtype.ext (((mem_centerIn_iff_s15 A x).1 hxZ).2 g hg)
    · rintro ⟨hx1, hx⟩
      refine ⟨hx1, ?_⟩
      have hxZ : (x : Y) ∈ KFactsPair.centerIn A := (mem_centerIn_iff_s15 A x).2 ⟨hx1, fun a ha => by
        have := hx ⟨a, hAC ha⟩ ha
        exact congrArg Subtype.val this⟩
      rw [hAB] at hxZ
      exact hxZ.2
  · ext x
    show _ ↔ x ∈ CFSG.centerIn (B.subgroupOf (A ⊔ B))
    unfold CFSG.centerIn
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx2, fun g hg => ?_⟩
      have hxZ : (x : Y) ∈ KFactsPair.centerIn B := by rw [hBA]; exact ⟨hx1, hx2⟩
      exact Subtype.ext (((mem_centerIn_iff_s15 B x).1 hxZ).2 g hg)
    · rintro ⟨hx2, hx⟩
      have hxZ : (x : Y) ∈ KFactsPair.centerIn B := (mem_centerIn_iff_s15 B x).2 ⟨hx2, fun b hb => by
        have := hx ⟨b, hBC hb⟩ hb
        exact congrArg Subtype.val this⟩
      rw [hBA] at hxZ
      exact ⟨hxZ.1, hx2⟩

theorem map_centerIn_barO2 {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T)
    (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls) :
    (KFactsPair.centerIn (barO2 L)).map (barToStar T (pCore_le_gnC hX)) = KFactsPair.centerIn Ls := by
  obtain ⟨f, hfφ, hf, hker⟩ := barO2_centralExt' hX hLs hL
  have hK : commutator ↥(barO2 L) = ⊤ := hL.1.component.2.2.1
  have hc := center_comap_eq_of_central_ext hK f hf hker
  have h1 : (Subgroup.center ↥(barO2 L)).map f = Subgroup.center ↥Ls := by
    rw [← hc, Subgroup.map_comap_eq_self_of_surjective hf]
  unfold KFactsPair.centerIn
  rw [Subgroup.map_map]
  have hcomp : (barToStar T (pCore_le_gnC hX)).comp (barO2 L).subtype = Ls.subtype.comp f := by
    ext b
    exact (hfφ b).symm
  rw [hcomp, ← Subgroup.map_map, h1]

theorem centerIn_barO2_ne_conj (hK57 : K57) {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hcomm : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls) (hL : LiftOf T L Ls) {n : ℕ}
    (hn : 0 < n) (hev : Even n)
    (e : Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) {x : X}
    (hx : L.map (MulAut.conj x).toMonoidHom ≠ L) :
    KFactsPair.centerIn (barO2 L) ≠ KFactsPair.centerIn (barO2 (L.map (MulAut.conj x).toMonoidHom)) := by
  intro heq
  have hφx : toStar T x ∉ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) := fun h =>
    hx (liftOf_conj hX hLs hL x h)
  have hk := hK57 X T hX Ls hLs hcomm n hn hev e x hφx
  have hLs' : IsComponentOf (KFactsPair.conjSub (toStar T x) Ls) ⊤ :=
    liftOf_conj_aux3 hLs (MulAut.conj (toStar T x))
  have hL' : LiftOf T (L.map (MulAut.conj x).toMonoidHom) (KFactsPair.conjSub (toStar T x) Ls) := by
    refine ⟨liftOf_conj_aux4 hL.1 x, ?_⟩
    have hcomp : (toStar T).comp (MulAut.conj x).toMonoidHom =
        (MulAut.conj (toStar T x)).toMonoidHom.comp (toStar T) := by
      ext a
      simp [MulAut.conj_apply]
    unfold KFactsPair.conjSub
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hL.2]
  have h1 := map_centerIn_barO2 hX hLs hL
  have h2 := map_centerIn_barO2 hX hLs' hL'
  rw [heq, h2] at h1
  exact hk (by rw [← centerIn_eq_cfsg, ← centerIn_eq_cfsg]; exact h1.symm)

theorem dvd_card_of_liftOf {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)} (hL : LiftOf T L Ls)
    {q : ℕ} (h : q ∣ Nat.card Ls) : q ∣ Nat.card L := by
  rw [← hL.2] at h
  exact h.trans (Subgroup.card_dvd_of_surjective ((toStar T).subgroupMap_surjective L))

theorem three_dvd_card_gnYComponent {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls) : 3 ∣ Nat.card ↥Ls := by
  by_contra h3
  apply (hthree Ls hLs).1
  have hle : pElementSubgroup 3 (gnA T T₁ Ls) ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxA, k, hk⟩
    rw [SetLike.mem_coe, Subgroup.mem_bot]
    by_contra hx1
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by simpa using hk))
    have hxLs : x ∈ Ls := (inf_le_right : gnA T T₁ Ls ≤ Ls) hxA
    have hd : orderOf x ∣ Nat.card Ls := by
      rw [← Subgroup.orderOf_mk x hxLs]
      exact orderOf_dvd_natCard _
    rw [hk] at hd
    exact h3 ((dvd_pow_self 3 hk0).trans hd)
  exact hle.trans bot_le

theorem one_le_pRank_three_of_lift {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) : 1 ≤ CFSG.Open.pRank 3 L := by
  exact one_le_pRank_of_dvd L Nat.prime_three
    (dvd_card_of_liftOf hL (three_dvd_card_gnYComponent hthree hLs))

theorem xlevel_1515_gen (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hK57 : K57) (hK541 : K541) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hdat : RankDatum1512 T L Ls)
    (hsub : ∀ p : ℕ, p.Prime → 5 ≤ p → 3 < CFSG.Open.pRank p (⊤ : Subgroup X) →
      2 ≤ CFSG.Open.pRank p L → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
      In1512 d.1 → (∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ¬ p ∣ indexQ d.1 - 1)
    (hA7 : Nonempty (↥Ls ≃* alternatingGroup (Fin 7)) →
      Nonempty (↥(barO2 L) ≃* alternatingGroup (Fin 7)))
    {J : Subgroup X} (hJ : J = Subgroup.normalClosure (L : Set X)) :
    L = J ∨ IsCentralProdA6Z3 ↥(barO2 J) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧ Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ J} ≤ 3) := by
  subst hJ
  by_cases hLJ : L = Subgroup.normalClosure (L : Set X)
  · exact Or.inl hLJ
  right
  have hC : IsC2 L := hL.1
  have hk2 := two_le_ncard_of_ne_normalClosure hC hLJ
  obtain ⟨k, hk⟩ : ∃ k, k = Set.ncard {L' : Subgroup X |
      IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} := ⟨_, rfl⟩
  rw [← hk] at hk2
  have hm1 : 1 ≤ CFSG.Open.pRank 3 L := one_le_pRank_three_of_lift hg.three hLs hL
  have hmJ3 : CFSG.Open.pRank 3 (Subgroup.normalClosure (L : Set X)) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans h3X
  by_cases hZ3 : 3 ∣ Nat.card (Subgroup.center ↥(barO2 L))
  ·
    obtain ⟨hZc, hm2, hshapeZ⟩ := centre_three_shape hKSML3 hKSMAlt hKSMOdd hKSMU4 hK541 hX
      hg.shape hLs hL hdat hA7 hZ3
    have hA : Nat.card (KFactsPair.centerIn (barO2 L)) = 3 := (card_centerIn_s15 _).trans hZc
    have hs : CFSG.Open.pRank 3 (KFactsPair.centerIn (barO2 L)) ≤ 1 := pRank_le_one_of_card_eq Nat.prime_three hA
    have hcount := pRank_normalClosure_ge hC Nat.prime_three (by norm_num) hs
    rw [← hk, hm2] at hcount
    have hJ3 := hmJ3
    have hk_eq : k = 2 := by omega
    obtain ⟨x, hxne, hJsup⟩ := eq_sup_of_ncard_two hC (hk.symm.trans hk_eq)
    have hC' : IsC2 (L.map (MulAut.conj x).toMonoidHom) := liftOf_conj_aux4 hC x
    have hcomm := isC2_commute_of_ne hC hC' (Ne.symm hxne)
    have hc : ∀ a ∈ barO2 L, ∀ b ∈ barO2 (L.map (MulAut.conj x).toMonoidHom), a * b = b * a := by
      intro a ha b hb
      have ha' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
      exact ((Subgroup.mem_centralizer_iff.1 ha') b hb).symm
    have hov := pRank_add_le_pRank_sup_add_pRank_inf hc Nat.prime_three
    have hbar : barO2 (Subgroup.normalClosure (L : Set X)) =
        barO2 L ⊔ barO2 (L.map (MulAut.conj x).toMonoidHom) := by
      rw [hJsup]; exact Subgroup.map_sup _ _ _
    have hr1 : CFSG.Open.pRank 3 (barO2 L) = 2 := by
      rw [← pRank_barO2_eq hC Nat.prime_three (by norm_num), hm2]
    have hr2 : CFSG.Open.pRank 3 (barO2 (L.map (MulAut.conj x).toMonoidHom)) = 2 := by
      rw [← pRank_barO2_eq hC' Nat.prime_three (by norm_num),
        exists_yComponent_dvd_aux_pRank_map_conj (by norm_num) L x, hm2]
    have hrJ : CFSG.Open.pRank 3 (barO2 L ⊔ barO2 (L.map (MulAut.conj x).toMonoidHom)) ≤ 3 := by
      rw [← hbar, ← pRank_barO2_eq_aux_eq _ Nat.prime_three (by norm_num)]
      exact hJ3
    have hinf : 3 ∣ Nat.card ↥(barO2 L ⊓ barO2 (L.map (MulAut.conj x).toMonoidHom)) :=
      (one_le_pRank_iff_dvd _ Nat.prime_three).1 (by omega)
    have hB : Nat.card (KFactsPair.centerIn (barO2 (L.map (MulAut.conj x).toMonoidHom))) = 3 := by
      rw [barO2_map_conj, card_centerIn_map_conj]; exact hA
    obtain ⟨hAB, hBA⟩ := centerIn_eq_inf_of_dvd hc Nat.prime_three hA hB hinf
    rcases hshapeZ with ⟨n, hn, hev, e⟩ | hA6
    · exact absurd (hAB.trans hBA.symm)
        (centerIn_barO2_ne_conj hK57 hX hLs.1 (hg.shape Ls hLs).1 hL hn hev e hxne)
    · left
      rw [hbar]
      exact isCentralProdA6Z3_of_two_comps hA6 (isAltSixCoverThree_barO2_conj hA6 x) hc hAB hBA
  ·
    have hs0 : CFSG.Open.pRank 3 (KFactsPair.centerIn (barO2 L)) = 0 :=
      pRank_eq_zero_of_not_dvd_s15 Nat.prime_three (by rw [card_centerIn_s15]; exact hZ3)
    have hcount := pRank_normalClosure_ge hC Nat.prime_three (by norm_num) hs0.le
    rw [← hk] at hcount
    have hJ3 := hmJ3
    have hm1' : CFSG.Open.pRank 3 L = 1 := by
      by_contra hne
      have h2 : 2 ≤ CFSG.Open.pRank 3 L := by omega
      nlinarith
    obtain ⟨hZ1, hshape1⟩ := rankOneShape_of_datum hKSML3 hX hLs.1 hL hdat hm1'
    rcases hshape1 with ⟨m, d, Q, hodd, hm2, hQp, hQe, hd, e, hrank⟩ | ⟨hL3, -⟩
    · exfalso
      obtain ⟨p, hp, hp2, hpd⟩ := exists_odd_prime_dvd_two_pow_sub_one_s15 hm2
      have hcard : Q.card = 2 ^ m := by
        rw [← hQe, ← hQp]; exact (ksm_card_eq rfl).symm
      have hpr : CFSG.Open.pRank p L = 2 := by
        rw [hrank p hp hp2, hd]
        exact rkLin_three_true_eq_two (by rw [hcard]; exact Nat.one_le_two_pow) (by rw [hcard]; exact hpd) hp
      have hs0p : CFSG.Open.pRank p (KFactsPair.centerIn (barO2 L)) = 0 :=
        pRank_eq_zero_of_not_dvd_s15 hp (by rw [card_centerIn_s15, hZ1]; exact hp.not_dvd_one)
      have hc2 := pRank_normalClosure_ge hC hp hp2 hs0p.le
      rw [← hk, hpr] at hc2
      by_cases hXp : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3
      · have hmJp := (CFSG.SectionRank.pRank_mono hp.one_lt
          (le_top : Subgroup.normalClosure (L : Set X) ≤ ⊤)).trans hXp
        nlinarith
      · push Not at hXp
        have hp3 : p ≠ 3 := by
          rintro rfl
          have hmod := two_pow_mod_three_of_odd hodd
          obtain ⟨k, hk⟩ := hpd
          have h1 : 2 ^ m = 3 * k + 1 := by omega
          rw [h1] at hmod
          omega
        have hp4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by decide)
        have hp5 : 5 ≤ p := by
          have := hp.two_le
          omega
        exact hsub p hp hp5 hXp (by omega) d (by rw [hd]; exact ⟨hQp, le_refl 2⟩)
          (by rw [hd]; exact hQp) (fun Q' h => by rw [hd] at h; cases h) e (by
            rw [hd]
            show p ∣ Q.card - 1
            rw [hcard]
            exact hpd)
    · rw [hm1'] at hcount
      exact Or.inr ⟨hL3, by omega⟩



theorem xlevel_1515 (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hK57 : K57) (hK541 : K541) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂)
    (hr3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 3)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hdat : RankDatum1512 T L Ls)
    (hA7 : Nonempty (↥Ls ≃* alternatingGroup (Fin 7)) →
      Nonempty (↥(barO2 L) ≃* alternatingGroup (Fin 7)))
    {J : Subgroup X} (hJ : J = Subgroup.normalClosure (L : Set X)) :
    L = J ∨ IsCentralProdA6Z3 ↥(barO2 J) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧ Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ J} ≤ 3)  :=
  xlevel_1515_gen hKSML3 hKSMAlt hKSMOdd hKSMU4 hK57 hK541 hX hg
    (hr3 3 Nat.prime_three (by norm_num)) hLs hL hdat
    (fun p hp hp5 hXp _ _ _ _ _ _ _ => absurd hXp (not_lt.2 (hr3 p hp (by omega)))) hA7 hJ

end Row1515

theorem row1515 (hT : LieOddRankTable) (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hK57 : K57) (hK541 : K541) (hKA7 : KLiftA7) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15Ctx2 G M T T₁ T₂) :
    Row1515 G M T T₁ T₂ := by
  intro Ls L hLs hL J hJ
  have h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3 := fun r hr hr2 =>
    (CFSG.SectionRank.pRank_mono hr.one_lt le_top).trans (ctx.rank_odd r hr hr2)
  exact xlevel_1515 hKSML3 hKSMAlt hKSMOdd hKSMU4 hK57 hK541 ctx.gn (S15Ctx2.good ctx)
    ctx.rank_odd hLs hL (rankDatum1512_of_ctx hT ctx.gn ctx.shape hLs hL h3)
    (hKA7 ↥M (T.subgroupOf M) T₁ T₂ ctx.gn (S15Ctx2.good ctx) Ls L hLs hL) hJ

theorem row1515_gen (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hK57 : K57) (hK541 : K541) (hKA7 : KLiftA7) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (ctx : S15CtxGen G M T T₁ T₂)
    (h11 : Row1511 G M T T₁ T₂)
    (h12 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Row1512Datum G M T T₁ T₂)
    (hsub : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.RowNotDvdSubOne G M T T₁ T₂) :
    Row1515 G M T T₁ T₂ := by
  intro Ls L hLs hL J hJ
  have h3X : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h11
  have hxsub : ∀ p : ℕ, p.Prime → 5 ≤ p → 3 < CFSG.Open.pRank p (⊤ : Subgroup ↥M) →
      2 ≤ CFSG.Open.pRank p L → ∀ d : TauCeti.ValidLieTypeIndex, IsRankTwoPlus d.1 →
      In1512 d.1 → (∀ Q, d.1 = .twistedA 4 Q → p ≠ 5) →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ¬ p ∣ indexQ d.1 - 1 := by
    intro p hp hp5 hXp h2 d hdr hd h5 e
    have hp2 : p ≠ 2 := by omega
    have hpσ : p ∈ sigmaSet G M := by
      by_contra hnot
      exact absurd hXp (not_lt.2 (ctx.rank_odd_off p hp hp2 hnot))
    exact hsub p hpσ hp5 Ls L hLs hL h2 d hdr hd h5 e
  exact xlevel_1515_gen hKSML3 hKSMAlt hKSMOdd hKSMU4 hK57 hK541 ctx.gn (S15CtxGen.good ctx)
    h3X hLs hL (h12 Ls L hLs hL) hxsub
    (hKA7 ↥M (T.subgroupOf M) T₁ T₂ ctx.gn (S15CtxGen.good ctx) Ls L hLs hL) hJ


end CFSG.LocalAnalysis.RankThreeUC.S15
