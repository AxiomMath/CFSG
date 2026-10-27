module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenS1
import CFSG.GroupTheory.QuasisimpleCenterDivisibility
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Facts
public import CFSG.LocalAnalysis.GLTheoremA.S9.Basic
public import CFSG.RankThree.PartOne.S11d.LieFieldTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem quasisimple_chev_of_comp {Q : TauCeti.LieTypeIndex → Prop}
    (h2 : GenCompQuasiOn Q) (h3 : GenCompChevOn Q) {p q : ℕ} {S B : Subgroup Ω}
    (H : GenHyp Q p q S B) {d : Ω} (hdp : d ^ p = 1) (hdS : d ∉ centModSubgroup p S)
    {J : Subgroup Ω} (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({d} : Set Ω)) J) :
    CFSG.Open.IsQuasisimple ↥J ∧ IsChevSimple q (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨e, hchar, hQe, hOdd⟩ := H.exists_oddLie
  set x := normalizerToCenterQuotientAut S ⊤ (H.le_normalizer ⊤) ⟨d, Subgroup.mem_top d⟩
    with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← map_pow, show (⟨d, Subgroup.mem_top d⟩ : ↥(⊤ : Subgroup Ω)) ^ p = 1 from
      Subtype.ext hdp, map_one]
  have hx1 : x ≠ 1 := fun h => hdS ((H.aut_eq_one_iff ⊤ _).1 h)
  have hJS : J ≤ S := fun j hj => (hJ.1 hj).1
  set f : ↥J →* ↥S ⧸ Subgroup.center ↥S :=
    (QuotientGroup.mk' (Subgroup.center ↥S)).comp (Subgroup.inclusion hJS) with hf
  have hJ₀ : GLAPComponent p (fixSubgroup x) f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact glaPComponent_fixSubgroup_of_inf_centralizer H.pPrime (H.le_normalizer ⊤) _ hJ
  have hq₀ := (h2 p _ e hOdd hQe x hxp hx1 _ hJ₀).2.2
  have hc₀ := h3 p _ e hOdd hQe x hxp hx1 _ hJ₀
  rw [hchar] at hc₀
  have hperfJ : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  have hker : f.rangeRestrict.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hf, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    have hgj := congrArg Subtype.val (Subgroup.mem_center_iff.1 hj (Subgroup.inclusion hJS g))
    exact hgj
  obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.nonempty_centerQuotientEquiv_of_surjective hperfJ
    f.rangeRestrict f.rangeRestrict_surjective hker
  haveI : IsSimpleGroup (↥f.range ⧸ Subgroup.center ↥f.range) := hq₀.2
  exact ⟨⟨hperfJ.commutator_eq_top, e₁.isSimpleGroup⟩,
    (CFSG.LocalAnalysis.GLTheoremA.S9.isChevSimple_congr e₁).2 hc₀⟩

private theorem card_sup_zpowers {p : ℕ} [Fact p.Prime] {D : Subgroup Ω} {e : Ω}
    (hep : e ^ p = 1) (heD : e ∉ D) (hcomm : ∀ x ∈ D, x * e = e * x) :
    Nat.card ↥(D ⊔ Subgroup.zpowers e) = Nat.card D * p := by
  have he1 : e ≠ 1 := fun h => heD (h ▸ D.one_mem)
  have hord : Nat.card (Subgroup.zpowers e) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hep he1
  have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set Ω) :=
    Subgroup.zpowers_le.2
      (Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 hcomm))
  have hinf : D ⊓ Subgroup.zpowers e = ⊥ := by
    have hdvd : Nat.card ↥(D ⊓ Subgroup.zpowers e) ∣ p :=
      hord ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exfalso
      have heq : D ⊓ Subgroup.zpowers e = Subgroup.zpowers e :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hord])
      have hmem : e ∈ D ⊓ Subgroup.zpowers e := by
        rw [heq]
        exact Subgroup.mem_zpowers e
      exact heD hmem.1
  have h := card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, hord] at h
  exact h

private theorem exists_orderOf_eq_two_of_one_le {X : Type} [Group X] [Finite X] {p : ℕ}
    (h : 1 ≤ GLATwoLocalRank p X) : ∃ t : X, orderOf t = 2 := by
  have hne : {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hem
    have h0 : GLATwoLocalRank p X = 0 := by
      show sSup {k | ∃ H : Subgroup X, IsTwoLocal H ∧ CFSG.Open.pRank p H = k} = 0
      rw [hem]
      exact csSup_empty
    omega
  obtain ⟨_, _, ⟨T, hT, hT2, -⟩, -⟩ := hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hT (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 (hn ▸ dvd_pow_self 2 hn0)
  exact ⟨x, by rw [Subgroup.orderOf_coe, hx]⟩

private theorem le_pRank_center {p : ℕ} (hp : p.Prime) {J X : Subgroup Ω} (hXJ : X ≤ J)
    (hXC : X ≤ Subgroup.centralizer (J : Set Ω)) (hX : IsElemAbelian p X) {k : ℕ}
    (hk : Nat.card X = p ^ k) :
    k ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(Subgroup.center ↥J)) := by
  set ι : ↥(Subgroup.center ↥J) →* Ω := J.subtype.comp (Subgroup.center ↥J).subtype
  have hιinj : Function.Injective ι :=
    J.subtype_injective.comp (Subgroup.center ↥J).subtype_injective
  have hXr : X ≤ ι.range := by
    intro x hx
    refine ⟨⟨⟨x, hXJ hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_⟩, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hXC hx) g g.2
  have hmap : (X.comap ι).map ι = X := Subgroup.map_comap_eq_self hXr
  have hXc : IsElemAbelian p (X.comap ι) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hιinj ?_⟩
    · apply Subtype.ext
      apply hιinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact isElemAbelian_commute hX a.2 b.2
    · rw [map_pow, map_one]
      exact hX.2 _ hy
  have hXk : Nat.card (X.comap ι) = p ^ k := by
    rw [← Subgroup.card_map_of_injective hιinj, hmap, hk]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hXc hXk

theorem genStep5On_of_leaves {Q : TauCeti.LieTypeIndex → Prop} (h4 : GenPlaneCompOn Q) :
    GenStep5On Q := by
  intro p q Ω _ _ S B H B' d J hT _ hcomp
  obtain ⟨⟨hB'el, hB'c, -⟩, hdB', hdS, hJ⟩ := hT
  have hp := H.pPrime
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup Ω := B' ⊓ centModSubgroup p J
  set B₀ : Subgroup Ω := B' ⊓ centModSubgroup p S
  have hJS : J ≤ S := fun j hj => (hJ.1 hj).1
  have hB₀D : B₀ ≤ D := fun b hb => ⟨hb.1, centMod_iff.1 (centMod_of_mem_centralizer
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hJS)
      (by rw [← H.centModSubgroup_eq]; exact hb.2)))⟩
  have hdD : d ∈ D := ⟨hdB', centMod_iff.1 (centMod_of_mem_centralizer
    (Subgroup.mem_centralizer_iff.2 fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hj).2))⟩
  have hDel : IsElemAbelian p D := hB'el.mono inf_le_left
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hDel
  have hlt : B₀ < D := lt_of_le_of_ne hB₀D fun h => hdS (h ▸ hdD).2
  have hk2 : 2 ≤ k := by
    have h1 := card_lt_of_lt' hlt
    rw [hB'c, hk] at h1
    by_contra hk2
    have h2 : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at h2
    omega
  rw [hk]
  suffices k ≤ 2 by rw [show k = 2 by omega]
  by_contra hk3
  set ψ := normalizerToCenterQuotientAut S D (H.le_normalizer D)
  have hcardψ : Nat.card ψ.range * p = p ^ k := by
    have h1 := H.card_range_mul D
    rw [show D ⊓ centModSubgroup p S = B₀ from le_antisymm (fun b hb => ⟨hb.1.1, hb.2⟩)
      (fun b hb => ⟨hB₀D hb, hb.2⟩), hB'c, hk] at h1
    exact h1
  have hψc : Nat.card ψ.range = p ^ (k - 1) := by
    have h : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h] at hcardψ
    exact Nat.eq_of_mul_eq_mul_right hp.pos hcardψ
  have hRel : IsElemAbelian p ψ.range := isElemAbelian_range (H.le_normalizer D) hDel
  have hrank : 2 ≤ CFSG.Open.pRank p ψ.range :=
    (by omega : 2 ≤ k - 1).trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hRel hψc)
  obtain ⟨P, hPR, hPel, hPc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hrank
  obtain ⟨e, -, hQe, hOdd⟩ := H.exists_oddLie
  refine h4 p _ e hOdd hQe P hPel hPc
    ((J.subgroupOf S).map (QuotientGroup.mk' (Subgroup.center ↥S))) fun x hxP hx1 => ?_
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 (hPR hxP)
  have hbS : (b : Ω) ∉ centModSubgroup p S := fun h => hx1 ((H.aut_eq_one_iff D b).2 h)
  exact glaPComponent_fixSubgroup_of_inf_centralizer hp (H.le_normalizer D) b
    (hcomp b b.2.1 (centMod_iff.2 b.2.2) hbS)

theorem genStep6On_of_leaves {Q : TauCeti.LieTypeIndex → Prop} (h1 : GenGood)
    (h2 : GenCompQuasiOn Q) (h3 : GenCompChevOn Q) (h5 : GenLpEpsLocal)
    (hamb : CFSG.LocalAnalysis.GLTheoremA.S2019.S2019FactAmbAut) : GenStep6On Q := by
  intro p q Ω _ _ S B H B' d J hT hN hD
  obtain ⟨⟨hB'el, -, hB'case⟩, hdB', hdS, hJ⟩ := hT
  have hp := H.pPrime
  haveI : Fact p.Prime := ⟨hp⟩
  set D : Subgroup Ω := B' ⊓ centModSubgroup p J
  have hDB' : D ≤ B' := inf_le_left
  have hDel : IsElemAbelian p D := hB'el.mono hDB'
  obtain ⟨hJq, hChev⟩ := quasisimple_chev_of_comp h2 h3 H (hB'el.2 d hdB') hdS hJ
  have hpJ : p ∣ Nat.card J :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116pI_pcomp_card_dvd hp hJ
  have hDC : D ≤ Subgroup.centralizer (J : Set Ω) := fun b hb =>
    genStepCentOn_of_leaves h2 p q Ω S B H d J (hB'el.2 d hdB') hdS hJ b (centMod_iff.2 hb.2)
  have hperfJ : Group.IsPerfect ↥J := ⟨hJq.1⟩
  set ψ := normalizerToCenterQuotientAut J B' hN with hψ
  have hker : ∀ b : ↥B', ψ b = 1 ↔ (b : Ω) ∈ D := fun b => by
    rw [hψ, normalizerToCenterQuotientAut_eq_one_iff hperfJ hN b]
    exact ⟨fun h => ⟨h.1, centMod_iff.1 (centMod_of_mem_centralizer h.2)⟩,
      fun h => ⟨h.1, hDC h⟩⟩
  have hBD : B' ⊓ Subgroup.centralizer (J : Set Ω) = D :=
    le_antisymm (fun b hb => ⟨hb.1, centMod_iff.1 (centMod_of_mem_centralizer hb.2)⟩)
      (fun b hb => ⟨hb.1, hDC hb⟩)
  have hAcard : Nat.card ψ.range * p ^ 2 = Nat.card B' := by
    rw [hψ, card_range_normalizerToCenterQuotientAut hperfJ hN, hBD, ← hD]
    have h := Subgroup.relIndex_mul_card D B'
    rwa [inf_eq_left.2 hDB'] at h
  have hBB' : Nat.card B ≤ Nat.card B' := by
    rcases hB'case with rfl | ⟨hle, -⟩
    · exact le_rfl
    · exact hle
  have hA2 : p ^ 2 ≤ Nat.card ψ.range := by
    have h : p ^ 2 * p ^ 2 ≤ Nat.card ψ.range * p ^ 2 := by
      rw [hAcard, ← pow_add]
      exact H.four.trans hBB'
    exact Nat.le_of_mul_le_mul_right h (pow_pos hp.pos 2)
  have hAel : IsElemAbelian p ψ.range := isElemAbelian_range hN hB'el
  rcases hChev with ⟨i, hi, ⟨eJ⟩⟩ | hambJ
  swap
  · exact absurd hA2 (not_le.2 (hamb p q hp H.pOdd H.qPrime H.qOdd H.qp _ hambJ _ hAel))
  cases i with
  | cyclic r hr => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie e =>
    have hchar : e.1.characteristic = q := hi
    have hOdd : OddLie p (↥J ⧸ Subgroup.center ↥J) e :=
      ⟨hp, H.pOdd, ⟨eJ⟩, by rw [hchar]; exact H.qOdd, by rw [hchar]; exact fun h => H.qp h.symm⟩
    have hpT : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
      CFSG.dvd_card_quotient_center_of_quasisimple
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isQuasisimple_of_open' hJq) hp hpJ
    rcases h1 p _ e hOdd hpT ψ.range hAel hA2 with ⟨a, haA, ha1, hlay⟩ | ⟨hlp, hAc⟩
    ·
      obtain ⟨⟨e₀, he₀B'⟩, rfl⟩ := MonoidHom.mem_range.1 haA
      have he₀D : e₀ ∉ D := fun h => ha1 ((hker _).2 h)
      have hlay' : GLAPLayer p (J ⊓ Subgroup.centralizer ({e₀} : Set Ω)) ≠ ⊥ := fun h =>
        hlay ((glaPLayer_inf_centralizer_eq_bot_iff hp hN ⟨e₀, he₀B'⟩).1 h)
      have hEB' : D ⊔ Subgroup.zpowers e₀ ≤ B' := sup_le hDB' (Subgroup.zpowers_le.2 he₀B')
      refine ⟨D ⊔ Subgroup.zpowers e₀, hEB', hB'el.mono hEB', ?_, le_sup_left, ?_⟩
      · rw [card_sup_zpowers (hB'el.2 e₀ he₀B') he₀D
          (fun x hx => isElemAbelian_commute hB'el (hDB' hx) he₀B'), hD]
        ring
      · have hEq : J ⊓ Subgroup.centralizer ((D ⊔ Subgroup.zpowers e₀ : Subgroup Ω) : Set Ω) =
            J ⊓ Subgroup.centralizer ({e₀} : Set Ω) := by
          apply le_antisymm
          · exact inf_le_inf_left _ (Subgroup.centralizer_le
              (Set.singleton_subset_iff.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₀))))
          · rintro y ⟨hyJ, hye⟩
            refine ⟨hyJ, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
            have hle : D ⊔ Subgroup.zpowers e₀ ≤ Subgroup.centralizer ({y} : Set Ω) :=
              sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
                  (Subgroup.mem_centralizer_iff.1 (hDC hx) y hyJ).symm)
                (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
                  (Subgroup.mem_centralizer_singleton_iff.1 hye).symm))
            exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
        rw [hEq]
        exact hlay'
    ·
      exfalso
      have hB'c : Nat.card B' = p ^ 4 := by
        rw [← hAcard, hAc]
        ring
      have hBc : Nat.card B = p ^ 4 := le_antisymm (hBB'.trans hB'c.le) H.four
      by_cases hp3 : p = 3
      · exact H.not81 ⟨hp3, by rw [hBc, hp3]⟩
      have hp5 : 5 ≤ p := by
        have hp4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by norm_num)
        have := hp.two_le
        have := H.pOdd
        omega
      have hloc := h5 p hp H.pOdd ↥J hJq e hlp (by rw [hchar]; exact H.qOdd) ⟨eJ⟩
      have hw1 : 1 ≤ GLATwoLocalRank p ↥J := by omega
      obtain ⟨T, F, hTJ, hFJ, hT, hT2, hFel, hFN, hFc⟩ :=
        CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_twoLocal_attaining_subgroup
          hp.one_lt J (exists_orderOf_eq_two_of_one_le hw1)
      have hFD : ∀ a ∈ F, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
        Subgroup.mem_centralizer_iff.1 (hDC hb) a (hFJ ha)
      have hFDel : IsElemAbelian p (F ⊔ D) := hFel.sup_of_commute hDel hFD
      have hDNF : D ≤ Subgroup.normalizer (F : Set Ω) := fun b hb =>
        Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.2 fun a ha => hFD a ha b hb)
      have hcard := card_sup_mul_card_inf_of_le_normalizer hDNF
      obtain ⟨n, hn⟩ := exists_card_eq_pow_of_isElemAbelian hp hFDel
      obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp
        (hFel.mono (inf_le_left : F ⊓ D ≤ F))
      have hkm := le_pRank_center hp (inf_le_left.trans hFJ) (inf_le_right.trans hDC)
        (hFel.mono inf_le_left) hk
      rw [hn, hk, hFc, hD, ← pow_add, ← pow_add] at hcard
      have hnk := Nat.pow_right_injective hp.two_le hcard
      have hDNT : D ≤ Subgroup.normalizer (T : Set Ω) := fun b hb =>
        Subgroup.centralizer_le_normalizer _
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hTJ) (hDC hb))
      have hle :=
        CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
          hp.one_lt hT hT2 hFDel (sup_le hFN hDNT) hn
      have h4 : GLATwoLocalRank p Ω ≤ 4 :=
        (Nat.pow_le_pow_iff_right hp.one_lt).1 (H.twoLocal.trans hBc.le)
      omega

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
