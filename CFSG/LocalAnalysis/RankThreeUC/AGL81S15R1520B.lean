module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520B0
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section Centralizer

variable {Y : Type} [Group Y] [Finite Y]

theorem two_le_pRank_centralizer_aux_card_le {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (E : Subgroup (A × B)) :
    Nat.card E ≤ Nat.card (E.map (MonoidHom.fst A B)) * Nat.card (E.map (MonoidHom.snd A B)) := by
  let f : E → (E.map (MonoidHom.fst A B)) × (E.map (MonoidHom.snd A B)) := fun e =>
    (⟨(e : A × B).1, Subgroup.mem_map_of_mem (MonoidHom.fst A B) e.2⟩,
      ⟨(e : A × B).2, Subgroup.mem_map_of_mem (MonoidHom.snd A B) e.2⟩)
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun z => (z.1 : A)) h
    have h2 := congrArg (fun z => (z.2 : B)) h
    exact Subtype.ext (Prod.ext h1 h2)
  calc Nat.card E ≤ Nat.card ((E.map (MonoidHom.fst A B)) × (E.map (MonoidHom.snd A B))) :=
        Nat.card_le_card_of_injective f hf
    _ = _ := Nat.card_prod _ _

theorem two_le_pRank_centralizer_aux_card_pow {Z : Type} [Group Z] [Finite Z] {p : ℕ}
    (hp : p.Prime) {E : Subgroup Z} (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.iff_card.1 fun g => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hE.2 _ g.2)⟩

theorem two_le_pRank_centralizer_aux_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} (hp : p.Prime) (H : Subgroup (A × B)) :
    CFSG.Open.pRank p H ≤ CFSG.Open.pRank p (H.map (MonoidHom.fst A B)) +
      CFSG.Open.pRank p (H.map (MonoidHom.snd A B)) := by
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E hEH hE => ?_
  have hE1 : IsElemAbelian p (E.map (MonoidHom.fst A B)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hE2 : IsElemAbelian p (E.map (MonoidHom.snd A B)) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  obtain ⟨a, ha⟩ := two_le_pRank_centralizer_aux_card_pow hp hE1
  obtain ⟨b, hb⟩ := two_le_pRank_centralizer_aux_card_pow hp hE2
  have ha' : a ≤ CFSG.Open.pRank p (H.map (MonoidHom.fst A B)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hEH) hE1 ha
  have hb' : b ≤ CFSG.Open.pRank p (H.map (MonoidHom.snd A B)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hEH) hE2 hb
  calc Nat.card E ≤ _ := two_le_pRank_centralizer_aux_card_le E
    _ = p ^ a * p ^ b := by rw [ha, hb]
    _ = p ^ (a + b) := (pow_add p a b).symm
    _ ≤ _ := Nat.pow_le_pow_right hp.pos (add_le_add ha' hb')

@[expose] def two_le_pRank_centralizer_aux_prodHom (S : Subgroup Y) :
    ↥S × ↥(Subgroup.centralizer (S : Set Y)) →* Y :=
  S.subtype.noncommCoprod (Subgroup.centralizer (S : Set Y)).subtype
    (fun s c => (Subgroup.mem_centralizer_iff.1 c.2) (s : Y) s.2)

theorem two_le_pRank_centralizer_aux_prodHom_apply (S : Subgroup Y) (s : ↥S)
    (c : ↥(Subgroup.centralizer (S : Set Y))) :
    two_le_pRank_centralizer_aux_prodHom S (s, c) = (s : Y) * (c : Y) := rfl

theorem two_le_pRank_centralizer_aux_prodHom_ker_card_dvd (S : Subgroup Y) :
    Nat.card (two_le_pRank_centralizer_aux_prodHom S).ker ∣ Nat.card (Subgroup.center ↥S) := by
  set φ := two_le_pRank_centralizer_aux_prodHom S with hφ
  let ψ : φ.ker →* ↥S := (MonoidHom.fst _ _).comp φ.ker.subtype
  have hψ : ∀ x : φ.ker, ψ x ∈ Subgroup.center ↥S := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : (x.1.1 : Y) * (x.1.2 : Y) = 1 := x.2
    have h2 : (x.1.2 : Y) = (x.1.1 : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have h3 : Commute (g : Y) (x.1.2 : Y) :=
      (Subgroup.mem_centralizer_iff.1 x.1.2.2) (g : Y) g.2
    rw [h2] at h3
    exact Subtype.ext (Commute.inv_right_iff.1 h3).eq
  let ψ' : φ.ker →* Subgroup.center ↥S := ψ.codRestrict _ hψ
  have hinj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h0 : x.1.1 = 1 := congrArg Subtype.val hx
    have h1 : (x.1.1 : Y) * (x.1.2 : Y) = 1 := x.2
    rw [h0, OneMemClass.coe_one, one_mul] at h1
    have h2 : x.1.2 = 1 := Subtype.ext h1
    exact Subtype.ext (Prod.ext h0 h2)
  exact Subgroup.card_dvd_of_injective ψ' hinj

theorem two_le_pRank_centralizer_aux_sup {p : ℕ} (hp : p.Prime) {S : Subgroup Y}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S)) :
    CFSG.Open.pRank p (S ⊔ Subgroup.centralizer (S : Set Y)) ≤
      CFSG.Open.pRank p S + CFSG.Open.pRank p (Subgroup.centralizer (S : Set Y)) := by
  set C := Subgroup.centralizer (S : Set Y) with hC
  set φ := two_le_pRank_centralizer_aux_prodHom S with hφ
  have hker : ¬ p ∣ Nat.card φ.ker := fun h =>
    hZ (h.trans (two_le_pRank_centralizer_aux_prodHom_ker_card_dvd S))
  have h1 : S ⊔ C ≤ (⊤ : Subgroup (↥S × ↥C)).map φ := by
    rw [← MonoidHom.range_eq_map]
    refine sup_le ?_ ?_
    · intro s hs
      exact ⟨(⟨s, hs⟩, 1), by simp [hφ, two_le_pRank_centralizer_aux_prodHom_apply]⟩
    · intro c hc
      exact ⟨(1, ⟨c, hc⟩), by simp [hφ, two_le_pRank_centralizer_aux_prodHom_apply]⟩
  have hp1 := hp.one_lt
  calc CFSG.Open.pRank p (S ⊔ C) ≤ CFSG.Open.pRank p ((⊤ : Subgroup (↥S × ↥C)).map φ) :=
        CFSG.SectionRank.pRank_mono hp1 h1
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥S × ↥C)) :=
        CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd hp φ hker ⊤
    _ ≤ CFSG.Open.pRank p ((⊤ : Subgroup (↥S × ↥C)).map (MonoidHom.fst _ _)) +
        CFSG.Open.pRank p ((⊤ : Subgroup (↥S × ↥C)).map (MonoidHom.snd _ _)) :=
        two_le_pRank_centralizer_aux_prod hp _
    _ ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥S) + CFSG.Open.pRank p (⊤ : Subgroup ↥C) :=
        add_le_add (CFSG.SectionRank.pRank_mono hp1 le_top)
          (CFSG.SectionRank.pRank_mono hp1 le_top)
    _ = CFSG.Open.pRank p S + CFSG.Open.pRank p C := by
        rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]

theorem two_le_pRank_centralizer_aux_sylow {p : ℕ} (hp : p.Prime) {P : Subgroup Y}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) :
    CFSG.Open.pRank p P = CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hPg, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hdvd' : ¬ p ∣ P.index := by rwa [Subgroup.relIndex_top_right] at hdvd
  exact (CFSG.SectionRank.pRank_sylow (hPg.toSylow hdvd')).1

theorem two_le_pRank_centralizer_gen {p : ℕ} (hp : p.Prime) {S : Subgroup Y}
    (hY : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y)) (hS : CFSG.Open.pRank p S ≤ 1)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥S))
    (hP : ∃ P : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧
      P ≤ S ⊔ Subgroup.centralizer (S : Set Y)) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer (S : Set Y)) := by
  obtain ⟨P, hPS, hPle⟩ := hP
  have h1 : 3 ≤ CFSG.Open.pRank p P := by
    rw [two_le_pRank_centralizer_aux_sylow hp hPS]
    exact hY
  have h2 : 3 ≤ CFSG.Open.pRank p (S ⊔ Subgroup.centralizer (S : Set Y)) :=
    h1.trans (CFSG.SectionRank.pRank_mono hp.one_lt hPle)
  have h3 := two_le_pRank_centralizer_aux_sup hp hZ
  omega

end Centralizer

section CMBar

variable {X : Type} [Group X] [Finite X]

theorem two_le_pRank_cMBar_aux_sylow_of_pElements {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) {H : Subgroup Y} (hH : ∀ x : Y, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ H) :
    ∃ P : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧ P ≤ H := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (⊤ : Subgroup Y)
  refine ⟨P, hP, fun x hx => hH x ?_⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP.isPGroup) ⟨x, hx⟩
  exact ⟨k, by rw [← Subgroup.orderOf_mk x hx]; exact hk⟩

theorem two_le_pRank_cMBar_aux_sylow_of_outTwo {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Y} {k : ℕ} (hk : k < p)
    (hconj : {S' : Subgroup Y | ∃ y : Y, S' = S.map (MulAut.conj y).toMonoidHom}.ncard ≤ k)
    (hOut : OutTwoGroup ↥S) :
    ∃ P : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧
      P ≤ S ⊔ Subgroup.centralizer (S : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP, hPN⟩ := exists_sylow_le_normalizer hp hk hconj
  refine ⟨P, hP, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.1 hP.isPGroup) ⟨x, hx⟩
  have hx' : orderOf x = p ^ j := by rw [← Subgroup.orderOf_mk x hx]; exact hj
  have hodd : Odd (orderOf x) := by
    rw [hx']
    exact (hp.odd_of_ne_two hp2).pow
  exact mem_sup_centralizer_of_outTwo hOut (hPN hx) hodd

theorem two_le_pRank_cMBar_aux_outList {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    IsOutTwoGroupList S := by
  rcases h with ⟨-, d, q, hq, hd, he⟩ | ⟨h, -⟩
  · exact Or.inr (Or.inr ⟨d, Or.inr (Or.inr ⟨q, hq, hd⟩), he⟩)
  · omega

theorem two_le_pRank_cMBar_aux_barO2_top : barO2 (⊤ : Subgroup X) = ⊤ := by
  unfold barO2
  rw [Subgroup.map_top, QuotientGroup.range_mk']

theorem two_le_pRank_cMBar_aux_no_index (p : ℕ)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ p) :
    ∀ N : Subgroup (X ⧸ CFSG.pCore 2 X), N.Normal → N.index ≠ p := by
  intro N hN hNi
  haveI := Subgroup.normal_comap (H := N) (QuotientGroup.mk' (CFSG.pCore 2 X))
  exact hno (N.comap (QuotientGroup.mk' (CFSG.pCore 2 X))) this
    (by rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hNi])

theorem two_le_pRank_cMBar_aux_conj_count {L : Subgroup X} (hL : IsC2 L) :
    {S' : Subgroup (X ⧸ CFSG.pCore 2 X) |
        ∃ y : X ⧸ CFSG.pCore 2 X, S' = (barO2 L).map (MulAut.conj y).toMonoidHom}.ncard ≤
      Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} := by
  have hsub : {S' : Subgroup (X ⧸ CFSG.pCore 2 X) |
        ∃ y : X ⧸ CFSG.pCore 2 X, S' = (barO2 L).map (MulAut.conj y).toMonoidHom} ⊆
      barO2 '' {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} := by
    rintro S' ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨L.map (MulAut.conj x).toMonoidHom, ⟨liftOf_conj_aux4 hL x, ?_⟩, ?_⟩
    · rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.normalClosure_normal (s := (L : Set X))).conj_mem l
        (Subgroup.subset_normalClosure hl) x
    · exact barO2_map_conj L x
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem two_le_pRank_cMBar_gen (hK7145 : K7145) (hKOut : KOut) (hXK : CFSG.Open.IsKGroup X)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Subgroup X} (hL : IsC2 L)
    (hXp : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) (hLp : CFSG.Open.pRank p L ≤ 1)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥(barO2 L)))
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ p)
    (h15 : L = Subgroup.normalClosure (L : Set X) ∨
      IsCentralProdA6Z3 ↥(barO2 (Subgroup.normalClosure (L : Set X))) ∨
      (IsLThreeOfExp 1 ↥(barO2 L) ∧
        Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3)) :
    2 ≤ CFSG.Open.pRank p (cMBar L) := by
  have hp2 : p ≠ 2 := by omega
  have hY3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ CFSG.pCore 2 X)) := by
    have h := pRank_barO2_eq_aux_eq (⊤ : Subgroup X) hp hp2
    rw [two_le_pRank_cMBar_aux_barO2_top] at h
    rw [← h]
    exact hXp
  have hS1 : CFSG.Open.pRank p (barO2 L) ≤ 1 := by
    rw [← pRank_barO2_eq_aux_eq L hp hp2]
    exact hLp
  have hYK : CFSG.Open.IsKGroup (X ⧸ CFSG.pCore 2 X) := hXK.quotient _
  have hnoY := two_le_pRank_cMBar_aux_no_index p hno
  have hsyl : ∃ P : Subgroup (X ⧸ CFSG.pCore 2 X), CFSG.ABGLocalTools.IsSylowOf p P ⊤ ∧
      P ≤ barO2 L ⊔ Subgroup.centralizer (barO2 L : Set (X ⧸ CFSG.pCore 2 X)) := by
    rcases h15 with h | h | ⟨h3, hcnt⟩
    · haveI hn : L.Normal := by
        rw [h]
        exact Subgroup.normalClosure_normal
      haveI : (barO2 L).Normal := Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
      exact two_le_pRank_cMBar_aux_sylow_of_pElements hp fun x hx =>
        pElement_mem_sup_centralizer hK7145 hYK hp hp2 hL.component.2.2 hS1 hnoY hx
    · obtain ⟨hA6, hcnt⟩ := isAltSixCoverThree_of_centralProd hL h
      exact two_le_pRank_cMBar_aux_sylow_of_outTwo hp hp2 (k := 2) (by omega)
        ((two_le_pRank_cMBar_aux_conj_count hL).trans hcnt)
        (outTwoGroup_of_isAltSixCoverThree hKOut hA6)
    · exact two_le_pRank_cMBar_aux_sylow_of_outTwo hp hp2 (k := 3) (by omega)
        ((two_le_pRank_cMBar_aux_conj_count hL).trans hcnt)
        (hKOut _ (two_le_pRank_cMBar_aux_outList h3))
  exact two_le_pRank_centralizer_gen hp hY3 hS1 hZ hsyl

end CMBar

end CFSG.LocalAnalysis.RankThreeUC.S15
