module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseU
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaK
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBetaZ
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95C
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure BetaInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l105 : Lemma105Inputs G p
  u48 : U48CentInvAt G
  u48z : U48CentInvFieldAt G
  i307 : I307At G
  u48c3 : U48Cent3AtK G
  i158 : I158AtK G
  i141 : I141RankAtK G
  su32 : Su32InterAt G
  fieldu3 : FieldU3RestrictAt G
  fieldpow : FieldAutPowClosedAt

namespace S10

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem not_mem_zpowers_symm {x a : G} (hx3 : x ^ 3 = 1) (hx : x ≠ 1) (ha3 : a ^ 3 = 1) (ha : a ≠ 1)
    (hax : a ∉ Subgroup.zpowers x) : x ∉ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hxa
  have hle : Subgroup.zpowers x ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hxa
  have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hx3 hx, orderOf_eq_prime ha3 ha]
  exact hax (Subgroup.eq_of_le_of_card_ge hle hcard ▸ Subgroup.mem_zpowers a)

theorem fieldOn_b_U (hc : S10Ctx G 3) (hin : Lemma105Inputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) : FieldOn 3 b L :=
  hU.field

private theorem casebeta_chev2_u4eight {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    IsChevSimple 2 S := by
  refine Or.inl (catalogIs_imp (fun i hi => ?_) h)
  rcases i with _ | _ | ⟨d, hdv⟩ | _
  · simp [S9.isU4eight, onLie] at hi
  · simp [S9.isU4eight, onLie] at hi
  · cases d with
    | twistedA n q =>
      by_cases hn3 : n = 3
      · subst hn3
        have h8 : q.p ^ q.exponent = 8 := by
          simpa [S9.isU4eight, onLie] using hi
        have hdvd : q.p ∣ 2 ^ 3 := by
          have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
          rw [h8] at h1
          norm_num
          exact h1
        have hp2 : q.p = 2 :=
          (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
        simp only [onLie, TauCeti.LieTypeIndex.characteristic_twistedA]
        exact hp2
      · exfalso
        simp [S9.isU4eight, onLie, hn3] at hi
    | _ => simp [S9.isU4eight, onLie] at hi
  · simp [S9.isU4eight, onLie] at hi

theorem Ipart_Ja_eq (hc : S10Ctx G 3) (hin : Lemma105Inputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (hax : a ∉ Subgroup.zpowers x)
    (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a)) {d : G} (hd : d ∈ Dgrp b x)
    (hdf : FieldOn 3 d (Jpart 3 (Ipart 3 L b) a)) :
    Ipart 3 (Jpart 3 (Ipart 3 L b) a) d = Ipart 3 L b := by
  set J := Jpart 3 (Ipart 3 L b) a with hJdef
  have haux := hin.l103.aut
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ Subgroup.one_mem _)
  have hJchev : IsChevSimple 2 (PSimple 3 J) := casebeta_chev2_u4eight hJ
  have hJa : J ≤ cx a := Jpart_le_cx h ha
  have hxB : x ∈ B := (sstar_triple h.star).2.1.1
  have hDB : Dgrp b x ≤ B :=
    (Subgroup.closure_le B).2 (Set.insert_subset_iff.2 ⟨h.mem, Set.singleton_subset_iff.2 hxB⟩)
  have hda : d ∉ Subgroup.zpowers a := by
    intro hmem
    have hacs : a ∈ cs J := Subgroup.mem_centralizer_iff.2 fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.1 (hJa hj)
    have hdcs : d ∈ cs J := (Subgroup.zpowers_le.2 hacs) hmem
    have hcm : CentMod 3 J d := centMod_of_mem_centralizer hdcs
    have hinn : InducesInnerMod 3 J d := inducesInnerMod_of_centMod hcm
    have hnd : InnDiagOn 3 (Subgroup.zpowers d) J :=
      haux.inner_innDiag (cx a) J d hsingle hJchev hcm.1 hinn
    exact (haux.field_nonInnDiag (cx a) J d hsingle hJchev hdf).2 hnd
  have hcomp : GLAPComponent 3 (J ⊓ cx d) (Ipart 3 L b) :=
    I_comp_in_J hc hin.l104 h ha ha1 hd hda hsingle
  have hle : Ipart 3 L b ≤ Ipart 3 J d := le_sSup (show Ipart 3 L b ∈ {K | GLAPComponent 3 (J ⊓ cx d) K} from hcomp)
  have hIJ : Ipart 3 J d ≠ ⊥ := fun h0 => h.I_ne (le_bot_iff.1 (le_trans hle (le_of_eq h0)))
  have hd3 : d ^ 3 = 1 := (B_el h).2 d (hDB hd)
  have hK' : GLAPComponent 3 (J ⊓ cx d) (Ipart 3 J d) :=
    (hin.i91comp (cx a) J d hsingle hJchev hd3 (Or.inl hdf) hIJ).1
  have hbar : barX 3 (J ⊓ cx d) (Ipart 3 L b) ≤ barX 3 (J ⊓ cx d) (Ipart 3 J d) := barX_mono 3 hle
  have heq : barX 3 (J ⊓ cx d) (Ipart 3 L b) = barX 3 (J ⊓ cx d) (Ipart 3 J d) :=
    CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hcomp.2.2.1 hK'.2.2.1 hbar
  exact (glaPComponent_unique hcomp hK' heq).symm

theorem beta_y_I (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) :
    ∃ y : G, y ∈ B ∧ y ∈ Ipart 3 L b ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ IsCentralIn 3 y (Ipart 3 L b) := by
  obtain ⟨z, -, hz2, hz1, hzc, hBz⟩ := exists_z hc hin.l105 hin.u48 hin.u48z h hU
  obtain ⟨E₂, hE₂I, hE₂el, hE₂card, hBE, -⟩ := hU.decomp
  have hE₂B : E₂ ≤ B := by
    rw [hBE]
    exact le_sup_right
  obtain ⟨hIcomp, -⟩ := Icomp_of_cfg hc hin.l105 h
  obtain ⟨y, hyE, hy1, hyc⟩ := hin.i307.one (L ⊓ cx b) (Ipart 3 L b) E₂ z hIcomp hU.I_iso
    (odd_core_I hc hin.l105.l103 h hU) hzc hz2 hz1 (le_inf hE₂I (fun g hg => hBz (hE₂B hg))) hE₂el hE₂card
  exact ⟨y, hE₂B hyE, hE₂I hyE, hE₂el.2 y hyE, hy1, hyc⟩

theorem beta_y1 (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (hax : a ∉ Subgroup.zpowers x)
    (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hfield : ∃ d ∈ Dgrp b x, FieldOn 3 d (Jpart 3 (Ipart 3 L b) a)) :
    ∃ y : G, y ∈ B ∧ y ∈ Ipart 3 L b ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ IsCentralIn 3 y (Ipart 3 L b) ∧
      IsCentralIn 3 y L ∧ IsCentralIn 3 y (Jpart 3 (Ipart 3 L b) a) := by
  obtain ⟨y, hyB, hyI, hy3, hy1, hyIc⟩ := beta_y_I hc hin h hU
  obtain ⟨d, hdD, hdf⟩ := hfield
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hb3 : b ^ 3 = 1 := (B_el h).2 b h.mem
  have hd3 : d ^ 3 = 1 := (B_el h).2 d (hDB hdD)
  refine ⟨y, hyB, hyI, hy3, hy1, hyIc, ?_, ?_⟩
  · exact hin.i307.two (cx x) L b y (sstar_triple h.star).2.2 (psimple_L_isU48 hc h hU)
      (fieldOn_b_U hc hin.l105 h hU) hb3 hyIc
  · refine hin.i307.two (cx a) _ d y hsingle hJ hdf hd3 ?_
    rw [Ipart_Ja_eq hc hin.l105 h hU ha hax hJ hsingle hdD hdf]
    exact hyIc

theorem beta_y2 (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (hax : a ∉ Subgroup.zpowers x)
    (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hfield : ∃ d ∈ Dgrp b x, FieldOn 3 d (Jpart 3 (Ipart 3 L b) a)) {y : G} (hyB : y ∈ B)
    (hyI : y ∈ Ipart 3 L b) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hyIc : IsCentralIn 3 y (Ipart 3 L b))
    (hyL : IsCentralIn 3 y L) (hyJ : IsCentralIn 3 y (Jpart 3 (Ipart 3 L b) a)) :
    GLAPComponent 3 (L ⊓ cx y) (layerC 3 L y) ∧ catalogIs (PSimple 3 (layerC 3 L y)) S9.isU3eight ∧
      GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx y) (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) ∧
      catalogIs (PSimple 3 (layerC 3 (Jpart 3 (Ipart 3 L b) a) y)) S9.isU3eight ∧
      ∃ Q : Subgroup G, Q ≤ layerC 3 L y ⊓ layerC 3 (Jpart 3 (Ipart 3 L b) a) y ∧
        (∃ g ∈ Q, ∃ g' ∈ Q, g * g' ≠ g' * g) ∧ GLAPPrimeCoreOf 3 Q = ⊥ := by
  have hL := hin.u48c3.1 (cx x) L y (sstar_triple h.star).2.2 (psimple_L_isU48 hc h hU) hy3 hy1 hyL
  have hJc := hin.u48c3.1 (cx a) (Jpart 3 (Ipart 3 L b) a) y hsingle hJ hy3 hy1 hyJ
  refine ⟨hL.1, hL.2, hJc.1, hJc.2, ?_⟩
  obtain ⟨d, hdD, hdf⟩ := hfield
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have hb3 : b ^ 3 = 1 := (B_el h).2 b h.mem
  have hd3 : d ^ 3 = 1 := (B_el h).2 d (hDB hdD)
  exact hin.su32 (cx x) (cx a) L (Jpart 3 (Ipart 3 L b) a) b d y (sstar_triple h.star).2.2 hsingle
    (psimple_L_isU48 hc h hU) hJ hU.field hdf hb3 hd3
    (Ipart_Ja_eq hc hin.l105 h hU ha hax hJ hsingle hdD hdf).symm hyI hy3 hy1 hyIc hyL hyJ

theorem Ky_single_gen (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {z y : G} {M : Subgroup G}
    (hBmax : GLAIsBmax 3 B) (hzB : z ∈ B) (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hM : GLAPComponent 3 (cx z) M) (hBM : B ≤ Subgroup.normalizer (M : Set G))
    (hMt : catalogIs (PSimple 3 M) S9.isU4eight)
    (hKzy : GLAPComponent 3 (M ⊓ cx y) (layerC 3 M y))
    (hKzyt : catalogIs (PSimple 3 (layerC 3 M y)) S9.isU3eight) :
    GLAPComponent 3 (cx y) (closureIn (layerC 3 M y) (GLAPLayer 3 (cx y))) ∧
      GLAPComponent 3 (closureIn (layerC 3 M y) (GLAPLayer 3 (cx y)) ⊓ cx z) (layerC 3 M y) := by
  have hp : Nat.Prime 3 := by norm_num
  have hzE : z ∈ Dgrp y z := Subgroup.subset_closure (by simp)
  have hCyz : cx y ⊓ cx z ≤ Subgroup.centralizer ((Dgrp y z : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hEg : Dgrp y z ≤ cx g := (Subgroup.closure_le (cx g)).2 (by
      intro k hk
      rcases hk with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hg.1).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hEg he)
  have hyE : y ∈ Dgrp y z := Subgroup.subset_closure (by simp)
  have hMEq : M ⊓ Subgroup.centralizer ((Dgrp y z : Subgroup G) : Set G) = M ⊓ cx y := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hg.2 y hyE).symm
    · intro g hg
      exact ⟨hg.1, hCyz ⟨hg.2, hM.1 hg.1⟩⟩
  have hKzyE : GLAPComponent 3 (M ⊓ Subgroup.centralizer ((Dgrp y z : Subgroup G) : Set G))
      (layerC 3 M y) := by
    rw [hMEq]
    exact hKzy
  have hJE : GLAPComponent 3 (Subgroup.centralizer ((Dgrp y z : Subgroup G) : Set G))
      (layerC 3 M y) :=
    S9.glaPComponent_centralizer hp hM hzE hKzyE
  refine ⟨?_, ?_⟩
  ·
    have hBel : IsElemAbelian 3 B := hBmax.1
    have hBy : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
    have hK : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
    have hrank : 3 ^ GLATwoLocalRank 3 ↥(cx y) ≤ Nat.card ↥B := by
      rw [hBmax.2.1]
      exact Nat.pow_le_pow_right (by norm_num)
        (glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y))
    have hcsz : Subgroup.centralizer ((Dgrp y z : Subgroup G) : Set G) =
        cx y ⊓ cs (Subgroup.zpowers z) := by
      apply le_antisymm
      · intro g hg
        refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun e he => ?_⟩
        · exact Subgroup.mem_centralizer_singleton_iff.2
            (Subgroup.mem_centralizer_iff.1 hg y hyE).symm
        · exact Subgroup.mem_centralizer_iff.1 hg e (Subgroup.zpowers_le.2 hzE he)
      · intro g hg
        obtain ⟨hgy, hgz⟩ := Subgroup.mem_inf.1 hg
        exact hCyz ⟨hgy, Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hgz z (Subgroup.mem_zpowers z)).symm⟩
    have hJcomp : GLAPComponent 3 (cx y ⊓ cs (Subgroup.zpowers z)) (layerC 3 M y) := by
      rw [← hcsz]
      exact hJE
    have hBJ : B ≤ Subgroup.normalizer ((layerC 3 M y : Subgroup G) : Set G) := by
      intro u hu
      refine mem_normalizer_glaPLayer ?_
      have hcomm' : Commute u y := isElemAbelian_commute hBel hu hyB
      have key : ∀ v ∈ B, Commute v y → ∀ l ∈ M ⊓ cx y, v * l * v⁻¹ ∈ M ⊓ cx y := by
        intro v hv hvy l hl
        refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hBM hv) l).1 hl.1, ?_⟩
        exact Subgroup.mem_centralizer_singleton_iff.2
          ((hvy.mul_left (Subgroup.mem_centralizer_singleton_iff.1 hl.2)).mul_left hvy.inv_left)
      rw [Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        exact key u hu hcomm' l hl
      · intro hl
        have h1 := key u⁻¹ (B.inv_mem hu) hcomm'.inv_left _ hl
        have e : u⁻¹ * (u * l * u⁻¹) * u⁻¹⁻¹ = l := by group
        rw [e] at h1
        exact h1
    obtain ⟨K', hK'comp, hJK', -⟩ := hin.l105.l103.single38 (cx y) z B
      (layerC 3 M y) hK hzB hBy hBel hrank hJcomp hBJ hKzyt
    rw [closureIn_layer_eq_of_component hp hK'comp hKzy hJK']
    exact hK'comp
  · have hcy : closureIn (layerC 3 M y) (GLAPLayer 3 (cx y)) ≤ cx y :=
      closureIn_le_of_le ((layer_le 3 _).trans inf_le_right) (layer_le 3 _)
    have hKz : layerC 3 M y ≤ cx z := (layer_le 3 _).trans (inf_le_left.trans hM.1)
    exact glaPComponent_of_le hp hJE (le_inf (le_closureIn_self _ _) hKz)
      (fun g hg => hCyz ⟨hcy hg.1, hg.2⟩)

theorem beta_Ky_single (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G}
    {b : G} (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x)
    (hax : a ∉ Subgroup.zpowers x) (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a)) {y : G} (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hKxy : GLAPComponent 3 (L ⊓ cx y) (layerC 3 L y)) (hKxyt : catalogIs (PSimple 3 (layerC 3 L y)) S9.isU3eight)
    (hKay : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx y) (layerC 3 (Jpart 3 (Ipart 3 L b) a) y))
    (hKayt : catalogIs (PSimple 3 (layerC 3 (Jpart 3 (Ipart 3 L b) a) y)) S9.isU3eight) :
    GLAPComponent 3 (cx y) (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y))) ∧
      GLAPComponent 3 (cx y) (closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y))) ∧
      GLAPComponent 3 (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) ⊓ cx x) (layerC 3 L y) ∧
      GLAPComponent 3 (closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y)) ⊓ cx a)
        (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) := by
  have hS := sstar_triple h.star
  have h1 := Ky_single_gen hc hin hS.1 hS.2.1.1 hyB hy1 hS.2.2 (sstar_norm h.star) (psimple_L_isU48 hc h hU)
    hKxy hKxyt
  have h2 := Ky_single_gen hc hin hS.1 ((dgrp_facts hc h).1 ha) hyB hy1 hsingle (B_le_N_J hc h ha).2 hJ hKay hKayt
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

private theorem beta_inf_core_le {H C : Subgroup G} (hHC : H ≤ C) :
    H ⊓ GLAPPrimeCoreOf 3 C ≤ GLAPPrimeCoreOf 3 H := by
  set K : Subgroup G := H ⊓ GLAPPrimeCoreOf 3 C with hK
  have hnorm : (K.subgroupOf H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnH, hnO⟩ := hn
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem h.2 hnH) (H.inv_mem h.2)
      simpa using this
    · have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 C (hHC h.2)) (n : G)).1 hnO
      simpa using this
  have hcop : Nat.Coprime 3 (Nat.card (K.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ≤ H)).toEquiv]
    refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right : K ≤ _)) ?_
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (not_dvd_card_glaPPrimeCoreOf Nat.prime_three C)
  have hle : K.subgroupOf H ≤ GLAPPrimeCore 3 ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx), rfl⟩

theorem beta_Ky_eq (hc : S10Ctx G 3) {L : Subgroup G} {b : G} {a : G}
    {y : G} (hKy : GLAPComponent 3 (cx y) (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y))))
    (hKy' : GLAPComponent 3 (cx y) (closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y))))
    (hLle : layerC 3 L y ≤ closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)))
    (hJle : layerC 3 (Jpart 3 (Ipart 3 L b) a) y ≤
      closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y)))
    (hQ : ∃ Q : Subgroup G, Q ≤ layerC 3 L y ⊓ layerC 3 (Jpart 3 (Ipart 3 L b) a) y ∧
      (∃ g ∈ Q, ∃ g' ∈ Q, g * g' ≠ g' * g) ∧ GLAPPrimeCoreOf 3 Q = ⊥) :
    closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) =
      closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y)) := by
  by_contra hne
  obtain ⟨Q, hQle, ⟨g, hg, g', hg', hgg⟩, hQ1⟩ := hQ
  have hcomm := CFSG.HardMathSupport.Solomon.LocalBalance.commutator_le_gLAPPrimeCore_of_ne
    Nat.prime_three hKy hKy' hne
  have hQC : Q ≤ cx y := hQle.trans (inf_le_left.trans ((layer_le 3 _).trans inf_le_right))
  have hmem : ⁅g, g'⁆ ∈ GLAPPrimeCoreOf 3 (cx y) :=
    hcomm (Subgroup.commutator_mem_commutator (hLle (hQle hg).1) (hJle (hQle hg').2))
  have hmemQ : ⁅g, g'⁆ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hg hg') (Q.inv_mem hg)) (Q.inv_mem hg')
  have hcoreQ : ⁅g, g'⁆ ∈ GLAPPrimeCoreOf 3 Q :=
    beta_inf_core_le hQC ⟨hmemQ, hmem⟩
  rw [hQ1, Subgroup.mem_bot] at hcoreQ
  exact hgg (commutatorElement_eq_one_iff_mul_comm.1 hcoreQ)

theorem beta_Ky (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (hax : a ∉ Subgroup.zpowers x)
    (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a)) {y : G} (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hKxy : GLAPComponent 3 (L ⊓ cx y) (layerC 3 L y)) (hKxyt : catalogIs (PSimple 3 (layerC 3 L y)) S9.isU3eight)
    (hKay : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx y) (layerC 3 (Jpart 3 (Ipart 3 L b) a) y))
    (hKayt : catalogIs (PSimple 3 (layerC 3 (Jpart 3 (Ipart 3 L b) a) y)) S9.isU3eight)
    (hQ : ∃ Q : Subgroup G, Q ≤ layerC 3 L y ⊓ layerC 3 (Jpart 3 (Ipart 3 L b) a) y ∧
      (∃ g ∈ Q, ∃ g' ∈ Q, g * g' ≠ g' * g) ∧ GLAPPrimeCoreOf 3 Q = ⊥) :
    GLAPComponent 3 (cx y) (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y))) ∧
      closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) =
        closureIn (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) (GLAPLayer 3 (cx y)) ∧
      GLAPComponent 3 (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) ⊓ cx x) (layerC 3 L y) ∧
      GLAPComponent 3 (closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) ⊓ cx a)
        (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) := by
  obtain ⟨h1, h2, h3, h4⟩ := beta_Ky_single hc hin h hU ha hax hJ hsingle hyB hy1 hKxy hKxyt hKay hKayt
  have heq := beta_Ky_eq hc h1 h2 (le_closureIn_self _ _) (le_closureIn_self _ _) hQ
  refine ⟨h1, heq, h3, ?_⟩
  rw [heq]
  exact h4

theorem beta_field (hc : S10Ctx G 3) (hin : BetaInputs G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg 3 B x L b) (hU : CaseU G 3 B x L b) {a : G} (ha : a ∈ Dgrp b x) (hax : a ∉ Subgroup.zpowers x)
    (hJ : catalogIs (PSimple 3 (Jpart 3 (Ipart 3 L b) a)) S9.isU4eight)
    (hsingle : GLAPComponent 3 (cx a) (Jpart 3 (Ipart 3 L b) a))
    (hfield : ∃ d ∈ Dgrp b x, FieldOn 3 d (Jpart 3 (Ipart 3 L b) a)) {y : G} (hyB : y ∈ B) (hy3 : y ^ 3 = 1)
    (hy1 : y ≠ 1) (hyL : IsCentralIn 3 y L) (hyJ : IsCentralIn 3 y (Jpart 3 (Ipart 3 L b) a))
    (hKxy : GLAPComponent 3 (L ⊓ cx y) (layerC 3 L y)) (hKxyt : catalogIs (PSimple 3 (layerC 3 L y)) S9.isU3eight)
    (hKay : GLAPComponent 3 (Jpart 3 (Ipart 3 L b) a ⊓ cx y) (layerC 3 (Jpart 3 (Ipart 3 L b) a) y))
    (hKayt : catalogIs (PSimple 3 (layerC 3 (Jpart 3 (Ipart 3 L b) a) y)) S9.isU3eight) :
    FieldOn 3 a (layerC 3 L y) ∧ FieldOn 3 x (layerC 3 (Jpart 3 (Ipart 3 L b) a) y) := by
  obtain ⟨hDB, hDel, hDc⟩ := dgrp_facts hc h
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := B_el h
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have haB : a ∈ B := hDB ha
  have ha3 : a ^ 3 = 1 := hBel.2 a haB
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ Subgroup.one_mem _)
  have hxD : x ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbD : b ∈ Dgrp b x := Subgroup.subset_closure (Set.mem_insert b {x})
  have haD : a ∈ Dgrp b x := ha
  have hacmL : CentMod 3 L x := centMod_zpowers_of_le hS.2.2.1 (Subgroup.mem_zpowers x)
  have hfa : FieldOn 3 a L :=
    fieldOn_of_mem_D hin.fieldpow Nat.prime_three hDel hDc hxD hx1 hbD ha h.not_mem hax hacmL hU.field
  obtain ⟨d, hdD, hdf⟩ := hfield
  set J := Jpart 3 (Ipart 3 L b) a with hJdef
  have haux := hin.l105.l103.aut
  have hJchev : IsChevSimple 2 (PSimple 3 J) := casebeta_chev2_u4eight hJ
  have hJa : J ≤ cx a := Jpart_le_cx h ha
  have hacmJ : CentMod 3 J a := centMod_zpowers_of_le hJa (Subgroup.mem_zpowers a)
  have hda : d ∉ Subgroup.zpowers a := by
    intro hmem
    have hacs : a ∈ cs J := Subgroup.mem_centralizer_iff.2 fun j hj =>
      Subgroup.mem_centralizer_singleton_iff.1 (hJa hj)
    have hdcs : d ∈ cs J := (Subgroup.zpowers_le.2 hacs) hmem
    have hcm : CentMod 3 J d := centMod_of_mem_centralizer hdcs
    have hinn : InducesInnerMod 3 J d := inducesInnerMod_of_centMod hcm
    have hnd : InnDiagOn 3 (Subgroup.zpowers d) J :=
      haux.inner_innDiag (cx a) J d hsingle hJchev hcm.1 hinn
    exact (haux.field_nonInnDiag (cx a) J d hsingle hJchev hdf).2 hnd
  have hxa' : x ∉ Subgroup.zpowers a := not_mem_zpowers_symm hx3 hx1 ha3 ha1 hax
  have hfx : FieldOn 3 x J :=
    fieldOn_of_mem_D hin.fieldpow Nat.prime_three hDel hDc haD ha1 hdD hxD hda hxa' hacmJ hdf
  exact ⟨hin.fieldu3 (cx x) L a y hS.2.2 (psimple_L_isU48 hc h hU) hfa hy3 hy1 hyL
      (isElemAbelian_commute hBel haB hyB),
    hin.fieldu3 (cx a) J x y hsingle hJ hfx hy3 hy1 hyJ (isElemAbelian_commute hBel hxB hyB)⟩

theorem caseBeta (hc : S10Ctx G p) (hin : BetaInputs G p) {B : Subgroup G} {x : G} {L : Subgroup G} {b : G}
    (h : Cfg p B x L b) (hd5 : dLevel G p = 5) (hβ : CaseBeta G p B x L b) : False := by
  have hU := hβ.1
  have hcase : CaseAB G p B x L b := Or.inr hβ
  have c := lemma105 hc hin.l105 h hd5 hcase
  obtain ⟨a, haD, hax, hlt, -⟩ := lemma107 hc hin.l105 h hd5 hcase c
  have ha1 : a ≠ 1 := fun h1 => hax (h1 ▸ Subgroup.one_mem _)
  have hH := h104_of_concl105 c haD ha1 hlt
  have hJ := beta_type hc h hU hH (hβ.2 a haD ha1)
  have hsingle := (c.single a haD ha1).1
  have hfield := lemma104_beta_field hc hin.l105.l104 h hU hH (hβ.2 a haD ha1)
  have hp3 := hU.p3
  subst hp3
  have hS := sstar_triple h.star
  have hBel : IsElemAbelian 3 B := B_el h
  obtain ⟨hDB, -, -⟩ := dgrp_facts hc h
  have haB : a ∈ B := hDB haD
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have ha3 : a ^ 3 = 1 := hBel.2 a haB
  obtain ⟨y, hyB, hyI, hy3, hy1, hyIc, hyL, hyJ⟩ := beta_y1 hc hin h hU haD hax hJ hsingle hfield
  obtain ⟨hKxy, hKxyt, hKay, hKayt, hQ⟩ :=
    beta_y2 hc hin h hU haD hax hJ hsingle hfield hyB hyI hy3 hy1 hyIc hyL hyJ
  obtain ⟨hKy, -, hKyx, hKya⟩ :=
    beta_Ky hc hin h hU haD hax hJ hsingle hyB hy1 hKxy hKxyt hKay hKayt hQ
  obtain ⟨hfa, hfx⟩ := beta_field hc hin h hU haD hax hJ hsingle hfield hyB hy3 hy1 hyL hyJ hKxy hKxyt hKay hKayt
  set Ky := closureIn (layerC 3 L y) (GLAPLayer 3 (cx y)) with hKydef
  set Kxy := layerC 3 L y with hKxydef
  set Kay := layerC 3 (Jpart 3 (Ipart 3 L b) a) y with hKaydef
  have hKyK : CFSG.Open.IsKGroup ↥(cx y) := S8.isKGroup_cx hc.ctx hy1
  have hBy : B ≤ cx y := isElemAbelian_le_centralizer hBel hyB
  have hxy : x ∈ cx y := hBy hxB
  have hay : a ∈ cx y := hBy haB
  have hxa : x * a = a * x := isElemAbelian_commute hBel hxB haB
  have hxa' : x ∉ Subgroup.zpowers a := not_mem_zpowers_symm hx3 hx1 ha3 ha1 hax
  have hrk : GLATwoLocalRank 3 ↥(Subgroup.centralizer ({y} : Set G)) ≤ GLATwoLocalRank 3 G :=
    glaTwoLocalRank_subgroup_le (by norm_num : 1 < 3) (cx y)
  have hchev1 : IsChevSimple 2 (PSimple 3 Kxy) := isChevTwo_of_isU3eight hKxyt
  have hchev2 : IsChevSimple 2 (PSimple 3 Kay) := isChevTwo_of_isU3eight hKayt
  have hhyp : I158Base 3 (cx y) Ky B x a Kxy Kay :=
    ⟨hKyK, hKy, hBel, hBy, by
      rw [hS.1.2.1]
      exact Nat.pow_le_pow_right (by norm_num) hrk, hxB, haB, hx1, ha1, hKyx, hchev1, hKya, hchev2⟩
  obtain ⟨hinx, hina⟩ := hin.i158.inn 3 Nat.prime_three (by norm_num) _ _ _ _ _ _ _ hhyp hfx hfa hKxyt hKayt
  have hKxyZ : Subgroup.center (PQuot 3 Kxy) ≠ ⊥ :=
    hin.u48c3.2 (cx x) L y (sstar_triple h.star).2.2 (psimple_L_isU48 hc h hU) hy3 hy1 hyL
  have h5 := hin.i141 Ky Kxy Kay x a y hKyK hKy hx3 ha3 hxa hxa' hxy hay hKyx hKxyt hKxyZ hKya hKayt hfa hfx
    hinx hina
  have h4 := hU.rank
  omega

end S10

end CFSG.LocalAnalysis.GLTheoremA
