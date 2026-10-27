module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H2017LLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Root8
public import CFSG.LocalAnalysis.GLTheoremA.S6.I2013
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Alt

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.I2017
open CFSG.LocalAnalysis.GLTheoremA.H2017L
open scoped commutatorElement

theorem fb_contradiction {Q : Type} [Group Q] [Finite Q] {Ibar Rbar : Subgroup Q}
    (hI : Nonempty (↥Ibar ≃* ↥(alternatingGroup (Fin 7)))) (hR2 : IsPGroup 2 Rbar)
    (hIN : Ibar ≤ Subgroup.normalizer (Rbar : Set Q))
    (hRne : ¬ Ibar ≤ Subgroup.centralizer (Rbar : Set Q))
    (hB' : ∀ (T : Subgroup (Q ⧸ Subgroup.center Q)), IsPGroup 2 T → T ≠ ⊥ →
      ∀ H : Subgroup (Q ⧸ Subgroup.center Q), H ≤ Subgroup.normalizer (T : Set (Q ⧸ Subgroup.center Q)) →
        ¬ Nonempty (↥H ≃* ↥(alternatingGroup (Fin 7)))) : False := by
  classical
  obtain ⟨eI⟩ := hI
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Ibar := eI.isSimpleGroup
  set f : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hf
  set φ : ↥Ibar →* Q ⧸ Subgroup.center Q := f.comp Ibar.subtype with hφ
  have hcard7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hbot | htop
  ·
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have ha' : a ∈ φ.ker := ha
      rw [hbot] at ha'
      exact Subgroup.mem_bot.1 ha'
    have hHiso : Nonempty (↥φ.range ≃* ↥(alternatingGroup (Fin 7))) :=
      ⟨(MonoidHom.ofInjective hinj).symm.trans eI⟩
    set T : Subgroup (Q ⧸ Subgroup.center Q) := Rbar.map f with hT
    have hT2 : IsPGroup 2 T := IsPGroup.map hR2 f
    have hTne : T ≠ ⊥ := by
      intro hTbot
      apply hRne
      have hRZ : Rbar ≤ Subgroup.center Q := by
        intro r hr
        have hr' : f r ∈ T := Subgroup.mem_map_of_mem f hr
        rw [hTbot, Subgroup.mem_bot] at hr'
        have hrker : r ∈ f.ker := hr'
        rw [QuotientGroup.ker_mk'] at hrker
        exact hrker
      intro i hi
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact ((Subgroup.mem_center_iff.1 (hRZ hr)) i).symm
    have hHle : φ.range ≤ Subgroup.normalizer (T : Set (Q ⧸ Subgroup.center Q)) := by
      rintro _ ⟨a, rfl⟩
      exact (Subgroup.le_normalizer_map f) (Subgroup.mem_map_of_mem f (hIN a.2))
    exact hB' T hT2 hTne φ.range hHle hHiso
  ·
    exfalso
    have hcomm : IsMulCommutative ↥Ibar := by
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : (a : Q) ∈ Subgroup.center Q := by
        have : a ∈ φ.ker := by rw [htop]; exact Subgroup.mem_top a
        exact (QuotientGroup.eq_one_iff (a : Q)).1 this
      exact ((Subgroup.mem_center_iff.1 ha) (b : Q)).symm
    have hprime : Nat.Prime (Nat.card ↥Ibar) := Group.is_simple_iff_prime_card.1 inferInstance
    have hIcard : Nat.card ↥Ibar = 2520 := by
      rw [Nat.card_congr eI.toEquiv, hcard7]
    rw [hIcard] at hprime
    norm_num at hprime

theorem i2017Lie_of_facts {G : Type} [Group G] [Finite G] (hA : I2017LieClassification) (hB : I2017LieNoA7)
    (hC : I2017LieRank) (hZ1 : I2017LieCenterL62) (hZ2 : I2017LieRankCenter) : I2017LieAt G := by
  intro X K D J I R hX hK hDN hD hD9 hdz hE hJLay hJC hJA hIJ hIA hRK hR hIDR hnc hLie
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (p := 3) (n := 2) (by rw [hD9]; norm_num)
  obtain ⟨d, hd, hd1, hdC⟩ := hdz
  have hd3 : d ^ 3 = 1 := hD.2 d hd
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hIN : I ≤ Subgroup.normalizer (R : Set G) := le_trans le_sup_left hIDR
  have hIRbar : imageMod 3 K I ≤ Subgroup.normalizer (imageMod 3 K R : Set (PQuot 3 K)) :=
    S8.L83.imageMod_le_normalizer hIN
  have hRbar : IsPGroup 2 (imageMod 3 K R) := S8.L83.isPGroup_imageMod hR
  by_cases hall : ∀ x ∈ D, CentMod 3 K x
  ·
    have hfix1 : ∀ q : PQuot 3 K, barAut 3 K ⟨1, Subgroup.one_mem _⟩ q = q →
        ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q := by
      intro q _ e he
      rw [(barAut_eq_one_iff_centMod (hDN he)).2 (hall e he), MulAut.one_apply]
    have hJt := i2017_component_fix hDN hDp D.one_mem hfix1 hJC
    have h1 : (⟨(1 : G), Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 := rfl
    rw [h1, map_one, up7a8_fixSubgroup_one] at hJt
    have hJtop : imageMod 3 K J = ⊤ := top_of_component_top hq hJt
    obtain ⟨eJ⟩ := hJA
    let eK : PQuot 3 K ≃* ↥(alternatingGroup (Fin 8)) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hJtop).symm.trans eJ)
    have hroot : IsRootAlt eK (⊤ : Subgroup (PQuot 3 K)) 8 := isRootAlt_top (by norm_num) eK
    have hI7 : IsRootAlt eK (imageMod 3 K I) 7 :=
      root7_of_le_root8 eK hroot le_top (by
        obtain ⟨eI⟩ := hIA
        exact ⟨eI⟩)
    exact (hnc (i2013At_holds (PQuot 3 K) 8 7 eK _ (by norm_num) (by norm_num) hI7 _ hRbar hIRbar)).elim
  ·
    push Not at hall
    obtain ⟨x, hx, hxC⟩ := hall
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hDN hx
    have hα3 : (barAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have h3 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hD.2 x hx)
      rw [h3, map_one]
    have hα1 : barAut 3 K ⟨x, hxN⟩ ≠ 1 := fun h => hxC ((barAut_eq_one_iff_centMod hxN).1 h)
    have hfixD : ∀ q : PQuot 3 K, barAut 3 K ⟨x, hxN⟩ q = q →
        ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q :=
      fun q hq' e he => fix_all_of_fix_x hDN hD hD9 hd hx hdC hd1 hxC hq' e he
    have hJt := i2017_component_fix hDN hDp hx hfixD hJC
    obtain ⟨eJ⟩ := hJA
    have hJ8 : IsAltPType 3 (imageMod 3 K J) 8 := isAltPType_of_mulEquiv_alt8 eJ
    obtain ⟨r, _, hcat⟩ := hLie
    obtain ⟨i, hi, ⟨eS⟩⟩ := hcat
    cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie dl =>
      have hcatA : catalogIs (PSimple 3 K) (onLie fun d' => d' = dl.1) :=
        ⟨TauCeti.CFSGIndex.lie dl, rfl, ⟨eS⟩⟩
      have hsh := hA (PQuot 3 K) hq (barAut 3 K ⟨x, hxN⟩) (imageMod 3 K J) hα3 hα1 hJt hJ8 dl.1 hcatA
      rcases hsh with hA8 | ⟨N, hN6, hNev, hNd⟩ | hD4 | ⟨k, hk5, hk⟩
      ·
        have hcatB : catalogIs (PSimple 3 K) (onLie I2017LieNoA7Shape) :=
          ⟨TauCeti.CFSGIndex.lie dl, Or.inl hA8, ⟨eS⟩⟩
        exact (fb_contradiction hIA hRbar hIRbar hnc (hB (PSimple 3 K) hcatB)).elim
      · by_cases hN : N = 6
        ·
          subst hN
          have hcatL : catalogIs (PSimple 3 K) (onLie fun d' => d' = .A 5 gfTwoPP) :=
            ⟨TauCeti.CFSGIndex.lie dl, hNd, ⟨eS⟩⟩
          exact ⟨hcatL, hZ1 (PQuot 3 K) hq hcatL⟩
        ·
          obtain ⟨m, hm⟩ := hNev
          have hN8 : 8 ≤ N := by omega
          have hRshape : I2017LieRankShape dl.1 := Or.inl ⟨N, hN8, ⟨m, hm⟩, hNd⟩
          have hcatR : catalogIs (PSimple 3 K) (onLie I2017LieRankShape) :=
            ⟨TauCeti.CFSGIndex.lie dl, hRshape, ⟨eS⟩⟩
          obtain ⟨E, hEfix, hEab, hEcard⟩ :=
            hC (PQuot 3 K) hq (barAut 3 K ⟨x, hxN⟩) (imageMod 3 K J) hα3 hα1 hJt hJ8 hcatR
          have hEfixD : ∀ q ∈ E, ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q :=
            fun q hq e he => hfixD q (hEfix hq) e he
          obtain ⟨P, hPK, hPab, hPcard⟩ := exists_elemAb_lift hDN hDp hEab hEcard hEfixD
          have hdK : d ∉ K := not_mem_of_centMod hDN hd hd1 hd3 hdC (hZ2 (PQuot 3 K) hq hcatR)
          obtain ⟨P', hP'le, hP'ab, hP'card⟩ := exists_rank_five hD hd hd1 hdK hPK hPab hPcard
          have hbound := hE P' hP'le hP'ab
          rw [hP'card] at hbound
          norm_num at hbound
      ·
        have hcatB : catalogIs (PSimple 3 K) (onLie I2017LieNoA7Shape) :=
          ⟨TauCeti.CFSGIndex.lie dl, Or.inr hD4, ⟨eS⟩⟩
        exact (fb_contradiction hIA hRbar hIRbar hnc (hB (PSimple 3 K) hcatB)).elim
      ·
        have hRshape : I2017LieRankShape dl.1 := Or.inr ⟨k, hk5, hk⟩
        have hcatR : catalogIs (PSimple 3 K) (onLie I2017LieRankShape) :=
          ⟨TauCeti.CFSGIndex.lie dl, hRshape, ⟨eS⟩⟩
        obtain ⟨E, hEfix, hEab, hEcard⟩ :=
          hC (PQuot 3 K) hq (barAut 3 K ⟨x, hxN⟩) (imageMod 3 K J) hα3 hα1 hJt hJ8 hcatR
        have hEfixD : ∀ q ∈ E, ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q :=
          fun q hq e he => hfixD q (hEfix hq) e he
        obtain ⟨P, hPK, hPab, hPcard⟩ := exists_elemAb_lift hDN hDp hEab hEcard hEfixD
        have hdK : d ∉ K := not_mem_of_centMod hDN hd hd1 hd3 hdC (hZ2 (PQuot 3 K) hq hcatR)
        obtain ⟨P', hP'le, hP'ab, hP'card⟩ := exists_rank_five hD hd hd1 hdK hPK hPab hPcard
        have hbound := hE P' hP'le hP'ab
        rw [hP'card] at hbound
        norm_num at hbound

end CFSG.LocalAnalysis.GLTheoremA
