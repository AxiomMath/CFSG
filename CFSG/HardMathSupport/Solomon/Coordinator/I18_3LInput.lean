module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem i183l_comp_inf {x y : G}
    {J : Subgroup G}
    (hJ : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
      Subgroup.centralizer ({y} : Set G))) J) :
    GLAPComponent 3 (GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
        Subgroup.centralizer ({y} : Set G)) J ∧
      GLAPComponent 3 (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set W : Subgroup G := GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)) ⊓
    Subgroup.centralizer ({y} : Set G) with hW
  have hW1 : GLAPLayer 3 W ≤ W := i183_glaPLayer_le 3 W
  have hWn : W ≤ Subgroup.normalizer ((GLAPLayer 3 W : Subgroup G) : Set G) :=
    i183v_le_normalizer_glaPLayer 3 W
  have hsnW : IsSubnormal J W :=
    isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hW1
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hW1).2 hWn))
  have hJW : GLAPComponent 3 W J := LocalBalance.Lemma512Ns.glaPComponent_up hp hJ hW1 hsnW
  have hH0 : W ≤ Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans (i183_glaPLayer_le 3 _))
  have hnorm : Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer ((W : Subgroup G) : Set G) := fun h hh =>
    i183_mem_normalizer_inf (i183v_le_normalizer_glaPLayer 3 _ hh.2) (Subgroup.le_normalizer hh.1)
  have hsn : IsSubnormal J (Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isSubnormal_trans' hJW.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hH0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hH0).2 hnorm))
  exact ⟨hJW, i183v_comp_up hp hJW hH0 hsn⟩

end Helpers

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns in
theorem lemma512_input18_3_of_input14_5 (hS : CatalogueRelativeB.CatalogueSchreier)
    (i145 : LocalBalance.Lemma27Ns.Input14_5) : LocalBalance.Lemma512Ns.Input18_3 := by
  intro G _ _ _ hnab hKP u v hu3 hv3 huv J hJ
  have hp : Nat.Prime 3 := Nat.prime_three
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have hv3' : v ^ 3 = 1 := by rw [← hv3]; exact pow_orderOf_eq_one v
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu3; omega
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv3; omega
  have hKP' : CFSG.IsKProper G :=
    CatalogueKProper.isKProper_of_kProper (CatalogueKProper.open_isKProper_iff.1 hKP)
  obtain ⟨hJW, hJ'⟩ := i183l_comp_inf (x := u) (y := v) hJ
  have h12 := input18_3_12_of_schreier hS G hKP' u v hu1 hv1 hu3' hv3' huv J hJW
  refine ⟨?_, fun hu => ?_⟩
  · rcases h12 with ⟨hc, hn⟩ | ⟨M, hM, hM1, hM2, hK, -⟩
    · exact Or.inl ⟨_, hc, rfl, mem_normalizer_iff_gLBConj_eq.1 hn⟩
    · right
      have hu_norm : u ∈ Subgroup.normalizer
          ((Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) :=
        Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 huv)
      have hcomp : ∀ L, GLAPComponent 3 (Subgroup.centralizer ({v} : Set G)) L →
          GLAPComponent 3 (Subgroup.centralizer ({v} : Set G)) (GLBConj u L) := fun L hL => by
        have := glaPComponent_gLBConj hL u
        rwa [gLBConj_eq_of_mem_normalizer hu_norm] at this
      have hu3'' : u * (u * u) = 1 := by
        rw [← pow_three]
        exact hu3'
      have h3 : GLBConj u (GLBConj u (GLBConj u M)) = M := by
        rw [gLBConj_gLBConj, gLBConj_gLBConj, hu3'', gLBConj_one]
      refine ⟨M, GLBConj u M, GLBConj u (GLBConj u M), hM, hcomp M hM, hcomp _ (hcomp M hM),
        fun h => hM1 h.symm, ?_, hM2, rfl, rfl, h3, hK⟩
      intro h
      apply hM2
      have := congrArg (GLBConj u) h
      rwa [h3] at this
  · have hCne : Subgroup.centralizer ({v} : Set G) ≠ ⊤ := by
      intro htop
      have hvc : v ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have : g ∈ Subgroup.centralizer ({v} : Set G) := htop ▸ Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.1 this
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact hv1 (Subgroup.mem_bot.1 (h ▸ hvc))
      · obtain ⟨a, b, hab⟩ := hnab
        exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    set Cv : Subgroup G := Subgroup.centralizer ({v} : Set G) with hCv
    set u' : ↥Cv := ⟨u, hu⟩ with hu'
    set A_H : Subgroup ↥Cv := Subgroup.centralizer ({u'} : Set ↥Cv) with hAH
    have hAmap : A_H.map Cv.subtype = Cv ⊓ Subgroup.centralizer ({u} : Set G) := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx))⟩
      · rintro ⟨hgJ, hgC⟩
        exact ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
    obtain ⟨J', hJ'c, hJ'J⟩ := exists_glaPComponent_map_eq hp Cv.subtype (s1t_ker_sub Cv A_H)
      (K' := J) (by rw [hAmap]; exact hJ')
    set π : ↥Cv →* (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Cv) with hπ
    have hu'3 : u' ^ 3 = 1 := Subtype.ext (by simpa using hu3')
    have hπu3 : π u' ^ 3 = 1 := by rw [← map_pow, hu'3, map_one]
    have hAπ : A_H.map π = Subgroup.centralizer ({π u'} : Set (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv)) :=
      s1t_map_cent hu'3
    have hKH : CFSG.Open.IsKGroup ↥Cv := isKGroup_of_isKProper hKP hCne
    have hKY : CFSG.Open.IsKGroup (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv) := s1t_isKGroup_quotient hKH _
    have hcoreY : GLAPPrimeCore 3 (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
    have hcomm := i145 (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv) (s1t_isKGroup_of_open hKY) hcoreY (π u') hπu3
    have hc : GLAPComponent 3 (Subgroup.centralizer ({π u'} : Set (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv)))
        (J'.map π) := hAπ ▸ glaPComponent_map hp π (s1t_ker_pi A_H) hJ'c
    have hq := s1t_isQuasisimple hc hcomm
    have hbar : barX 3 Cv J = J'.map π := by
      have hsub : (J'.map Cv.subtype).subgroupOf Cv = J' :=
        Subgroup.comap_map_eq_self_of_injective Cv.subtype_injective J'
      show (J.subgroupOf Cv).map π = J'.map π
      rw [← hJ'J, hsub]
    have hJK : J ≤ LocalBalance.Lemma512Ns.conjHull v J :=
      le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (gLBConj_one J).ge
    have hle : J'.map π ≤ barX 3 Cv (LocalBalance.Lemma512Ns.conjHull v J) ⊓
        Subgroup.centralizer ({π u'} : Set (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv)) :=
      le_inf (by rw [← hbar]; exact barX_mono 3 hJK) hc.1
    have hsnW := isSubnormal_of_le_of_le hc.2.1 hle inf_le_right
    have hcompW : IsComponentOf (J'.map π) (barX 3 Cv (LocalBalance.Lemma512Ns.conjHull v J) ⊓
        Subgroup.centralizer ({π u'} : Set (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv))) := ⟨hle, hsnW, hq⟩
    have hle2 := i25_le_layer hcompW
    rw [hbar]
    exact ⟨hle2, isSubnormal_of_le_of_le hsnW hle2 (i25_layer_le _), hq⟩

open CFSG.HardMathSupport.Solomon.LocalBalance in
theorem lemma512_input18_3_holds


    (i145 : Lemma27Ns.Input14_5) : Lemma512Ns.Input18_3 :=
  lemma512_input18_3_of_input14_5 CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds i145

end CFSG.HardMathSupport.Solomon.Coordinator
