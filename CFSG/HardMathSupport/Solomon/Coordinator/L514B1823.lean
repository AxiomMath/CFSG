module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3VMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns in
theorem l514b_input18_3_23_of_input14_5 (hS : CatalogueRelativeB.CatalogueSchreier)
    (i145 : LocalBalance.Lemma27Ns.Input14_5) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Open.IsKProper G) {x y : G} (hx3 : orderOf x = 3)
    (hxy : x * y = y * x) (hyc : y ∉ Subgroup.center G) {J : Subgroup G}
    (hJ : GLAPComponent 3 (GLAPLayer 3 (Cs x) ⊓ Cs y) J) :
    GLAPComponent 3 (GLAPLayer 3 (ncl (GLAPLayer 3 (Cs y)) J ⊓ Cs x)) J ∧
      ∃ hx : x ∈ Cs y,
        IsComponentOf (barX 3 (Cs y) J)
          (barX 3 (Cs y) (ncl (GLAPLayer 3 (Cs y)) J) ⊓
            Subgroup.centralizer ({(QuotientGroup.mk ⟨x, hx⟩ :
              ↥(Cs y) ⧸ GLAPPrimeCore 3 ↥(Cs y))} : Set (↥(Cs y) ⧸ GLAPPrimeCore 3 ↥(Cs y)))) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hCne : Cs y ≠ ⊤ := by
    intro htop
    apply hyc
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Cs y := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.1 this
  have hxX : x ∈ Cs y := Subgroup.mem_centralizer_singleton_iff.2 hxy
  have hEX : Subgroup.zpowers x ≤ Cs y := Subgroup.zpowers_le.2 hxX
  have hE : IsElemAbelian 3 (Subgroup.zpowers x) := i183v_isElemAbelian_zpowers hx3'
  have hEp : IsPGroup 3 ↥(Subgroup.zpowers x) := isPGroup_of_isElemAbelian' hE
  have hcz : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = Cs x := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hH0 : GLAPLayer 3 (Cs x) ⊓ Cs y ≤ Cs y ⊓ Cs x :=
    le_inf inf_le_right (inf_le_left.trans (i183_glaPLayer_le 3 _))
  have hnorm : Cs y ⊓ Cs x ≤ Subgroup.normalizer ((GLAPLayer 3 (Cs x) ⊓ Cs y : Subgroup G) :
      Set G) := fun h hh =>
    i183_mem_normalizer_inf (i183v_le_normalizer_glaPLayer 3 _ hh.2) (Subgroup.le_normalizer hh.1)
  have hsn : IsSubnormal J (Cs y ⊓ Cs x) :=
    isSubnormal_trans' hJ.2.1 (CFSG.Quasithin.A3.subnormal_of_normal hH0
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hH0).2 hnorm))
  have hJ' : GLAPComponent 3 (Cs y ⊓ Cs x) J := i183v_comp_up hp hJ hH0 hsn
  have hJL : J ≤ GLAPLayer 3 (Cs y) := by
    refine (le_sSup hJ' : J ≤ GLAPLayer 3 (Cs y ⊓ Cs x)).trans ?_
    have hK : CFSG.Open.IsKGroup ↥(Cs y) := isKGroup_of_isKProper hKP hCne
    have := i183_glaPLayer_inf_centralizer_le hS hK hp hEX hEp
    rwa [hcz] at this
  have hJy : J ≤ Cs y := hJ'.1.trans inf_le_left
  have hJK : J ≤ ncl (GLAPLayer 3 (Cs y)) J :=
    le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (gLBConj_one J).ge
  refine ⟨?_, hxX, ?_⟩
  ·
    have hKy : ncl (GLAPLayer 3 (Cs y)) J ≤ Cs y := by
      refine iSup₂_le fun g hg z hz => ?_
      have hgC : g ∈ Cs y := i183_glaPLayer_le 3 _ hg
      have hzJ : g * z * g⁻¹ ∈ J := mem_gLBConj.1 hz
      have := mul_mem (mul_mem (inv_mem hgC) (hJy hzJ)) hgC
      simpa [mul_assoc] using this
    have hle : J ≤ ncl (GLAPLayer 3 (Cs y)) J ⊓ Cs x :=
      le_inf hJK (hJ'.1.trans inf_le_right)
    have hJ2 : GLAPComponent 3 (ncl (GLAPLayer 3 (Cs y)) J ⊓ Cs x) J :=
      glaPComponent_of_le hp hJ' hle (inf_le_inf_right _ hKy)
    exact glaPComponent_of_le hp hJ2 (le_sSup hJ2) (i183_glaPLayer_le 3 _)
  ·
    set Cv : Subgroup G := Cs y with hCv
    set u' : ↥Cv := ⟨x, hxX⟩ with hu'
    set A_H : Subgroup ↥Cv := Subgroup.centralizer ({u'} : Set ↥Cv) with hAH
    have hAmap : A_H.map Cv.subtype = Cv ⊓ Cs x := by
      ext g
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hz))⟩
      · rintro ⟨hgJ, hgC⟩
        exact ⟨⟨g, hgJ⟩, Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hgC)), rfl⟩
    have hJ'' : GLAPComponent 3 (Cv ⊓ Cs x) J := hJ'
    obtain ⟨J', hJ'c, hJ'J⟩ := exists_glaPComponent_map_eq hp Cv.subtype (s1t_ker_sub Cv A_H)
      (K' := J) (by rw [hAmap]; exact hJ'')
    set π : ↥Cv →* (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv) := QuotientGroup.mk' (GLAPPrimeCore 3 ↥Cv) with hπ
    have hu'3 : u' ^ 3 = 1 := Subtype.ext (by simpa using hx3')
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
    have hle : J'.map π ≤ barX 3 Cv (ncl (GLAPLayer 3 Cv) J) ⊓
        Subgroup.centralizer ({π u'} : Set (↥Cv ⧸ GLAPPrimeCore 3 ↥Cv)) :=
      le_inf (by rw [← hbar]; exact barX_mono 3 hJK) hc.1
    have hsnW := isSubnormal_of_le_of_le hc.2.1 hle inf_le_right
    rw [hbar]
    exact ⟨hle, hsnW, hq⟩

end CFSG.HardMathSupport.Solomon.Coordinator
