module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec74_C_cover [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    (hO : Asc82Outside) {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hk : (∃ α : ℤˣ, InducesTypeSome L (g⁻¹ * t * g) 6 1 3 α) ∨
      InducesOutsideGStar L 6 1 (g⁻¹ * t * g)) :
    ∃ u : G, u ∈ L ∧ u ∈ CFSG.conjugate L g ∧ orderOf u = 2 ∧ InducesTypeSome L u 6 1 4 1 ∧
      u ∈ centralizer ({g⁻¹ * t * g} : Set G) ∧
      (g⁻¹ * t * g) * u ∈ conjClassIn L (g⁻¹ * t * g) := by
  let s : G := g⁻¹ * t * g
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hs2 : orderOf s = 2 := hA.orderOf_s
  have hsN : s ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  obtain ⟨u, huX, hu2, hu4, hsu⟩ := hP.cover_i4 G L hLP s hs2 hsN hk
  obtain ⟨huL, huCs⟩ := Subgroup.mem_inf.mp ((xout_le L s) huX)
  have hX : Asc82XSub L s 1 (XOut L s) := by
    rcases hk with ⟨α, hα⟩ | hout
    · exact Or.inr ⟨⟨α, hα⟩, hP.xout_i3 G L hLP s hs2 hsN ⟨α, hα⟩⟩
    · have hne : layerCent L s ≠ ⊥ := by
        rcases hP.layer_outer G L hLP s hs2 hsN hout with h3 | h29
        · exact ne_bot_of_shape (Or.inr (Or.inr (Or.inr h3)))
        · exact ne_bot_of_shape (Or.inr (Or.inl h29))
      exact Or.inl (hP.xout_eq G L hLP s hs2 hsN hne)
  have hle : twoPrimeRes (XOut L s) ≤ CFSG.conjugate L g :=
    hO.thm2L G t L hctx.toSec3SettingLB
      (h72 G t L hctx.toSec3SettingLB hctx.omega6)
      (asc82OddInnerOm6_holds G L (Or.inr (Or.inl hLP))) 1 g hA.comm hA.ne (XOut L s) hX
  have hug : u ∈ CFSG.conjugate L g := hle (mem_twoPrimeRes_of_orderOf_two huX hu2)
  exact ⟨u, huL, hug, hu2, hu4, huCs, hsu⟩

theorem sec74_C_type [Finite G] (h73 : Asc82Lemma73) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g) {u : G} (hu : u ∈ L)
    (hug : u ∈ CFSG.conjugate L g) (hu2 : orderOf u = 2) (hu4 : InducesTypeSome L u 6 1 4 1)
    (huC : u ∈ centralizer ({g⁻¹ * t * g} : Set G)) :
    InducesTypeSome (CFSG.conjugate L g) u 6 1 4 1 := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hLP g
  obtain ⟨hz2, hz4⟩ := sec7_z_type hF hctx
  have hzu : u ∈ conjClassIn L z :=
    hP.i4_one_class G L hLP z u hctx.z_mem_L hu hz2 hu2 hz4 hu4
  have hconj : IsConj z u := isConj_of_mem_conjClassIn hzu
  rcases sec7_lemma73_sym h73 hctx g hconj huC with ⟨α, hα⟩ | h4
  · rcases sec7_involution_types hP hLPg hug hu2 with h4' | h2
    · exact h4'
    · exfalso
      have hK1 : KindP (CFSG.conjugate L g) u 1 := h2
      have hK3 : KindP (CFSG.conjugate L g) u 3 := ⟨α, hα⟩
      exact (hP.excl G (CFSG.conjugate L g) hLPg u hu2 (Subgroup.le_normalizer hug)
        1 3 (by norm_num) (by norm_num) (by norm_num) hK1) hK3
  · exact h4

theorem sec74_C_final [Finite G] (hP : Asc82Tab6P) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G}
    {z g : G} (hA : Sec74Ass G t L S z g) {u : G} (hug : u ∈ CFSG.conjugate L g)
    (hu2 : orderOf u = 2) (hu4g : InducesTypeSome (CFSG.conjugate L g) u 6 1 4 1)
    (hsu : (g⁻¹ * t * g) * u ∈ conjClassIn L (g⁻¹ * t * g)) : IsConj t (t * z) := by
  let s : G := g⁻¹ * t * g
  let zg : G := g⁻¹ * z * g
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hLP g
  have hctxg : Sec7Ctx G s (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g) :=
    hctx.conjugate g
  obtain ⟨hz2, hz4⟩ := sec7_z_type hF hctx
  have hzg : zg ∈ CFSG.conjugate L g := by
    rw [mem_conjugate_iff]
    have hgz : g * zg * g⁻¹ = z := by
      show g * (g⁻¹ * z * g) * g⁻¹ = z
      group
    rw [hgz]
    exact hctx.z_mem_L
  have hzg2 : orderOf zg = 2 := by
    show orderOf (g⁻¹ * z * g) = 2
    rw [orderOf_conj_inv g z]
    exact hz2
  have hzg4 : InducesTypeSome (CFSG.conjugate L g) zg 6 1 4 1 :=
    inducesTypeSome_conjugate hz4 g
  have hclass : u ∈ conjClassIn (CFSG.conjugate L g) zg :=
    hP.i4_one_class G (CFSG.conjugate L g) hLPg zg u hzg hug hzg2 hu2 hzg4 hu4g
  obtain ⟨m, hmLg, hmu⟩ := hclass
  have hms : s * m = m * s :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctxg.le_centralizer hmLg)).symm
  have h_zg_su : IsConj (s * zg) (s * u) := by
    refine isConj_of_mem_conjClassIn (H := CFSG.conjugate L g) ⟨m, hmLg, ?_⟩
    rw [hmu]
    calc
      s * (m * zg * m⁻¹) = s * m * zg * m⁻¹ := by group
      _ = m * s * zg * m⁻¹ := by rw [hms]
      _ = m * (s * zg) * m⁻¹ := by group
  have h_s_su : IsConj s (s * u) := isConj_of_mem_conjClassIn (H := L) hsu
  have h_tz_stzg : IsConj (t * z) (s * zg) := by
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    show g⁻¹ * (t * z) * (g⁻¹)⁻¹ = (g⁻¹ * t * g) * (g⁻¹ * z * g)
    group
  have h_ts : IsConj t s := by
    refine isConj_iff.mpr ⟨g⁻¹, ?_⟩
    show g⁻¹ * t * (g⁻¹)⁻¹ = g⁻¹ * t * g
    group
  exact h_ts.trans (h_s_su.trans (h_tz_stzg.trans h_zg_su).symm)

theorem sec74CaseC_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hO : Asc82Outside) : Sec74CaseC := by
  intro G _ _ t L S z g hA hk
  obtain ⟨u, hu, hug, hu2, hu4, huC, hsu⟩ := sec74_C_cover h36 h72 hP hO hA hk
  exact hA.not1
    (sec74_C_final hP hF hA hug hu2 (sec74_C_type h73 hP hF hA hu hug hu2 hu4 huC) hsu)

end CFSG.OddStandard.SmallF3.Omega
