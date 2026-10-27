module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L74Symm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Helpers

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem layerCent_le_aux (L : Subgroup G) (s : G) : layerCent L s ≤ L :=
  (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)))).trans inf_le_left

theorem sec74_B_decomp [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (hP : Asc82Tab6P)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g)
    (hB : InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1)) :
    ∃ v ∈ L, ∃ c : G, c ∈ centralizer (L : Set G) ∧ (c = 1 ∨ c = t) ∧ orderOf v = 2 ∧
      InducesTypeSome L v 6 1 2 (-1) ∧ g⁻¹ * t * g = v * c := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  have hin : InnerOn L (g⁻¹ * t * g) :=
    ((hP.inner_iff G L hLP (g⁻¹ * t * g) hs2 hsN).mpr (Or.inr hB)).1
  obtain ⟨v, hvL, c, hcC, hv2, hc, hsv⟩ :=
    sec7_inner_decomp h72 hP hctx hs2 hA.comm hA.ne hin
  refine ⟨v, hvL, c, hcC, hc, hv2, ?_, hsv⟩
  have hcv : (g⁻¹ * t * g) * c⁻¹ = v := by rw [hsv]; group
  have h := inducesTypeSome_mul_centralizer (L := L) (s := g⁻¹ * t * g) (c := c⁻¹)
    (inv_mem hcC) hB
  rw [hcv] at h
  exact h

theorem sec74_B_not_one [Finite G] (h36 : Asc82Lemma36) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z g : G}
    (hA : Sec74Ass G t L S z g) (hB : InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1))
    (hX29 : IsL29 (layerCent L (g⁻¹ * t * g)))
    (hle : layerCent L (g⁻¹ * t * g) ≤ CFSG.conjugate L g)
    (hLg : ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
      InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1)) (hsL : g⁻¹ * t * g ∈ L) : False := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hLP g
  have hs2 : orderOf (g⁻¹ * t * g) = 2 := hA.orderOf_s
  have hsN : g⁻¹ * t * g ∈ normalizer (L : Set G) := hA.s_mem_normalizer h36
  have hctxg : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hctx.conjugate g
  have hcomp : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hX29))
  obtain ⟨u, huX, hu2⟩ := exists_involution_of_isComponentIn hcomp
  have huL : u ∈ L := (hcomp.le huX).1
  have huC : u ∈ centralizer ({g⁻¹ * t * g} : Set G) := (hcomp.le huX).2
  have huLg : u ∈ CFSG.conjugate L g := hle huX
  have hne : layerCent L (g⁻¹ * t * g) ≠ ⊥ := ne_bot_of_shape (Or.inr (Or.inl hX29))
  have hxout : XOut L (g⁻¹ * t * g) = layerCent L (g⁻¹ * t * g) :=
    hP.xout_eq G L hLP (g⁻¹ * t * g) hs2 hsN hne
  have huXOut : u ∈ XOut L (g⁻¹ * t * g) := by rw [hxout]; exact huX
  obtain ⟨hus2, hus4⟩ := hP.prod_i2 G L hLP (g⁻¹ * t * g) hsL hB u huXOut hu2
  have husL : u * (g⁻¹ * t * g) ∈ L := mul_mem huL hsL
  obtain ⟨hz2, hz4⟩ := sec7_z_type hF hctx
  have hconj : IsConj z (u * (g⁻¹ * t * g)) :=
    isConj_of_mem_conjClassIn
      (hP.i4_one_class G L hLP z (u * (g⁻¹ * t * g)) hctx.z_mem_L husL hz2 hus2 hz4 hus4)
  have hC : u * (g⁻¹ * t * g) ∈ centralizer ({g⁻¹ * t * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsu : (g⁻¹ * t * g) * u = u * (g⁻¹ * t * g) :=
      (Subgroup.mem_centralizer_singleton_iff.mp huC).symm
    rw [show (g⁻¹ * t * g) * (u * (g⁻¹ * t * g)) =
      ((g⁻¹ * t * g) * u) * (g⁻¹ * t * g) by group, hsu]
  have hsC : g⁻¹ * t * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hctxg.t_mem_centralizer
  have hus_type_g : KindP (CFSG.conjugate L g) (u * (g⁻¹ * t * g)) 1 :=
    inducesTypeSome_mul_centralizer hsC (hLg u huX hu2)
  have hN : u * (g⁻¹ * t * g) ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    mul_mem (Subgroup.le_normalizer huLg)
      (Subgroup.centralizer_le_normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) hsC)
  rcases sec7_lemma73_sym h73 hctx g hconj hC with ⟨α, hα⟩ | h4
  · have hK3 : KindP (CFSG.conjugate L g) (u * (g⁻¹ * t * g)) 3 := ⟨α, hα⟩
    exact (hP.excl G (CFSG.conjugate L g) hLPg (u * (g⁻¹ * t * g)) hus2 hN 3 1
      (by norm_num) (by norm_num) (by norm_num) hK3) hus_type_g
  · have hK0 : KindP (CFSG.conjugate L g) (u * (g⁻¹ * t * g)) 0 := h4
    exact (hP.excl G (CFSG.conjugate L g) hLPg (u * (g⁻¹ * t * g)) hus2 hN 0 1
      (by norm_num) (by norm_num) (by norm_num) hK0) hus_type_g

theorem sec74_B_dec [Finite G] (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hBX : Sec74BX) {t : G} {L S : Subgroup G}
    {z g : G} (hA : Sec74Ass G t L S z g) (hB : InducesTypeSome L (g⁻¹ * t * g) 6 1 2 (-1)) :
    ∃ v ∈ L, orderOf v = 2 ∧ InducesTypeSome L v 6 1 2 (-1) ∧ g⁻¹ * t * g = t * v := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  obtain ⟨hX29, hle, hu⟩ := hBX G t L S z g hA hB
  have hLg : ∀ u ∈ layerCent L (g⁻¹ * t * g), orderOf u = 2 →
      InducesTypeSome (CFSG.conjugate L g) u 6 1 2 (-1) :=
    fun u hu' hu2 => (hu u hu' hu2).2
  obtain ⟨v, hvL, c, hcC, hc, hv2, hvB, hsv⟩ := sec74_B_decomp h36 h72 hP hA hB
  rcases hc with hc1 | hct
  · exfalso
    rw [hc1] at hsv
    exact sec74_B_not_one h36 h73 hP hF hA hB hX29 hle hLg (by rw [hsv]; simpa using hvL)
  · refine ⟨v, hvL, hv2, hvB, ?_⟩
    rw [hct] at hsv
    have htv : t * v = v * t :=
      (Subgroup.mem_centralizer_iff.mp hctx.t_mem_centralizer v hvL).symm
    rw [hsv, ← htv]

theorem sec74_B_uv_Lg [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (hF : Asc82AutFacts)
    {t : G} {L S : Subgroup G} {z g : G} (hA : Sec74Ass G t L S z g) {u v' : G}
    (hne : layerCent (CFSG.conjugate L g) t ≠ ⊥) (hu : u ∈ layerCent (CFSG.conjugate L g) t)
    (hu2 : orderOf u = 2) (hv'L : v' ∈ CFSG.conjugate L g) (hv'2 : orderOf v' = 2)
    (hv'B : InducesTypeSome (CFSG.conjugate L g) v' 6 1 2 (-1))
    (hts : t = (g⁻¹ * t * g) * v') :
    ∃ m ∈ CFSG.conjugate L g, u * v' = m * (g⁻¹ * z * g) * m⁻¹ := by
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  have hLPg : IsOm6P (CFSG.conjugate L g) := isOm6P_conjugate hLP g
  have hctxg : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := hctx.conjugate g
  have hsC : g⁻¹ * t * g ∈ centralizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hctxg.t_mem_centralizer
  have hsv' : (g⁻¹ * t * g) * v' = v' * (g⁻¹ * t * g) :=
    (Subgroup.mem_centralizer_iff.mp hsC v' hv'L).symm
  have hts' : t = v' * (g⁻¹ * t * g) := hts.trans hsv'
  have htC : t ∈ centralizer ({g⁻¹ * t * g} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hA.comm).symm
  have hNt : t ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    hctxg.cent_le_normalizer h36 t htC
  have hcent : CFSG.conjugate L g ⊓ centralizer ({t} : Set G) =
      CFSG.conjugate L g ⊓ centralizer ({v'} : Set G) := by
    rw [hts']
    exact inf_centralizer_eq_of_mul_centralizer hsC
  have hxout_eq : XOut (CFSG.conjugate L g) t = XOut (CFSG.conjugate L g) v' := by
    unfold XOut
    rw [hcent]
  have hxout_t : XOut (CFSG.conjugate L g) t = layerCent (CFSG.conjugate L g) t :=
    hP.xout_eq G (CFSG.conjugate L g) hLPg t hctx.involution hNt hne
  have hu_XOut : u ∈ XOut (CFSG.conjugate L g) v' := by
    rw [← hxout_eq, hxout_t]
    exact hu
  obtain ⟨huv'2, huv'4⟩ := hP.prod_i2 G (CFSG.conjugate L g) hLPg v' hv'L hv'B u hu_XOut hu2
  obtain ⟨hz2, hz4⟩ := sec7_z_type hF hctx
  have hzg2 : orderOf (g⁻¹ * z * g) = 2 := by rw [orderOf_conj_inv]; exact hz2
  have hzg4 : InducesTypeSome (CFSG.conjugate L g) (g⁻¹ * z * g) 6 1 4 1 :=
    inducesTypeSome_conjugate hz4 g
  have hzgLg : g⁻¹ * z * g ∈ CFSG.conjugate L g := hctxg.z_mem_L
  have huLg : u ∈ CFSG.conjugate L g := layerCent_le_aux (CFSG.conjugate L g) t hu
  have huv'Lg : u * v' ∈ CFSG.conjugate L g := mul_mem huLg hv'L
  obtain ⟨m, hmLg, hm⟩ := hP.i4_one_class G (CFSG.conjugate L g) hLPg (g⁻¹ * z * g) (u * v')
    hzgLg huv'Lg hzg2 huv'2 hzg4 huv'4
  exact ⟨m, hmLg, hm⟩

theorem sec74_B_final {t z g u v l m : G} {L : Subgroup G} (hv2 : v * v = 1)
    (huv : u * v = v * u) (hsv : g⁻¹ * t * g = t * v) (hl : l ∈ L) (hlu : u = l * v * l⁻¹)
    (htL : ∀ x ∈ L, x * t = t * x) (hmC : m * (g⁻¹ * t * g) = (g⁻¹ * t * g) * m)
    (hm : u * v = m * (g⁻¹ * z * g) * m⁻¹) : IsConj t (t * z) := by
  have hts : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have htu : IsConj (g⁻¹ * t * g) (t * u) := by
    refine isConj_iff.mpr ⟨l, ?_⟩
    rw [hlu, hsv]
    calc l * (t * v) * l⁻¹ = (l * t) * v * l⁻¹ := by group
      _ = (t * l) * v * l⁻¹ := by rw [htL l hl]
      _ = t * (l * v * l⁻¹) := by group
  have hsu : (g⁻¹ * t * g) * (u * v) = t * u := by
    rw [hsv]
    calc (t * v) * (u * v) = t * (v * u) * v := by group
      _ = t * (u * v) * v := by rw [← huv]
      _ = t * u * (v * v) := by group
      _ = t * u := by rw [hv2, mul_one]
  have h3 : (g⁻¹ * t * g) * (u * v) = m * (g⁻¹ * (t * z) * g) * m⁻¹ := by
    rw [hm]
    calc (g⁻¹ * t * g) * (m * (g⁻¹ * z * g) * m⁻¹)
        = ((g⁻¹ * t * g) * m) * (g⁻¹ * z * g) * m⁻¹ := by group
      _ = (m * (g⁻¹ * t * g)) * (g⁻¹ * z * g) * m⁻¹ := by rw [← hmC]
      _ = m * ((g⁻¹ * t * g) * (g⁻¹ * z * g)) * m⁻¹ := by group
      _ = m * (g⁻¹ * (t * z) * g) * m⁻¹ := by
            rw [show (g⁻¹ * t * g) * (g⁻¹ * z * g) = g⁻¹ * (t * z) * g by group]
  have h4 : IsConj (t * z) ((g⁻¹ * t * g) * (u * v)) := by
    rw [h3]
    exact isConj_iff.mpr ⟨m * g⁻¹, by group⟩
  rw [hsu] at h4
  exact (hts.trans htu).trans h4.symm

theorem sec74CaseB_of (h36 : Asc82Lemma36) (h72 : Asc82Lemma72) (h73 : Asc82Lemma73)
    (hP : Asc82Tab6P) (hF : Asc82AutFacts) (hBX : Sec74BX) (hBT : Sec74BT) : Sec74CaseB := by
  intro G _ _ t L S z g hA hB
  have hctx : Sec7Ctx G t L S z := hA.ctx
  have hLP : IsOm6P L := hctx.isOm6P
  obtain ⟨hX29, hle, hu⟩ := hBX G t L S z g hA hB
  obtain ⟨ht, hlayer⟩ := hBT G t L S z g hA hB
  obtain ⟨v, hvL, hv2, hvB, hsv⟩ := sec74_B_dec h36 h72 h73 hP hF hBX hA hB
  have ht' : InducesTypeSome (CFSG.conjugate L g) ((g⁻¹)⁻¹ * (g⁻¹ * t * g) * g⁻¹) 6 1 2 (-1) := by
    rw [inv_conj_inv_cancel g t]
    exact ht
  obtain ⟨v', hv'L, hv'2, hv'B, hsv'⟩ :=
    sec74_B_dec h36 h72 h73 hP hF hBX hA.symm ht'
  rw [inv_conj_inv_cancel g t] at hsv'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hctx.involution, pow_orderOf_eq_one]
  have hs2 : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
    rw [← pow_two, ← hA.orderOf_s, pow_orderOf_eq_one]
  have htv : t * v = v * t :=
    (Subgroup.mem_centralizer_iff.mp hctx.t_mem_centralizer v hvL).symm
  have hv_eq : v = (g⁻¹ * t * g) * t := by
    calc v = (t * t) * v := by rw [ht2, one_mul]
      _ = t * (t * v) := by group
      _ = t * (v * t) := by rw [htv]
      _ = (t * v) * t := by group
      _ = (g⁻¹ * t * g) * t := by rw [← hsv]
  have hv'_eq : v' = (g⁻¹ * t * g) * t := by
    calc v' = ((g⁻¹ * t * g) * (g⁻¹ * t * g)) * v' := by rw [hs2, one_mul]
      _ = (g⁻¹ * t * g) * ((g⁻¹ * t * g) * v') := by group
      _ = (g⁻¹ * t * g) * t := by rw [← hsv']
  have hv'v : v' = v := hv'_eq.trans hv_eq.symm
  have hcomp : IsComponentIn (layerCent L (g⁻¹ * t * g))
      (L ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hX29))
  obtain ⟨u, huX, hu2⟩ := exists_involution_of_isComponentIn hcomp
  have huL : u ∈ L := (hcomp.le huX).1
  have huXg : u ∈ CFSG.conjugate L g := hle huX
  have huXgt : u ∈ layerCent (CFSG.conjugate L g) t := by rw [hlayer]; exact huX
  obtain ⟨l, hlL, hlu⟩ :=
    hP.i2_one_class G L hLP v u hvL huL hv2 hu2 hvB (hu u huX hu2).1
  have hut : u * t = t * u := Subgroup.mem_centralizer_iff.mp hctx.t_mem_centralizer u huL
  have hsu : (g⁻¹ * t * g) * u = u * (g⁻¹ * t * g) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hcomp.le huX).2).symm
  have huv : u * v = v * u := by
    have h := hsu
    rw [hsv] at h
    have hcancel : t * (v * u) = t * (u * v) := by
      calc t * (v * u) = (t * v) * u := by group
        _ = u * (t * v) := h
        _ = (u * t) * v := by group
        _ = (t * u) * v := by rw [hut]
        _ = t * (u * v) := by group
    exact (mul_left_cancel hcancel).symm
  have hv2' : v * v = 1 := by rw [← pow_two, ← hv2, pow_orderOf_eq_one]
  have hne : layerCent (CFSG.conjugate L g) t ≠ ⊥ := by
    rw [hlayer]
    exact ne_bot_of_shape (Or.inr (Or.inl hX29))
  obtain ⟨m, hmLg, hm'⟩ :=
    sec74_B_uv_Lg h36 hP hF hA hne huXgt hu2 hv'L hv'2 hv'B hsv'
  have hm : u * v = m * (g⁻¹ * z * g) * m⁻¹ := by
    rw [← hv'v]
    exact hm'
  have hmC : m * (g⁻¹ * t * g) = (g⁻¹ * t * g) * m :=
    Subgroup.mem_centralizer_singleton_iff.mp ((hctx.conjugate g).le_centralizer hmLg)
  have htL : ∀ x ∈ L, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hctx.t_mem_centralizer x hx
  exact hA.not1 (sec74_B_final hv2' huv hsv hlL hlu htL hmC hm)

end CFSG.OddStandard.SmallF3.Omega
