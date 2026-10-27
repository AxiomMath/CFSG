module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Five
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYS8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYSec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYFus
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYD
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import Certificates.Data.A5

public section

namespace CFSG.EvenSporadicStandard.HSStd

section FiveYStep

open Subgroup Equiv CFSG.RankThree.Native CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem false_of_fiveYStep
    (M : HS100Model)
    (hH2 : Harada39Two) {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    {S : Subgroup G} {z n v s : G} (h : HSOuterSetup G L t S z n v s) (r : G) (hrL : r ∈ L)
    (hrv : r * v = v * r) (hr5 : orderOf r = 5) (htr : t ∈ centralizer ({r} : Set G))
    (hvr : v ∈ centralizer ({r} : Set G)) (htv : t * v ∈ centralizer ({r} : Set G))
    (hM12 : IsSporadic (HSFiveBar G r) .M12)
    (hfus : ∃ h : HSFiveBar G r, h * fiveBar htr * h⁻¹ = fiveBar hvr ∧
      h * fiveBar hvr * h⁻¹ = fiveBar htv) : False := by
  obtain ⟨e⟩ := h.ctx.v_cls
  have hrT : r ∈ centralizer ({v} : Set G) ⊓ L := ⟨mem_centralizer_singleton_iff.2 hrv, hrL⟩
  obtain ⟨d⟩ := FiveY.exists_s8Data e hrT hr5
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have ht2 : t * t = 1 := h.t_sq
  have ht1 : t ≠ 1 := h.t_ne_one
  have hv2 : v * v = 1 := h.ctx.v_sq
  have hθ : OuterSection t ≃* ↥hs100R := (outerSection_t_equiv M h).some
  have hyt : d.y ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 (htcomm d.y d.y_mem)
  have hP : ∀ a b : G, a ∈ centralizer ({t} : Set G) → b ∈ centralizer ({t} : Set G) →
      orderOf a = 3 → orderOf b = 3 → ∃ n ∈ centralizer ({t} : Set G), n * a * n⁻¹ = b :=
    fun a b ha hb ha3 hb3 => FiveY.exists_conj_cent_three ht2 ht1 hθ ha hb ha3 hb3
  have htL : t ∉ L := by
    intro htl
    have hZ : center L = ⊥ := M.center_eq_bot L h.setting.2.1
    have h1 : (⟨t, htl⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (htcomm g g.2)
    rw [hZ, mem_bot] at h1
    exact ht1 (congrArg Subtype.val h1)
  have hvL : v ∉ L := fun hvl => h.ctx.v_outer (mem_sup_left hvl)
  have htvL : t * v ∉ L := by
    intro hh
    apply h.ctx.v_outer
    have : t * (t * v) = v := by rw [← mul_assoc, ht2, one_mul]
    rw [← this]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hh)
  obtain ⟨hh, hh1, hh2⟩ := hfus
  have hx2 : (⟨t, htr⟩ * ⟨t, htr⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext ht2
  have hv2' : (⟨v, hvr⟩ * ⟨v, hvr⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext hv2
  have htv2 : (⟨t * v, htv⟩ * ⟨t * v, htv⟩ : ↥(centralizer ({r} : Set G))) = 1 := by
    apply Subtype.ext
    show t * v * (t * v) = 1
    calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [h.t_comm_v]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [ht2, hv2, one_mul]
  obtain ⟨g₁, hg₁⟩ := FiveY.exists_conj_of_mk_conj hx2 hv2' ⟨hh, hh1⟩
  obtain ⟨g₂, hg₂⟩ := FiveY.exists_conj_of_mk_conj hv2' htv2 ⟨hh, hh2⟩
  have hgv : (g₁ : G) * t * (g₁ : G)⁻¹ = v := congrArg Subtype.val hg₁
  have hgtv : ((g₂ * g₁ : ↥(centralizer ({r} : Set G))) : G) * t *
      ((g₂ * g₁ : ↥(centralizer ({r} : Set G))) : G)⁻¹ = t * v := by
    have h2 : (g₂ : G) * v * (g₂ : G)⁻¹ = t * v := congrArg Subtype.val hg₂
    calc ((g₂ * g₁ : ↥(centralizer ({r} : Set G))) : G) * t *
          ((g₂ * g₁ : ↥(centralizer ({r} : Set G))) : G)⁻¹ =
        (g₂ : G) * ((g₁ : G) * t * (g₁ : G)⁻¹) * (g₂ : G)⁻¹ := by
          show (g₂ : G) * (g₁ : G) * t * ((g₂ : G) * (g₁ : G))⁻¹ = _
          group
      _ = t * v := by rw [hgv, h2]
  obtain ⟨g₄, hg₄⟩ := FiveY.exists_conj_t_tu M h d.tr hM12
  have hyu : d.y * d.u₁ = d.u₁ * d.y := by
    rw [d.u₁_eq]
    exact (d.J_comm_y _ (d.ψ (swap 2 3)).2).symm
  have hytv : d.y * (t * v) = t * v * d.y := by
    calc d.y * (t * v) = (d.y * t) * v := by rw [mul_assoc]
      _ = (t * d.y) * v := by rw [htcomm d.y d.y_mem]
      _ = t * (d.y * v) := by rw [mul_assoc]
      _ = t * (v * d.y) := by rw [d.y_comm_v]
      _ = t * v * d.y := by rw [mul_assoc]
  have hytu : d.y * (t * d.u₁) = t * d.u₁ * d.y := by
    calc d.y * (t * d.u₁) = (d.y * t) * d.u₁ := by rw [mul_assoc]
      _ = (t * d.y) * d.u₁ := by rw [htcomm d.y d.y_mem]
      _ = t * (d.y * d.u₁) := by rw [mul_assoc]
      _ = t * (d.u₁ * d.y) := by rw [hyu]
      _ = t * d.u₁ * d.y := by rw [mul_assoc]
  obtain ⟨a₁, ha₁y, ha₁⟩ := FiveY.exists_conj_cent_y hP hyt d.y_ord d.y_comm_v hgv
  obtain ⟨a₂, ha₂y, ha₂⟩ := FiveY.exists_conj_cent_y hP hyt d.y_ord hytv hgtv
  obtain ⟨a₃, ha₃y, ha₃⟩ := FiveY.exists_conj_cent_y hP hyt d.y_ord hytu hg₄
  set D : Subgroup G := centralizer ({d.y} : Set G) with hD
  have hJD : d.J ≤ D := fun j hj => mem_centralizer_singleton_iff.2 (d.J_comm_y j hj)
  have htD : t ∈ D := mem_centralizer_singleton_iff.2 (htcomm d.y d.y_mem).symm
  have hvD : v ∈ D := mem_centralizer_singleton_iff.2 d.y_comm_v.symm
  have hyD : d.y ∈ D := mem_centralizer_singleton_iff.2 rfl
  have hcard := FiveY.card_cent_ty_le ht2 ht1 hθ hyt d.y_ord
  refine FiveY.false_of_dConfig hH2 (D := ↥D)
    (h.setting.1.isKGroupCat_centralizer_of_orderOf (n := 3) (by norm_num) d.y_ord)
    { y := ⟨d.y, hyD⟩
      t := ⟨t, htD⟩
      v := ⟨v, hvD⟩
      J := d.J.subgroupOf D
      ψ := d.ψ.trans (Subgroup.subgroupOfEquivOfLe hJD).symm
      σ₀ := swap 2 3
      y_ord := (Subgroup.orderOf_mk d.y hyD).trans d.y_ord
      y_central := fun x => Subtype.ext (mem_centralizer_singleton_iff.1 x.2)
      t_sq := Subtype.ext ht2
      v_sq := Subtype.ext hv2
      t_ne_one := fun h1 => ht1 (congrArg Subtype.val h1)
      v_ne_one := fun h1 => h.v_ne_one (congrArg Subtype.val h1)
      t_ne_v := fun h1 => h.t_ne_v (congrArg Subtype.val h1)
      tv_comm := Subtype.ext h.t_comm_v
      J_t := fun j hj => Subtype.ext (htcomm (j : G) (d.J_le (mem_subgroupOf.1 hj)))
      J_v := fun j hj => Subtype.ext (d.J_comm_v (j : G) (mem_subgroupOf.1 hj))
      t_not_J := fun hj => htL (d.J_le (mem_subgroupOf.1 hj))
      v_not_J := fun hj => hvL (d.J_le (mem_subgroupOf.1 hj))
      tv_not_J := fun hj => htvL (d.J_le (mem_subgroupOf.1 hj))
      card_cent := by
        rw [FiveY.card_centralizer_subtype D ⟨t, htD⟩]
        rwa [inf_comm] at hcard
      σ₀_sq := by decide
      σ₀_ne := by decide
      fus_v := ⟨⟨a₁, mem_centralizer_singleton_iff.2 ha₁y⟩, Subtype.ext ha₁⟩
      fus_tv := ⟨⟨a₂, mem_centralizer_singleton_iff.2 ha₂y⟩, Subtype.ext ha₂⟩
      fus_u := ⟨⟨a₃, mem_centralizer_singleton_iff.2 ha₃y⟩, Subtype.ext (by
        change a₃ * t * a₃⁻¹ = t * ((d.ψ (swap 2 3) : ↥d.J) : G)
        rw [ha₃, d.u₁_eq])⟩ }

end FiveYStep

section FiveCase

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem false_of_fiveCase
    (M : HS100Model)
    (hH : Harada39One) (hI : HaradaFourInspection) (hY : NoA8.HSOuterFiveYStep)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G} {z n v s : G}
    (h : HSOuterSetup G L t S z n v s) (h' : HSOuterSetup G L t S z n (t * v) s)
    (hHiS : HSInductionHiS G) (hX : HSOuterOutcomeFive (OuterSection v))
    (hX' : HSOuterOutcomeFive (OuterSection (t * v))) : False := by
  obtain ⟨e⟩ := h.ctx.v_cls
  obtain ⟨r, u₁, u₂, tr⟩ := exists_fiveTriple e
  have tr' : FiveTriple L (t * v) r u₁ u₂ := tr.mul_t h.t_mem
  obtain ⟨Ct⟩ := centralizer_five_t M h tr
  obtain ⟨Cv⟩ := centralizer_five_of_section M h tr hX
  obtain ⟨Ctv⟩ := centralizer_five_of_section M h' tr' hX'
  have htcomm : ∀ x ∈ L, x * t = t * x := fun x hx => mem_centralizer_iff.1 h.t_mem x hx
  have htr : t ∈ centralizer ({r} : Set G) :=
    mem_centralizer_singleton_iff.2 (htcomm r tr.r_mem).symm
  have hvr : v ∈ centralizer ({r} : Set G) := mem_centralizer_singleton_iff.2 tr.r_comm.symm
  have hwr : t * v ∈ centralizer ({r} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc t * v * r = t * (v * r) := by rw [mul_assoc]
      _ = t * (r * v) := by rw [tr.r_comm]
      _ = (t * r) * v := by rw [mul_assoc]
      _ = (r * t) * v := by rw [htcomm r tr.r_mem]
      _ = r * (t * v) := by rw [mul_assoc]
  have htv : t * v = v * t := h.t_comm_v
  have ht2 : t * t = 1 := h.t_sq
  have hv2 : v * v = 1 := h.ctx.v_sq
  have hw2 : t * v * (t * v) = 1 := h'.ctx.v_sq
  have hZ := fusionZStar_bar_eq_bot tr.r_ord htr hvr ht2 hv2 h.t_ne_one h.v_ne_one htv h.t_ne_v
    Ct Cv
  have hlist := harada_bar hH
    (h.setting.1.isKGroupCat_centralizer_of_orderOf (n := 5) (by norm_num) tr.r_ord) tr.r_ord htr
    hvr ht2 hv2 h.t_ne_one h.v_ne_one htv h.t_ne_v Ct Cv
  have gt := good_bar tr.r_ord htr ht2 h.t_ne_one Ct
  have gv := good_bar tr.r_ord hvr hv2 h.v_ne_one Cv
  have gw := good_bar tr.r_ord hwr hw2 h'.v_ne_one Ctv
  have hab : fiveBar htr * fiveBar hvr = fiveBar hwr := by
    unfold fiveBar
    rw [← QuotientGroup.mk_mul]
    rfl
  have hba : fiveBar hvr * fiveBar htr = fiveBar htr * fiveBar hvr := by
    unfold fiveBar
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext htv.symm
  have hne : fiveBar htr ≠ fiveBar hvr :=
    mk_ne_of_involutions (K := ↥(centralizer ({r} : Set G))) (t := ⟨t, htr⟩) (v := ⟨v, hvr⟩)
      (Subtype.ext ht2) (Subtype.ext hv2) (Subtype.ext htv)
      (fun hh => h.t_ne_v (congrArg Subtype.val hh))
  obtain ⟨hM12, hh, h1, h2⟩ := hI (HSFiveBar G r) hZ hlist (fiveBar htr) (fiveBar hvr)
    (orderOf_fiveBar htr ht2 h.t_ne_one) (orderOf_fiveBar hvr hv2 h.v_ne_one) hne hba.symm gt gv
    (by rw [hab]; exact gw)
  exact hY G L t S z n v s h hHiS r tr.r_mem tr.r_comm tr.r_ord htr hvr hwr hM12
    ⟨hh, h1, by rw [← hab]; exact h2⟩

end FiveCase

end CFSG.EvenSporadicStandard.HSStd

namespace CFSG.EvenSporadicStandard.HSStd.NoA8

theorem hsOuterFiveYStep_of_harada39Two
    (M : HS100Model)
    (hH2 : Harada39Two) : NoA8.HSOuterFiveYStep :=
  fun _ _ _ _ _ _ _ _ _ _ h _ => false_of_fiveYStep M hH2 h

theorem hsOuterFiveCase_of_steps
    (M : HS100Model)
    (hH : Harada39One) (hI : HaradaFourInspection) (hY : NoA8.HSOuterFiveYStep) :
    NoA8.HSOuterFiveCase :=
  fun _ _ _ _ _ _ _ _ _ _ h h' => false_of_fiveCase M hH hI hY h h'

end CFSG.EvenSporadicStandard.HSStd.NoA8
