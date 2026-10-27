module

public import CFSG.LargeExtraspecial.DW2AAlphaLbar
public import CFSG.LargeExtraspecial.DW2AAlphaCount
public import CFSG.LargeExtraspecial.DW2ABeta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

namespace Alpha

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {W : Submodule (ZMod 2) S.Qt}

variable (S W) in
@[expose] def Dset : Set S.Qt := {v | ∃ h : G, IsDx S W h ∧ S.cl (h * S.z * h⁻¹) = v}

variable (S W) in
@[expose] def adj (a b : S.Qt) : Prop := b ∈ Dset S W ∧ polar S.q a b ≠ 0

variable (S W) in
@[expose] def gcomp (a : S.Qt) : Set S.Qt := {b | Relation.ReflTransGen (adj S W) a b}

theorem mem_Dset_of_mem_gcomp {a b : S.Qt} (ha : a ∈ Dset S W) (hb : b ∈ gcomp S W a) :
    b ∈ Dset S W := by
  induction hb with
  | refl => exact ha
  | tail _ hr _ => exact hr.1

theorem gcomp_trans {a b c : S.Qt} (hb : b ∈ gcomp S W a) (hc : c ∈ gcomp S W b) :
    c ∈ gcomp S W a :=
  Relation.ReflTransGen.trans hb hc

theorem gcomp_symm {a b : S.Qt} (ha : a ∈ Dset S W) (hb : b ∈ gcomp S W a) :
    a ∈ gcomp S W b := by
  induction hb with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d hc hcd ih =>
    have hcD := mem_Dset_of_mem_gcomp ha hc
    refine Relation.ReflTransGen.head ⟨hcD, ?_⟩ ih
    rw [polar_comm]
    exact hcd.2

theorem polar_eq_zero_of_not_mem {a d e : S.Qt} (hd : d ∈ gcomp S W a) (he : e ∈ Dset S W)
    (hea : e ∉ gcomp S W a) : polar S.q d e = 0 := by
  by_contra h
  exact hea (Relation.ReflTransGen.tail hd ⟨he, h⟩)

theorem apply_mem_gcomp {s : S.O} (hs : ∀ v ∈ Dset S W, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Dset S W)
    {a : S.Qt} (hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a) {b : S.Qt} (hb : b ∈ gcomp S W a) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) b ∈ gcomp S W a := by
  induction hb with
  | refl => rw [hsa]; exact Relation.ReflTransGen.refl
  | tail _ hr ih =>
    refine Relation.ReflTransGen.tail ih ⟨hs _ hr.1, ?_⟩
    rw [polar_apply_apply]
    exact hr.2

variable (hA : Hyp S W)
include hA

theorem ρ_mem_Dset (m : S.M) {v : S.Qt} (hv : v ∈ Dset S W) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Dset S W := by
  obtain ⟨h, hx, rfl⟩ := hv
  refine ⟨(m : G) * h, hx.mul hA m, ?_⟩
  rw [S.ρ_cl m hx.1]
  congr 1
  group

theorem Dset_le_perp {v : S.Qt} (hv : v ∈ Dset S W) : v ∈ perp S W := by
  obtain ⟨h, hx, rfl⟩ := hv
  exact hA.cl_mem_perp hx.1

variable (S W) in
@[expose] noncomputable def Pspan : Submodule (ZMod 2) S.Qt :=
  Submodule.span (ZMod 2) (Dset S W) ⊔ W

omit hA [Finite G] in
theorem le_Pspan : W ≤ Pspan S W := le_sup_right

theorem Pspan_le_perp : Pspan S W ≤ perp S W :=
  sup_le (Submodule.span_le.mpr fun _ hv => Dset_le_perp hA hv) hA.le_perp

theorem isMbarInvariant_Pspan : IsMbarInvariant S (Pspan S W) := by
  intro m v hv
  have key : ∀ d ∈ Submodule.span (ZMod 2) (Dset S W),
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) d ∈ Submodule.span (ZMod 2) (Dset S W) := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (ρ_mem_Dset hA m hx)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  obtain ⟨d, hd, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  exact add_mem (Submodule.mem_sup_left (key d hd)) (Submodule.mem_sup_right (hA.inv m w hw))

theorem exists_adj {h : G} (hx : IsDx S W h) :
    ∃ b ∈ Dset S W, polar S.q (S.cl (h * S.z * h⁻¹)) b = 1 := by
  by_contra hcon
  push Not at hcon
  have hperp : ∀ b ∈ Dset S W, polar S.q (S.cl (h * S.z * h⁻¹)) b = 0 :=
    fun b hb => (zmod2_cases _).resolve_right (hcon b hb)
  have hD : S.cl (h * S.z * h⁻¹) ∈ Dset S W := ⟨h, hx, rfl⟩
  have key : ∀ d ∈ Submodule.span (ZMod 2) (Dset S W),
      polar S.q (S.cl (h * S.z * h⁻¹)) d = 0 := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx' => exact hperp x hx'
    | zero => exact polar_zero_right _ _
    | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [polar_smul_right, hx, smul_zero]
  have hrad : S.cl (h * S.z * h⁻¹) ∈ radSing S (Pspan S W) := by
    refine ⟨⟨Submodule.mem_sup_left (Submodule.subset_span hD), mem_perp.mpr fun p hp => ?_⟩,
      S.q_cl_conj_z hx.1⟩
    obtain ⟨d, hd, w, hw, rfl⟩ := Submodule.mem_sup.mp hp
    rw [polar_add_left, mem_perp.mp (hA.cl_mem_perp hx.1) w hw, add_zero, polar_comm]
    exact key d hd
  rw [radSing_eq hA (isMbarInvariant_Pspan hA) le_Pspan (Pspan_le_perp hA)] at hrad
  exact hx.2 hrad

theorem le_finrank_of_gcomp [FiniteDimensional (ZMod 2) S.Qt] {h : G} (hx : IsDx S W h)
    {U : Submodule (ZMod 2) S.Qt} (hWU : W ≤ U)
    (hU : ∀ d ∈ gcomp S W (S.cl (h * S.z * h⁻¹)), d ∈ U) :
    S.width - 1 + finrank (ZMod 2) W ≤ finrank (ZMod 2) U := by
  obtain ⟨b, hb, hbx⟩ := exists_adj hA hx
  have hbg : b ∈ gcomp S W (S.cl (h * S.z * h⁻¹)) :=
    Relation.ReflTransGen.single ⟨hb, by rw [hbx]; exact one_ne_zero⟩
  have hDset : ∀ s ∈ S.Lbar h, ∀ v ∈ Dset S W, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Dset S W := by
    intro s hs v hv
    obtain ⟨y, -, rfl⟩ := S.mem_Lbar_iff.mp hs
    exact ρ_mem_Dset hA y hv
  have hcard := card_le_of_orbit hA.le_perp (Y := S.Lbar h) (fun s hs w hw => Lbar_fix hA hx hs hw)
    (fun s hs => Lbar_faith hA hx hs)
    (fun s hs t ht => congrArg Subtype.val
      ((S.isElementaryAbelian_Lbar hx.1).is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩))
    (hA.cl_mem_perp hx.1) hx.2 (fun s hs => Lbar_fix_x hx hs) (Rx_le_perp hA.le_perp)
    (fun s hs v hv hvx => Lbar_sub_mem_Rx hA hx hs hv hvx)
    (fun s hs r hr => Lbar_sub_mem_Rx_sup hA hx hs hr)
    (fun r hr hfix => mem_sup_of_Lbar_fix hA hx hr hfix) (Dset_le_perp hA hb)
    (by rw [polar_comm]; exact hbx) hWU fun s hs =>
      sub_mem (hU _ (apply_mem_gcomp (hDset s hs) (Lbar_fix_x hx hs) hbg)) (hU _ hbg)
  have hge := S.card_Lbar_ge hx.1 hx.ne_z
  have h1 := hge.trans hcard
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h3 := Submodule.finrank_mono hWU
  omega

omit hA in
theorem Hyp.two_le_finrank [IsSimpleGroup G] (hA : Hyp S W) (h2 : 2 ≤ S.width) :
    2 ≤ finrank (ZMod 2) W := by
  have h1 : 1 ≤ finrank (ZMod 2) W := Submodule.one_le_finrank_iff.mpr hA.ne_bot
  by_contra hlt
  have hW1 : finrank (ZMod 2) W = 1 := by omega
  obtain ⟨w, hw0, hW⟩ := finrank_eq_one_iff'.mp hW1
  have hspan : W = ZMod 2 ∙ (w : S.Qt) := by
    refine le_antisymm (fun v hv => ?_) ?_
    · obtain ⟨c, hc⟩ := hW ⟨v, hv⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact w.2
  have hw0' : (w : S.Qt) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hinv : IsMbarInvariant S (ZMod 2 ∙ (w : S.Qt)) := hspan ▸ hA.inv
  exact hw0' (eq_zero_of_forall_ρ_apply_eq S h2 (apply_eq_of_invariant_span hw0' hinv))

theorem mem_gcomp [IsSimpleGroup G] [FiniteDimensional (ZMod 2) S.Qt] (hn : 2 ≤ S.width)
    {a b : S.Qt}
    (ha : a ∈ Dset S W) (hb : b ∈ Dset S W) : b ∈ gcomp S W a := by
  by_contra hba
  have hm := hA.two_le_finrank (by omega)
  obtain ⟨g₁, hx₁, rfl⟩ := ha
  obtain ⟨g₂, hx₂, rfl⟩ := hb
  set a := S.cl (g₁ * S.z * g₁⁻¹) with ha_def
  set b := S.cl (g₂ * S.z * g₂⁻¹) with hb_def
  have haD : a ∈ Dset S W := ⟨g₁, hx₁, rfl⟩
  have hbD : b ∈ Dset S W := ⟨g₂, hx₂, rfl⟩
  set C₁ := gcomp S W a
  set C₂ := Dset S W \ gcomp S W a
  set U₁ := Submodule.span (ZMod 2) C₁ ⊔ W
  set U₂ := Submodule.span (ZMod 2) C₂ ⊔ W
  have hC₁D : C₁ ⊆ Dset S W := fun d hd => mem_Dset_of_mem_gcomp haD hd
  have h1 := le_finrank_of_gcomp hA hx₁ (U := U₁) le_sup_right
    fun d hd => Submodule.mem_sup_left (Submodule.subset_span hd)
  have h2 := le_finrank_of_gcomp hA hx₂ (U := U₂) le_sup_right fun d hd => by
    refine Submodule.mem_sup_left (Submodule.subset_span ⟨mem_Dset_of_mem_gcomp hbD hd, ?_⟩)
    intro hda
    exact hba (gcomp_trans hda (gcomp_symm hbD hd))
  have horth : ∀ d ∈ C₁, ∀ e ∈ C₂, polar S.q d e = 0 :=
    fun d hd e he => polar_eq_zero_of_not_mem hd he.1 he.2
  have horth' : ∀ e ∈ C₂, ∀ d ∈ C₁, polar S.q e d = 0 :=
    fun e he d hd => by rw [polar_comm]; exact horth d hd e he
  have hspan_perp : ∀ (X Y : Set S.Qt), (∀ d ∈ X, ∀ e ∈ Y, polar S.q d e = 0) →
      ∀ v ∈ Submodule.span (ZMod 2) Y, ∀ d ∈ X, polar S.q d v = 0 := by
    intro X Y hXY v hv d hd
    induction hv using Submodule.span_induction with
    | mem e he => exact hXY d hd e he
    | zero => exact polar_zero_right _ _
    | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [polar_smul_right, hx, smul_zero]
  have hDperp : ∀ d ∈ Dset S W, ∀ w ∈ W, polar S.q d w = 0 := fun d hd w hw => by
    rw [polar_comm]
    exact mem_perp.mp (Dset_le_perp hA hd) w hw
  have hint : U₁ ⊓ U₂ ≤ Pspan S W ⊓ perp S (Pspan S W) := by
    rintro v ⟨hv₁, hv₂⟩
    have hU₁P : U₁ ≤ Pspan S W :=
      sup_le_sup_right (Submodule.span_mono hC₁D) W
    refine ⟨hU₁P hv₁, mem_perp.mpr fun p hp => ?_⟩
    have hvC₁ : ∀ d ∈ C₁, polar S.q d v = 0 := by
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hv₂
      intro d hd
      rw [polar_add_right, hspan_perp C₁ C₂ horth y hy d hd, hDperp d (hC₁D hd) w hw, add_zero]
    have hvC₂ : ∀ e ∈ C₂, polar S.q e v = 0 := by
      obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hv₁
      intro e he
      rw [polar_add_right, hspan_perp C₂ C₁ horth' y hy e he, hDperp e he.1 w hw, add_zero]
    have hvW : ∀ w ∈ W, polar S.q w v = 0 := by
      have hU₁W : U₁ ≤ perp S W :=
        sup_le (Submodule.span_le.mpr fun d hd => Dset_le_perp hA (hC₁D hd)) hA.le_perp
      exact mem_perp.mp (hU₁W hv₁)
    have key : ∀ d ∈ Submodule.span (ZMod 2) (Dset S W), polar S.q d v = 0 := by
      intro d hd
      induction hd using Submodule.span_induction with
      | mem e he =>
        by_cases heC : e ∈ C₁
        · exact hvC₁ e heC
        · exact hvC₂ e ⟨he, heC⟩
      | zero => exact polar_zero_left _ _
      | add x y _ _ hx hy => rw [polar_add_left, hx, hy, add_zero]
      | smul c x _ hx => rw [polar_smul_left, hx, smul_zero]
    obtain ⟨d, hd, w, hw, rfl⟩ := Submodule.mem_sup.mp hp
    rw [polar_add_left, hvW w hw, add_zero]
    exact key d hd
  have hrad := finrank_rad_le hA (isMbarInvariant_Pspan hA) le_Pspan (Pspan_le_perp hA)
  have hint' := (Submodule.finrank_mono hint).trans hrad
  have hsup : U₁ ⊔ U₂ ≤ perp S W := by
    refine sup_le (sup_le ?_ hA.le_perp) (sup_le ?_ hA.le_perp)
    · exact Submodule.span_le.mpr fun d hd => Dset_le_perp hA (hC₁D hd)
    · exact Submodule.span_le.mpr fun d hd => Dset_le_perp hA hd.1
  have hperp := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width] at hperp
  change finrank (ZMod 2) (perp S W) = _ at hperp
  have hsupd := Submodule.finrank_mono hsup
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
  have hW := finrank_le_width_of_le_perp hA.le_perp
  omega

end Alpha

end CFSG.LargeExtraspecial.DW
