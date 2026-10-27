module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedPartsB
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Six
public import CFSG.LocalAnalysis.EvenBN.U5.ModelThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofNineA
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3TenCoprime

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups Pointwise

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem s4o_sc {X H : Subgroup G} (hX : IsPGroup 2 X) (hH : Odd (Nat.card H)) :
    Group.IsSolvable X ∧ (Nat.card H).Coprime (Nat.card X) := by
  haveI : Group.IsNilpotent X := hX.isNilpotent
  exact ⟨inferInstance, Data.coprime_card_of_odd hH hX⟩

theorem s4o_I_le_normalizer_U₁ (hd : d.Hyp) : d.I ≤ normalizer (d.U₁ : Set G) := by
  rw [d.U₁_eq hd.two_le]
  intro i hi
  refine mem_normalizer_inf (d.I_le_normalizer_P hi)
    (Prelim.normalizer_le_normalizer_centralizer d.I₁ ?_)
  exact Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun j hj =>
    d.I_comm (d.I₁_le_I hj) hi)

theorem Hyp.s4o_I_le_normalizer_V₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.I ≤ normalizer (d.V₁ : Set G) := by
  intro x hxI0
  have hxI : d.s * x * d.s ∈ d.I := by
    have : x ∈ d.I.map (MulAut.conj d.s).toMonoidHom := by
      rw [d.sec2_1_five.2.1]; exact hxI0
    exact mem_map_conj_s.1 this
  refine mem_normalizer_fintype fun v hv => ?_
  rw [SetLike.mem_coe, V₁, mem_map_conj_s] at hv ⊢
  have e : d.s * (x * v * x⁻¹) * d.s =
      (d.s * x * d.s) * (d.s * v * d.s) * (d.s * x * d.s)⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, d.s_inv]
    calc d.s * (x * v * x⁻¹) * d.s = d.s * x * (d.s * d.s) * v * (d.s * d.s) * x⁻¹ * d.s := by
          rw [d.s_mul_s]; group
      _ = _ := by group
  rw [e]
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hd.I_le_normalizer_F hGMS hxI) _).1 hv.1,
    mem_centralizer_iff.2 fun i hi => ?_⟩
  have hi' : i ∈ d.I := d.I₄_le_I hi
  set z := d.s * x * d.s with hz
  set w := d.s * v * d.s with hw
  have e1 : i * w = w * i := mem_centralizer_iff.1 hv.2 i hi
  have e2 : i * z = z * i := d.I_comm hi' hxI
  have e3 : i * z⁻¹ = z⁻¹ * i := d.I_comm hi' (inv_mem hxI)
  calc i * (z * w * z⁻¹) = z * (i * w) * z⁻¹ := by
        rw [show i * (z * w * z⁻¹) = (i * z) * w * z⁻¹ by group, e2]; group
    _ = z * (w * i) * z⁻¹ := by rw [e1]
    _ = z * w * z⁻¹ * i := by
        rw [show z * (w * i) * z⁻¹ = z * w * (i * z⁻¹) by group, e3]; group

theorem Hyp.s4o_cF (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {H : Subgroup G}
    (hH : H ≤ d.I) :
    Nat.card ↥(d.F ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hFB3, hFel, -, ψ, hψs, hψk, -, hψc⟩ := hd.sec3_4 hGMS
  have hA₁F : d.A₁ ≤ d.F := hFB3 ▸ inf_le_left
  have hF2 : IsPGroup 2 d.F := hFel.isPGroup
  have hA₁2 : IsPGroup 2 d.A₁ := hF2.to_le hA₁F
  have hodd : Odd (Nat.card H) := s2a2_odd_card_of_le_I hH
  obtain ⟨hFs, hFc⟩ := s4o_sc hF2 hodd
  obtain ⟨hAs, hAc⟩ := s4o_sc hA₁2 hodd
  have key := s4o_card_of_equivariant_subgroup (X := d.F) (N := d.A₁) (Y := d.A₁) (H := H)
    hA₁F (hH.trans (hd.I_le_normalizer_F hGMS)) (hH.trans d.I_le_normalizer_A₁)
    (hH.trans d.I_le_normalizer_A₁) hFs hAs hFc hAc ψ hψs hψk
    (fun c hc x => hψc c (hd.I_le_normalizer_B₁ (hH hc)) x)
  rw [key]
  ring

theorem Hyp.s4o_cV₁ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {H : Subgroup G}
    (hH : H ≤ d.I) :
    Nat.card ↥(d.V₁ ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.U₁ ⊓ centralizer (H : Set G)) ^ 2 := by
  let ψ : d.V₁ →* d.U₁ := MonoidHom.mk'
    (fun v => ⟨(v : G)⁻¹ * d.t * v * d.t, hd.cr_V₁_mem v.2⟩)
    (fun x y => Subtype.ext (hd.cr_V₁_mul x.2 y.2))
  have hV2 : IsPGroup 2 d.V₁ := (hd.isElementaryAbelian_V₁ hGMS).isPGroup
  have hU₁V : d.U₁ ≤ d.V₁ := hd.U₁_le_V₁ hGMS
  have hU2 : IsPGroup 2 d.U₁ := hV2.to_le hU₁V
  have hodd : Odd (Nat.card H) := s2a2_odd_card_of_le_I hH
  obtain ⟨hVs, hVc⟩ := s4o_sc hV2 hodd
  obtain ⟨hUs, hUc⟩ := s4o_sc hU2 hodd
  have key := s4o_card_of_equivariant_subgroup (X := d.V₁) (N := d.U₁) (Y := d.U₁) (H := H)
    hU₁V (hH.trans (hd.s4o_I_le_normalizer_V₁ hGMS)) (hH.trans (s4o_I_le_normalizer_U₁ hd))
    (hH.trans (s4o_I_le_normalizer_U₁ hd)) hVs hUs hVc hUc ψ
    (fun u => by
      obtain ⟨v, hv, hvu⟩ := hd.exists_V₁_cr_eq hGMS u.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩)
    (by
      ext x
      simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        have h1 : (x : G)⁻¹ * d.t * x * d.t = 1 := congrArg Subtype.val hx
        rw [← hd.V₁_inf_centralizer_t hGMS]
        exact Subgroup.mem_inf.2 ⟨x.2, hd.cr_eq_one_iff'.1 h1⟩
      · intro hx
        rw [← hd.V₁_inf_centralizer_t hGMS] at hx
        exact Subtype.ext (hd.cr_eq_one_iff'.2 (Subgroup.mem_inf.1 hx).2))
    (fun c hc x => by
      have hct : c ∈ centralizer ({d.t} : Set G) := hd.s2a2_I_le_centralizer_t (hH hc)
      have hx' : c * (x : G) * c⁻¹ ∈ d.V₁ :=
        (mem_normalizer_iff.1 (hH.trans (hd.s4o_I_le_normalizer_V₁ hGMS) hc) _).1 x.2
      exact ⟨hx', d.cr_conj hct⟩)
  rw [key]
  ring

theorem Hyp.s4o_zpowers_t_inf (hd : d.Hyp) {H : Subgroup G} (hH : H ≤ d.I) :
    zpowers d.t ⊓ centralizer (H : Set G) = zpowers d.t := by
  refine inf_eq_left.2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  refine mem_centralizer_iff.2 fun i hi => ?_
  have hit : i * d.t = d.t * i :=
    mem_centralizer_singleton_iff.1 (hd.s2a2_I_le_centralizer_t (hH hi))
  exact (Commute.zpow_right hit n).eq

theorem Hyp.s4o_card_zpowers_t_inf (hd : d.Hyp) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card ↥(zpowers d.t ⊓ centralizer (H : Set G)) = 2 := by
  rw [hd.s4o_zpowers_t_inf hH]
  exact hd.card_zpowers_t

theorem Hyp.s4o_cB₃ (hd : d.Hyp) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card ↥(d.B₃ ⊓ centralizer (H : Set G)) =
      2 * Nat.card ↥(d.A₃ ⊓ centralizer (H : Set G)) := by
  have hnorm : zpowers d.t ≤ normalizer (d.A₃ : Set G) :=
    (le_sup_left : zpowers d.t ≤ d.B₃).trans hd.B₃_le_normalizer_A₃
  have hmul : ((zpowers d.t ⊔ d.A₃ : Subgroup G) : Set G) =
      (zpowers d.t : Set G) * (d.A₃ : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hbot : zpowers d.t ⊓ d.A₃ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rcases hd.s2a2_zpowers_t (Subgroup.mem_inf.1 hx).1 with h1 | h1
    · exact (Subgroup.mem_bot).2 h1
    · exact absurd (d.P_le_L (d.A₃_le_P (h1 ▸ (Subgroup.mem_inf.1 hx).2))) hd.t_not_mem_L
  have key := s4o_card_inf_centralizer_mul (X := d.B₃) (A := zpowers d.t) (B := d.A₃) H
    le_sup_left le_sup_right hbot
    (fun x hx => by
      have : x ∈ ((zpowers d.t ⊔ d.A₃ : Subgroup G) : Set G) := hx
      rw [hmul] at this
      obtain ⟨a, ha, b, hb, hab⟩ := this
      exact ⟨a, ha, b, hb, hab.symm⟩)
    (fun i hi => d.mem_normalizer_zpowers_t (hd.s2a2_I_le_centralizer_t (hH hi)))
    (hH.trans (fun i hi => hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)))
  rw [key, hd.s4o_card_zpowers_t_inf hH]

theorem Hyp.s4o_cFB₃ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {H : Subgroup G}
    (hH : H ≤ d.I) :
    Nat.card ↥(d.F ⊓ centralizer (H : Set G)) * Nat.card ↥(d.B₃ ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) *
        Nat.card ↥((d.F ⊔ d.B₃) ⊓ centralizer (H : Set G)) := by
  obtain ⟨hN13, -, -, hFN, -, -, hFB3, hFel, -, -⟩ := hd.sec3_4 hGMS
  have hFB₃B₆ : d.F ⊔ d.B₃ ≤ d.B₆ := (hd.sec3_7 hGMS).1
  have hA₁F : d.A₁ ≤ d.F := hFB3 ▸ inf_le_left
  have hFB₃N : d.F ⊔ d.B₃ ≤ normalizer (d.B₃ : Set G) :=
    sup_le (hFN.trans hN13.le) le_normalizer
  haveI : (d.B₃.subgroupOf (d.F ⊔ d.B₃)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hFB₃N
  have hF2 : IsPGroup 2 d.F := hFel.isPGroup
  have hFB2 : IsPGroup 2 (d.F ⊔ d.B₃ : Subgroup G) := d.isPGroup_B₆_caseB.to_le hFB₃B₆
  have hodd : Odd (Nat.card H) := s2a2_odd_card_of_le_I hH
  obtain ⟨hFs, hFc⟩ := s4o_sc hF2 hodd
  obtain ⟨hFBs, hFBc⟩ := s4o_sc hFB2 hodd
  let ψ : d.F →* (d.F ⊔ d.B₃ : Subgroup G) ⧸ d.B₃.subgroupOf (d.F ⊔ d.B₃) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_left)
  have hmul : ((d.F ⊔ d.B₃ : Subgroup G) : Set G) = (d.F : Set G) * (d.B₃ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hd.B₃_le_normalizer_F
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    have ha : (a : G) ∈ ((d.F ⊔ d.B₃ : Subgroup G) : Set G) := a.2
    rw [hmul] at ha
    obtain ⟨x, hx, b, hb, hxb⟩ := ha
    refine ⟨⟨x, hx⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion le_sup_left ⟨x, hx⟩) = QuotientGroup.mk a
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    show x⁻¹ * (a : G) ∈ d.B₃
    rw [← hxb, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hb
  have hψk : ψ.ker = d.A₁.subgroupOf d.F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hFB3]
    show QuotientGroup.mk (Subgroup.inclusion le_sup_left x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    show (x : G) ∈ d.B₃ ↔ (x : G) ∈ d.F ⊓ d.B₃
    exact ⟨fun hb => Subgroup.mem_inf.2 ⟨x.2, hb⟩, fun hb => (Subgroup.mem_inf.1 hb).2⟩
  have hequ : ∀ c ∈ H, ∀ (e : d.F) (a : ↥(d.F ⊔ d.B₃)) (he : c * e * c⁻¹ ∈ d.F)
      (ha : c * a * c⁻¹ ∈ d.F ⊔ d.B₃),
      ψ e = QuotientGroup.mk a → ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ := by
    intro c hc e a he ha hea
    have h1 : (e : G)⁻¹ * (a : G) ∈ d.B₃ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hea)
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    show (c * (e : G) * c⁻¹)⁻¹ * (c * (a : G) * c⁻¹) ∈ d.B₃
    have e1 : (c * (e : G) * c⁻¹)⁻¹ * (c * (a : G) * c⁻¹) = c * ((e : G)⁻¹ * (a : G)) * c⁻¹ := by
      group
    rw [e1]
    exact (mem_normalizer_iff.1 (hH.trans hd.s2a2_I_le_B₃ hc) _).1 h1
  exact s4o_card_mul_card_of_equivariant (X := d.F) (N := d.A₁) (A := d.F ⊔ d.B₃) (B := d.B₃)
    (H := H) hA₁F le_sup_right (hH.trans (hd.I_le_normalizer_F hGMS))
    (hH.trans d.I_le_normalizer_A₁)
    (fun i hi => Common.mem_normalizer_sup (hd.I_le_normalizer_F hGMS (hH hi))
      (hd.s2a2_I_le_B₃ (hH hi)))
    (hH.trans hd.s2a2_I_le_B₃) hFs hFBs hFc hFBc ψ hψs hψk hequ

theorem Hyp.s4o_cB₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {H : Subgroup G}
    (hH : H ≤ d.I) :
    Nat.card ↥(d.B₆ ⊓ centralizer (H : Set G)) =
      2 * Nat.card ↥(d.A₃ ⊓ centralizer (H : Set G)) ^ 2 := by
  obtain ⟨ψ, hψs, hψk, hψc⟩ := hd.s2a2_psi hGMS
  have hFB₃B₆ : d.F ⊔ d.B₃ ≤ d.B₆ := (hd.sec3_7 hGMS).1
  have hodd : Odd (Nat.card H) := s2a2_odd_card_of_le_I hH
  obtain ⟨hBs, hBc⟩ := s4o_sc d.isPGroup_B₆_caseB hodd
  obtain ⟨hAs, hAc⟩ := s4o_sc (s2a2_isPGroup_A₃ d) hodd
  have ha := s4o_card_mul_card_of_equivariant (X := d.B₆) (N := d.F ⊔ d.B₃) (A := d.A₃)
    (B := d.A₁) (H := H) hFB₃B₆ d.A₁_le_A₃ (hH.trans (hd.s2a2_I_le_B₆ hGMS))
    (fun i hi => Common.mem_normalizer_sup (hd.I_le_normalizer_F hGMS (hH hi))
      (hd.s2a2_I_le_B₃ (hH hi)))
    (hH.trans (fun i hi => hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)))
    (hH.trans d.I_le_normalizer_A₁) hBs hAs hBc hAc ψ hψs hψk
    (fun c hc s a hs ha => hψc c (hH hc) s a hs ha)
  have hb := hd.s4o_cFB₃ hGMS hH
  have hF := hd.s4o_cF hGMS hH
  have hB₃ := hd.s4o_cB₃ hH
  have hpos : 0 < Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) := Nat.card_pos
  rw [hF, hB₃] at hb
  have hFB : Nat.card ↥((d.F ⊔ d.B₃) ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) *
        (2 * Nat.card ↥(d.A₃ ⊓ centralizer (H : Set G))) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [← hb]
    ring
  rw [hFB] at ha
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) * Nat.card ↥(d.B₆ ⊓ centralizer (H : Set G))
      = Nat.card ↥(d.B₆ ⊓ centralizer (H : Set G)) *
        Nat.card ↥(d.A₁ ⊓ centralizer (H : Set G)) := mul_comm _ _
    _ = _ := ha
    _ = _ := by ring

theorem Hyp.s4o_cD (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) (htD : d.t ∉ d.D) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card ↥(d.D ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.A₃ ⊓ centralizer (H : Set G)) ^ 2 := by
  have hnorm : zpowers d.t ≤ normalizer (d.D : Set G) :=
    Subgroup.zpowers_le.2 hd.t_mem_normalizer_D
  have hmul : ((d.D ⊔ zpowers d.t : Subgroup G) : Set G) =
      (d.D : Set G) * (zpowers d.t : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm
  have hbot : d.D ⊓ zpowers d.t = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rcases hd.s2a2_zpowers_t (Subgroup.mem_inf.1 hx).2 with h1 | h1
    · exact Subgroup.mem_bot.2 h1
    · exact absurd (h1 ▸ (Subgroup.mem_inf.1 hx).1) htD
  have key := s4o_card_inf_centralizer_mul (X := d.B₆) (A := d.D) (B := zpowers d.t) H
    (hd.s2a2_D_le_B₆ hGMS) (by rw [hB₆]; exact le_sup_right) hbot
    (fun x hx => by
      have : x ∈ ((d.D ⊔ zpowers d.t : Subgroup G) : Set G) := hB₆ ▸ hx
      rw [hmul] at this
      obtain ⟨a, ha, b, hb, hab⟩ := this
      exact ⟨a, ha, b, hb, hab.symm⟩)
    (hH.trans (hd.s2a2_I_le_D hGMS))
    (fun i hi => d.mem_normalizer_zpowers_t (hd.s2a2_I_le_centralizer_t (hH hi)))
  have h6 := hd.s4o_cB₆ hGMS hH
  rw [key, hd.s4o_card_zpowers_t_inf hH] at h6
  linarith

theorem s4o_comm_of_mem {A : Subgroup G} [hA : CFSG.IsElementaryAbelian 2 A] {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Hyp.s4o_A₁_inf_C₅ (hd : d.Hyp) : d.A₁ ⊓ centralizer (d.I₅ : Set G) = d.Zp := by
  have e : d.A₁ ⊓ centralizer (d.I₅ : Set G) = d.A₁ ⊓ (d.P ⊓ centralizer (d.I₅ : Set G)) := by
    rw [← inf_assoc, inf_of_le_left d.A₁_le_P]
  rw [e, hd.P_inf_centralizer_I₅]
  have hVU : Vsub h ≤ hypUnitriangular h 2 1 := by
    rw [Vsub_eq_patSub]
    exact patSub_le_U _ _
  have hA : d.A₁ = d.pull (Vsub h) := rfl
  have hZ : d.Zp = d.pull (ZPsub h) := rfl
  rw [hA, hZ, ← d.pull_inf hVU (patSub_le_U _ _)]
  congr 1
  refine le_antisymm (fun g hg => ?_) (le_inf ZPsub_le_Vsub ZPsub_le_patSub_I₅)
  obtain ⟨hgV, hgI⟩ := Subgroup.mem_inf.1 hg
  refine mem_ZPsub_of_patSub_I₅ hgI ?_
  rw [Vsub_eq_patSub, mem_patSub] at hgV
  exact hgV.2 (ιe₁, ιz) (by simp [sA₁])

theorem Hyp.s4o_card_A₁_inf_C₅ (hd : d.Hyp) :
    Nat.card ↥(d.A₁ ⊓ centralizer (d.I₅ : Set G)) = 2 ^ f := by
  rw [hd.s4o_A₁_inf_C₅]
  exact d.card_Zp

theorem Hyp.s4o_P_inf_I₂ (hd : d.Hyp) : d.P ⊓ centralizer (d.I₂ : Set G) = d.CPI₂ := by
  have e : d.P ⊓ centralizer (d.I₂ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₂sub h : Set (hypSU h 2 1))) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  rw [e, U_inf_centralizer_I₂ hd.two_le]
  rfl

theorem Hyp.s4o_A₃_inf_I₂ (hd : d.Hyp) :
    d.A₃ ⊓ centralizer (d.I₂ : Set G) = d.CPI₂ ∧ Nat.card d.CPI₂ = (2 ^ f) ^ 3 := by
  have e := hd.s4o_P_inf_I₂
  refine ⟨le_antisymm ((inf_le_inf_right _ d.A₃_le_P).trans e.le) ?_, ?_⟩
  · exact le_inf (d.pull_mono patSub_I₂_le_Ssub) (e.symm.le.trans inf_le_right)
  · rw [CPI₂, d.card_pull (patSub_le_U _ _), card_patSub_sI₂]

theorem Hyp.s4o_P_inf_I₆ (hd : d.Hyp) : d.P ⊓ centralizer (d.I₆ : Set G) = d.CPI₆ := by
  have e : d.P ⊓ centralizer (d.I₆ : Set G) =
      d.pull (hypUnitriangular h 2 1 ⊓ centralizer (I₆sub h : Set (hypSU h 2 1))) :=
    (d.pull_U_inf_centralizer (torusEq_le _)).symm
  rw [e, U_inf_centralizer_I₆ hd.two_le]
  rfl

theorem Hyp.s4o_card_C₃₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card ↥(d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G)) = (2 ^ f) ^ 2 := by
  obtain ⟨-, -, -, ⟨h4, h4b⟩, -⟩ := d.sec2_1_two hd.two_le
  obtain ⟨-, -, -, -, -, -, hFB3, hFel, -, -⟩ := hd.sec3_4 hGMS
  have hA₁F : d.A₁ ≤ d.F := hFB3 ▸ inf_le_left
  haveI : CFSG.IsElementaryAbelian 2 d.A₁ := isElementaryAbelian_of_le' hFel hA₁F
  have hle : d.P ⊓ centralizer ((d.I₃ ⊓ d.I₆ : Subgroup G) : Set G) ≤
      normalizer ((d.P ⊓ centralizer (d.I₄ : Set G) : Subgroup G) : Set G) := by
    refine s2a2_le_normalizer_of_comm fun x hx n hn => ?_
    have hx' : x ∈ d.A₁ := h4 ▸ Subgroup.mem_sup_right hx
    have hn' : n ∈ d.A₁ := h4 ▸ Subgroup.mem_sup_left hn
    exact s4o_comm_of_mem hx' hn'
  have key := Common.card_sup_mul_card_inf_eq hle
  rw [← h4, h4b, Subgroup.card_bot, hd.card_C₄, d.card_A₁] at key
  have hq : 0 < (2 ^ f) ^ 2 := by positivity
  apply Nat.eq_of_mul_eq_mul_left hq
  rw [← key]
  ring

theorem Hyp.s4o_cP (hd : d.Hyp) {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card ↥(d.P ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.A₃ ⊓ centralizer (H : Set G)) * Nat.card ↥(d.U₁ ⊓ centralizer (H : Set G)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨hPeq, hPbot⟩⟩ := d.sec2_1_two hd.two_le
  rw [← d.U₁_eq hd.two_le] at hPeq hPbot
  have hnorm : d.U₁ ≤ normalizer (d.A₃ : Set G) := d.U₁_le_N₁.trans d.N₁_le_normalizer_A₃
  have hmul : ((d.A₃ ⊔ d.U₁ : Subgroup G) : Set G) = (d.A₃ : Set G) * (d.U₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm
  exact s4o_card_inf_centralizer_mul (X := d.P) (A := d.A₃) (B := d.U₁) H d.A₃_le_P d.U₁_le_P
    hPbot
    (fun x hx => by
      have : x ∈ ((d.A₃ ⊔ d.U₁ : Subgroup G) : Set G) := hPeq ▸ hx
      rw [hmul] at this
      obtain ⟨a, ha, b, hb, hab⟩ := this
      exact ⟨a, ha, b, hb, hab.symm⟩)
    (hH.trans (fun i hi => hd.normalizer_B₁_inf_le_normalizer_A₃ (hd.I_le_normalizer_B₁ hi)))
    (hH.trans (s4o_I_le_normalizer_U₁ hd))

theorem Hyp.s4o_V₁_le_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V₁ ≤ d.E := by
  have hCF : d.F ⊓ centralizer (d.I₄ : Set G) ≤ d.E := by
    have h35 := (hd.sec3_5_one hGMS).2.2.1
    rw [← h35]
    exact (le_sup_right : (d.F ⊔ d.P) ⊓ centralizer (d.I₄ : Set G) ≤ d.W).trans d.W_le_E
  intro x hx
  rw [V₁, mem_map_conj_s] at hx
  have h1 := hCF hx
  have hs : d.s ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E d.s_mem_N₂
  have h2 := (mem_normalizer_iff.1 hs _).1 h1
  rwa [d.s_inv, d.s_conj_s_conj] at h2

theorem Hyp.s4o_cS (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {S : Subgroup G} (hS : S = d.D ⊔ d.V₁) (hV₁D : d.V₁ ≤ normalizer (d.D : Set G))
    (hDV : d.D ⊓ d.V₁ = ⊥) (hB₆ : d.B₆ = d.D ⊔ zpowers d.t) (htD : d.t ∉ d.D)
    {H : Subgroup G} (hH : H ≤ d.I) :
    Nat.card ↥(S ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.P ⊓ centralizer (H : Set G)) ^ 2 := by
  have hmul : ((d.D ⊔ d.V₁ : Subgroup G) : Set G) = (d.D : Set G) * (d.V₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hV₁D
  have key := s4o_card_inf_centralizer_mul (X := S) (A := d.D) (B := d.V₁) H
    (by rw [hS]; exact le_sup_left) (by rw [hS]; exact le_sup_right) hDV
    (fun x hx => by
      have : x ∈ ((d.D ⊔ d.V₁ : Subgroup G) : Set G) := hS ▸ hx
      rw [hmul] at this
      obtain ⟨a, ha, b, hb, hab⟩ := this
      exact ⟨a, ha, b, hb, hab.symm⟩)
    (hH.trans (hd.s2a2_I_le_D hGMS)) (hH.trans (hd.s4o_I_le_normalizer_V₁ hGMS))
  rw [key, hd.s4o_cD hGMS hB₆ htD hH, hd.s4o_cV₁ hGMS hH, hd.s4o_cP hH]
  ring

theorem sec3101Orders_of_hyp (hp : d.CaseHyp) (k : d.Know93) : d.Sec3101OrdersAll := by
  intro S hS hPS
  have hGMS := hp.gms
  have hd := hp.hyp
  have sa := k.s9a S hS hPS
  have se := k.s9e
  obtain ⟨hSED, hEchar, hDchar⟩ := k.s9_1 S hS hPS
  haveI : (d.E.subgroupOf S).Characteristic := hEchar
  haveI : (d.D.subgroupOf S).Characteristic := hDchar
  have hES : d.E ≤ S := hSED ▸ le_sup_left
  have hDS : d.D ≤ S := hSED ▸ le_sup_right
  have hSE : S ≤ normalizer (d.E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 inferInstance
  have hSD : S ≤ normalizer (d.D : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).1 inferInstance
  have hV₁S : d.V₁ ≤ S := (hd.s4o_V₁_le_E hGMS).trans hES
  have hV₁D : d.V₁ ≤ normalizer (d.D : Set G) := hV₁S.trans hSD
  have hDV : d.D ⊓ d.V₁ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ d.D ⊓ centralizer (d.I₁ : Set G) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, d.V₁_le_centralizer_I₁ (Subgroup.mem_inf.1 hx).2⟩
    rw [se.centralizer_I₁] at hx'
    exact hx'
  have hcI₂ : Nat.card ↥(S ⊓ centralizer (d.I₂ : Set G)) = (2 ^ f) ^ 6 := by
    rw [← sa.cD₂, hd.s4o_cD hGMS sa.B₆_eq se.t_not_mem_D d.I₂_le_I, (hd.s4o_A₃_inf_I₂).1,
      (hd.s4o_A₃_inf_I₂).2]
    ring
  have hcardS : Nat.card S = (2 ^ f) ^ 20 := by
    have key := Common.card_sup_mul_card_inf_eq (A := d.E) (B := S ⊓ centralizer (d.I₂ : Set G))
      (inf_le_left.trans hSE)
    rw [← sa.S_eq₂, sa.E_inf₂, Subgroup.card_bot, hd.card_E hGMS, hcI₂, mul_one] at key
    rw [key]
    ring
  have hSDV : S = d.D ⊔ d.V₁ := by
    have hle : d.D ⊔ d.V₁ ≤ S := sup_le hDS hV₁S
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have key := Common.card_sup_mul_card_inf_eq (A := d.D) (B := d.V₁) hV₁D
    rw [hDV, Subgroup.card_bot, se.card_D, hd.card_V₁ hGMS, mul_one] at key
    rw [hcardS, key]
    ring_nf
    exact le_rfl
  have hO4 : ∀ H : Subgroup G, H ≤ d.I → Nat.card ↥(S ⊓ centralizer (H : Set G)) =
      Nat.card ↥(d.P ⊓ centralizer (H : Set G)) ^ 2 := fun H hH =>
    hd.s4o_cS hGMS hSDV hV₁D hDV sa.B₆_eq se.t_not_mem_D hH
  refine ⟨hcardS, ?_, hcI₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hO4 _ d.I₁_le_I, ← d.U₁_eq hd.two_le, d.card_U₁]
    ring
  · rw [hO4 _ d.I₃_le_I, ← (d.sec2_1_two hd.two_le).1, d.card_Zp]
  · rw [hO4 _ d.I₄_le_I, hd.card_C₄]
    ring
  · rw [hO4 _ d.I₅_le_I, hd.card_C₅]
    ring
  · rw [hO4 _ (s2a2_I₆_le_I d), hd.s4o_P_inf_I₆, d.card_CPI₆]
  · rw [hO4 _ (inf_le_left.trans d.I₃_le_I), hd.s4o_card_C₃₆ hGMS]
    ring
  · rw [hd.s4o_cF hGMS d.I₅_le_I, hd.s4o_card_A₁_inf_C₅]

end Data

namespace CaseBParts

theorem sec3101Orders : Sec3101OrdersStatement :=
  fun _ _ _ _ _ _ _ _ hp k => Data.sec3101Orders_of_hyp hp k

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
