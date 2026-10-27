module

public import CFSG.LargeExtraspecial.S8A5I
public import CFSG.LargeExtraspecial.S8FiveC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

universe u

theorem eq_top_of_centralizer_le_center' {P : Type*} [Group P] [Finite P]
    (hP : IsExtraspecialPGroup 2 P) {D : Subgroup P} (hZ : center P ≤ D)
    (hC : ∀ x : P, (∀ d ∈ D, x * d = d * x) → x ∈ center P) : D = ⊤ := by
  let := CFSG.GroupTheory.extraspecialQuotientModule hP
  have : Module.Finite (ZMod 2) (Additive (Abelianization P)) := Module.Finite.of_finite
  set q := extraspecialQuadForm hP
  let W : Submodule (ZMod 2) (Additive (Abelianization P)) :=
    { carrier := (fun x : P => Additive.ofMul (Abelianization.of x)) '' D
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, D.mul_mem hx hy, ofMul_of_mul x y⟩
      zero_mem' := ⟨1, D.one_mem, by simp⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        rcases zmod2_cases c with rfl | rfl
        · exact ⟨1, D.one_mem, by simp⟩
        · exact ⟨x, hx, by simp⟩ }
  have hnd := extraspecialQuadForm_nondegenerate hP
  have hperp : LinearMap.BilinForm.orthogonal q.polarBilin W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := exists_ofMul_of v
    rw [Submodule.mem_bot, ofMul_of_eq_zero_iff hP]
    refine hC x fun d hd => ?_
    have h1 : polar q (Additive.ofMul (Abelianization.of d))
        (Additive.ofMul (Abelianization.of x)) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) _ ⟨d, hd, rfl⟩
    exact ((polar_extraspecialQuadForm_eq_zero_iff hP d x).mp h1).symm
  have hfin := LinearMap.BilinForm.finrank_orthogonal hnd W
  rw [hperp, finrank_bot] at hfin
  have hW : W = ⊤ := Submodule.eq_top_of_finrank_eq
    (le_antisymm (Submodule.finrank_le W) (by omega))
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : Additive.ofMul (Abelianization.of x) ∈ W := hW ▸ Submodule.mem_top
  obtain ⟨d, hd, hdx⟩ := hx
  have h0 : Additive.ofMul (Abelianization.of (d⁻¹ * x)) = 0 := by
    rw [ofMul_of_mul, ← hdx, ← ofMul_of_mul, inv_mul_cancel, map_one, ofMul_one]
  have hc := (ofMul_of_eq_zero_iff hP _).mp h0
  have := D.mul_mem hd (hZ hc)
  rwa [mul_inv_cancel_left] at this

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_zpowers_of_comm_mem_Rbar' (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : PairGen S g t)
    (hN0 : Nbar S g t = N0bar S g t) [NQHyp S g t] (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t))
    {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    {x : S.O} (hx : x ∈ Nbar S g t)
    (hfix : ∀ r ∈ Rbar S g t, r * x * r⁻¹ * x⁻¹ ∈ zpowers t) : x ∈ zpowers t := by
  have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hxa : x ∈ S.Lbar (((1 : S.M) : G) * g) :=
    mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb h1R hx fun l hl =>
      hfix l (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht h1R) hl)
  have hxb : x ∈ S.Lbar ((h : G) * g) :=
    mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb hh hx fun l hl =>
      hfix l (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht hh) hl)
  rw [OneMemClass.coe_one, one_mul] at hxa
  rw [← (timmesfeld_6_5_bar H C ht ht1 hVQ hgen hN0 hh hb).2]
  exact ⟨hxa, hxb⟩

theorem comm_mem_zpowers_of_centralizes' (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    [NQHyp S g t] (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (htN : t ∈ Nbar S g t)
    (ht1 : t ≠ 1) {x : S.O} (hx : x ∈ Nbar S g t)
    (hxD : ∀ d ∈ ⁅Rbar S g t, Rbar S g t⁆ ⊓ Nbar S g t, x * d = d * x) {r : S.O}
    (hr : r ∈ Rbar S g t) : r * x * r⁻¹ * x⁻¹ ∈ zpowers t := by
  obtain ⟨k, hkr⟩ : ∃ k : S.M, S.ρ k = r := Rbar_le_Mbar hr
  have hc0 : r * t = t * r := commute_of_mem_Rbar haQ hr
  have hc0' : r⁻¹ * t = t * r⁻¹ := by
    calc r⁻¹ * t = r⁻¹ * (t * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * t) * r⁻¹ := by rw [hc0]
      _ = t * r⁻¹ := by group
  have hxN' : r * x * r⁻¹ ∈ Nbar S g t := by
    have := conj_mem_Nbar haQ (k := k) (by rw [hkr]; exact hc0) hx
    rwa [hkr] at this
  have hconjN : ∀ v ∈ Nbar S g t, r⁻¹ * v * r ∈ Nbar S g t := fun v hv => by
    have := conj_mem_Nbar haQ (k := k⁻¹) (by rw [map_inv, hkr]; exact hc0') hv
    rwa [map_inv, hkr, inv_inv] at this
  have hzr : ∀ c ∈ zpowers t, c * r = r * c := by
    rintro c ⟨i, rfl⟩
    exact (Commute.zpow_left (show Commute t r from hc0.symm) i).eq
  have hzN : ∀ c ∈ zpowers t, ∀ v ∈ Nbar S g t, c * v = v * c := by
    rintro c ⟨i, rfl⟩ v hv
    exact (Commute.zpow_left
      (show Commute t v from (commute_of_mem_Rbar haQ (Nbar_le_Rbar hv)).symm) i).eq
  have hy : ∀ v ∈ Nbar S g t, (x⁻¹ * (r * x * r⁻¹)) * v = v * (x⁻¹ * (r * x * r⁻¹)) := by
    intro v hv
    have hw := hconjN v hv
    have hdR : v⁻¹ * (r⁻¹ * v * r) ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
      have := commutator_mem_commutator (inv_mem (Nbar_le_Rbar hv)) (inv_mem hr)
      rw [commutatorElement_def, inv_inv, inv_inv] at this
      simpa only [mul_assoc] using this
    have hd := hxD _ ⟨hdR, (Nbar S g t).mul_mem ((Nbar S g t).inv_mem hv) hw⟩
    have hc : x * v * x⁻¹ * v⁻¹ ∈ zpowers t := NQHyp.comm x hx v hv
    have hcr := hzr _ hc
    have e1 : x * v = (x * v * x⁻¹ * v⁻¹) * v * x := by group
    have e2 : x * (r⁻¹ * v * r) = (x * v * x⁻¹ * v⁻¹) * (r⁻¹ * v * r) * x := by
      calc x * (r⁻¹ * v * r) = x * v * (v⁻¹ * (r⁻¹ * v * r)) := by group
        _ = (x * v * x⁻¹ * v⁻¹) * v * x * (v⁻¹ * (r⁻¹ * v * r)) := by rw [← e1]
        _ = (x * v * x⁻¹ * v⁻¹) * v * (x * (v⁻¹ * (r⁻¹ * v * r))) := by group
        _ = (x * v * x⁻¹ * v⁻¹) * v * ((v⁻¹ * (r⁻¹ * v * r)) * x) := by rw [hd]
        _ = (x * v * x⁻¹ * v⁻¹) * (r⁻¹ * v * r) * x := by group
    have e3 : r * x * r⁻¹ * v = (x * v * x⁻¹ * v⁻¹) * v * (r * x * r⁻¹) := by
      calc r * x * r⁻¹ * v = r * (x * (r⁻¹ * v * r)) * r⁻¹ := by group
        _ = r * ((x * v * x⁻¹ * v⁻¹) * (r⁻¹ * v * r) * x) * r⁻¹ := by rw [e2]
        _ = (r * (x * v * x⁻¹ * v⁻¹)) * (r⁻¹ * v * r) * x * r⁻¹ := by group
        _ = ((x * v * x⁻¹ * v⁻¹) * r) * (r⁻¹ * v * r) * x * r⁻¹ := by rw [hcr]
        _ = (x * v * x⁻¹ * v⁻¹) * v * (r * x * r⁻¹) := by group
    calc x⁻¹ * (r * x * r⁻¹) * v = x⁻¹ * (r * x * r⁻¹ * v) := by group
      _ = x⁻¹ * ((x * v * x⁻¹ * v⁻¹) * v * (r * x * r⁻¹)) := by rw [e3]
      _ = v * (x⁻¹ * (r * x * r⁻¹)) := by group
  have hyN : x⁻¹ * (r * x * r⁻¹) ∈ Nbar S g t := mul_mem (inv_mem hx) hxN'
  have hyc : (⟨_, hyN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (hy v v.2).symm
  have htc : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar v.2))
  have hyt : x⁻¹ * (r * x * r⁻¹) ∈ zpowers t := by
    by_cases hy1 : (⟨_, hyN⟩ : Nbar S g t) = 1
    · have h1 : x⁻¹ * (r * x * r⁻¹) = 1 := congrArg Subtype.val hy1
      rw [h1]
      exact one_mem _
    · have ht1' : (⟨t, htN⟩ : Nbar S g t) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
      have h1 : x⁻¹ * (r * x * r⁻¹) = t :=
        congrArg Subtype.val (eq_of_mem_center hext hyc htc hy1 ht1')
      rw [h1]
      exact mem_zpowers t
  have hcomm := hzN _ hyt x hx
  have e : r * x * r⁻¹ * x⁻¹ = x⁻¹ * (r * x * r⁻¹) := by
    calc r * x * r⁻¹ * x⁻¹ = x * (x⁻¹ * (r * x * r⁻¹)) * x⁻¹ := by group
      _ = (x⁻¹ * (r * x * r⁻¹)) * x * x⁻¹ := by rw [← hcomm]
      _ = x⁻¹ * (r * x * r⁻¹) := by group
  rw [e]
  exact hyt

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem commutator_Rbar_eq_A5 (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2) (hmin : D.IsMinus)
    (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t := by
  have haQ := H.conj_mem
  have hext := timmesfeld_8_5 hNo hΩ D hA7
  obtain ⟨hs, hnc⟩ : IsSimpleGroup (RmodN S g t) ∧ ¬ ∀ x y : RmodN S g t, x * y = y * x := by
    rw [D.hX]
    refine isSimpleGroup_omegaGroup_minus_four D.hQ (by rw [D.hdim, hm2]) fun U hU => ?_
    by_contra hcon
    push Not at hcon
    have := hmin U hcon
    omega
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ D.hgen D.hN0 D.hh D.hb
  have h3 := D.three_le_finrank
  have hNR : Nbar S g t ≤ Rbar S g t := fun _ hx => Nbar_le_Rbar hx
  have htN : t ∈ Nbar S g t := self_mem_Nbar H ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htR : t ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
    obtain ⟨a, b, hab⟩ : ∃ a b : Nbar S g t, a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have hc : commutator (Nbar S g t) = ⊥ :=
        (commutator_eq_bot_iff _).mpr ⟨⟨fun a b => hcon a b⟩⟩
      have h2 := hext.2.2.2
      rw [← hext.2.1, hc, card_bot] at h2
      exact absurd h2 (by norm_num)
    have hc : (a : S.O) * b * (a : S.O)⁻¹ * (b : S.O)⁻¹ ∈ zpowers t :=
      NQHyp.comm _ a.2 _ b.2
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hc with h1 | h1
    · exfalso
      apply hab
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (a : S.O) * b = ((a : S.O) * b * (a : S.O)⁻¹ * (b : S.O)⁻¹) * b * a := by group
        _ = b * a := by rw [h1, one_mul]
    · have := commutator_mem_commutator (hNR a.2) (hNR b.2)
      rwa [commutatorElement_def, h1] at this
  set Dn := (⁅Rbar S g t, Rbar S g t⁆ ⊓ Nbar S g t).subgroupOf (Nbar S g t) with hDdef
  have htc : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar v.2))
  have ht1' : (⟨t, htN⟩ : Nbar S g t) ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  have hZ : center (Nbar S g t) ≤ Dn := by
    intro z hz
    rw [hDdef, mem_subgroupOf]
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    · rw [eq_of_mem_center hext hz htc hz1 ht1']
      exact ⟨htR, htN⟩
  have hCen : ∀ x : Nbar S g t, (∀ d ∈ Dn, x * d = d * x) → x ∈ center (Nbar S g t) := by
    intro x hxd
    have hxD : ∀ d ∈ ⁅Rbar S g t, Rbar S g t⁆ ⊓ Nbar S g t, (x : S.O) * d = d * x := by
      intro d hd
      have := congrArg Subtype.val (hxd ⟨d, hd.2⟩ (mem_subgroupOf.mpr hd))
      simpa only [Subgroup.coe_mul] using this
    have hxt := mem_zpowers_of_comm_mem_Rbar' H C ht ht1 hVQ D.hgen D.hN0 h3 D.hh D.hb x.2
      fun r hr => comm_mem_zpowers_of_centralizes' haQ hext htN ht1 x.2 hxD hr
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hxt with h1 | h1
    · rw [show x = 1 from Subtype.ext h1]
      exact one_mem _
    · rw [show x = ⟨t, htN⟩ from Subtype.ext h1]
      exact htc
  have hD := eq_top_of_centralizer_le_center' hext hZ hCen
  have hNR' : Nbar S g t ≤ ⁅Rbar S g t, Rbar S g t⁆ := fun x hx => by
    have : (⟨x, hx⟩ : Nbar S g t) ∈ Dn := hD ▸ mem_top _
    exact (mem_subgroupOf.mp this).1
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact (Rbar_le_commutator_sup_Nbar' haQ hs hnc).trans (sup_le le_rfl hNR')

end CFSG.LargeExtraspecial.S8
