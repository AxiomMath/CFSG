module

public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S8CorBApply

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial.S4
open CFSG.RankThree.Literature.FSmith

theorem eq_top_of_centralizer_le_center {P : Type*} [Group P] [Finite P]
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

theorem map_subtype_commutator {X : Type*} [Group X] (K : Subgroup X) :
    (commutator K).map K.subtype = ⁅K, K⁆ := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Rbar_le_commutator_sup_Nbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hs : IsSimpleGroup (RmodN S g t)) (hnab : ¬ IsMulCommutative (RmodN S g t)) :
    Rbar S g t ≤ ⁅Rbar S g t, Rbar S g t⁆ ⊔ Nbar S g t := by
  have hperf : ⁅RmodN S g t, RmodN S g t⁆ = RmodN S g t := by
    rw [← map_subtype_commutator, CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup hs hnab,
      ← MonoidHom.range_eq_map, range_subtype]
  have himg : (commutator (Rbar S g t)).map (resV haQ t) = RmodN S g t := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_resV, hperf]
  intro r hr
  have hmem : resV haQ t ⟨r, hr⟩ ∈ (commutator (Rbar S g t)).map (resV haQ t) := by
    rw [himg, ← range_resV haQ t]
    exact ⟨⟨r, hr⟩, rfl⟩
  obtain ⟨c, hc, hcr⟩ := hmem
  have h1 : resV haQ t (c⁻¹ * ⟨r, hr⟩) = 1 := by rw [map_mul, map_inv, hcr, inv_mul_cancel]
  rw [resV_eq_one_iff] at h1
  have hc' : (c : S.O) ∈ ⁅Rbar S g t, Rbar S g t⁆ := by
    rw [← map_subtype_commutator]
    exact ⟨c, hc, rfl⟩
  have e : r = (c : S.O) * ((c⁻¹ * ⟨r, hr⟩ : Rbar S g t) : S.O) := by simp
  rw [e]
  exact mul_mem (mem_sup_left hc') (mem_sup_right h1)

theorem mem_zpowers_of_comm_mem_Rbar (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hgen : S6.PairGen S g t)
    (hN0 : Nbar S g t = N0bar S g t) [S6.NQHyp S g t] (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t))
    {h : S.M} (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
    {x : S.O} (hx : x ∈ Nbar S g t)
    (hfix : ∀ r ∈ Rbar S g t, r * x * r⁻¹ * x⁻¹ ∈ zpowers t) : x ∈ zpowers t := by
  have h1R : S.ρ 1 ∈ Rbar S g t := by rw [map_one]; exact one_mem _
  have hxa : x ∈ S.Lbar (((1 : S.M) : G) * g) :=
    S6.mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb h1R hx fun l hl =>
      hfix l (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht h1R) hl)
  have hxb : x ∈ S.Lbar ((h : G) * g) :=
    S6.mem_Lbar_of_comm_mem H C ht ht1 hVQ hgen hN0 h3 hh hb hh hx fun l hl =>
      hfix l (Lbar_mul_le_Rbar (mem_Lbar_mul_of_mem_Rbar H ht hh) hl)
  rw [OneMemClass.coe_one, one_mul] at hxa
  rw [← (S6.timmesfeld_6_5_bar H C ht ht1 hVQ hgen hN0 hh hb).2]
  exact ⟨hxa, hxb⟩

theorem comm_mem_zpowers_of_centralizes (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    [S6.NQHyp S g t] (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (htN : t ∈ Nbar S g t)
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
    have hc : x * v * x⁻¹ * v⁻¹ ∈ zpowers t := S6.NQHyp.comm x hx v hv
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

theorem commutator_Rbar_eq_of_case (hCE : CentralExtInput.{0}) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) (hext : IsExtraspecialPGroup 2 (Nbar S g t)) :
    ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t := by
  have haQ := H.conj_mem
  have hgen : S6.PairGen S g t := hcase.elim (S6.pairGen_of_omegaCase H hNo C ht ht1 hVQ)
    (S6.pairGen_of_spCase H C ht ht1 hVQ)
  have hN0 : Nbar S g t = N0bar S g t :=
    hcase.elim (S6.Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ)
      (S6.Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ)
  obtain ⟨hs, hnab2⟩ : IsSimpleGroup (RmodN S g t) ∧ S5.NonabelianSylowTwo (RmodN S g t) :=
    hcase.elim (fun hΩ => (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6)
      (fun hSp => (S45Q.hyp45Q H C).sp ht ht1 hVQ hSp h6)
  have : Finite (RmodN S g t) := by
    rw [← range_resV haQ t]
    exact Finite.of_surjective _ (resV haQ t).rangeRestrict_surjective
  have hnab : ¬ IsMulCommutative (RmodN S g t) := by
    intro hcomm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, -, y, -, hxy⟩ := S8.exists_noncomm_of_nonabelianSylowTwo (MulEquiv.refl _) hnab2
      (Sylow.nonempty (p := 2) (G := RmodN S g t)).some
    exact hxy (hcomm.is_comm.comm x y)
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  have : S6.NQHyp S g t := S6.timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by omega
  have hNR : Nbar S g t ≤ Rbar S g t := fun _ hx => Nbar_le_Rbar hx
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar H ht
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
      S6.NQHyp.comm _ a.2 _ b.2
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hc with h1 | h1
    · exfalso
      apply hab
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (a : S.O) * b = ((a : S.O) * b * (a : S.O)⁻¹ * (b : S.O)⁻¹) * b * a := by group
        _ = b * a := by rw [h1, one_mul]
    · have := commutator_mem_commutator (hNR a.2) (hNR b.2)
      rwa [commutatorElement_def, h1] at this
  set D := (⁅Rbar S g t, Rbar S g t⁆ ⊓ Nbar S g t).subgroupOf (Nbar S g t) with hDdef
  have htc : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (commute_of_mem_Rbar haQ (Nbar_le_Rbar v.2))
  have ht1' : (⟨t, htN⟩ : Nbar S g t) ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  have hZ : center (Nbar S g t) ≤ D := by
    intro z hz
    rw [hDdef, mem_subgroupOf]
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    · rw [eq_of_mem_center hext hz htc hz1 ht1']
      exact ⟨htR, htN⟩
  have hCen : ∀ x : Nbar S g t, (∀ d ∈ D, x * d = d * x) → x ∈ center (Nbar S g t) := by
    intro x hxd
    have hxD : ∀ d ∈ ⁅Rbar S g t, Rbar S g t⁆ ⊓ Nbar S g t, (x : S.O) * d = d * x := by
      intro d hd
      have := congrArg Subtype.val (hxd ⟨d, hd.2⟩ (mem_subgroupOf.mpr hd))
      simpa only [Subgroup.coe_mul] using this
    have hxt := mem_zpowers_of_comm_mem_Rbar H C ht ht1 hVQ hgen hN0 h3 hh hb x.2
      fun r hr => comm_mem_zpowers_of_centralizes haQ hext htN ht1 x.2 hxD hr
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hxt with h1 | h1
    · rw [show x = 1 from Subtype.ext h1]
      exact one_mem _
    · rw [show x = ⟨t, htN⟩ from Subtype.ext h1]
      exact htc
  have hD := eq_top_of_centralizer_le_center hext hZ hCen
  have hNR' : Nbar S g t ≤ ⁅Rbar S g t, Rbar S g t⁆ := fun x hx => by
    have : (⟨x, hx⟩ : Nbar S g t) ∈ D := hD ▸ mem_top _
    exact (mem_subgroupOf.mp this).1
  refine le_antisymm (commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · exact (Rbar_le_commutator_sup_Nbar haQ hs hnab).trans (sup_le le_rfl hNR')

theorem rbarPerfectStmt_of (hCE : CentralExtInput.{0}) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
      (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
        ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t := by
  intro G _ _ _ S g t c hSt hocc hext
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  have hΩ : ∀ d, 6 ≤ d → RNOmega S g t d → ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩
    exact commutator_Rbar_eq_of_case hCE H hNo C ht ht1 hVQ (Or.inl hΩ) (by omega) hext
  have hSp : ∀ d, 6 ≤ d → RNSp S g t d → ⁅Rbar S g t, Rbar S g t⁆ = Rbar S g t := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩
    exact commutator_Rbar_eq_of_case hCE H hNo C ht ht1 hVQ (Or.inr hSp) (by omega) hext
  obtain ⟨hh, -, -⟩ := hocc
  cases c with
  | omegaMinus8 => exact hΩ 8 (by norm_num) hh.1
  | omegaMinus6 => exact hΩ 6 (by norm_num) hh.1
  | omegaPlus12 => exact hΩ 12 (by norm_num) hh.1
  | omegaPlus10 => exact hΩ 10 (by norm_num) hh.1
  | omegaPlus8a => exact hΩ 8 (by norm_num) hh.1
  | omegaPlus8b => exact hΩ 8 (by norm_num) hh.1
  | omegaPlus6 => exact hΩ 6 (by norm_num) hh.1
  | sp6 => exact hSp 6 (by norm_num) hh
  | sp8 => exact hSp 8 (by norm_num) hh

end CFSG.LargeExtraspecial.S14
