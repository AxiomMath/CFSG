module

public import CFSG.LargeExtraspecial.S14Perfect
public import CFSG.LargeExtraspecial.S14Claims

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial.S4
open CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

@[expose] noncomputable def ind1 {X : Type*} [Group X] (c : X) : ZMod 2 :=
  open Classical in if c = 1 then 0 else 1

theorem ind1_mul {X : Type*} [Group X] {t c d : X} (htt : t * t = 1) (hc : c ∈ zpowers t)
    (hd : d ∈ zpowers t) : ind1 (c * d) = ind1 c + ind1 d := by
  rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hc with h1 | h1 <;>
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hd with h2 | h2 <;>
    rw [h1, h2]
  · simp [ind1]
  · rw [one_mul]
    simp [ind1]
  · rw [mul_one]
    simp [ind1]
  · rw [htt]
    simp only [ind1]
    split_ifs <;> decide

theorem exists_conj_eq_of_comm_mem_zpowers {X : Type*} [Group X] {N : Subgroup X} [Finite N]
    (hN : IsExtraspecialPGroup 2 N) {t : X} (htN : t ∈ N) (htt : t * t = 1) (ht1 : t ≠ 1)
    (htc : ∀ y ∈ N, t * y = y * t) {g : X} (hg : ∀ y ∈ N, g * y * g⁻¹ * y⁻¹ ∈ zpowers t) :
    ∃ u ∈ N, ∀ y ∈ N, g * y * g⁻¹ = u * y * u⁻¹ := by
  classical
  let := CFSG.GroupTheory.extraspecialQuotientModule hN
  have hzN : zpowers t ≤ N := zpowers_le.mpr htN
  have hzc : ∀ c ∈ zpowers t, ∀ y ∈ N, c * y = y * c := by
    rintro c ⟨i, rfl⟩ y hy
    exact (Commute.zpow_left (show Commute t y from htc y hy) i).eq
  let μ : N →* Multiplicative (ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (ind1 (g * (y : X) * g⁻¹ * (y : X)⁻¹))
      map_one' := by simp [ind1]
      map_mul' := fun y y' => by
        have e : g * ((y : X) * y') * g⁻¹ * ((y : X) * y')⁻¹ =
            (g * (y : X) * g⁻¹ * (y : X)⁻¹) * (g * (y' : X) * g⁻¹ * (y' : X)⁻¹) := by
          have hc := hzc _ (hg y' y'.2) y y.2
          calc g * ((y : X) * y') * g⁻¹ * ((y : X) * y')⁻¹ =
              (g * (y : X) * g⁻¹ * (y : X)⁻¹) * ((y : X) * (g * (y' : X) * g⁻¹ * (y' : X)⁻¹)) *
                (y : X)⁻¹ := by group
            _ = (g * (y : X) * g⁻¹ * (y : X)⁻¹) * ((g * (y' : X) * g⁻¹ * (y' : X)⁻¹) * (y : X)) *
                (y : X)⁻¹ := by rw [hc]
            _ = _ := by group
        rw [Subgroup.coe_mul, e, ind1_mul htt (hg y y.2) (hg y' y'.2), ofAdd_add] }
  let μ' : Additive (Abelianization N) →+ ZMod 2 := MonoidHom.toAdditive (Abelianization.lift μ)
  have : Module.Finite (ZMod 2) (Additive (Abelianization N)) := Module.Finite.of_finite
  obtain ⟨u, hu⟩ := (LinearMap.BilinForm.toDual (extraspecialQuadForm hN).polarBilin
    (extraspecialQuadForm_nondegenerate hN)).surjective (AddMonoidHom.toZModLinearMap 2 μ')
  obtain ⟨q₀, rfl⟩ := exists_ofMul_of u
  have htc' : (⟨t, htN⟩ : N) ∈ center N := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (htc y y.2).symm
  have ht1' : (⟨t, htN⟩ : N) ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  refine ⟨q₀, q₀.2, fun y hy => ?_⟩
  have h := LinearMap.congr_fun hu (Additive.ofMul (Abelianization.of (⟨y, hy⟩ : N)))
  rw [LinearMap.BilinForm.toDual_def, polarBilin_apply_apply,
    polar_extraspecialQuadForm_apply] at h
  have h' : ind ⁅q₀, (⟨y, hy⟩ : N)⁆ = ind1 (g * y * g⁻¹ * y⁻¹) := h
  have hc1 : ((⁅q₀, (⟨y, hy⟩ : N)⁆ : N) : X) ∈ zpowers t := by
    have hz := commutatorElement_mem_center hN q₀ ⟨y, hy⟩
    by_cases h1 : ⁅q₀, (⟨y, hy⟩ : N)⁆ = 1
    · rw [h1]
      exact one_mem _
    · rw [eq_of_mem_center hN hz htc' h1 ht1']
      exact mem_zpowers t
  have hkey : ((⁅q₀, (⟨y, hy⟩ : N)⁆ : N) : X) = g * y * g⁻¹ * y⁻¹ := by
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hc1 with h1 | h1 <;>
      rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp (hg y hy) with h2 | h2
    · rw [h1, h2]
    · exfalso
      have e1 : ⁅q₀, (⟨y, hy⟩ : N)⁆ = 1 := Subtype.ext h1
      have h0 : ind1 t = 1 := by simp [ind1, ht1]
      rw [e1, ind_one, h2, h0] at h'
      exact absurd h' (by decide)
    · exfalso
      have e1 : ⁅q₀, (⟨y, hy⟩ : N)⁆ ≠ 1 := fun e => ht1 (by rw [← h1, e]; rfl)
      have h0 : ind1 (1 : X) = 0 := by simp [ind1]
      rw [h2, h0] at h'
      exact e1 ((ind_eq_zero_iff).mp h')
    · rw [h1, h2]
  have hk : (q₀ : X) * y * (q₀ : X)⁻¹ * y⁻¹ = g * y * g⁻¹ * y⁻¹ := by
    rw [← hkey]
    simp [commutatorElement_def]
  calc g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    _ = ((q₀ : X) * y * (q₀ : X)⁻¹ * y⁻¹) * y := by rw [hk]
    _ = (q₀ : X) * y * (q₀ : X)⁻¹ := by group

theorem commutator_eq_bot_of_forall_mem_zpowers {X : Type*} [Group X] {N : Subgroup X} {t : X}
    (htt : t * t = 1) (hall : ∀ n ∈ N, n ∈ zpowers t) : commutator N = ⊥ := by
  refine (commutator_eq_bot_iff _).mpr ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp (hall a a.2) with h1 | h1 <;>
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp (hall b b.2) with h2 | h2 <;>
    simp [Subgroup.coe_mul, h1, h2]

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

@[expose] def CentRbarStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O)
    (c : Config), Stage S g t → c.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      ∀ x ∈ S.Mbar, (∀ r ∈ Rbar S g t, x * r = r * x) → x ∈ zpowers t

theorem case_of_occurs {t : S.O} {c : Config} (hocc : c.Occurs S g t) :
    ∃ (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
      (hVQ : ¬ V S g t ≤ S.Qa g), (OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ) ∧
        6 ≤ finrank (ZMod 2) (Vt S g t) := by
  have hΩ : ∀ d, 6 ≤ d → RNOmega S g t d → ∃ (H : Hyp4 S g) (C : Cons311 S g)
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      (OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ) ∧ 6 ≤ finrank (ZMod 2) (Vt S g t) := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩
    exact ⟨H, C, ht, ht1, hVQ, Or.inl hΩ, by omega⟩
  have hSp : ∀ d, 6 ≤ d → RNSp S g t d → ∃ (H : Hyp4 S g) (C : Cons311 S g)
      (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g),
      (OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ) ∧ 6 ≤ finrank (ZMod 2) (Vt S g t) := by
    rintro d hd ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩
    exact ⟨H, C, ht, ht1, hVQ, Or.inr hSp, by omega⟩
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

theorem conj_mem_Nbar_of_mem_Rbar (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x y : S.O}
    (hx : x ∈ Rbar S g t) (hy : y ∈ Nbar S g t) : x * y * x⁻¹ ∈ Nbar S g t := by
  obtain ⟨k, rfl⟩ : ∃ k : S.M, S.ρ k = x := Rbar_le_Mbar hx
  exact conj_mem_Nbar haQ (commute_of_mem_Rbar haQ hx) hy

@[expose] noncomputable def kerNQ (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    Subgroup (Rbar S g t) where
  carrier := {r | ∀ y ∈ Nbar S g t, (r : S.O) * y * (r : S.O)⁻¹ * y⁻¹ ∈ zpowers t}
  one_mem' := fun y _ => by simp
  mul_mem' := by
    intro r s hr hs y hy
    have hsy := hs y hy
    have hc : (r : S.O) * ((s : S.O) * y * (s : S.O)⁻¹ * y⁻¹) * (r : S.O)⁻¹ =
        (s : S.O) * y * (s : S.O)⁻¹ * y⁻¹ := by
      obtain ⟨i, hi⟩ := hsy
      rw [← hi, (Commute.zpow_right (show Commute (r : S.O) t from
        commute_of_mem_Rbar haQ r.2) i).eq, mul_inv_cancel_right]
    have e : ((r * s : Rbar S g t) : S.O) * y * ((r * s : Rbar S g t) : S.O)⁻¹ * y⁻¹ =
        ((r : S.O) * ((s : S.O) * y * (s : S.O)⁻¹ * y⁻¹) * (r : S.O)⁻¹) *
          ((r : S.O) * y * (r : S.O)⁻¹ * y⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    rw [e, hc]
    exact mul_mem hsy (hr y hy)
  inv_mem' := by
    intro r hr y hy
    have hy' := hr _ (conj_mem_Nbar_of_mem_Rbar haQ (inv_mem r.2) hy)
    have e : ((r⁻¹ : Rbar S g t) : S.O) * y * ((r⁻¹ : Rbar S g t) : S.O)⁻¹ * y⁻¹ =
        ((r : S.O) * ((r : S.O)⁻¹ * y * (r : S.O)⁻¹⁻¹) * (r : S.O)⁻¹ *
          ((r : S.O)⁻¹ * y * (r : S.O)⁻¹⁻¹)⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]
      group
    rw [e]
    exact inv_mem hy'

theorem kerNQ_normal (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) : (kerNQ haQ t).Normal := by
  refine ⟨fun k hk x y hy => ?_⟩
  have hy' := conj_mem_Nbar_of_mem_Rbar haQ (inv_mem x.2) hy
  have hc := hk _ hy'
  obtain ⟨i, hi⟩ := hc
  have hcx : (x : S.O) * t ^ i * (x : S.O)⁻¹ = t ^ i := by
    rw [(Commute.zpow_right (show Commute (x : S.O) t from commute_of_mem_Rbar haQ x.2) i).eq,
      mul_inv_cancel_right]
  have e : ((x * k * x⁻¹ : Rbar S g t) : S.O) * y * ((x * k * x⁻¹ : Rbar S g t) : S.O)⁻¹ * y⁻¹ =
      (x : S.O) * ((k : S.O) * ((x : S.O)⁻¹ * y * (x : S.O)⁻¹⁻¹) * (k : S.O)⁻¹ *
        ((x : S.O)⁻¹ * y * (x : S.O)⁻¹⁻¹)⁻¹) * (x : S.O)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, ← hi, hcx]
  exact zpow_mem_zpowers t i

theorem mem_Nbar_of_comm_mem (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    {r : S.O} (hr : r ∈ Rbar S g t)
    (hrN : ∀ y ∈ Nbar S g t, r * y * r⁻¹ * y⁻¹ ∈ zpowers t) : r ∈ Nbar S g t := by
  have haQ := H.conj_mem
  have hgen : S6.PairGen S g t := hcase.elim (S6.pairGen_of_omegaCase H hNo C ht ht1 hVQ)
    (S6.pairGen_of_spCase H C ht ht1 hVQ)
  have hN0 : Nbar S g t = N0bar S g t :=
    hcase.elim (S6.Nbar_eq_N0bar_of_omegaCase hCE H hNo C ht ht1 hVQ)
      (S6.Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ)
  obtain ⟨hs, -⟩ : IsSimpleGroup (RmodN S g t) ∧ S5.NonabelianSylowTwo (RmodN S g t) :=
    hcase.elim (fun hΩ => (S45Q.hyp45Q H C).omega ht ht1 hVQ hΩ h6)
      (fun hSp => (S45Q.hyp45Q H C).sp ht ht1 hVQ hSp h6)
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  have : S6.NQHyp S g t := S6.timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by omega
  have hNK : ∀ x : Rbar S g t, (x : S.O) ∈ Nbar S g t → x ∈ kerNQ haQ t :=
    fun x hx y hy => S6.NQHyp.comm _ hx _ hy
  have hs' : IsSimpleGroup (resV haQ t).range :=
    (MulEquiv.isSimpleGroup_congr (MulEquiv.subgroupCongr (range_resV haQ t))).mpr hs
  have hKn : ((kerNQ haQ t).map (resV haQ t).rangeRestrict).Normal :=
    (kerNQ_normal haQ t).map _ (resV haQ t).rangeRestrict_surjective
  have hlift : ∀ x : Rbar S g t, (resV haQ t).rangeRestrict x ∈
      (kerNQ haQ t).map (resV haQ t).rangeRestrict → x ∈ kerNQ haQ t := by
    rintro x ⟨k, hk, hkx⟩
    have h1 : resV haQ t (k⁻¹ * x) = 1 := by
      have := congrArg Subtype.val hkx
      simp only [MonoidHom.coe_rangeRestrict] at this
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 := hNK _ ((resV_eq_one_iff haQ _).mp h1)
    have := mul_mem hk h2
    rwa [mul_inv_cancel_left] at this
  rcases hs'.eq_bot_or_eq_top_of_normal ((kerNQ haQ t).map (resV haQ t).rangeRestrict) with
    hbot | htop
  · have h1 : (resV haQ t).rangeRestrict ⟨r, hr⟩ = 1 := by
      have : (resV haQ t).rangeRestrict ⟨r, hr⟩ ∈
          (kerNQ haQ t).map (resV haQ t).rangeRestrict := ⟨⟨r, hr⟩, hrN, rfl⟩
      rwa [hbot, mem_bot] at this
    have h2 : resV haQ t ⟨r, hr⟩ = 1 := by
      have := congrArg Subtype.val h1
      simpa only [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one] using this
    exact (resV_eq_one_iff haQ _).mp h2
  · exfalso
    have hall : ∀ n ∈ Nbar S g t, n ∈ zpowers t := fun n hn =>
      mem_zpowers_of_comm_mem_Rbar H C ht ht1 hVQ hgen hN0 h3 hh hb hn fun x hx =>
        hlift ⟨x, hx⟩ (by rw [htop]; exact mem_top _) n hn
    have hc : commutator (Nbar S g t) = ⊥ :=
      commutator_eq_bot_of_forall_mem_zpowers (mul_self_of_mem_Lbar S haQ ht) hall
    have h2 := hext.2.2.2
    rw [← hext.2.1, hc, card_bot] at h2
    exact absurd h2 (by norm_num)

theorem commutator_eq_top_of_perfect {X : Type*} [Group X] {K : Subgroup X} (hK : ⁅K, K⁆ = K) :
    commutator K = ⊤ := by
  apply map_injective K.subtype_injective
  rw [map_subtype_commutator, hK, ← MonoidHom.range_eq_map, range_subtype]

theorem mem_Nbar_of_centralizes_quotient [IsSimpleGroup G] (hCE : CentralExtInput.{0})
    (hcent : CentRbarStmt) {t : S.O} {c : Config} (hSt : Stage S g t) (hocc : c.Occurs S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) {x : S.O} (hx : x ∈ S.Mbar)
    (hxN : ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) : x ∈ Nbar S g t := by
  obtain ⟨H, C, ht, ht1, hVQ, hcase, h6⟩ := case_of_occurs hocc
  have haQ := H.conj_mem
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  have hperf := rbarPerfectStmt_of hCE G S g t c hSt hocc hext
  have htN := S6.self_mem_Nbar H ht
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have htc' : (⟨t, htN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
    rw [mem_center_iff]
    intro v
    exact Subtype.ext (htc v v.2).symm
  have ht1' : (⟨t, htN⟩ : Nbar S g t) ≠ 1 := fun e => ht1 (congrArg Subtype.val e)
  obtain ⟨u, huN, hu⟩ := exists_conj_eq_of_comm_mem_zpowers hext htN htt ht1 htc hxN
  have huR : u ∈ Rbar S g t := Nbar_le_Rbar huN
  have hx'M : u⁻¹ * x ∈ S.Mbar := mul_mem (inv_mem (Rbar_le_Mbar huR)) hx
  have hx'c : ∀ y ∈ Nbar S g t, u⁻¹ * x * y = y * (u⁻¹ * x) := fun y hy => by
    calc u⁻¹ * x * y = u⁻¹ * (x * y * x⁻¹) * x := by group
      _ = u⁻¹ * (u * y * u⁻¹) * x := by rw [hu y hy]
      _ = y * (u⁻¹ * x) := by group
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = u⁻¹ * x := id hx'M
  have hkt : S.ρ k * t = t * S.ρ k := by rw [hk]; exact hx'c t htN
  have hf : ∀ r ∈ Rbar S g t, r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ ∈ zpowers t := by
    intro r hr
    have hR : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ ∈ Rbar S g t := by
      have h1 := conj_mem_Rbar hkt (inv_mem hr)
      rw [hk] at h1
      have := mul_mem hr h1
      simpa only [mul_assoc] using this
    have hC : ∀ y ∈ Nbar S g t, (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) * y =
        y * (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) := by
      intro y hy
      have hw := conj_mem_Nbar_of_mem_Rbar haQ (inv_mem hr) hy
      rw [inv_inv] at hw
      have h1 := hx'c _ hw
      have h2 := hx'c y hy
      have h3 : (u⁻¹ * x)⁻¹ * y = y * (u⁻¹ * x)⁻¹ := by
        calc (u⁻¹ * x)⁻¹ * y = (u⁻¹ * x)⁻¹ * (y * (u⁻¹ * x)) * (u⁻¹ * x)⁻¹ := by group
          _ = (u⁻¹ * x)⁻¹ * (u⁻¹ * x * y) * (u⁻¹ * x)⁻¹ := by rw [h2]
          _ = y * (u⁻¹ * x)⁻¹ := by group
      calc (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) * y =
          r * (u⁻¹ * x) * r⁻¹ * ((u⁻¹ * x)⁻¹ * y) := by group
        _ = r * (u⁻¹ * x) * r⁻¹ * (y * (u⁻¹ * x)⁻¹) := by rw [h3]
        _ = r * ((u⁻¹ * x) * (r⁻¹ * y * r)) * r⁻¹ * (u⁻¹ * x)⁻¹ := by group
        _ = r * ((r⁻¹ * y * r) * (u⁻¹ * x)) * r⁻¹ * (u⁻¹ * x)⁻¹ := by rw [h1]
        _ = y * (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) := by group
    have hN := mem_Nbar_of_comm_mem hCE H hNo C ht ht1 hVQ hcase h6 hext hR fun y hy => by
      have e : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ * y *
          (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹)⁻¹ * y⁻¹ = 1 := by
        rw [hC y hy]
        group
      rw [e]
      exact one_mem _
    have hz : (⟨_, hN⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
      rw [mem_center_iff]
      intro v
      exact Subtype.ext (hC v v.2).symm
    by_cases h1 : (⟨_, hN⟩ : Nbar S g t) = 1
    · have h2 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = 1 := congrArg Subtype.val h1
      rw [h2]
      exact one_mem _
    · have h2 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = t :=
        congrArg Subtype.val (eq_of_mem_center hext hz htc' h1 ht1')
      rw [h2]
      exact mem_zpowers t
  have hzr : ∀ e ∈ zpowers t, ∀ r ∈ Rbar S g t, r * e * r⁻¹ = e := by
    rintro e ⟨i, rfl⟩ r hr
    rw [(Commute.zpow_right (show Commute r t from commute_of_mem_Rbar haQ hr) i).eq,
      mul_inv_cancel_right]
  let ψ : Rbar S g t →* Multiplicative (ZMod 2) :=
    { toFun := fun r => Multiplicative.ofAdd
        (ind1 ((r : S.O) * (u⁻¹ * x) * (r : S.O)⁻¹ * (u⁻¹ * x)⁻¹))
      map_one' := by simp [ind1]
      map_mul' := fun r s => by
        have e : ((r * s : Rbar S g t) : S.O) * (u⁻¹ * x) * ((r * s : Rbar S g t) : S.O)⁻¹ *
            (u⁻¹ * x)⁻¹ = ((r : S.O) * ((s : S.O) * (u⁻¹ * x) * (s : S.O)⁻¹ * (u⁻¹ * x)⁻¹) *
              (r : S.O)⁻¹) * ((r : S.O) * (u⁻¹ * x) * (r : S.O)⁻¹ * (u⁻¹ * x)⁻¹) := by
          simp only [Subgroup.coe_mul]
          group
        rw [e, hzr _ (hf s s.2) r r.2, ind1_mul htt (hf s s.2) (hf r r.2), add_comm, ofAdd_add] }
  have hψ : commutator (Rbar S g t) ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [commutator_eq_top_of_perfect hperf] at hψ
  have hcomm : ∀ r ∈ Rbar S g t, (u⁻¹ * x) * r = r * (u⁻¹ * x) := by
    intro r hr
    have h1 : ψ ⟨r, hr⟩ = 1 := hψ (mem_top _)
    have h2 : ind1 (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹) = 0 := h1
    have h3 : r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹ = 1 := by
      unfold ind1 at h2
      split_ifs at h2 with h
      · exact h
      · exact absurd h2 (by decide)
    calc u⁻¹ * x * r = (r * (u⁻¹ * x) * r⁻¹ * (u⁻¹ * x)⁻¹)⁻¹ * (r * (u⁻¹ * x)) := by group
      _ = r * (u⁻¹ * x) := by rw [h3, inv_one, one_mul]
  have hx'z := hcent G S g t c hSt hocc hext _ hx'M hcomm
  have e : x = u * (u⁻¹ * x) := by group
  rw [e]
  exact mul_mem huN (zpowers_le.mpr htN hx'z)

theorem isPGroup_fstar_Ct (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (hA : ∀ x ∈ S.Mbar, (∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) → x ∈ Nbar S g t)
    (hN2 : IsPGroup 2 (Nbar S g t)) : IsPGroup 2 (timmesfeldFStar (Ct S t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC : Nbar S g t ≤ Ct S t := fun n hn =>
    ⟨Rbar_le_Mbar (Nbar_le_Rbar hn), mem_centralizer_singleton_iff.mpr
      (commute_of_mem_Rbar haQ (Nbar_le_Rbar hn))⟩
  set N' := (Nbar S g t).subgroupOf (Ct S t) with hN'
  have hN'n : N'.Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [hN', mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = (c : S.O) := c.2.1
    have hkt : S.ρ k * t = t * S.ρ k := by
      rw [hk]
      exact mem_centralizer_singleton_iff.mp c.2.2
    have := conj_mem_Nbar haQ hkt hn
    rw [hk] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hN'2 : IsPGroup 2 N' :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNC).symm
  have key : ∀ x : Ct S t, (∀ y ∈ N', x * y = y * x) → (x : S.O) ∈ Nbar S g t := by
    intro x hx
    refine hA x x.2.1 fun y hy => ?_
    have h1 := congrArg Subtype.val (hx ⟨y, hNC hy⟩ (mem_subgroupOf.mpr hy))
    simp only [Subgroup.coe_mul] at h1
    rw [h1, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hE : timmesfeldLayer (Ct S t) = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun L hL => ?_)
    exfalso
    have : Group.IsNilpotent N' := hN'2.isNilpotent
    have : Group.IsSolvable N' := IsNilpotent.to_isSolvable
    have hcomm := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
      L N' hL (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
        hN'n.isSubnormal)
    have hLN : ∀ l ∈ L, ((l : Ct S t) : S.O) ∈ Nbar S g t := fun l hl =>
      key l fun y hy => (commutator_eq_bot_iff_le_centralizer.mp hcomm hl y hy).symm
    have hL2 : IsPGroup 2 L := by
      intro l
      obtain ⟨k, hk⟩ := hN2 ⟨(l : S.O), hLN l l.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    let : Group.IsPerfect L := ⟨hL.2.2.1⟩
    let : Nontrivial L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
    have : Group.IsNilpotent L := hL2.isNilpotent
    exact Group.IsPerfect.not_isSolvable L IsNilpotent.to_isSolvable
  have hOp : ∀ p : {p : ℕ // p.Prime}, p.val ≠ 2 →
      CFSG.ComponentClassification.PrimeCore.subgroup p.val (Ct S t) = ⊥ := by
    intro p hp2
    have : Fact p.val.Prime := ⟨p.2⟩
    have hOn := CFSG.ComponentClassification.PrimeCore.normal p.val (Ct S t)
    have hOp := CFSG.ComponentClassification.PrimeCore.isPGroup p.val (Ct S t)
    have hdisj : Disjoint (CFSG.ComponentClassification.PrimeCore.subgroup p.val (Ct S t)) N' :=
      IsPGroup.disjoint_of_coprime hOp hN'2
        ((Nat.coprime_primes p.2 Nat.prime_two).mpr hp2)
    have hcomm : ⁅CFSG.ComponentClassification.PrimeCore.subgroup p.val (Ct S t), N'⁆ = ⊥ :=
      eq_bot_iff.mpr ((commutator_le_inf _ _).trans hdisj.eq_bot.le)
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxN := key x fun y hy => (commutator_eq_bot_iff_le_centralizer.mp hcomm hx y hy).symm
    have hx' : x ∈ CFSG.ComponentClassification.PrimeCore.subgroup p.val (Ct S t) ⊓ N' :=
      ⟨hx, mem_subgroupOf.mpr hxN⟩
    rwa [hdisj.eq_bot] at hx'
  have hF : timmesfeldFStar (Ct S t) ≤
      CFSG.ComponentClassification.PrimeCore.subgroup 2 (Ct S t) := by
    change CFSG.ComponentClassification.Fitting.subgroup (Ct S t) ⊔ timmesfeldLayer (Ct S t) ≤ _
    rw [hE, sup_bot_eq, CFSG.ComponentClassification.PrimeCore.fitting_eq_join]
    refine iSup_le fun p => ?_
    by_cases hp2 : p.val = 2
    · rw [hp2]
    · rw [hOp p hp2]
      exact bot_le
  exact (CFSG.ComponentClassification.PrimeCore.isPGroup 2 (Ct S t)).to_le hF

theorem claim14_7_of (hCE : CentralExtInput.{0}) (hcent : CentRbarStmt) : Claim14_7 := by
  intro G _ _ _ S g t c hSt hocc hext
  have hA : ∀ x ∈ S.Mbar, (∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t) →
      x ∈ Nbar S g t := fun x hx hxN =>
    mem_Nbar_of_centralizes_quotient hCE hcent hSt hocc hext hx hxN
  exact ⟨hA, isPGroup_fstar_Ct hSt.hyp4.conj_mem hA hext.1⟩

end CFSG.LargeExtraspecial.S14
