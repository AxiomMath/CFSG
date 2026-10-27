module

public import CFSG.LargeExtraspecial.S9Basic
public import CFSG.LargeExtraspecial.S9Mod
public import CFSG.LargeExtraspecial.S45QMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Group

variable {X : Type*} [Group X]

theorem commute_of_mem_zpowers {t c x : X} (hc : c ∈ zpowers t) (hx : x * t = t * x) :
    c * x = x * c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  exact ((Commute.zpow_left (Commute.symm hx) k)).eq

variable (X) in
@[expose] def commZ (y t : X) : Subgroup X where
  carrier := {r | r * t = t * r ∧ y * r * y⁻¹ * r⁻¹ ∈ zpowers t}
  mul_mem' := by
    rintro r s ⟨hr, hrc⟩ ⟨hs, hsc⟩
    refine ⟨by rw [mul_assoc, hs, ← mul_assoc, hr, mul_assoc], ?_⟩
    have e : y * (r * s) * y⁻¹ * (r * s)⁻¹ =
        (y * r * y⁻¹ * r⁻¹) * (r * (y * s * y⁻¹ * s⁻¹) * r⁻¹) := by group
    rw [e, show r * (y * s * y⁻¹ * s⁻¹) * r⁻¹ = y * s * y⁻¹ * s⁻¹ by
      rw [← commute_of_mem_zpowers hsc hr, mul_inv_cancel_right]]
    exact mul_mem hrc hsc
  one_mem' := ⟨by rw [one_mul, mul_one], by simp⟩
  inv_mem' := by
    rintro r ⟨hr, hrc⟩
    have hr' : r⁻¹ * t = t * r⁻¹ := by
      calc r⁻¹ * t = r⁻¹ * (t * r) * r⁻¹ := by group
        _ = r⁻¹ * (r * t) * r⁻¹ := by rw [hr]
        _ = t * r⁻¹ := by group
    refine ⟨hr', ?_⟩
    have e : y * r⁻¹ * y⁻¹ * r⁻¹⁻¹ = r⁻¹ * (y * r * y⁻¹ * r⁻¹)⁻¹ * r := by group
    rw [e, ← commute_of_mem_zpowers (inv_mem hrc) hr', inv_mul_cancel_right]
    exact inv_mem hrc

theorem comm_identity {a b c d : X} (hca : Commute c a) (hcb : Commute c b) (hcd : Commute c d)
    (hda : Commute d a) (hdb : Commute d b) (hdd : d * d = 1) :
    (c * a) * (d * b) * (c * a)⁻¹ * (d * b) = a * b * a⁻¹ * b := by
  have hX : Commute c (a * (d * b) * a⁻¹) :=
    (hca.mul_right (hcd.mul_right hcb)).mul_right hca.inv_right
  have hY : Commute d (a * b * a⁻¹) := (hda.mul_right hdb).mul_right hda.inv_right
  calc (c * a) * (d * b) * (c * a)⁻¹ * (d * b) =
      (c * (a * (d * b) * a⁻¹)) * c⁻¹ * (d * b) := by group
    _ = (a * (d * b) * a⁻¹) * (d * b) := by rw [hX.eq]; group
    _ = (d * (a * b * a⁻¹)) * (d * b) := by
      congr 1
      calc a * (d * b) * a⁻¹ = (a * d) * b * a⁻¹ := by group
        _ = (d * a) * b * a⁻¹ := by rw [← hda.eq]
        _ = d * (a * b * a⁻¹) := by group
    _ = ((a * b * a⁻¹) * d) * (d * b) := by rw [hY.eq]
    _ = a * b * a⁻¹ * (d * d) * b := by group
    _ = a * b * a⁻¹ * b := by rw [hdd, mul_one]

theorem mem_commZ {y t : X} {r : X} :
    r ∈ commZ X y t ↔ r * t = t * r ∧ y * r * y⁻¹ * r⁻¹ ∈ zpowers t :=
  Iff.rfl

theorem exists_mul_ne_one_of_three_le (K : Subgroup X) (hK : 3 ≤ Nat.card K)
    (hsq : ∀ x ∈ K, x * x = 1) : ∃ x ∈ K, ∃ y ∈ K, x ≠ 1 ∧ y ≠ 1 ∧ x * y ≠ 1 := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have hcard : Nat.card K ≤ 2 := by
    by_cases hx : ∃ x ∈ K, x ≠ 1
    · obtain ⟨x, hxK, hx1⟩ := hx
      have hsub : (K : Set X) ⊆ {1, x} := by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · right
          have h1 := hcon x hxK y hy hx1 hy1
          calc y = x * x * y := by rw [hsq x hxK, one_mul]
            _ = x * (x * y) := mul_assoc _ _ _
            _ = x := by rw [h1, mul_one]
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      calc (K : Set X).ncard ≤ ({1, x} : Set X).ncard := Set.ncard_le_ncard hsub
        _ ≤ ({x} : Set X).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    · push Not at hx
      have hsub : (K : Set X) ⊆ {1} := fun y hy => hx y hy
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      calc (K : Set X).ncard ≤ ({1} : Set X).ncard := Set.ncard_le_ncard hsub
        _ ≤ 2 := by rw [Set.ncard_singleton]; omega
  omega

end Group

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem comm_mem_zpowers_of_fix (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w)
    {l : S.O} (hl : l ∈ S.Lbar g) : τ * l * τ⁻¹ * l⁻¹ ∈ zpowers t := by
  have hτa := hτV _ (cl_a_mem_Vt ht)
  have hτN : τ ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hτM (by simpa using hτa)
    simpa using this
  have hconj : τ * l * τ⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hτN l).mp hl
  refine mem_zpowers_of_fix_clSub_inf_Wt H C ht ht1 hVQ (mul_mem hconj (inv_mem hl))
    fun w hw => ?_
  have hτinv : ∀ v, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    fun v hv => by
      conv_lhs => rw [← hv]
      exact inv_apply_apply_O τ v
  have h1 := Lbar_apply_sub_mem_span' H.conj_mem hw.1 (inv_mem hl)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h1
  have h2 : ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + c • S.cl (g * S.z * g⁻¹) := by
    rw [hc]
    abel
  have h3 : ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      ((l⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w := by
    rw [h2, map_add, map_smul, hτinv w (hτP w hw), hτinv _ hτa]
  rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, h3, apply_inv_apply_O]
  exact hτP w hw

section Cent

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem Rbar_le_sup_Lbar : Rbar S g t ≤ S.Lbar g ⊔ S.Lbar ((h : G) * g) := by
  have h1 := pair_one (t := t) hb
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp 1 h h1.1 hh h1.2
  have hN := Nbar_eq_sup_sp hCE H hNo C ht ht1 hVQ hSp hh hb
  simp only [OneMemClass.coe_one, one_mul] at hgen
  refine hgen.trans (sup_le le_rfl ?_)
  rw [hN]
  exact sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

omit hNo in
theorem commute_Nbar_of_comm_mem (hNo : NoA2 S g) {y : S.O} (hyt : y * t = t * y)
    (hyR : ∀ r ∈ Rbar S g t, y * r * y⁻¹ * r⁻¹ ∈ zpowers t) :
    ∀ n ∈ Nbar S g t, y * n = n * y := by
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  have : NQHyp S g t := timmesfeld_6_5_nqHyp H C ht ht1 hVQ hgen hN0 hh hb
  have hD := timmesfeld_6_5_sp H hNo C ht ht1 hVQ hSp hN0 hh hb
  have hβa := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  obtain ⟨m, hm⟩ := even_finrank_Vt H C ht ht1 hVQ
  have htop := sup_map_sub_one_eq_top (nqRep S g t hSp.eq_sp) hβa hnd (m := m) (by omega)
    (beta_aV_bV H C ht ht1 hVQ hh hb) hD
  have htK : t ∈ centralizer ({y} : Set S.O) := mem_centralizer_singleton_iff.mpr hyt.symm
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hsub : ∀ (x : TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)) (n : Nbar S g t),
      nqRep S g t hSp.eq_sp x (nqMk n) - nqMk n ∈
        S8.nqImage S g t (centralizer ({y} : Set S.O)) := by
    intro x n
    have hxR : (x : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ RmodN S g t := by
      rw [hSp.eq_sp]
      exact x.2
    rw [← range_resV H.conj_mem t] at hxR
    obtain ⟨r, hr⟩ := hxR
    rw [nqRep_apply hSp.eq_sp hr.symm n, vec_sub, ← nqMk_mul]
    refine (S8.mem_nqImage_mk htK _).mpr (mem_centralizer_singleton_iff.mpr ?_)
    rw [coe_mul, coe_nConj]
    have hrt := commute_of_mem_Rbar H.conj_mem r.2
    have hnt := commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar n.2)
    have hcr := hyR r r.2
    have hcn := hyR n (Nbar_le_Rbar n.2)
    have e1 : y * r * y⁻¹ = (y * r * y⁻¹ * (r : S.O)⁻¹) * r := by group
    have e2 : y * n * y⁻¹ = (y * n * y⁻¹ * (n : S.O)⁻¹) * n := by group
    have e3 : y * (r * n * (r : S.O)⁻¹ * n) * y⁻¹ =
        (y * r * y⁻¹) * (y * n * y⁻¹) * (y * r * y⁻¹)⁻¹ * (y * n * y⁻¹) := by group
    have hcnn : (y * n * y⁻¹ * (n : S.O)⁻¹) * (y * n * y⁻¹ * (n : S.O)⁻¹) = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hcn
      rw [← hk, ← zpow_add, ← two_mul, zpow_mul, zpow_two, htt, one_zpow]
    have e4 : y * (r * n * (r : S.O)⁻¹ * n) * y⁻¹ = r * n * (r : S.O)⁻¹ * n := by
      rw [e3, e1, e2]
      exact comm_identity (commute_of_mem_zpowers hcr hrt) (commute_of_mem_zpowers hcr hnt)
        (commute_of_mem_zpowers hcr (commute_of_mem_zpowers hcn (x := t) rfl))
        (commute_of_mem_zpowers hcn hrt) (commute_of_mem_zpowers hcn hnt) hcnn
    refine (?_ : y * (r * n * (r : S.O)⁻¹ * n) = r * n * (r : S.O)⁻¹ * n * y).symm
    calc y * (r * n * (r : S.O)⁻¹ * n) = (y * (r * n * (r : S.O)⁻¹ * n) * y⁻¹) * y := by group
      _ = r * n * (r : S.O)⁻¹ * n * y := by rw [e4]
  intro n hn
  have h1 : nqMk (⟨n, hn⟩ : Nbar S g t) ∈ (⊤ : Submodule (ZMod 2) (NQ S g t)) :=
    Submodule.mem_top
  rw [← htop] at h1
  obtain ⟨u₁, ⟨m₁, -, rfl⟩, u₂, ⟨m₂, -, rfl⟩, hsum⟩ := Submodule.mem_sup.mp h1
  obtain ⟨n₁, rfl⟩ := nqMk_surjective m₁
  obtain ⟨n₂, rfl⟩ := nqMk_surjective m₂
  have hmem : nqMk (⟨n, hn⟩ : Nbar S g t) ∈ S8.nqImage S g t (centralizer ({y} : Set S.O)) := by
    rw [← hsum]
    exact add_mem (hsub _ n₁) (hsub _ n₂)
  have := (S8.mem_nqImage_mk htK _).mp hmem
  exact (mem_centralizer_singleton_iff.mp this).symm

omit hCE hNo hh hb in
theorem exists_Lbar_mul_not_mem (h4 : 4 ≤ finrank (ZMod 2) (Vt S g t)) :
    ∃ l₁ ∈ S.Lbar g, ∃ l₂ ∈ S.Lbar g, l₁ ∉ Nbar S g t ∧ l₂ ∉ Nbar S g t ∧
      l₁ * l₂ ∉ Nbar S g t := by
  have hcard : 3 ≤ Nat.card (LmodN S g t) := by
    rw [hSp.LmodN_eq, card_spPointRadical (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) (aV_ne_zero H ht)]
    calc 3 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (finrank (ZMod 2) (Vt S g t) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsq : ∀ e ∈ LmodN S g t, e * e = 1 := by
    rintro e ⟨x, hx, hex⟩
    ext v
    rw [LinearEquiv.mul_apply, hex, hex, ← coe_mul_apply, mul_self_of_mem_Lbar S H.conj_mem hx]
    rfl
  obtain ⟨e₁, ⟨l₁, hl₁, he₁⟩, e₂, ⟨l₂, hl₂, he₂⟩, he₁1, he₂1, he₁₂⟩ :=
    exists_mul_ne_one_of_three_le _ hcard hsq
  have hnot : ∀ (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) (x : S.O), e ≠ 1 →
      (∀ v : Vt S g t, ((e v : Vt S g t) : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) →
      x ∉ Nbar S g t := by
    intro e x he1 hex hxN
    apply he1
    ext v
    rw [hex]
    exact (mem_Nbar.mp hxN).2 v v.2
  refine ⟨l₁, hl₁, l₂, hl₂, hnot e₁ l₁ he₁1 he₁, hnot e₂ l₂ he₂1 he₂,
    hnot (e₁ * e₂) (l₁ * l₂) he₁₂ fun v => ?_⟩
  rw [LinearEquiv.mul_apply, he₁, he₂, coe_mul_apply]

omit hCE hNo C ht ht1 hVQ hSp hh hb in
theorem normal_centralizer_subgroupOf {y : S.O}
    (hyR : ∀ r ∈ Rbar S g t, y * r * y⁻¹ * r⁻¹ ∈ zpowers t) :
    ((centralizer ({y} : Set S.O)).subgroupOf (Rbar S g t)).Normal := by
  refine ⟨fun k hk r => ?_⟩
  rw [mem_subgroupOf, mem_centralizer_singleton_iff] at hk ⊢
  have hcr := hyR r r.2
  have hkt : ((r * k * r⁻¹ : Rbar S g t) : S.O) * t = t * ((r * k * r⁻¹ : Rbar S g t) : S.O) :=
    commute_of_mem_Rbar H.conj_mem (r * k * r⁻¹).2
  have hc := commute_of_mem_zpowers hcr hkt
  simp only [coe_mul, coe_inv] at hc hk ⊢
  have e1 : y * r * y⁻¹ = (y * r * y⁻¹ * (r : S.O)⁻¹) * r := by group
  have e3 : y * (r : S.O)⁻¹ = (r : S.O)⁻¹ * (y * r * y⁻¹ * (r : S.O)⁻¹)⁻¹ * y := by group
  refine (?_ : y * (r * k * (r : S.O)⁻¹) = r * k * (r : S.O)⁻¹ * y).symm
  calc y * (r * k * (r : S.O)⁻¹) = (y * r * y⁻¹) * (y * k) * (r : S.O)⁻¹ := by group
    _ = ((y * r * y⁻¹ * (r : S.O)⁻¹) * r) * (k * y) * (r : S.O)⁻¹ := by rw [← e1, ← hk]
    _ = (y * r * y⁻¹ * (r : S.O)⁻¹) * r * k * (y * (r : S.O)⁻¹) := by group
    _ = (y * r * y⁻¹ * (r : S.O)⁻¹) * r * k *
        ((r : S.O)⁻¹ * (y * r * y⁻¹ * (r : S.O)⁻¹)⁻¹ * y) := by rw [e3]
    _ = ((y * r * y⁻¹ * (r : S.O)⁻¹) * (r * k * (r : S.O)⁻¹)) *
        (y * r * y⁻¹ * (r : S.O)⁻¹)⁻¹ * y := by group
    _ = ((r * k * (r : S.O)⁻¹) * (y * r * y⁻¹ * (r : S.O)⁻¹)) *
        (y * r * y⁻¹ * (r : S.O)⁻¹)⁻¹ * y := by rw [hc]
    _ = r * k * (r : S.O)⁻¹ * y := by group

omit hCE hNo hh hb in
theorem exists_commute_not_mem_Nbar (h4 : 4 ≤ finrank (ZMod 2) (Vt S g t)) {y : S.O}
    (hyR : ∀ r ∈ Rbar S g t, y * r * y⁻¹ * r⁻¹ ∈ zpowers t) :
    ∃ r ∈ Rbar S g t, r ∉ Nbar S g t ∧ y * r = r * y := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  obtain ⟨l₁, hl₁, l₂, hl₂, hl₁N, hl₂N, hl₁₂N⟩ := exists_Lbar_mul_not_mem H C ht ht1 hVQ hSp h4
  by_contra hcon
  push Not at hcon
  have hcomm : ∀ l ∈ S.Lbar g, l ∉ Nbar S g t → y * l * y⁻¹ = t * l := by
    intro l hl hlN
    have hlR := Lbar_le_Rbar ht hl
    rcases S8.eq_one_or_eq_of_mem_zpowers htt (hyR l hlR) with h1 | h1
    · exfalso
      apply hcon l hlR hlN
      calc y * l = (y * l * y⁻¹ * l⁻¹) * l * y := by group
        _ = l * y := by rw [h1, one_mul]
    · calc y * l * y⁻¹ = (y * l * y⁻¹ * l⁻¹) * l := by group
        _ = t * l := by rw [h1]
  apply hcon (l₁ * l₂) (Lbar_le_Rbar ht (mul_mem hl₁ hl₂)) hl₁₂N
  have h1 := hcomm l₁ hl₁ hl₁N
  have h2 := hcomm l₂ hl₂ hl₂N
  have hl₁t : l₁ * t = t * l₁ := Lbar_comm S H.conj_mem hl₁ ht
  calc y * (l₁ * l₂) = (y * l₁ * y⁻¹) * (y * l₂ * y⁻¹) * y := by group
    _ = t * l₁ * (t * l₂) * y := by rw [h1, h2]
    _ = l₁ * (t * t) * l₂ * y := by rw [← hl₁t]; group
    _ = l₁ * l₂ * y := by rw [htt, mul_one]

theorem commute_Rbar_of_comm_mem (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {y : S.O}
    (hyt : y * t = t * y) (hyR : ∀ r ∈ Rbar S g t, y * r * y⁻¹ * r⁻¹ ∈ zpowers t) :
    ∀ r ∈ Rbar S g t, y * r = r * y := by
  have hyN := commute_Nbar_of_comm_mem hCE H C ht ht1 hVQ hSp hh hb hNo hyt hyR
  have hnorm := normal_centralizer_subgroupOf H hyR
  have hS : IsSimpleGroup (resV H.conj_mem t).range := by
    rw [range_resV H.conj_mem t]
    exact ((S45Q.hyp45Q H C).sp ht ht1 hVQ hSp h6).1
  have hK₁ : (((centralizer ({y} : Set S.O)).subgroupOf (Rbar S g t)).map
      (resV H.conj_mem t).rangeRestrict).Normal :=
    hnorm.map _ (resV H.conj_mem t).rangeRestrict_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((centralizer ({y} : Set S.O)).subgroupOf
      (Rbar S g t)).map (resV H.conj_mem t).rangeRestrict) with hbot | htop
  · exfalso
    obtain ⟨r, hr, hrN, hry⟩ := exists_commute_not_mem_Nbar H C ht ht1 hVQ hSp (by omega) hyR
    apply hrN
    have hmem : (⟨r, hr⟩ : Rbar S g t) ∈ (centralizer ({y} : Set S.O)).subgroupOf (Rbar S g t) := by
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      exact hry.symm
    have : (resV H.conj_mem t).rangeRestrict ⟨r, hr⟩ ∈
        ((centralizer ({y} : Set S.O)).subgroupOf (Rbar S g t)).map
          (resV H.conj_mem t).rangeRestrict := ⟨⟨r, hr⟩, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (resV_eq_one_iff H.conj_mem ⟨r, hr⟩).mp (congrArg Subtype.val this)
  · intro r hr
    have : (resV H.conj_mem t).rangeRestrict ⟨r, hr⟩ ∈
        ((centralizer ({y} : Set S.O)).subgroupOf (Rbar S g t)).map
          (resV H.conj_mem t).rangeRestrict := by rw [htop]; exact mem_top _
    obtain ⟨k, hk, hkr⟩ := this
    rw [SetLike.mem_coe, mem_subgroupOf, mem_centralizer_singleton_iff] at hk
    have h1 : resV H.conj_mem t (k⁻¹ * ⟨r, hr⟩) = 1 := by
      have : resV H.conj_mem t k = resV H.conj_mem t ⟨r, hr⟩ := congrArg Subtype.val hkr
      rw [map_mul, map_inv, this, inv_mul_cancel]
    have h2 := hyN _ ((resV_eq_one_iff H.conj_mem _).mp h1)
    simp only [coe_mul, coe_inv] at h2
    calc y * r = y * (k * ((k : S.O)⁻¹ * r)) := by group
      _ = k * y * ((k : S.O)⁻¹ * r) := by rw [← mul_assoc, ← hk]
      _ = k * ((k : S.O)⁻¹ * r) * y := by rw [mul_assoc, h2, ← mul_assoc]
      _ = r * y := by group

theorem exists_Abar_comm_mem_of_fix {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    ∃ α ∈ S.Lbar g ⊓ Nbar S g t, α⁻¹ * τ * t = t * (α⁻¹ * τ) ∧
      ∀ r ∈ Rbar S g t, (α⁻¹ * τ) * r * (α⁻¹ * τ)⁻¹ * r⁻¹ ∈ zpowers t := by
  have hc : ∀ l ∈ S.Lbar g, τ * l * τ⁻¹ * l⁻¹ ∈ zpowers t :=
    fun l hl => comm_mem_zpowers_of_fix H C ht ht1 hVQ hτM hτV hτP hl
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hτM
  have hτR : τ * S.ρ h * τ⁻¹ ∈ Rbar S g t := by
    have := conj_mem_Rbar (k := k) (by rw [hk]; exact hτt) hh
    rwa [hk] at this
  have hσN : τ * S.ρ h * τ⁻¹ * (S.ρ h)⁻¹ ∈ Nbar S g t := by
    refine mem_Nbar.mpr ⟨mul_mem hτR (inv_mem hh), fun v hv => ?_⟩
    have hv' := apply_mem_Vt_of_mem_Rbar H.conj_mem (inv_mem hh) hv
    have hτinv : ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        ((((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
          (((S.ρ h)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
      conv_lhs => rw [← hτV _ hv']
      exact inv_apply_apply_O τ _
    rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hτinv, apply_inv_apply_O, hτV v hv]
  have h1 := pair_one (t := t) hb
  have hgen := pairGen_of_spCase H C ht ht1 hVQ hSp 1 h h1.1 hh h1.2
  have hN0 := Nbar_eq_N0bar_of_spCase hCE H hNo C ht ht1 hVQ hSp
  obtain ⟨α, hα, β, hβ, hσ⟩ := exists_mul_of_pair H ht h1.1 hh hgen hN0 hσN
  simp only [OneMemClass.coe_one, one_mul] at hα
  have hαt : α * t = t * α := Lbar_comm S H.conj_mem hα.1 ht
  have hαit : α⁻¹ * t = t * α⁻¹ := by
    calc α⁻¹ * t = α⁻¹ * (t * α) * α⁻¹ := by group
      _ = α⁻¹ * (α * t) * α⁻¹ := by rw [hαt]
      _ = t * α⁻¹ := by group
  have hβt : β * t = t * β := commute_of_mem_Rbar H.conj_mem (Nbar_le_Rbar hβ.2)
  have hyt : α⁻¹ * τ * t = t * (α⁻¹ * τ) := by
    rw [mul_assoc, hτt, ← mul_assoc, hαit, mul_assoc]
  have hle : S.Lbar g ⊔ S.Lbar ((h : G) * g) ≤ commZ S.O (α⁻¹ * τ) t := by
    refine sup_le (fun l hl => ⟨Lbar_comm S H.conj_mem hl ht, ?_⟩) (fun l' hl' => ⟨?_, ?_⟩)
    · have hcl := hc l hl
      have hαl : α * l = l * α := Lbar_comm S H.conj_mem hα.1 hl
      have e : (α⁻¹ * τ) * l * (α⁻¹ * τ)⁻¹ * l⁻¹ =
          α⁻¹ * (τ * l * τ⁻¹ * l⁻¹) * (l * α * l⁻¹) := by group
      rw [e, ← commute_of_mem_zpowers hcl hαit, show l * α * l⁻¹ = α by
        rw [← hαl, mul_inv_cancel_right]]
      simpa using hcl
    · exact Lbar_comm S (H.mul h).conj_mem hl' (mem_Lbar_of_pair H ht hh)
    · have hl'' : l' ∈ (S.Lbar g).map (MulAut.conj (S.ρ h)).toMonoidHom := by
        rw [← Lbar_mul S h g]
        exact hl'
      obtain ⟨l, hl, rfl⟩ := hl''
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hcl := hc l hl
      have hτh : τ * S.ρ h * τ⁻¹ = α * β * S.ρ h := by
        calc τ * S.ρ h * τ⁻¹ = (τ * S.ρ h * τ⁻¹ * (S.ρ h)⁻¹) * S.ρ h := by group
          _ = α * β * S.ρ h := by rw [hσ]
      have hτl : τ * l * τ⁻¹ = (τ * l * τ⁻¹ * l⁻¹) * l := by group
      have hhc := (commute_of_mem_zpowers hcl (commute_of_mem_Rbar H.conj_mem hh)).symm
      have hαc := (commute_of_mem_zpowers hcl hαt).symm
      have hβc := (commute_of_mem_zpowers hcl hβt).symm
      have hβl : β * (S.ρ h * l * (S.ρ h)⁻¹) = S.ρ h * l * (S.ρ h)⁻¹ * β := by
        have := Lbar_comm S (H.mul h).conj_mem hβ.1 (conj_mem_Lbar_mul S h hl)
        exact this
      set c := τ * l * τ⁻¹ * l⁻¹ with hcdef
      have e : (α⁻¹ * τ) * (S.ρ h * l * (S.ρ h)⁻¹) * (α⁻¹ * τ)⁻¹ *
          (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ = c := by
        calc (α⁻¹ * τ) * (S.ρ h * l * (S.ρ h)⁻¹) * (α⁻¹ * τ)⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ =
            α⁻¹ * ((τ * S.ρ h * τ⁻¹) * (τ * l * τ⁻¹) * (τ * S.ρ h * τ⁻¹)⁻¹) * α *
              (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ := by group
          _ = α⁻¹ * ((α * β * S.ρ h) * (c * l) * (α * β * S.ρ h)⁻¹) * α *
              (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ := by rw [hτh, hτl]
          _ = β * (S.ρ h * c) * l * (S.ρ h)⁻¹ * β⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ := by group
          _ = (β * c) * (S.ρ h * l * (S.ρ h)⁻¹) * β⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ := by
            rw [hhc]; group
          _ = c * (β * (S.ρ h * l * (S.ρ h)⁻¹)) * β⁻¹ * (S.ρ h * l * (S.ρ h)⁻¹)⁻¹ := by
            rw [hβc]; group
          _ = c := by rw [hβl]; group
      rw [e]
      exact hcl
  have hyR : ∀ r ∈ Rbar S g t, (α⁻¹ * τ) * r * (α⁻¹ * τ)⁻¹ * r⁻¹ ∈ zpowers t := fun r hr =>
    (hle (Rbar_le_sup_Lbar hCE H hNo C ht ht1 hVQ hSp hh hb hr)).2
  exact ⟨α, hα, hyt, hyR⟩

theorem commute_Lbar_of_fix (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    ∀ l ∈ S.Lbar g, τ * l = l * τ := by
  obtain ⟨α, hα, hyt, hyR⟩ :=
    exists_Abar_comm_mem_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb hτM hτt hτV hτP
  have hyc := commute_Rbar_of_comm_mem hCE H hNo C ht ht1 hVQ hSp hh hb h6 hyt hyR
  intro l hl
  have h2 := hyc l (Lbar_le_Rbar ht hl)
  have hαl : α * l = l * α := Lbar_comm S H.conj_mem hα.1 hl
  calc τ * l = α * (α⁻¹ * τ * l) := by group
    _ = α * (l * (α⁻¹ * τ)) := by rw [h2]
    _ = (α * l) * α⁻¹ * τ := by group
    _ = (l * α) * α⁻¹ * τ := by rw [hαl]
    _ = l * τ := by group

end Cent

end CFSG.LargeExtraspecial.S9
