module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Corollary
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Conj
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Hall
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Orders
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Rank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Solv
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Thompson
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.Glauberman281.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3Aux

section HeisenbergFacts

open Subgroup

variable {G : Type} [Group G]

@[expose] def zc (T : Subgroup G) : Subgroup G := T ⊓ centralizer (T : Set G)

theorem mem_zc {T : Subgroup G} {z : G} : z ∈ zc T ↔ z ∈ T ∧ ∀ g ∈ T, g * z = z * g := by
  unfold zc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem zc_le {T : Subgroup G} : zc T ≤ T := inf_le_left

theorem zc_card {T : Subgroup G} (hc : Nat.card T = 3 ^ 3) (hnc : ¬ IsMulCommutative T) :
    Nat.card (zc T) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Generic49U3.card_inf_centralizer_of_nonabelian_card_p_cube hc hnc

theorem comm_mem_zc {T : Subgroup G} (hc : Nat.card T = 3 ^ 3) (hnc : ¬ IsMulCommutative T) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ zc T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : Nat.card (center T) = 3 :=
    Generic49U3.card_center_of_nonabelian_card_p_cube hc hnc
  have hQ : Nat.card (T ⧸ center T) = 3 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [hc, hZ] at h1
    norm_num at h1 ⊢
    omega
  have hcomm : IsMulCommutative (T ⧸ center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  intro a ha b hb
  have key : (⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ ∈ center T := by
    rw [← QuotientGroup.eq_one_iff]
    have hab := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ center T)
      (QuotientGroup.mk ⟨b, hb⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hab
  refine mem_zc.2 ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb), ?_⟩
  intro s hs
  have := mem_center_iff.mp key ⟨s, hs⟩
  exact congrArg Subtype.val this

theorem zc_comm {T : Subgroup G} {z g : G} (hz : z ∈ zc T) (hg : g ∈ T) : z * g = g * z :=
  ((mem_zc.1 hz).2 g hg).symm

theorem commute_of_zc {T : Subgroup G} {z g : G} (hz : z ∈ zc T) (hg : g ∈ T) : Commute z g :=
  zc_comm hz hg

@[expose] def cm (a b : G) : G := a * b * a⁻¹ * b⁻¹

theorem cm_mul_zc_left {T : Subgroup G} {z x y : G} (hz : z ∈ zc T) (hx : x ∈ T) (hy : y ∈ T) :
    cm (z * x) y = cm x y := by
  have hc : Commute z (x * y * x⁻¹) :=
    commute_of_zc hz (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx))
  unfold cm
  calc z * x * y * (z * x)⁻¹ * y⁻¹ = (z * (x * y * x⁻¹) * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hc.mul_inv_cancel]

theorem cm_mul_zc_right {T : Subgroup G} {z x y : G} (hz : z ∈ zc T) (hx : x ∈ T) (hy : y ∈ T) :
    cm x (z * y) = cm x y := by
  have hxz : x * z = z * x := (zc_comm hz hx).symm
  have hc : Commute z (x * y * x⁻¹ * y⁻¹) :=
    commute_of_zc hz (T.mul_mem (T.mul_mem (T.mul_mem hx hy) (T.inv_mem hx)) (T.inv_mem hy))
  unfold cm
  calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = (x * z) * (y * x⁻¹ * y⁻¹ * z⁻¹) := by group
    _ = z * x * (y * x⁻¹ * y⁻¹ * z⁻¹) := by rw [hxz]
    _ = (z * (x * y * x⁻¹ * y⁻¹) * z⁻¹) := by group
    _ = x * y * x⁻¹ * y⁻¹ := hc.mul_inv_cancel

theorem cm_inv_right {T : Subgroup G} {a b : G} (hb : b ∈ T) (hw : cm a b ∈ zc T) :
    cm a b⁻¹ = (cm a b)⁻¹ := by
  have hc : Commute (cm a b) b := commute_of_zc hw hb
  unfold cm at hc ⊢
  calc a * b⁻¹ * a⁻¹ * b⁻¹⁻¹ = ((a * b * a⁻¹ * b⁻¹) * b)⁻¹ * b := by group
    _ = b⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * b := by group
    _ = (a * b * a⁻¹ * b⁻¹)⁻¹ := (hc.symm.inv_right).inv_mul_cancel

theorem isMulCommutative_of_lt {T X : Subgroup G} (hc : Nat.card T = 3 ^ 3) (hXT : X ≤ T)
    (hne : X ≠ T) : IsMulCommutative X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have hdvd : Nat.card X ∣ 3 ^ 3 := hc ▸ Subgroup.card_dvd_of_le hXT
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hi3 : i ≠ 3 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hXT (by rw [hci, hc]))
  have hi' : i < 3 := lt_of_le_of_ne hi hi3
  interval_cases i
  · have h1 : Nat.card X = 1 := by rw [hci]; norm_num
    haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.1 h1).1
    exact isMulCommutative_iff.2 fun a b => Subsingleton.elim _ _
  · have h3 : Nat.card X = 3 := by rw [hci]; norm_num
    haveI : IsCyclic X := isCyclic_of_prime_card h3
    exact inferInstance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hci

theorem eq_of_sup_zc {T X : Subgroup G} (hc : Nat.card T = 3 ^ 3) (hnc : ¬ IsMulCommutative T)
    (hXT : X ≤ T) (h : ∀ t ∈ T, ∃ x ∈ X, ∃ z ∈ zc T, t = x * z) : X = T := by
  by_contra hne
  have hX := isMulCommutative_of_lt hc hXT hne
  apply hnc
  refine isMulCommutative_iff.2 fun a b => ?_
  obtain ⟨x, hx, z, hz, hab⟩ := h a a.2
  obtain ⟨x', hx', z', hz', hba⟩ := h b b.2
  apply Subtype.ext
  have hxx : x * x' = x' * x :=
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : X) ⟨x', hx'⟩)
  have hzx' : z * x' = x' * z := zc_comm hz (hXT hx')
  have hz'x : z' * x = x * z' := zc_comm hz' (hXT hx)
  have hzz' : z * z' = z' * z := zc_comm hz (zc_le hz')
  show (a : G) * b = b * a
  rw [hab, hba]
  calc x * z * (x' * z') = x * (z * x') * z' := by group
    _ = x * (x' * z) * z' := by rw [hzx']
    _ = (x * x') * (z * z') := by group
    _ = (x' * x) * (z' * z) := by rw [hxx, hzz']
    _ = x' * (x * z') * z := by group
    _ = x' * (z' * x) * z := by rw [hz'x]
    _ = x' * z' * (x * z) := by group

theorem noReflection {T : Subgroup G} (hc : Nat.card T = 3 ^ 3) (hnc : ¬ IsMulCommutative T)
    (he : ∀ t ∈ T, t ^ 3 = 1) {φ : G → G}
    (hφT : ∀ t ∈ T, φ t ∈ T) (hφm : ∀ a ∈ T, ∀ b ∈ T, φ (a * b) = φ a * φ b)
    (hφZ : ∀ z ∈ zc T, φ z = z) (hφ2 : ∀ t ∈ T, φ (φ t) = t) :
    (∀ t ∈ T, φ t = t) ∨ (∀ t ∈ T, φ t * t ∈ zc T) := by
  have hcm := comm_mem_zc hc hnc
  have hφ1 : φ 1 = 1 := by
    have h := hφm 1 T.one_mem 1 T.one_mem
    rw [one_mul] at h
    exact mul_left_cancel (a := φ 1) (b := φ 1) (c := 1) (by rw [mul_one]; exact h.symm)
  have hφinv : ∀ t ∈ T, φ t⁻¹ = (φ t)⁻¹ := by
    intro t ht
    have h := hφm t⁻¹ (T.inv_mem ht) t ht
    rw [inv_mul_cancel, hφ1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hz1 : ∀ z ∈ zc T, z * z = 1 → z = 1 := by
    intro z hz h2
    have h3 := he z (zc_le hz)
    have h4 : z ^ 3 = z := by rw [pow_three, h2, mul_one]
    rw [← h4]; exact h3
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, ∀ t, t ∈ C ↔ t ∈ T ∧ φ t * t⁻¹ ∈ zc T := by
    refine ⟨{ carrier := {t | t ∈ T ∧ φ t * t⁻¹ ∈ zc T}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun t => Iff.rfl⟩
    · rintro a b ⟨ha, hua⟩ ⟨hb, hub⟩
      refine ⟨T.mul_mem ha hb, ?_⟩
      have e : φ (a * b) * (a * b)⁻¹ = (φ a * a⁻¹) * (φ b * b⁻¹) := by
        rw [hφm a ha b hb]
        calc φ a * φ b * (a * b)⁻¹ = φ a * ((φ b * b⁻¹) * a⁻¹) := by group
          _ = φ a * (a⁻¹ * (φ b * b⁻¹)) := by rw [(commute_of_zc hub (T.inv_mem ha)).eq]
          _ = (φ a * a⁻¹) * (φ b * b⁻¹) := by group
      rw [e]; exact (zc T).mul_mem hua hub
    · refine ⟨T.one_mem, ?_⟩
      rw [hφ1]; simpa using (zc T).one_mem
    · rintro a ⟨ha, hua⟩
      refine ⟨T.inv_mem ha, ?_⟩
      rw [hφinv a ha, inv_inv]
      have hφa : φ a = (φ a * a⁻¹) * a := by group
      have e : (φ a)⁻¹ * a = (φ a * a⁻¹)⁻¹ := by
        calc (φ a)⁻¹ * a = ((φ a * a⁻¹) * a)⁻¹ * a := by rw [← hφa]
          _ = a⁻¹ * (φ a * a⁻¹)⁻¹ * a := by group
          _ = (φ a * a⁻¹)⁻¹ := ((commute_of_zc hua ha).symm.inv_right).inv_mul_cancel
      rw [e]; exact (zc T).inv_mem hua
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, ∀ t, t ∈ D ↔ t ∈ T ∧ φ t * t ∈ zc T := by
    refine ⟨{ carrier := {t | t ∈ T ∧ φ t * t ∈ zc T}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun t => Iff.rfl⟩
    · rintro a b ⟨ha, hua⟩ ⟨hb, hub⟩
      refine ⟨T.mul_mem ha hb, ?_⟩
      have hφa : φ a = (φ a * a) * a⁻¹ := by group
      have hφb : φ b = (φ b * b) * b⁻¹ := by group
      have e : φ (a * b) * (a * b) = ((φ a * a) * (φ b * b)) * cm a⁻¹ b⁻¹ := by
        rw [hφm a ha b hb]
        unfold cm
        calc φ a * φ b * (a * b) = (φ a * a) * a⁻¹ * ((φ b * b) * b⁻¹) * (a * b) := by
              rw [← hφa, ← hφb]
          _ = (φ a * a) * ((a⁻¹ * (φ b * b)) * b⁻¹) * (a * b) := by group
          _ = (φ a * a) * (((φ b * b) * a⁻¹) * b⁻¹) * (a * b) := by
              rw [← (commute_of_zc hub (T.inv_mem ha)).eq]
          _ = ((φ a * a) * (φ b * b)) * (a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹) := by group
      rw [e]
      exact (zc T).mul_mem ((zc T).mul_mem hua hub) (hcm _ (T.inv_mem ha) _ (T.inv_mem hb))
    · refine ⟨T.one_mem, ?_⟩
      rw [hφ1]; simpa using (zc T).one_mem
    · rintro a ⟨ha, hua⟩
      refine ⟨T.inv_mem ha, ?_⟩
      rw [hφinv a ha]
      have hφa : φ a = (φ a * a) * a⁻¹ := by group
      have e : (φ a)⁻¹ * a⁻¹ = (φ a * a)⁻¹ := by
        calc (φ a)⁻¹ * a⁻¹ = (a * φ a)⁻¹ := by group
          _ = (a * ((φ a * a) * a⁻¹))⁻¹ := by rw [← hφa]
          _ = (φ a * a)⁻¹ := by rw [(commute_of_zc hua ha).symm.mul_inv_cancel_assoc]
      rw [e]; exact (zc T).inv_mem hua
  have hZC : zc T ≤ C := by
    intro z hz
    rw [hC]
    refine ⟨zc_le hz, ?_⟩
    rw [hφZ z hz, mul_inv_cancel]; exact (zc T).one_mem
  have hZD : zc T ≤ D := by
    intro z hz
    rw [hD]
    refine ⟨zc_le hz, ?_⟩
    rw [hφZ z hz]; exact (zc T).mul_mem hz hz
  have hCT : C ≤ T := fun t ht => ((hC t).1 ht).1
  have hDT : D ≤ T := fun t ht => ((hD t).1 ht).1
  have hcd : ∀ c ∈ C, ∀ d ∈ D, c * d = d * c := by
    intro c hc' d hd'
    obtain ⟨hcT, hcu⟩ := (hC c).1 hc'
    obtain ⟨hdT, hdu⟩ := (hD d).1 hd'
    have hφc : φ c = (φ c * c⁻¹) * c := by group
    have hφd : φ d = (φ d * d) * d⁻¹ := by group
    have hw : cm c d ∈ zc T := hcm c hcT d hdT
    have h1 : φ (cm c d) = cm (φ c) (φ d) := by
      unfold cm
      have e1 : φ (c * d * c⁻¹ * d⁻¹) = φ (c * d * c⁻¹) * φ d⁻¹ :=
        hφm _ (T.mul_mem (T.mul_mem hcT hdT) (T.inv_mem hcT)) _ (T.inv_mem hdT)
      have e2 : φ (c * d * c⁻¹) = φ (c * d) * φ c⁻¹ :=
        hφm _ (T.mul_mem hcT hdT) _ (T.inv_mem hcT)
      have e3 : φ (c * d) = φ c * φ d := hφm c hcT d hdT
      rw [e1, e2, e3, hφinv c hcT, hφinv d hdT]
    have h2 : cm (φ c) (φ d) = (cm c d)⁻¹ := by
      have hz₂d : (φ d * d) * d⁻¹ ∈ T := T.mul_mem (zc_le hdu) (T.inv_mem hdT)
      calc cm (φ c) (φ d) = cm ((φ c * c⁻¹) * c) ((φ d * d) * d⁻¹) := by rw [← hφc, ← hφd]
        _ = cm c ((φ d * d) * d⁻¹) := cm_mul_zc_left hcu hcT hz₂d
        _ = cm c d⁻¹ := cm_mul_zc_right hdu hcT (T.inv_mem hdT)
        _ = (cm c d)⁻¹ := cm_inv_right hdT hw
    have h3 : cm c d = (cm c d)⁻¹ := by
      rw [← h2, ← h1, hφZ _ hw]
    have h4 : cm c d * cm c d = 1 := by
      calc cm c d * cm c d = cm c d * (cm c d)⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel _
    have h5 : cm c d = 1 := hz1 _ hw h4
    unfold cm at h5
    calc c * d = (c * d * c⁻¹ * d⁻¹) * (d * c) := by group
      _ = d * c := by rw [h5, one_mul]
  have hTDC : ∀ t ∈ T, ∃ d ∈ D, ∃ c ∈ C, t = d * c := by
    intro t ht
    have hsT : φ t ∈ T := hφT t ht
    have hφs : φ (φ t) = t := hφ2 t ht
    have haT : t * φ t ∈ T := T.mul_mem ht hsT
    have hbT : t * (φ t)⁻¹ ∈ T := T.mul_mem ht (T.inv_mem hsT)
    have hw : cm (φ t) t ∈ zc T := hcm _ hsT _ ht
    have haC : t * φ t ∈ C := by
      rw [hC]
      refine ⟨haT, ?_⟩
      have e : φ (t * φ t) * (t * φ t)⁻¹ = cm (φ t) t := by
        rw [hφm t ht (φ t) hsT, hφs]
        unfold cm; group
      rw [e]; exact hw
    have hbD : t * (φ t)⁻¹ ∈ D := by
      rw [hD]
      refine ⟨hbT, ?_⟩
      have e : φ (t * (φ t)⁻¹) * (t * (φ t)⁻¹) = 1 := by
        rw [hφm t ht (φ t)⁻¹ (T.inv_mem hsT), hφinv (φ t) hsT, hφs]
        group
      rw [e]; exact (zc T).one_mem
    have hab : (t * φ t) * (t * (φ t)⁻¹) = cm (φ t) t * t ^ 2 := by
      have hc' : Commute (cm (φ t) t) t := commute_of_zc hw ht
      calc (t * φ t) * (t * (φ t)⁻¹) = t * (cm (φ t) t) * t := by unfold cm; group
        _ = (cm (φ t) t * t) * t := by rw [← hc'.eq]
        _ = cm (φ t) t * t ^ 2 := by rw [mul_assoc, pow_two]
    have ht2 : (t ^ 2)⁻¹ = t := by
      apply inv_eq_of_mul_eq_one_right
      have := he t ht
      calc t ^ 2 * t = t ^ 3 := by group
        _ = 1 := this
    refine ⟨(t * (φ t)⁻¹)⁻¹ * cm (φ t) t, ?_, (t * φ t)⁻¹, ?_, ?_⟩
    · exact (D.mul_mem (D.inv_mem hbD) (hZD hw))
    · exact C.inv_mem haC
    · have hc'' : Commute (cm (φ t) t) (t * φ t)⁻¹ := commute_of_zc hw (T.inv_mem haT)
      calc t = (t ^ 2)⁻¹ := ht2.symm
        _ = (cm (φ t) t * t ^ 2)⁻¹ * cm (φ t) t := by group
        _ = ((t * φ t) * (t * (φ t)⁻¹))⁻¹ * cm (φ t) t := by rw [hab]
        _ = (t * (φ t)⁻¹)⁻¹ * ((t * φ t)⁻¹ * cm (φ t) t) := by group
        _ = (t * (φ t)⁻¹)⁻¹ * (cm (φ t) t * (t * φ t)⁻¹) := by rw [hc''.eq]
        _ = (t * (φ t)⁻¹)⁻¹ * cm (φ t) t * (t * φ t)⁻¹ := by group
  by_cases hCT' : C = T
  · left
    intro t ht
    have htC : t ∈ C := hCT' ▸ ht
    obtain ⟨-, hu⟩ := (hC t).1 htC
    have hφt : φ t = (φ t * t⁻¹) * t := by group
    have h2 : t = (φ t * t⁻¹) * ((φ t * t⁻¹) * t) := by
      calc t = φ (φ t) := (hφ2 t ht).symm
        _ = φ ((φ t * t⁻¹) * t) := by rw [← hφt]
        _ = φ (φ t * t⁻¹) * φ t := hφm _ (zc_le hu) t ht
        _ = (φ t * t⁻¹) * ((φ t * t⁻¹) * t) := by rw [hφZ _ hu, ← hφt]
    have h3 : (φ t * t⁻¹) * (φ t * t⁻¹) = 1 :=
      mul_right_cancel (b := t) (by rw [one_mul, mul_assoc]; exact h2.symm)
    have h4 : φ t * t⁻¹ = 1 := hz1 _ hu h3
    exact mul_inv_eq_one.1 h4
  · by_cases hDT' : D = T
    · right
      intro t ht
      have htD : t ∈ D := hDT' ▸ ht
      exact ((hD t).1 htD).2
    · exfalso
      have hCab := isMulCommutative_of_lt hc hCT hCT'
      have hDab := isMulCommutative_of_lt hc hDT hDT'
      apply hnc
      refine isMulCommutative_iff.2 fun a b => ?_
      obtain ⟨d, hd, c, hcC, hab⟩ := hTDC a a.2
      obtain ⟨d', hd', c', hcC', hba⟩ := hTDC b b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [hab, hba]
      have hdd : d * d' = d' * d := congrArg Subtype.val (mul_comm' (⟨d, hd⟩ : D) ⟨d', hd'⟩)
      have hcc : c * c' = c' * c := congrArg Subtype.val (mul_comm' (⟨c, hcC⟩ : C) ⟨c', hcC'⟩)
      have hcd' : c * d' = d' * c := hcd c hcC d' hd'
      have hc'd : c' * d = d * c' := hcd c' hcC' d hd
      calc d * c * (d' * c') = d * (c * d') * c' := by group
        _ = d * (d' * c) * c' := by rw [hcd']
        _ = (d * d') * (c * c') := by group
        _ = (d' * d) * (c' * c) := by rw [hdd, hcc]
        _ = d' * (d * c') * c := by group
        _ = d' * (c' * d) * c := by rw [hc'd]
        _ = d' * c' * (d * c) := by group

end HeisenbergFacts

section ActionOnQuotient

open Subgroup

variable {G : Type} [Group G]

structure ActData (H T E : Subgroup G) : Prop where
  TH : T ≤ H
  EH : E ≤ H
  inf_eq : T ⊓ E = ⊥
  En : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E
  TEh : ∀ h ∈ H, ∀ t ∈ T, ∃ t' ∈ T, ∃ e ∈ E, h * t * h⁻¹ = t' * e

open Classical in
noncomputable def act (T E : Subgroup G) (h t : G) : G :=
  if hx : ∃ t' ∈ T, t'⁻¹ * (h * t * h⁻¹) ∈ E then hx.choose else 1

variable {H T E : Subgroup G}

theorem ActData.exists_rel (hd : ActData H T E) {h t : G} (hh : h ∈ H) (ht : t ∈ T) :
    act T E h t ∈ T ∧ ∃ e ∈ E, h * t * h⁻¹ = act T E h t * e := by
  have hx : ∃ t' ∈ T, t'⁻¹ * (h * t * h⁻¹) ∈ E := by
    obtain ⟨t', ht', e, he, h1⟩ := hd.TEh h hh t ht
    exact ⟨t', ht', by rw [h1]; simpa using he⟩
  unfold act
  rw [dif_pos hx]
  obtain ⟨hmem, hE⟩ := hx.choose_spec
  refine ⟨hmem, hx.choose⁻¹ * (h * t * h⁻¹), hE, ?_⟩
  group

theorem ActData.act_mem (hd : ActData H T E) {h t : G} (hh : h ∈ H) (ht : t ∈ T) :
    act T E h t ∈ T := (hd.exists_rel hh ht).1

theorem ActData.act_unique (hd : ActData H T E) {h t t' e : G} (hh : h ∈ H) (ht : t ∈ T)
    (ht' : t' ∈ T) (he : e ∈ E) (h1 : h * t * h⁻¹ = t' * e) : t' = act T E h t := by
  obtain ⟨hm, e₀, he₀, h2⟩ := hd.exists_rel hh ht
  have h3 : (act T E h t)⁻¹ * t' = e₀ * e⁻¹ := by
    have : act T E h t * e₀ = t' * e := by rw [← h2, h1]
    calc (act T E h t)⁻¹ * t' = (act T E h t)⁻¹ * (t' * e) * e⁻¹ := by group
      _ = (act T E h t)⁻¹ * (act T E h t * e₀) * e⁻¹ := by rw [this]
      _ = e₀ * e⁻¹ := by group
  have h4 : (act T E h t)⁻¹ * t' ∈ T ⊓ E :=
    ⟨T.mul_mem (T.inv_mem hm) ht', by rw [h3]; exact E.mul_mem he₀ (E.inv_mem he)⟩
  rw [hd.inf_eq, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.1 h4).symm

theorem ActData.act_one_right (hd : ActData H T E) {h : G} (hh : h ∈ H) :
    act T E h 1 = 1 := by
  symm
  exact hd.act_unique hh T.one_mem T.one_mem E.one_mem (by simp)

theorem ActData.act_mul (hd : ActData H T E) {h a b : G} (hh : h ∈ H) (ha : a ∈ T) (hb : b ∈ T) :
    act T E h (a * b) = act T E h a * act T E h b := by
  obtain ⟨hma, ea, hea, h1⟩ := hd.exists_rel hh ha
  obtain ⟨hmb, eb, heb, h2⟩ := hd.exists_rel hh hb
  have hE1 : (act T E h b)⁻¹ * ea * ((act T E h b)⁻¹)⁻¹ ∈ E :=
    hd.En _ (H.inv_mem (hd.TH hmb)) ea hea
  symm
  refine hd.act_unique hh (T.mul_mem ha hb) (T.mul_mem hma hmb) (E.mul_mem hE1 heb) ?_
  calc h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    _ = (act T E h a * ea) * (act T E h b * eb) := by rw [h1, h2]
    _ = (act T E h a * act T E h b) * (((act T E h b)⁻¹ * ea * ((act T E h b)⁻¹)⁻¹) * eb) := by
        group

theorem ActData.act_inv (hd : ActData H T E) {h t : G} (hh : h ∈ H) (ht : t ∈ T) :
    act T E h t⁻¹ = (act T E h t)⁻¹ := by
  have h1 := hd.act_mul hh (T.inv_mem ht) ht
  rw [inv_mul_cancel, hd.act_one_right hh] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem ActData.act_mul_left (hd : ActData H T E) {h h' t : G} (hh : h ∈ H) (hh' : h' ∈ H)
    (ht : t ∈ T) : act T E (h * h') t = act T E h (act T E h' t) := by
  obtain ⟨hm1, e1, he1, r1⟩ := hd.exists_rel hh' ht
  obtain ⟨hm2, e2, he2, r2⟩ := hd.exists_rel hh hm1
  have hE3 : h * e1 * h⁻¹ ∈ E := hd.En h hh e1 he1
  symm
  refine hd.act_unique (H.mul_mem hh hh') ht hm2 (E.mul_mem he2 hE3) ?_
  calc h * h' * t * (h * h')⁻¹ = h * (h' * t * h'⁻¹) * h⁻¹ := by group
    _ = h * (act T E h' t * e1) * h⁻¹ := by rw [r1]
    _ = (h * act T E h' t * h⁻¹) * (h * e1 * h⁻¹) := by group
    _ = (act T E h (act T E h' t) * e2) * (h * e1 * h⁻¹) := by rw [r2]
    _ = act T E h (act T E h' t) * (e2 * (h * e1 * h⁻¹)) := by group

theorem ActData.act_one (hd : ActData H T E) {t : G} (ht : t ∈ T) : act T E 1 t = t := by
  symm
  exact hd.act_unique H.one_mem ht ht E.one_mem (by simp)

end ActionOnQuotient

section InvolutionAction

open Subgroup

variable {G : Type} [Group G]

structure YData (H Y T E : Subgroup G) : Prop extends ActData H T E where
  perm : ∀ h ∈ H, ∃ y ∈ Y, ∃ t ∈ T, h = y * t
  YH : Y ≤ H
  EY : E ≤ Y
  TY : T ⊓ Y = ⊥
  Y2 : IsPGroup 2 Y
  ZY : ∀ z ∈ zc T, z ∈ normalizer (Y : Set G)
  Tc : Nat.card T = 3 ^ 3
  Te : ∀ t ∈ T, t ^ 3 = 1
  Tnc : ¬ IsMulCommutative T

variable {H Y T E : Subgroup G}

theorem YData.act_central (hy : YData H Y T E) {y z : G} (hyY : y ∈ Y) (hz : z ∈ zc T) :
    act T E y z = z := by
  have hzT : z ∈ T := zc_le hz
  have hyH : y ∈ H := hy.YH hyY
  obtain ⟨hm, e, he, h1⟩ := hy.exists_rel hyH hzT
  have hzN := hy.ZY z hz
  have hcT : act T E y z * z⁻¹ ∈ T := T.mul_mem hm (T.inv_mem hzT)
  have hcY : act T E y z * z⁻¹ ∈ Y := by
    have hzy : z * y⁻¹ * z⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 hzN y⁻¹).1 (Y.inv_mem hyY)
    have hyzY : y * z * y⁻¹ * z⁻¹ ∈ Y := by
      have := Y.mul_mem hyY hzy
      simpa [mul_assoc] using this
    have hzez : z * e⁻¹ * z⁻¹ ∈ E := by
      have := hy.En z (hy.TH hzT) e⁻¹ (E.inv_mem he)
      exact this
    have e1 : act T E y z * z⁻¹ = (y * z * y⁻¹ * z⁻¹) * (z * e⁻¹ * z⁻¹) := by
      rw [h1]; group
    rw [e1]
    exact Y.mul_mem hyzY (hy.EY hzez)
  have h2 : act T E y z * z⁻¹ ∈ T ⊓ Y := ⟨hcT, hcY⟩
  rw [hy.TY, Subgroup.mem_bot] at h2
  exact mul_inv_eq_one.1 h2

theorem YData.act_dichotomy (hy : YData H Y T E) {y : G} (hyY : y ∈ Y) (hy2 : y * y = 1) :
    (∀ t ∈ T, act T E y t = t) ∨ (∀ t ∈ T, act T E y t * t ∈ zc T) := by
  have hyH := hy.YH hyY
  refine noReflection hy.Tc hy.Tnc hy.Te (φ := act T E y)
    (fun t ht => hy.act_mem hyH ht) (fun a ha b hb => hy.act_mul hyH ha hb)
    (fun z hz => hy.act_central hyY hz) (fun t ht => ?_)
  rw [← hy.act_mul_left hyH hyH ht, hy2, hy.act_one ht]

theorem YData.triv_of_quot (hy : YData H Y T E) {y : G} (hyY : y ∈ Y)
    (h : ∀ t ∈ T, act T E y t * t⁻¹ ∈ zc T) : ∀ t ∈ T, act T E y t = t := by
  intro t ht
  have hyH := hy.YH hyY
  obtain ⟨z, hz⟩ : ∃ z, z = act T E y t * t⁻¹ := ⟨_, rfl⟩
  have hzc : z ∈ zc T := by rw [hz]; exact h t ht
  have hzT : z ∈ T := zc_le hzc
  have hact : act T E y t = z * t := by rw [hz]; group
  have hpow : ∀ n : ℕ, act T E (y ^ n) t = z ^ n * t := by
    intro n
    induction n with
    | zero => simpa using hy.act_one ht
    | succ n ih =>
      have hyn : y ^ n ∈ H := H.pow_mem hyH n
      have hzn : z ^ n ∈ zc T := (zc T).pow_mem hzc n
      have hznT : z ^ n * t ∈ T := T.mul_mem (zc_le hzn) ht
      rw [pow_succ', hy.act_mul_left hyH hyn ht, ih, hy.act_mul hyH (zc_le hzn) ht,
        hy.act_central hyY hzn, hact, pow_succ, mul_assoc]
  obtain ⟨m, hm⟩ := hy.Y2 ⟨y, hyY⟩
  have hym : y ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have h1 : z ^ (2 ^ m) * t = t := by
    rw [← hpow, hym]
    exact hy.act_one ht
  have h2 : z ^ (2 ^ m) = 1 := by
    have := h1
    exact (mul_eq_right.1 this)
  have h3 : z ^ 3 = 1 := hy.Te z hzT
  have h4 : z ^ (Nat.gcd (2 ^ m) 3) = 1 := pow_gcd_eq_one.2 ⟨h2, h3⟩
  have h5 : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  rw [h5, pow_one] at h4
  rw [hact, h4, one_mul]

theorem YData.neg_mul_neg (hy : YData H Y T E) {y y' : G} (hyY : y ∈ Y) (hy'Y : y' ∈ Y)
    (hn : ∀ t ∈ T, act T E y t * t ∈ zc T) (hn' : ∀ t ∈ T, act T E y' t * t ∈ zc T) :
    ∀ t ∈ T, act T E (y * y') t * t⁻¹ ∈ zc T := by
  intro t ht
  have hyH := hy.YH hyY
  have hy'H := hy.YH hy'Y
  set z₁ := act T E y' t * t with hz₁
  set z₂ := act T E y t * t with hz₂
  have hz₁c : z₁ ∈ zc T := hn' t ht
  have hz₂c : z₂ ∈ zc T := hn t ht
  have h1 : act T E y' t = z₁ * t⁻¹ := by rw [hz₁]; group
  have h2 : act T E y t = z₂ * t⁻¹ := by rw [hz₂]; group
  have hz₂T : z₂ ∈ T := zc_le hz₂c
  have e : act T E (y * y') t = z₁ * (t * z₂⁻¹) := by
    rw [hy.act_mul_left hyH hy'H ht, h1, hy.act_mul hyH (zc_le hz₁c) (T.inv_mem ht),
      hy.act_central hyY hz₁c, hy.act_inv hyH ht, h2]
    group
  rw [e]
  have hc : Commute z₂⁻¹ t := (commute_of_zc ((zc T).inv_mem hz₂c) ht)
  have e2 : z₁ * (t * z₂⁻¹) * t⁻¹ = z₁ * z₂⁻¹ := by
    calc z₁ * (t * z₂⁻¹) * t⁻¹ = z₁ * (t * z₂⁻¹ * t⁻¹) := by group
      _ = z₁ * z₂⁻¹ := by rw [hc.symm.mul_inv_cancel]
  rw [e2]
  exact (zc T).mul_mem hz₁c ((zc T).inv_mem hz₂c)

end InvolutionAction

section ActionKernel

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

noncomputable def Ktr (hy : YData H Y T E) : Subgroup G where
  carrier := {y | y ∈ Y ∧ ∀ t ∈ T, act T E y t = t}
  mul_mem' := by
    rintro a b ⟨haY, ha⟩ ⟨hbY, hb⟩
    refine ⟨Y.mul_mem haY hbY, fun t ht => ?_⟩
    rw [hy.act_mul_left (hy.YH haY) (hy.YH hbY) ht, hb t ht, ha t ht]
  one_mem' := ⟨Y.one_mem, fun t ht => hy.act_one ht⟩
  inv_mem' := by
    rintro a ⟨haY, ha⟩
    refine ⟨Y.inv_mem haY, fun t ht => ?_⟩
    have h1 := hy.act_mul_left (hy.YH (Y.inv_mem haY)) (hy.YH haY) ht
    rw [inv_mul_cancel, hy.act_one ht, ha t ht] at h1
    exact h1.symm

theorem mem_Ktr {hy : YData H Y T E} {y : G} :
    y ∈ Ktr hy ↔ y ∈ Y ∧ ∀ t ∈ T, act T E y t = t := Iff.rfl

theorem Ktr_le_Y (hy : YData H Y T E) : Ktr hy ≤ Y := fun _ h => h.1

theorem Ktr_conj (hy : YData H Y T E) {y k : G} (hyY : y ∈ Y) (hk : k ∈ Ktr hy) :
    y * k * y⁻¹ ∈ Ktr hy := by
  refine ⟨Y.mul_mem (Y.mul_mem hyY hk.1) (Y.inv_mem hyY), fun t ht => ?_⟩
  have hyH := hy.YH hyY
  have hkH := hy.YH hk.1
  have hyiH : y⁻¹ ∈ H := H.inv_mem hyH
  rw [hy.act_mul_left (H.mul_mem hyH hkH) hyiH ht, hy.act_mul_left hyH hkH (hy.act_mem hyiH ht),
    hk.2 _ (hy.act_mem hyiH ht), ← hy.act_mul_left hyH hyiH ht, mul_inv_cancel, hy.act_one ht]

theorem Ktr_comm (hy : YData H Y T E) {k t : G} (hk : k ∈ Ktr hy) (ht : t ∈ T) :
    ∃ e ∈ E, t * k * t⁻¹ = e * k := by
  have hkH := hy.YH hk.1
  obtain ⟨-, e, he, h1⟩ := hy.exists_rel hkH (T.inv_mem ht)
  rw [hk.2 t⁻¹ (T.inv_mem ht)] at h1
  refine ⟨e, he, ?_⟩
  calc t * k * t⁻¹ = t * (k * t⁻¹ * k⁻¹) * k := by group
    _ = t * (t⁻¹ * e) * k := by rw [h1]
    _ = e * k := by group

end ActionKernel

section ThompsonSubgroup

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

theorem mem_normalizer_of_forall_mem [Finite G] {L : Subgroup G} {g : G}
    (h : ∀ x ∈ L, g * x * g⁻¹ ∈ L) : g ∈ normalizer (L : Set G) := by
  have hle : L.map (MulAut.conj g).toMonoidHom ≤ L := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using h x hx
  have heq : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem le_thompsonJ' {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ thompsonJ S :=
  le_iSup₂_of_le A hA le_rfl

theorem thompsonJ_le_sup_Ktr (hy : YData H Y T E) {j₀ : G} (hj₀J : j₀ ∈ thompsonJ Y)
    (hneg : ∀ t ∈ T, act T E j₀ t * t ∈ zc T) [Finite G] :
    thompsonJ Y ≤ (thompsonJ Y ⊓ Ktr hy) ⊔ zpowers j₀ := by
  refine iSup₂_le fun A hA => ?_
  intro a ha
  have haY : a ∈ Y := hA.1 ha
  have haJ : a ∈ thompsonJ Y := le_thompsonJ' hA ha
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a ha
    rwa [pow_two] at this
  have hj₀Y : j₀ ∈ Y := Generic49U3.thompsonJ_le_self Y hj₀J
  rcases hy.act_dichotomy haY ha2 with hT | hN
  · exact mem_sup_left ⟨haJ, mem_Ktr.2 ⟨haY, hT⟩⟩
  · have hmul := hy.neg_mul_neg haY hj₀Y hN hneg
    have hK : a * j₀ ∈ Ktr hy :=
      mem_Ktr.2 ⟨Y.mul_mem haY hj₀Y, hy.triv_of_quot (Y.mul_mem haY hj₀Y) hmul⟩
    have hJ : a * j₀ ∈ thompsonJ Y := (thompsonJ Y).mul_mem haJ hj₀J
    have hae : a = (a * j₀) * j₀⁻¹ := by group
    rw [hae]
    exact Subgroup.mul_mem _ (mem_sup_left ⟨hJ, hK⟩)
      (mem_sup_right (Subgroup.inv_mem _ (mem_zpowers j₀)))

theorem T_le_sup [Finite G] (hy : YData H Y T E) (hYsyl : IsSylowTwoOf Y H) {j₀ : G}
    (hj₀J : j₀ ∈ thompsonJ Y) (hneg : ∀ t ∈ T, act T E j₀ t * t ∈ zc T) :
    T ≤ thompsonJ H ⊔ E := by
  have hj₀H : j₀ ∈ thompsonJ H := thompsonJ_le_thompsonJ_of_isSylowTwoOf hYsyl hj₀J
  have hj₀Y : j₀ ∈ Y := Generic49U3.thompsonJ_le_self Y hj₀J
  have hj₀Hm : j₀ ∈ H := hy.YH hj₀Y
  have hJN : H ≤ normalizer (thompsonJ H : Set G) := B2F.R_le_normalizer_thompsonJ H
  have key : ∀ u ∈ T, u * (act T E j₀ u)⁻¹ ∈ thompsonJ H ⊔ E := by
    intro u hu
    have huH := hy.TH hu
    obtain ⟨-, e, he, h1⟩ := hy.exists_rel hj₀Hm (T.inv_mem hu)
    rw [hy.act_inv hj₀Hm hu] at h1
    have hc : u * j₀ * u⁻¹ * j₀⁻¹ ∈ thompsonJ H := by
      have h2 : u * j₀ * u⁻¹ ∈ thompsonJ H := (Subgroup.mem_normalizer_iff.1 (hJN huH) j₀).1 hj₀H
      exact (thompsonJ H).mul_mem h2 ((thompsonJ H).inv_mem hj₀H)
    have h3 : u * (act T E j₀ u)⁻¹ = (u * j₀ * u⁻¹ * j₀⁻¹) * e⁻¹ := by
      have : j₀ * u⁻¹ * j₀⁻¹ = (act T E j₀ u)⁻¹ * e := h1
      calc u * (act T E j₀ u)⁻¹ = u * ((act T E j₀ u)⁻¹ * e) * e⁻¹ := by group
        _ = u * (j₀ * u⁻¹ * j₀⁻¹) * e⁻¹ := by rw [← this]
        _ = (u * j₀ * u⁻¹ * j₀⁻¹) * e⁻¹ := by group
    rw [h3]
    exact Subgroup.mul_mem _ (mem_sup_left hc) (mem_sup_right (E.inv_mem he))
  have hX : (T ⊓ (thompsonJ H ⊔ E)) = T := by
    refine eq_of_sup_zc hy.Tc hy.Tnc inf_le_left ?_
    intro t ht
    set u := t ^ 2 with hu
    have huT : u ∈ T := T.pow_mem ht 2
    set s := act T E j₀ u with hs
    have hsT : s ∈ T := hy.act_mem hj₀Hm huT
    have hz : s * u ∈ zc T := hneg u huT
    have hx : u * s⁻¹ ∈ T ⊓ (thompsonJ H ⊔ E) :=
      ⟨T.mul_mem huT (T.inv_mem hsT), key u huT⟩
    refine ⟨u * s⁻¹, hx, s * u, hz, ?_⟩
    have h4 : t ^ 3 = 1 := hy.Te t ht
    calc t = t ^ 4 := by
          calc t = t * t ^ 3 := by rw [h4, mul_one]
            _ = t ^ 4 := by group
      _ = u * u := by rw [hu]; group
      _ = u * s⁻¹ * (s * u) := by group
  intro t ht
  have : t ∈ T ⊓ (thompsonJ H ⊔ E) := by rw [hX]; exact ht
  exact this.2

end ThompsonSubgroup

section ActionOfThompson

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

theorem autI_inf_Ktr_eq_bot [Finite G] (hy : YData H Y T E) {V : Subgroup G}
    (hU : IsElemAbelian 2 V) (hred : IsTwoReducedIn H V) (hEV : E ≤ centralizer (V : Set G)) :
    autI hU (thompsonJ Y ⊓ Ktr hy) = ⊥ := by
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  set K₁ : Subgroup G := thompsonJ Y ⊓ Ktr hy with hK₁
  have hK₁Y : K₁ ≤ Y := inf_le_right.trans (Ktr_le_Y hy)
  have hK₁N : K₁ ≤ normalizer (V : Set G) := hK₁Y.trans (hy.YH.trans hHN)
  have hEN : E ≤ normalizer (V : Set G) := hy.EH.trans hHN
  have hEbot : autI hU E = ⊥ := autI_eq_bot_of_le_centralizer hU hEV
  have hconj : ∀ h ∈ H, ∀ k ∈ K₁, h * k * h⁻¹ ∈ E ⊔ K₁ := by
    intro h hh k hk
    obtain ⟨y, hyY, t, htT, rfl⟩ := hy.perm h hh
    obtain ⟨e, he, hte⟩ := Ktr_comm hy hk.2 htT
    have h1 : y * t * k * (y * t)⁻¹ = (y * e * y⁻¹) * (y * k * y⁻¹) := by
      calc y * t * k * (y * t)⁻¹ = y * (t * k * t⁻¹) * y⁻¹ := by group
        _ = y * (e * k) * y⁻¹ := by rw [hte]
        _ = (y * e * y⁻¹) * (y * k * y⁻¹) := by group
    rw [h1]
    refine Subgroup.mul_mem _ (mem_sup_left (hy.En y (hy.YH hyY) e he)) (mem_sup_right ?_)
    refine ⟨?_, Ktr_conj hy hyY hk.2⟩
    exact (Subgroup.mem_normalizer_iff.1 (B2F.R_le_normalizer_thompsonJ Y hyY) k).1 hk.1
  have hQle : autI hU K₁ ≤ autI hU H := autI_mono hU (hK₁Y.trans hy.YH)
  have hQn : autI hU H ≤ normalizer (autI hU K₁ : Set (MulAut (IntMod V hU))) := by
    intro φ hφ
    obtain ⟨g, hgH, rfl⟩ := (mem_autI hU).1 hφ
    apply mem_normalizer_of_forall_mem
    intro ψ hψ
    obtain ⟨k, hkK, rfl⟩ := (mem_autI hU).1 hψ
    have hmul : convI hU g * convI hU k * (convI hU g)⁻¹ = convI hU (g * k * g⁻¹) := by
      simp [map_mul, map_inv]
    rw [hmul]
    have hmem : ((g : G) * (k : G) * (g : G)⁻¹) ∈ E ⊔ K₁ := hconj g hgH k hkK
    have hmem2 := convI_mem_autI hU hmem
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 k.2) (Subgroup.inv_mem _ g.2))
    rw [autI_sup hU hEN hK₁N, hEbot, bot_sup_eq] at hmem2
    exact hmem2
  exact B2F.eq_bot_of_normal_isPGroup hU hred hQle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQle).2 hQn)
    (B2F.isPGroup_autI hU (hy.Y2.to_le hK₁Y) hK₁N)

theorem card_autI_zpowers_le [Finite G] {V : Subgroup G} (hU : IsElemAbelian 2 V) {j : G}
    (hjN : j ∈ normalizer (V : Set G)) (hj2 : j * j = 1) :
    Nat.card (autI hU (zpowers j)) ≤ 2 := by
  set c : MulAut (IntMod V hU) := convI hU ⟨j, hjN⟩ with hc
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two, hc, ← map_mul]
    have : (⟨j, hjN⟩ * ⟨j, hjN⟩ : normalizer (V : Set G)) = 1 := Subtype.ext (by simpa using hj2)
    rw [this, map_one]
  have hle : autI hU (zpowers j) ≤ zpowers c := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 hφ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hgn : g = ⟨j, hjN⟩ ^ n := Subtype.ext (by simpa using hn.symm)
    rw [hgn, map_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  calc Nat.card (autI hU (zpowers j)) ≤ Nat.card (zpowers c) := Subgroup.card_le_of_le hle
    _ = orderOf c := Nat.card_zpowers c
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hc2

theorem card_le_of_isSylowTwoOf [Finite G] {S B P : Subgroup G} (hS : IsSylowTwoOf S B)
    (hPB : P ≤ B) (hP : IsPGroup 2 P) : Nat.card P ≤ Nat.card S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  have h1 : Nat.card S * (S.subgroupOf B).index = Nat.card B := by
    have := Subgroup.card_mul_index (S.subgroupOf B)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv] at this
  have h2 : Nat.card P ∣ Nat.card B := Subgroup.card_dvd_of_le hPB
  rw [← h1, ha] at h2
  have hcop : Nat.Coprime (2 ^ a) (S.subgroupOf B).index :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hS.2.2)
  have h3 : 2 ^ a ∣ Nat.card S := hcop.dvd_of_dvd_mul_right h2
  rw [ha]
  exact Nat.le_of_dvd Nat.card_pos h3

end ActionOfThompson

section CaseTwoPrelim

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

theorem exists_neg_involution [Finite G] (hy : YData H Y T E) {V : Subgroup G}
    (hU : IsElemAbelian 2 V) (hred : IsTwoReducedIn H V) (hEV : E ≤ centralizer (V : Set G))
    (hJ : ¬ thompsonJ Y ≤ centralizer (V : Set G)) :
    ∃ j₀ ∈ thompsonJ Y, j₀ * j₀ = 1 ∧ ∀ t ∈ T, act T E j₀ t * t ∈ zc T := by
  by_contra hcon
  have hJK : thompsonJ Y ≤ Ktr hy := by
    refine iSup₂_le fun A hA => ?_
    intro a ha
    have haY : a ∈ Y := hA.1 ha
    have haJ : a ∈ thompsonJ Y := le_thompsonJ' hA ha
    have ha2 : a * a = 1 := by
      have := hA.2.1.2 a ha
      rwa [pow_two] at this
    rcases hy.act_dichotomy haY ha2 with hT | hN
    · exact mem_Ktr.2 ⟨haY, hT⟩
    · exact (hcon ⟨a, haJ, ha2, hN⟩).elim
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  have hJYN : thompsonJ Y ≤ normalizer (V : Set G) :=
    (Generic49U3.thompsonJ_le_self Y).trans (hy.YH.trans hHN)
  have hbot : autI hU (thompsonJ Y) = ⊥ := by
    have h1 := autI_inf_Ktr_eq_bot hy hU hred hEV
    rwa [inf_eq_left.2 hJK] at h1
  exact hJ ((autI_eq_bot_iff hU hJYN).1 hbot)

theorem card_autI_thompsonJ_le [Finite G] (hy : YData H Y T E) {V : Subgroup G}
    (hU : IsElemAbelian 2 V) (hred : IsTwoReducedIn H V) (hEV : E ≤ centralizer (V : Set G))
    {j₀ : G} (hj₀J : j₀ ∈ thompsonJ Y) (hj₀2 : j₀ * j₀ = 1)
    (hneg : ∀ t ∈ T, act T E j₀ t * t ∈ zc T) :
    Nat.card (autI hU (thompsonJ Y)) ≤ 2 := by
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  have hYN : Y ≤ normalizer (V : Set G) := hy.YH.trans hHN
  have hj₀Y : j₀ ∈ Y := Generic49U3.thompsonJ_le_self Y hj₀J
  have hj₀N : j₀ ∈ normalizer (V : Set G) := hYN hj₀Y
  have hK₁N : (thompsonJ Y ⊓ Ktr hy) ≤ normalizer (V : Set G) :=
    inf_le_right.trans ((Ktr_le_Y hy).trans hYN)
  have hzN : zpowers j₀ ≤ normalizer (V : Set G) := zpowers_le.2 hj₀N
  have hle : autI hU (thompsonJ Y) ≤ autI hU (zpowers j₀) := by
    calc autI hU (thompsonJ Y) ≤ autI hU ((thompsonJ Y ⊓ Ktr hy) ⊔ zpowers j₀) :=
          autI_mono hU (thompsonJ_le_sup_Ktr hy hj₀J hneg)
      _ = autI hU (thompsonJ Y ⊓ Ktr hy) ⊔ autI hU (zpowers j₀) := autI_sup hU hK₁N hzN
      _ = autI hU (zpowers j₀) := by rw [autI_inf_Ktr_eq_bot hy hU hred hEV, bot_sup_eq]
  exact (Subgroup.card_le_of_le hle).trans (card_autI_zpowers_le hU hj₀N hj₀2)

theorem card_eq_six_of_actsAsNaturalL2 {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {U : Subgroup W} (h : ActsAsNaturalL2 L U) : Nat.card L = 6 := by
  obtain ⟨e, -, -⟩ := h
  rw [Nat.card_congr e.toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end CaseTwoPrelim

section CaseTwo

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

theorem exists_involution_of_card_six {K : Type*} [Group K] [Finite K] (h : Nat.card K = 6) :
    ∃ a : K, a ≠ 1 ∧ a * a = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [h]; norm_num)
  refine ⟨a, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at ha
    omega
  · rw [← pow_two]
    rw [← ha]
    exact pow_orderOf_eq_one a

theorem caseTwo_card [Finite G] (hy : YData H Y T E) (hYsyl : IsSylowTwoOf Y H) {V : Subgroup G}
    (hU : IsElemAbelian 2 V) (hred : IsTwoReducedIn H V) (hEV : E ≤ centralizer (V : Set G))
    (hJ : ¬ thompsonJ Y ≤ centralizer (V : Set G))
    (I : Finset (Subgroup (MulAut (IntMod V hU))))
    (hSyl : IsSylowTwoOf (autI hU (thompsonJ Y)) (autI hU (thompsonJ H)))
    (hEq : autI hU (thompsonJ H) = ⨆ L ∈ I, L)
    (hcomm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥)
    (hNat : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)) :
    Nat.card (autI hU T) ≤ 3 := by
  have hHN : H ≤ normalizer (V : Set G) := hred.2.1
  have hYH : Y ≤ H := hy.YH
  have hJYH : thompsonJ Y ≤ thompsonJ H := thompsonJ_le_thompsonJ_of_isSylowTwoOf hYsyl
  have hJHN : thompsonJ H ≤ normalizer (V : Set G) :=
    (iSup₂_le fun _ hA => hA.1 : thompsonJ H ≤ H).trans hHN
  have hEN : E ≤ normalizer (V : Set G) := hy.EH.trans hHN
  obtain ⟨j₀, hj₀J, hj₀2, hneg⟩ := exists_neg_involution hy hU hred hEV hJ
  have h2 : Nat.card (autI hU (thompsonJ Y)) ≤ 2 :=
    card_autI_thompsonJ_le hy hU hred hEV hj₀J hj₀2 hneg
  have hIne : I.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hbot : autI hU (thompsonJ H) = ⊥ := by simpa using hEq
    have hle : autI hU (thompsonJ Y) ≤ ⊥ := hbot ▸ autI_mono hU hJYH
    exact hJ ((autI_eq_bot_iff hU ((Generic49U3.thompsonJ_le_self Y).trans (hYH.trans hHN))).1
      (le_bot_iff.1 hle))
  obtain ⟨L, hL⟩ := hIne
  have hL6 : ∀ L' ∈ I, Nat.card L' = 6 := fun L' hL' => card_eq_six_of_actsAsNaturalL2 (hNat L' hL')
  have hI1 : ∀ L' ∈ I, L' = L := by
    intro L' hL'
    by_contra hne
    haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [hL6 L hL]; norm_num)
    haveI : Finite L' := Nat.finite_of_card_ne_zero (by rw [hL6 L' hL']; norm_num)
    obtain ⟨a, ha1, ha2⟩ := exists_involution_of_card_six (hL6 L hL)
    obtain ⟨b, hb1, hb2⟩ := exists_involution_of_card_six (hL6 L' hL')
    have hcab : (a : MulAut (IntMod V hU)) * b = b * a :=
      hcomm L hL L' hL' (Ne.symm hne) a a.2 b b.2
    have hLL' : L ⊓ L' = ⊥ := by
      refine eq_bot_iff.2 ?_
      calc L ⊓ L' ≤ L ⊓ ⨆ L'' ∈ I, ⨆ (_ : L'' ≠ L), L'' :=
            inf_le_inf_left _ (le_iSup₂_of_le L' hL' (le_iSup_of_le hne le_rfl))
        _ = ⊥ := hind L hL
        _ ≤ ⊥ := le_rfl
    have haord : orderOf (a : MulAut (IntMod V hU)) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        simpa using congrArg Subtype.val ha2
      · intro h1
        exact ha1 (Subtype.ext h1)
    have hbord : orderOf (b : MulAut (IntMod V hU)) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        simpa using congrArg Subtype.val hb2
      · intro h1
        exact hb1 (Subtype.ext h1)
    have hza : Nat.card (zpowers (a : MulAut (IntMod V hU))) = 2 := by
      rw [Nat.card_zpowers, haord]
    have hzb : Nat.card (zpowers (b : MulAut (IntMod V hU))) = 2 := by
      rw [Nat.card_zpowers, hbord]
    have hzcomm : ∀ x ∈ zpowers (a : MulAut (IntMod V hU)),
        ∀ y ∈ zpowers (b : MulAut (IntMod V hU)), x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_zpow (show Commute (a : MulAut (IntMod V hU)) b from hcab) m n).eq
    have hzinf : zpowers (a : MulAut (IntMod V hU)) ⊓ zpowers (b : MulAut (IntMod V hU)) = ⊥ := by
      refine eq_bot_iff.2 ?_
      calc zpowers (a : MulAut (IntMod V hU)) ⊓ zpowers (b : MulAut (IntMod V hU)) ≤ L ⊓ L' :=
            inf_le_inf (zpowers_le.2 a.2) (zpowers_le.2 b.2)
        _ = ⊥ := hLL'
        _ ≤ ⊥ := le_rfl
    have hP := B2F.card_sup_mul_card_inf_of_commute hzcomm
    rw [hzinf, hza, hzb, Subgroup.card_bot] at hP
    have hP4 : Nat.card ↥(zpowers (a : MulAut (IntMod V hU)) ⊔
        zpowers (b : MulAut (IntMod V hU))) = 4 := by omega
    have hPp : IsPGroup 2 ↥(zpowers (a : MulAut (IntMod V hU)) ⊔
        zpowers (b : MulAut (IntMod V hU))) :=
      IsPGroup.of_card (n := 2) (by rw [hP4]; norm_num)
    have hPle : zpowers (a : MulAut (IntMod V hU)) ⊔ zpowers (b : MulAut (IntMod V hU)) ≤
        autI hU (thompsonJ H) := by
      rw [hEq]
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact (le_iSup₂ (f := fun L'' _ => L'') L hL : L ≤ ⨆ L'' ∈ I, L'') a.2
      · exact (le_iSup₂ (f := fun L'' _ => L'') L' hL' : L' ≤ ⨆ L'' ∈ I, L'') b.2
    have h4 := card_le_of_isSylowTwoOf hSyl hPle hPp
    omega
  have hEqL : autI hU (thompsonJ H) = L := by
    rw [hEq]
    exact le_antisymm (iSup₂_le fun L' hL' => (hI1 L' hL').le) (le_iSup₂_of_le L hL le_rfl)
  have hTle : T ≤ thompsonJ H ⊔ E := T_le_sup hy hYsyl hj₀J hneg
  have hEbot : autI hU E = ⊥ := autI_eq_bot_of_le_centralizer hU hEV
  have hTL : autI hU T ≤ L := by
    calc autI hU T ≤ autI hU (thompsonJ H ⊔ E) := autI_mono hU hTle
      _ = autI hU (thompsonJ H) ⊔ autI hU E := autI_sup hU hJHN hEN
      _ = L := by rw [hEbot, sup_bot_eq, hEqL]
  have hdvd : Nat.card (autI hU T) ∣ 6 := by
    have h1 : Nat.card (autI hU T) ∣ Nat.card L := Subgroup.card_dvd_of_le hTL
    rwa [hL6 L hL] at h1
  have hcube : ∀ x ∈ autI hU T, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hU).1 hx
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hy.Te g hgT)
    rw [← map_pow, hg3, map_one]
  haveI : Finite (autI hU T) := inferInstance
  have hodd : ¬ 2 ∣ Nat.card (autI hU T) := by
    intro h2d
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := autI hU T) 2 h2d
    have h3 : (a : MulAut (IntMod V hU)) ^ 3 = 1 := hcube a a.2
    have h4 : orderOf (a : MulAut (IntMod V hU)) = 2 := by
      rw [← ha]
      exact (Subgroup.orderOf_coe a)
    have h5 : orderOf (a : MulAut (IntMod V hU)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [h4] at h5
    omega
  have hcop : Nat.Coprime (Nat.card (autI hU T)) 2 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have h3d : Nat.card (autI hU T) ∣ 3 := by
    have : Nat.card (autI hU T) ∣ 2 * 3 := hdvd
    exact hcop.dvd_of_dvd_mul_left this
  exact Nat.le_of_dvd (by norm_num) h3d

end CaseTwo

section NoncentralNormalizing

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable {H Y T E : Subgroup G}

theorem le_centralizer_omegaOneCenter (Y : Subgroup G) :
    Y ≤ centralizer (quasithinOmegaOneCenter Y : Set G) := by
  have hZ : quasithinOmegaOneCenter Y ≤ centralizer (Y : Set G) := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    exact hz.1.2
  exact Subgroup.le_centralizer_iff.2 hZ

theorem le_centralizer_conjClosure [Finite G] (hy : YData H Y T E) :
    E ≤ centralizer ((conjClosure (quasithinOmegaOneCenter Y) H : Subgroup G) : Set G) := by
  have hZ : quasithinOmegaOneCenter Y ≤ centralizer (Y : Set G) := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    exact hz.1.2
  have : conjClosure (quasithinOmegaOneCenter Y) H ≤ centralizer (E : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have he' : h⁻¹ * e * h ∈ E := by
      have := hy.En h⁻¹ (H.inv_mem hh) e he
      simpa using this
    have hzc : (h⁻¹ * e * h) * z = z * (h⁻¹ * e * h) :=
      Subgroup.mem_centralizer_iff.1 (hZ hz) _ (hy.EY he')
    calc e * (h * z * h⁻¹) = h * ((h⁻¹ * e * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * e * h)) * h⁻¹ := by rw [hzc]
      _ = (h * z * h⁻¹) * e := by group
  exact Subgroup.le_centralizer_iff.2 this

theorem exists_noncentral_normalizing [Finite G] (hy : YData H Y T E) (hYsyl : IsSylowTwoOf Y H)
    (hsolv : Group.IsSolvable ↥H) (hF : CharTwo H) :
    ∃ t ∈ T, t ∉ zc T ∧ (t ∈ normalizer (thompsonJ Y : Set G) ∨
      t ∈ normalizer (quasithinOmegaOneCenter Y : Set G)) := by
  obtain ⟨hU, hred, hcase, -⟩ := B2_16 (G := G) (H := H) (T := Y)
    (V := conjClosure (quasithinOmegaOneCenter Y) H) hsolv hF hYsyl rfl
  have hHN : H ≤ normalizer ((conjClosure (quasithinOmegaOneCenter Y) H : Subgroup G) : Set G) :=
    hred.2.1
  have hEV := le_centralizer_conjClosure hy
  have hHle : H ≤ Y ⊔ T := fun h hh => by
    obtain ⟨y, hyY, t, htT, rfl⟩ := hy.perm h hh
    exact Subgroup.mul_mem _ (mem_sup_left hyY) (mem_sup_right htT)
  have hSup : Y ⊔ T ≤ H := sup_le hy.YH hy.TH
  have hperm : ∀ w ∈ Y ⊔ T, ∃ y ∈ Y, ∃ t ∈ T, w = y * t := fun w hw => hy.perm w (hSup hw)
  rcases hcase with ⟨-, hfac⟩ | ⟨hJ, I, hSyl, hEq, hcomm, hind, hNat, -⟩
  ·
    have hY₁ : Y ≤ H ⊓ normalizer (thompsonJ Y : Set G) :=
      le_inf hy.YH (B2F.R_le_normalizer_thompsonJ Y)
    have hY₂ : Y ≤ H ⊓ centralizer (quasithinOmegaOneCenter Y : Set G) :=
      le_inf hy.YH (le_centralizer_omegaOneCenter Y)
    have hprod := Glauberman281.exists_mul_of_factorization hperm hY₁ hY₂
      (inf_le_left.trans hHle) (fun w hw => hfac w (hSup hw))
    by_contra hcon
    have hnc : ∀ t ∈ T, (t ∈ normalizer (thompsonJ Y : Set G) ∨
        t ∈ normalizer (quasithinOmegaOneCenter Y : Set G)) → t ∈ zc T := by
      intro t ht hN
      by_contra hnz
      exact hcon ⟨t, ht, hnz, hN⟩
    have hcen : T ≤ zc T := by
      intro q hq
      obtain ⟨a, ha, b, hb, rfl⟩ := hprod q hq
      exact (zc T).mul_mem (hnc a ha.1 (Or.inl ha.2.2))
        (hnc b hb.1 (Or.inr (Subgroup.centralizer_le_normalizer _ hb.2.2)))
    exact hy.Tnc (isMulCommutative_iff.2 fun a b => Subtype.ext (zc_comm (hcen a.2) b.2))
  ·
    have h3 := caseTwo_card hy hYsyl hU hred hEV hJ I hSyl hEq hcomm hind hNat
    have hTN : T ≤ normalizer ((conjClosure (quasithinOmegaOneCenter Y) H : Subgroup G) : Set G) :=
      hy.TH.trans hHN
    have hcard := card_autI_mul_card_inf hU hTN
    have hpos : 0 < Nat.card (autI hU T) := Nat.card_pos
    rw [hy.Tc] at hcard
    have hcard' : Nat.card (autI hU T) *
        Nat.card ↥(T ⊓ centralizer ((conjClosure (quasithinOmegaOneCenter Y) H : Subgroup G) :
          Set G)) = 27 := by
      rw [hcard]; norm_num
    have h9 : 9 ≤ Nat.card ↥(T ⊓ centralizer ((conjClosure (quasithinOmegaOneCenter Y) H :
        Subgroup G) : Set G)) := by
      by_contra hlt
      have h8 : Nat.card ↥(T ⊓ centralizer ((conjClosure (quasithinOmegaOneCenter Y) H :
          Subgroup G) : Set G)) ≤ 8 := by omega
      have := Nat.mul_le_mul h3 h8
      omega
    have hnle : ¬ (T ⊓ centralizer ((conjClosure (quasithinOmegaOneCenter Y) H : Subgroup G) :
        Set G)) ≤ zc T := by
      intro hle
      have := Subgroup.card_le_of_le hle
      rw [zc_card hy.Tc hy.Tnc] at this
      omega
    obtain ⟨t, htC, htz⟩ := SetLike.not_le_iff_exists.1 hnle
    refine ⟨t, htC.1, htz, Or.inr ?_⟩
    have hZV : quasithinOmegaOneCenter Y ≤ conjClosure (quasithinOmegaOneCenter Y) H :=
      le_conjClosure _ _
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun z hz => hZV hz) htC.2)

end NoncentralNormalizing

section CaseOneLemmas

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
  (three_le_pRank_of_not_le normalizer_le_normalizer_thompsonJ'
    normalizer_le_normalizer_omegaOneCenter thompsonJ_ne_bot_of_two_group
    omegaOneCenter_ne_bot_of_two_group case1_mem_normalizer_of_comm)

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : A ≤ normalizer (B : Set G)) :
    ∀ v ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, v = a * b := by
  let D : Subgroup G :=
    { carrier := {v | ∃ a ∈ A, ∃ b ∈ B, v = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have h1 : a'⁻¹ * b * a' ∈ B := by
          have := (Subgroup.mem_normalizer_iff.1 (hAB (A.inv_mem ha')) b).1 hb
          simpa using this
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * b * a') * b', B.mul_mem h1 hb', ?_⟩
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have h1 : a * b⁻¹ * a⁻¹ ∈ B :=
          (Subgroup.mem_normalizer_iff.1 (hAB ha) b⁻¹).1 (B.inv_mem hb)
        refine ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, h1, ?_⟩
        group }
  have hA : A ≤ D := fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩
  have hB : B ≤ D := fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩
  exact fun v hv => (sup_le hA hB) hv

theorem central_le_sup_zpowers {T : Subgroup G} {x : G} (hxcT : ∀ t ∈ T, x * t = t * x)
    {z : G} (hz : z ∈ T ⊔ zpowers x) (hc : ∀ s ∈ T ⊔ zpowers x, z * s = s * z) :
    z ∈ zc T ⊔ zpowers x := by
  have hxN : zpowers x ≤ normalizer (T : Set G) :=
    zpowers_le.2 (case1_mem_normalizer_of_comm hxcT)
  obtain ⟨b, hb, t, ht, rfl⟩ := exists_mul_of_mem_sup hxN z (by rwa [sup_comm] at hz)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have htz : t ∈ zc T := by
    refine mem_zc.2 ⟨ht, fun g hg => ?_⟩
    have hgs : g ∈ T ⊔ zpowers x := mem_sup_left hg
    have h1 := hc g hgs
    have h2 : x ^ k * g = g * x ^ k := (Commute.zpow_left (hxcT g hg : Commute x g) k).eq
    have h3 : x ^ k * (t * g) = x ^ k * (g * t) := by
      calc x ^ k * (t * g) = (x ^ k * t) * g := by group
        _ = g * (x ^ k * t) := h1
        _ = (g * x ^ k) * t := by group
        _ = (x ^ k * g) * t := by rw [h2]
        _ = x ^ k * (g * t) := by group
    exact (mul_left_cancel h3).symm
  exact Subgroup.mul_mem _ (mem_sup_right hb) (mem_sup_left htz)

theorem case1_final_p3 {M Y S U : Subgroup G} {t : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) → H ≤ M)
    (hY2 : IsPGroup 2 Y) (hY1 : Y ≠ ⊥) (hSM : S ≤ M)
    (hexp : ∀ s ∈ S, s ^ 3 = 1) (hUS : U ≤ S) (hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u)
    (hUcard : Nat.card U = 3 ^ 2) (hUY : U ≤ normalizer (Y : Set G))
    (htS : t ∈ S) (htU : t ∉ U)
    (htN : t ∈ normalizer (thompsonJ Y : Set G) ∨
      t ∈ normalizer (quasithinOmegaOneCenter Y : Set G)) :
    normalizer (Y : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases htN with htJ | htZ
  · have hUA : U ≤ S ⊓ normalizer (thompsonJ Y : Set G) :=
      le_inf hUS (hUY.trans (normalizer_le_normalizer_thompsonJ' Y))
    have hA3 : 3 ≤ CFSG.Open.pRank 3 (S ⊓ normalizer (thompsonJ Y : Set G)) :=
      three_le_pRank_of_not_le hexp hUS hUc hUcard hUA inf_le_left (fun h => htU (h ⟨htS, htJ⟩))
    have hJ2 : IsPGroup 2 (thompsonJ Y) := hY2.to_le (Generic49U3.thompsonJ_le_self Y)
    have hloc : IsTwoLocal (normalizer (thompsonJ Y : Set G)) :=
      ⟨thompsonJ Y, thompsonJ_ne_bot_of_two_group hY2 hY1, hJ2, rfl⟩
    have hAle : S ⊓ normalizer (thompsonJ Y : Set G) ≤ normalizer (thompsonJ Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_thompsonJ' Y).trans
      (hD1' _ hloc (hA3.trans (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hAle)))
  · have hUB : U ≤ S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) :=
      le_inf hUS (hUY.trans (normalizer_le_normalizer_omegaOneCenter Y))
    have hB3 : 3 ≤ CFSG.Open.pRank 3 (S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G)) :=
      three_le_pRank_of_not_le hexp hUS hUc hUcard hUB inf_le_left (fun h => htU (h ⟨htS, htZ⟩))
    have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter Y) :=
      hY2.to_le (Generic49U3.omegaOneCenter_le_self Y)
    have hloc : IsTwoLocal (normalizer (quasithinOmegaOneCenter Y : Set G)) :=
      ⟨quasithinOmegaOneCenter Y, omegaOneCenter_ne_bot_of_two_group hY2 hY1, hZ2, rfl⟩
    have hBle : S ⊓ normalizer (quasithinOmegaOneCenter Y : Set G) ≤
        normalizer (quasithinOmegaOneCenter Y : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans hSM)
    exact (normalizer_le_normalizer_omegaOneCenter Y).trans
      (hD1' _ hloc (hB3.trans (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hBle)))

end CaseOneLemmas

section CaseOneYData

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mul_mem_of_pow {R : Subgroup G} {a s : G} (ha : a ∈ normalizer (R : Set G))
    {m : ℕ} (ham : a ^ (2 ^ m) = 1) (hs : s ^ 3 = 1) (hr : a * s ∈ R) : s ∈ R := by
  have hsr : s = a⁻¹ * (a * s) := by group
  have key : ∀ k : ℕ, ∃ q ∈ R, s ^ k = (a⁻¹) ^ k * q := by
    intro k
    induction k with
    | zero => exact ⟨1, R.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨q, hq, hk⟩ := ih
      have hq' : a * q * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 ha q).1 hq
      refine ⟨(a * q * a⁻¹) * (a * s), R.mul_mem hq' hr, ?_⟩
      calc s ^ (k + 1) = s ^ k * s := pow_succ s k
        _ = ((a⁻¹) ^ k * q) * (a⁻¹ * (a * s)) := by rw [hk, ← hsr]
        _ = (a⁻¹) ^ (k + 1) * ((a * q * a⁻¹) * (a * s)) := by rw [pow_succ]; group
  obtain ⟨q, hq, hk⟩ := key (2 ^ m)
  have h1 : s ^ (2 ^ m) = q := by rw [hk, inv_pow, ham, inv_one, one_mul]
  have hmod : 4 ^ m % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h4 : s ^ (4 ^ m) = s := by
    calc s ^ (4 ^ m) = s ^ (4 ^ m % 3 + 3 * (4 ^ m / 3)) := by rw [Nat.mod_add_div]
      _ = s := by rw [hmod, pow_add, pow_mul, hs, one_pow, mul_one, pow_one]
  have h5 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [← h4, h5, pow_mul, h1]
  exact R.pow_mem hq _

theorem sup_inf_le_of_perm {R Y S : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hSexp : ∀ s ∈ S, s ^ 3 = 1) (hYR : Y ≤ normalizer (R : Set G))
    (hRS : S ⊓ R = ⊥) (hperm : ∀ w ∈ Y ⊔ S, ∃ y ∈ Y, ∃ s ∈ S, w = y * s) :
    (Y ⊔ S) ⊓ R ≤ Y := by
  rintro w ⟨hw, hwR⟩
  obtain ⟨y, hy, s, hs, rfl⟩ := hperm w hw
  obtain ⟨m, hm⟩ := hY2 ⟨y, hy⟩
  have hym : y ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hsR : s ∈ R := mem_of_mul_mem_of_pow (hYR hy) hym (hSexp s hs) hwR
  have hs1 : s ∈ S ⊓ R := ⟨hs, hsR⟩
  rw [hRS, Subgroup.mem_bot] at hs1
  rw [hs1, mul_one]
  exact hy

theorem isSylowTwoOf_sup_of_perm {Y Q : Subgroup G} (hY : IsPGroup 2 Y) (hQ : IsPGroup 3 Q)
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q) : IsSylowTwoOf Y (Y ⊔ Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card Q) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hcard := Glauberman281.card_sup_eq_mul hcop hperm
  refine ⟨le_sup_left, hY, ?_⟩
  have h1 := Subgroup.card_mul_index ((Y).subgroupOf (Y ⊔ Q))
  have h2 : Nat.card ((Y).subgroupOf (Y ⊔ Q)) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [h2, hcard] at h1
  have h3 : ((Y).subgroupOf (Y ⊔ Q)).index = Nat.card Q := by
    have hpos : 0 < Nat.card Y := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  rw [h3, hb]
  intro hd
  have := Nat.prime_two.dvd_of_dvd_pow hd
  omega

theorem isSolvable_sup_of_perm {Y Q : Subgroup G} (hY : IsPGroup 2 Y) (hQ : IsPGroup 3 Q)
    (hperm : ∀ w ∈ Y ⊔ Q, ∃ y ∈ Y, ∃ q ∈ Q, w = y * q) : Group.IsSolvable ↥(Y ⊔ Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := hY.exists_card_eq
  obtain ⟨b, hb⟩ := hQ.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card Q) := by
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have hcard := Glauberman281.card_sup_eq_mul hcop hperm
  haveI : Fintype ↥(Y ⊔ Q) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard, ha, hb])

theorem yData_of_case1 {M R T S Y : Subgroup G}
    (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime 3 (Nat.card R))
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hSM : S ≤ M) (hTS : T ≤ S) (hSp : IsPGroup 3 S)
    (hSexp : ∀ s ∈ S, s ^ 3 = 1)
    (hperm : ∀ w ∈ Y ⊔ S, ∃ y ∈ Y, ∃ s ∈ S, w = y * s)
    (hTcard : Nat.card T = 3 ^ 3) (hTexp : ∀ t ∈ T, t ^ 3 = 1) (hTnc : ¬ IsMulCommutative T)
    (hZY : ∀ z ∈ zc T, z ∈ normalizer (Y : Set G)) :
    YData (Y ⊔ T) Y T (Y ⊓ R) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTM : T ≤ M := hTS.trans hSM
  have hTn : T ≤ normalizer (R : Set G) := hTM.trans hRn
  have hTR : T ⊓ R = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [hTcard]; exact Nat.Coprime.pow_left 3 hRcop))
  have hSR : S ⊓ R = ⊥ := by
    obtain ⟨b, hb⟩ := hSp.exists_card_eq
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [hb]; exact Nat.Coprime.pow_left b hRcop))
  have hWR : (Y ⊔ S) ⊓ R ≤ Y := sup_inf_le_of_perm hY2 hSexp (hYM.trans hRn) hSR hperm
  have hWM : Y ⊔ S ≤ M := sup_le hYM hSM
  have hYTW : Y ⊔ T ≤ Y ⊔ S := sup_le_sup_left hTS Y
  have hTW : T ≤ Y ⊔ S := hTS.trans le_sup_right
  have hWR' : ∀ w ∈ Y ⊔ S, w ∈ R → w ∈ Y ⊓ R := fun w hw hwR => ⟨hWR ⟨hw, hwR⟩, hwR⟩
  have hconjN : ∀ g ∈ M, ∀ n ∈ T ⊔ R, g * n * g⁻¹ ∈ T ⊔ R := fun g hg n hn =>
    (Subgroup.mem_normalizer_iff.1 (hNn hg) n).1 hn
  have hconjR : ∀ g ∈ M, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
    (Subgroup.mem_normalizer_iff.1 (hRn hg) r).1 hr
  have hTY : T ⊓ Y = ⊥ := by
    obtain ⟨a, ha⟩ := hY2.exists_card_eq
    exact Subgroup.inf_eq_bot_of_coprime
      (by rw [hTcard, ha]; exact Nat.Coprime.pow _ _ (by norm_num))
  have hEn : ∀ h ∈ Y ⊔ T, ∀ e ∈ Y ⊓ R, h * e * h⁻¹ ∈ Y ⊓ R := by
    intro h hh e he
    have hhW : h ∈ Y ⊔ S := hYTW hh
    refine hWR' _ ((Y ⊔ S).mul_mem ((Y ⊔ S).mul_mem hhW (mem_sup_left he.1))
      ((Y ⊔ S).inv_mem hhW)) (hconjR h (hWM hhW) e he.2)
  have hTEh : ∀ h ∈ Y ⊔ T, ∀ t ∈ T, ∃ t' ∈ T, ∃ e ∈ Y ⊓ R, h * t * h⁻¹ = t' * e := by
    intro h hh t ht
    have hhW : h ∈ Y ⊔ S := hYTW hh
    have hnW : h * t * h⁻¹ ∈ Y ⊔ S :=
      (Y ⊔ S).mul_mem ((Y ⊔ S).mul_mem hhW (hTW ht)) ((Y ⊔ S).inv_mem hhW)
    have hnN : h * t * h⁻¹ ∈ T ⊔ R := hconjN h (hWM hhW) t (mem_sup_left ht)
    obtain ⟨t', ht', r, hr, hn⟩ := exists_mul_of_mem_sup hTn _ hnN
    have hrW : r ∈ Y ⊔ S := by
      have : r = t'⁻¹ * (h * t * h⁻¹) := by rw [hn]; group
      rw [this]
      exact (Y ⊔ S).mul_mem ((Y ⊔ S).inv_mem (hTW ht')) hnW
    exact ⟨t', ht', r, hWR' r hrW hr, hn⟩
  have hperm' : ∀ h ∈ Y ⊔ T, ∃ y ∈ Y, ∃ t ∈ T, h = y * t := by
    let X : Subgroup G :=
      { carrier := {h | ∃ y ∈ Y, ∃ n ∈ (Y ⊔ S) ⊓ (T ⊔ R), h = y * n}
        mul_mem' := by
          rintro _ _ ⟨y, hy, n, hn, rfl⟩ ⟨y', hy', n', hn', rfl⟩
          have hy'W : y'⁻¹ ∈ Y ⊔ S := (Y ⊔ S).inv_mem (mem_sup_left hy')
          have hy'M : y'⁻¹ ∈ M := hYM (Y.inv_mem hy')
          have h1 : y'⁻¹ * n * y' ∈ (Y ⊔ S) ⊓ (T ⊔ R) := by
            refine ⟨?_, ?_⟩
            · have := (Y ⊔ S).mul_mem ((Y ⊔ S).mul_mem hy'W hn.1) ((Y ⊔ S).inv_mem hy'W)
              simpa using this
            · have := hconjN _ hy'M n hn.2
              simpa using this
          refine ⟨y * y', Y.mul_mem hy hy', (y'⁻¹ * n * y') * n',
            ((Y ⊔ S) ⊓ (T ⊔ R)).mul_mem h1 hn', ?_⟩
          group
        one_mem' := ⟨1, Y.one_mem, 1, ((Y ⊔ S) ⊓ (T ⊔ R)).one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨y, hy, n, hn, rfl⟩
          have hyW : y ∈ Y ⊔ S := mem_sup_left hy
          have hyM : y ∈ M := hYM hy
          have h1 : y * n⁻¹ * y⁻¹ ∈ (Y ⊔ S) ⊓ (T ⊔ R) := by
            refine ⟨(Y ⊔ S).mul_mem ((Y ⊔ S).mul_mem hyW ((Y ⊔ S).inv_mem hn.1))
              ((Y ⊔ S).inv_mem hyW), ?_⟩
            exact hconjN y hyM n⁻¹ ((T ⊔ R).inv_mem hn.2)
          refine ⟨y⁻¹, Y.inv_mem hy, y * n⁻¹ * y⁻¹, h1, ?_⟩
          group }
    have hYX : Y ≤ X := fun y hy => ⟨y, hy, 1, ((Y ⊔ S) ⊓ (T ⊔ R)).one_mem, by simp⟩
    have hTX : T ≤ X := fun t ht =>
      ⟨1, Y.one_mem, t, ⟨hTW ht, mem_sup_left ht⟩, by simp⟩
    intro h hh
    obtain ⟨y, hy, n, hn, rfl⟩ := (sup_le hYX hTX) hh
    obtain ⟨t, ht, r, hr, hnr⟩ := exists_mul_of_mem_sup hTn _ hn.2
    have hrW : r ∈ Y ⊔ S := by
      have : r = t⁻¹ * n := by rw [hnr]; group
      rw [this]
      exact (Y ⊔ S).mul_mem ((Y ⊔ S).inv_mem (hTW ht)) hn.1
    have htrt : t * r * t⁻¹ ∈ Y ⊓ R := by
      refine hWR' _ ((Y ⊔ S).mul_mem ((Y ⊔ S).mul_mem (hTW ht) hrW) ((Y ⊔ S).inv_mem (hTW ht)))
        (hconjR t (hTM ht) r hr)
    refine ⟨y * (t * r * t⁻¹), Y.mul_mem hy htrt.1, t, ht, ?_⟩
    rw [hnr]
    group
  exact
    { TH := le_sup_right
      EH := inf_le_left.trans le_sup_left
      inf_eq := eq_bot_iff.2 (hTR ▸ inf_le_inf_left T inf_le_right)
      En := hEn
      TEh := hTEh
      perm := hperm'
      YH := le_sup_left
      EY := inf_le_left
      TY := hTY
      Y2 := hY2
      ZY := hZY
      Tc := hTcard
      Te := hTexp
      Tnc := hTnc }

end CaseOneYData

section CaseOneCore

open Subgroup CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
  (exists_conj_normalizes_inf case1_orders_gen solvable_normalizer_inf_of_sylow
    exists_permutable_conj_sylow conj_commutes_of_mem_normalizer pow_eq_one_of_mem_sup_zpowers
    map_conj_le_of_mem mem_map_conj_iff mem_normalizer_map_conj_of_commute
    normalizer_le_of_normalizer_map_conj_le le_normalizer_inf_of_le_normalizer
    le_of_normal_isPGroup_of_isSylowOf case1_mem_normalizer_of_comm)

variable {G : Type} [Group G] [Finite G]

theorem case1_core_p3 {M R T Y U : Subgroup G} {x : G}
    (hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) → H ≤ M)
    (hM2 : pCoreOf 2 M ≠ ⊥) (hCharM : CharTwo M)
    (hRM : R ≤ M) (hRn : M ≤ normalizer (R : Set G)) (hRcop : Nat.Coprime 3 (Nat.card R))
    (hO2R : pCoreOf 2 M ≤ R)
    (hNn : M ≤ normalizer ((T ⊔ R : Subgroup G) : Set G))
    (hTM : T ≤ M) (hTcard : Nat.card T = 3 ^ 3) (hTexp : ∀ t ∈ T, t ^ 3 = 1)
    (hTnc : ¬ IsMulCommutative T)
    (hxM : x ∈ M) (hxp : x ^ 3 = 1) (hx1 : x ≠ 1) (hxT : x ∉ T)
    (hxcT : ∀ t ∈ T, x * t = t * x)
    (hVp : IsPGroup 3 (T ⊔ zpowers x : Subgroup G))
    (hUV : U ≤ T ⊔ zpowers x) (hxU : x ∈ U) (hUcard : Nat.card U = 3 ^ 2)
    (hUcT : ∀ u ∈ U, ∀ t ∈ T, u * t = t * u) (hUcx : ∀ u ∈ U, u * x = x * u)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hUY : U ≤ normalizer (Y : Set G))
    (hYB : IsSylowOf 2 (Y ⊓ R) R) :
    normalizer (Y : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hVM : T ⊔ zpowers x ≤ M := sup_le hTM (zpowers_le.2 hxM)
  have hTn : T ≤ normalizer (R : Set G) := hTM.trans hRn
  have hTR : T ⊓ R = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard
      (by rw [hTcard]; exact Nat.Coprime.pow_left 3 hRcop))
  have hxN : x ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) := hNn hxM
  obtain ⟨c, hcR, hcU, hYB', hVN⟩ :=
    exists_conj_normalizes_inf hVp hRcop (hVM.trans hRn) hUV (hYM.trans hRn) hUY hYB
  set Y' : Subgroup G := Y.map (MulAut.conj c).toMonoidHom with hY'
  have hcM : c ∈ M := hRM hcR
  have hY'M : Y' ≤ M := map_conj_le_of_mem hcM hYM
  have hY'2 : IsPGroup 2 Y' := hY2.map _
  have hUY' : U ≤ normalizer (Y' : Set G) := fun u hu =>
    mem_normalizer_map_conj_of_commute (hcU u hu) (hUY hu)
  have hxY' : x ∈ normalizer (Y' : Set G) := hUY' hxU
  have hKn' : Y' ⊔ zpowers x ≤ normalizer ((T ⊔ R : Subgroup G) : Set G) :=
    sup_le (hY'M.trans hNn) (zpowers_le.2 hxN)
  obtain ⟨hVsyl, hYsyl, hidx⟩ := case1_orders_gen (k := 3) hp2 hTn hRcop hKn' hTcard hxp hx1 hxT
    hxcT hY'2 hxY' hYB'
  set H₁ : Subgroup G := (T ⊔ R) ⊔ (Y' ⊔ zpowers x) with hH₁
  have hH₁M : H₁ ≤ M := sup_le (sup_le hTM hRM) (sup_le hY'M (zpowers_le.2 hxM))
  have hRH₁ : R ≤ H₁ := le_sup_right.trans le_sup_left
  have hVH₁ : T ⊔ zpowers x ≤ H₁ := hVsyl.le
  have hY'H₁ : Y' ≤ H₁ := hYsyl.le
  have hsolv := solvable_normalizer_inf_of_sylow hp hp2 hRH₁ (hH₁M.trans hRn) hidx hYB'
  set L : Subgroup G := H₁ ⊓ normalizer ((Y' ⊓ R : Subgroup G) : Set G) with hL
  have hVL : T ⊔ zpowers x ≤ L := le_inf hVH₁ hVN
  have hY'L : Y' ≤ L :=
    le_inf hY'H₁ (le_normalizer_inf_of_le_normalizer (hY'M.trans hRn))
  have hVsylL : IsSylowOf 3 (T ⊔ zpowers x) L := hVsyl.of_le hVL inf_le_left
  have hYsylL : IsSylowOf 2 Y' L := hYsyl.of_le hY'L inf_le_left
  have hUL : U ≤ L := hUV.trans hVL
  obtain ⟨l, hlL, hUS, hperm⟩ :=
    exists_permutable_conj_sylow hp2 hsolv hYsylL hVsylL hUL (hVp.to_le hUV) hUY'
  set S : Subgroup G := (T ⊔ zpowers x).map (MulAut.conj l).toMonoidHom with hS
  have hlM : l ∈ M := hH₁M (Subgroup.mem_inf.1 hlL).1
  have hSM : S ≤ M := map_conj_le_of_mem hlM hVM
  have hSp : IsPGroup 3 S := hVp.map _
  have hexpV := pow_eq_one_of_mem_sup_zpowers hTexp hxp hxcT
  have hexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have h1 := hexpV (l⁻¹ * s * l) (mem_map_conj_iff.1 hs)
    have h2 : (l⁻¹ * s * l) ^ 3 = l⁻¹ * s ^ 3 * l := by
      simpa using conj_pow (a := l⁻¹) (b := s) (i := 3)
    rw [h2] at h1
    calc s ^ 3 = l * (l⁻¹ * s ^ 3 * l) * l⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u := by
    intro u hu s hs
    have huM : u ∈ M := hVM (hUV hu)
    have hw : l⁻¹ * u * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 (hUS hu)
    have hlN : l ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) := hNn hlM
    have hcomm := conj_commutes_of_mem_normalizer hTn (hRn hlM) (hRn huM) hlN hTR hxcT
      (hUcT u hu) (hUcx u hu) hw
    have hv : l⁻¹ * s * l ∈ T ⊔ zpowers x := mem_map_conj_iff.1 hs
    have h := hcomm _ hv
    calc u * s = l * ((l⁻¹ * u * l) * (l⁻¹ * s * l)) * l⁻¹ := by group
      _ = l * ((l⁻¹ * s * l) * (l⁻¹ * u * l)) * l⁻¹ := by rw [h]
      _ = s * u := by group
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Subgroup G, T₁ = T.map (MulAut.conj l).toMonoidHom := ⟨_, rfl⟩
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : G, x₁ = l * x * l⁻¹ := ⟨_, rfl⟩
  have hT₁S : T₁ ≤ S := by rw [hT₁]; exact Subgroup.map_mono le_sup_left
  have hT₁card : Nat.card T₁ = 3 ^ 3 := by
    rw [hT₁, Subgroup.card_map_of_injective (MulAut.conj l).injective, hTcard]
  have hT₁exp : ∀ t ∈ T₁, t ^ 3 = 1 := fun t ht => hexp t (hT₁S ht)
  have hT₁nc : ¬ IsMulCommutative T₁ := by
    intro hc
    apply hTnc
    refine isMulCommutative_iff.2 fun a b => Subtype.ext ?_
    have ha : l * (a : G) * l⁻¹ ∈ T₁ := by rw [hT₁]; exact ⟨a, a.2, rfl⟩
    have hb : l * (b : G) * l⁻¹ ∈ T₁ := by rw [hT₁]; exact ⟨b, b.2, rfl⟩
    have h1 := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : T₁) ⟨_, hb⟩)
    have h2 : l * ((a : G) * b) * l⁻¹ = l * ((b : G) * a) * l⁻¹ := by
      calc l * ((a : G) * b) * l⁻¹ = (l * a * l⁻¹) * (l * b * l⁻¹) := by group
        _ = (l * b * l⁻¹) * (l * a * l⁻¹) := h1
        _ = l * ((b : G) * a) * l⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hlN : l ∈ normalizer ((T ⊔ R : Subgroup G) : Set G) := hNn hlM
  have hRl : R.map (MulAut.conj l).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hRn hlM)
  have hT₁R : T₁ ⊔ R = T ⊔ R := by
    have h1 : (T ⊔ R).map (MulAut.conj l).toMonoidHom = T ⊔ R :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hlN
    rw [Subgroup.map_sup, hRl] at h1
    rw [hT₁]
    exact h1
  have hNn₁ : M ≤ normalizer ((T₁ ⊔ R : Subgroup G) : Set G) := by rw [hT₁R]; exact hNn
  have hSeq : S = T₁ ⊔ zpowers x₁ := by
    rw [hS, Subgroup.map_sup, hT₁, MonoidHom.map_zpowers, hx₁]
    rfl
  have hx₁cT : ∀ t ∈ T₁, x₁ * t = t * x₁ := by
    intro t ht
    have h := hxcT (l⁻¹ * t * l) (mem_map_conj_iff.1 (hT₁ ▸ ht))
    calc x₁ * t = l * (x * (l⁻¹ * t * l)) * l⁻¹ := by rw [hx₁]; group
      _ = l * ((l⁻¹ * t * l) * x) * l⁻¹ := by rw [h]
      _ = t * x₁ := by rw [hx₁]; group
  have hx₁p : x₁ ^ 3 = 1 := by
    have : x₁ ^ 3 = l * x ^ 3 * l⁻¹ := by rw [hx₁]; exact conj_pow
    rw [this, hxp]; group
  have hUB : U ≤ zc T₁ ⊔ zpowers x₁ := by
    intro u hu
    have huS : u ∈ T₁ ⊔ zpowers x₁ := hSeq ▸ hUS hu
    exact central_le_sup_zpowers hx₁cT huS (fun s hs => hUc u hu s (hSeq ▸ hs))
  have hBcard : Nat.card (zc T₁ ⊔ zpowers x₁ : Subgroup G) ≤ 3 ^ 2 := by
    have hcomm : ∀ a ∈ zc T₁, ∀ b ∈ zpowers x₁, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hc : Commute x₁ a := hx₁cT a (zc_le ha)
      exact (hc.zpow_left k).symm.eq
    have h := B2F.card_sup_mul_card_inf_of_commute hcomm
    have h1 : Nat.card (zc T₁) = 3 := zc_card hT₁card hT₁nc
    have h2 : Nat.card (zpowers x₁) ≤ 3 := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx₁p)
    have h3 : 0 < Nat.card ↥(zc T₁ ⊓ zpowers x₁) := Nat.card_pos
    rw [h1] at h
    nlinarith
  have hUeq : U = zc T₁ ⊔ zpowers x₁ :=
    Subgroup.eq_of_le_of_card_ge hUB (by rw [hUcard]; exact hBcard)
  have hZU₁ : zc T₁ ≤ U := by rw [hUeq]; exact le_sup_left
  have hZY : ∀ z ∈ zc T₁, z ∈ normalizer (Y' : Set G) := fun z hz => hUY' (hZU₁ hz)
  have hy : YData (Y' ⊔ T₁) Y' T₁ (Y' ⊓ R) :=
    yData_of_case1 hRn hRcop hNn₁ hY'2 hY'M hSM hT₁S hSp hexp hperm hT₁card hT₁exp hT₁nc hZY
  have hH_le : Y' ⊔ T₁ ≤ M := sup_le hY'M (hT₁S.trans hSM)
  have hO2Y' : pCoreOf 2 M ≤ Y' ⊓ R :=
    le_of_normal_isPGroup_of_isSylowOf hYB' hO2R
      (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hO2Y : pCoreOf 2 M ≤ Y' := hO2Y'.trans inf_le_left
  have hF : CharTwo (Y' ⊔ T₁) :=
    Glauberman281.charTwo_of_le hH_le hCharM
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2Y.trans le_sup_left)
        (hH_le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M))
  have hY'1 : Y' ≠ ⊥ := fun h => hM2 (le_bot_iff.1 (hO2Y.trans h.le))
  have hsolv₁ := isSolvable_sup_of_perm hY'2 (hSp.to_le hT₁S) hy.perm
  have hsyl₁ := isSylowTwoOf_sup_of_perm hY'2 (hSp.to_le hT₁S) hy.perm
  obtain ⟨t, htT, htz, htN⟩ := exists_noncentral_normalizing hy hsyl₁ hsolv₁ hF
  have htU : t ∉ U := by
    intro htU
    exact htz (mem_zc.2 ⟨htT, fun g hg => (hUc t htU g (hT₁S hg)).symm⟩)
  have hfin := case1_final_p3 hD1' hY'2 hY'1 hSM hexp hUS hUc hUcard hUY' (hT₁S htT) htU htN
  exact normalizer_le_of_normalizer_map_conj_le hcM hfin

end CaseOneCore

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3Aux

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3Aux (case1_core_p3)

variable {G : Type} [Group G] [Finite G]

theorem u3PointLemma43_of_remark (hS : Setting G) (hD1 : TheoremD1 G)
    {P : Sylow 3 G} {M J : Subgroup G} {x : G} (hσ : 3 ∈ rankThreeSigmaA G)
    (hM : IsCoreMaxLocal 3 P M) (hgen : IsGenericPoint 3 P M x) (h34 : U3Prop34 3 P J x)
    (hnorm : M ≤ normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G)) :
    U3PointLemma43 3 P M J x := by
  intro Y hY2 hYM hUY hYB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPx, hTcard, hTexp, hTnc, ⟨Z, -, hxZ, -, hTZ, -⟩, -⟩ := h34
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = (P : Subgroup G) ⊓ J := ⟨_, rfl⟩
  rw [← hT] at hTcard hTexp hTnc hTZ hnorm
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hσ hM).1
  obtain ⟨hRM, hRn, hRcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M
  have hM2loc : IsTwoLocal M := hM.1.1
  have hCharM : CFSG.QuasithinUnique.CharTwo M := hS.charTwo M hM2loc
  have hM2 : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨P₂, hP₂1, hP₂2, hP₂M⟩ := hM2loc
    have hP₂le : P₂ ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP₂M ▸ Subgroup.le_normalizer)
        hP₂M.le hP₂2
    intro h
    exact hP₂1 (le_bot_iff.1 (hP₂le.trans h.le))
  have hO2R : pCoreOf 2 M ≤ GLBPrimeCore 3 M :=
    Generic49U3.pCoreOf_two_le_relPPrimeCore (by norm_num) M
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) → H ≤ M :=
    fun H hH hr => le_of_three_le_pRank_inf hD1 hσ hM hH hr
  have hTP : T ≤ (P : Subgroup G) := by rw [hT]; exact inf_le_left
  have hTM : T ≤ M := hTP.trans hPM
  have hxP : x ∈ (P : Subgroup G) := hgen.1
  have hxM : x ∈ M := hgen.2.1.1
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hxp : x ^ 3 = 1 := hgen.2.1.2.2.1
  have hxT : x ∉ T := by
    intro hxT
    have : x ∈ T ⊓ Z := ⟨hxT, hxZ⟩
    rw [hTZ, Subgroup.mem_bot] at this
    exact hx1 this
  have hxcT : ∀ t ∈ T, x * t = t * x := fun t ht =>
    Subgroup.mem_centralizer_iff.1 (hPx (hTP ht)) x rfl
  have hVp : IsPGroup 3 (T ⊔ zpowers x : Subgroup G) :=
    P.isPGroup'.to_le (sup_le hTP (zpowers_le.2 hxP))
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, A = (center ↥T).map T.subtype := ⟨_, rfl⟩
  have hUdef : u3VPlane (P : Subgroup G) J x = A ⊔ zpowers x := by rw [hA, hT]; rfl
  rw [hUdef] at hUY
  have hZTcard : Nat.card (center ↥T) = 3 :=
    Generic49U3.card_center_of_nonabelian_card_p_cube hTcard hTnc
  have hAcard : Nat.card A = 3 := by
    rw [hA, Subgroup.card_map_of_injective T.subtype_injective, hZTcard]
  have hAT : A ≤ T := by rw [hA]; exact Subgroup.map_subtype_le _
  have hAcT : ∀ a ∈ A, ∀ t ∈ T, a * t = t * a := by
    rw [hA]
    rintro _ ⟨a, ha, rfl⟩ t ht
    have := Subgroup.mem_center_iff.1 ha ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm
  have hxord : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hAB : ∀ a ∈ A, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hc : Commute x a := hxcT a (hAT ha)
    exact (hc.zpow_left k).symm.eq
  have hABinf : Nat.card ↥(A ⊓ zpowers x) = 1 := by
    have hdvd : Nat.card ↥(A ⊓ zpowers x) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ zpowers x ≤ zpowers x)
      rwa [hxord] at h
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : A ⊓ zpowers x = zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [h1, hxord]))
      have h2 : x ∈ A ⊓ zpowers x := by rw [heq]; exact Subgroup.mem_zpowers x
      exact hxT (hAT h2.1)
  have hUcard : Nat.card ↥(A ⊔ zpowers x) = 3 ^ 2 := by
    have h := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hAB
    rw [hABinf, hAcard, hxord, mul_one] at h
    rw [h]
    norm_num
  have hUcT : ∀ u ∈ A ⊔ zpowers x, ∀ t ∈ T, u * t = t * u := by
    intro u hu t ht
    have hle : A ⊔ zpowers x ≤ centralizer (T : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (hAcT a ha g hg).symm
      · rw [zpowers_le, Subgroup.mem_centralizer_iff]
        intro g hg
        exact (hxcT g hg).symm
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) t ht).symm
  have hUcx : ∀ u ∈ A ⊔ zpowers x, u * x = x * u := by
    intro u hu
    have hle : A ⊔ zpowers x ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        exact hPx (hTP (hAT ha))
      · rw [zpowers_le, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
    exact (Subgroup.mem_centralizer_iff.1 (hle hu) x rfl).symm
  exact case1_core_p3 (R := GLBPrimeCore 3 M) hD1' hM2 hCharM hRM hRn hRcop hO2R hnorm hTM hTcard
    hTexp hTnc hxM hxp hx1 hxT hxcT hVp (sup_le_sup_right hAT _)
    (mem_sup_right (Subgroup.mem_zpowers x)) hUcard hUcT hUcx hY2 hYM hUY hYB

@[expose] def GL83GenericPrimeThreeU3RemarkCond (G : Type) [Group G] [Finite G] : Prop :=
  GenericU3At G fun p P M x J => U3Prop34 p P J x →
    M ≤ normalizer ((((P : Subgroup G) ⊓ J) ⊔ GLBPrimeCore p M : Subgroup G) : Set G)

theorem gl83GenericPrimeThreeU3Lemma43_of_remarkCond (hS : Setting G) (hD1 : TheoremD1 G)
    (hrem : GL83GenericPrimeThreeU3RemarkCond G) : GL83GenericPrimeThreeU3Lemma43 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  subst hp3
  exact u3PointLemma43_of_remark hS hD1 hp hM hgen h34
    (hrem 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34)

theorem gl83GenericU3Lemma43E3_holds_of_remark_stone
    (hrem : ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeU3RemarkCond G) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeU3Lemma43 G :=
  fun G _ _ hS hD1 hU0 => gl83GenericPrimeThreeU3Lemma43_of_remarkCond hS hD1 (hrem G hS hD1 hU0)

end CFSG.LocalAnalysis.RankThreeTheoremC
