module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TSwapA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TK0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Steps

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec10T_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem sec10T_mem_secK0_of_mem_inf_of_odd {t z x : G}
    (hx : x ∈ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G))
    (hodd : Odd (orderOf x)) : x ∈ secK0 t z := by
  unfold secK0 oTwoRes
  exact Subgroup.subset_closure ⟨hx, hodd⟩

theorem sec10T_swap_false [Finite G] (hC : Asc82Step105C) (hK0 : Asc82Lemma10K0)
    (h36 : Asc82Lemma36) (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) (hneg : ¬ ∃ g : G, g⁻¹ * t * g = t * z) {h : G}
    (hh : h ∈ centralizer ({z} : Set G)) (hs : h⁻¹ * t * h ∈ S)
    (hsw : ∀ x ∈ K1, (h⁻¹ * t * h) * x * (h⁻¹ * t * h)⁻¹ ∈ K2) : False := by
  have hpsp : IsPSp43 L := (hb G t L S z hctx.toSec10Z).1
  set s : G := h⁻¹ * t * h with hsdef
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution, pow_two] at h
    exact h
  have hs2 : s * s = 1 := by
    rw [hsdef]
    rw [show (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h by group, ht2]
    group
  have hst : h * s * h⁻¹ = t := by
    rw [hsdef]; group
  have hhz : Commute h z := Subgroup.mem_centralizer_singleton_iff.mp hh
  have hhzi : h⁻¹ * z = z * h⁻¹ :=
    Subgroup.mem_centralizer_singleton_iff.mp ((centralizer ({z} : Set G)).inv_mem hh)
  obtain ⟨g, hgQ1, hgnotZ, hsgK2, x1, x2, hx1odd, hx2odd, hx1s, hx2s, hx1z, hx2z, e, heZ,
    hfinal⟩ := sec10T_swap_data hP5 hC5 hb hpsp hctx hs hs2 hsw
  have hgK1 : g ∈ K1 := sec10T_twoCoreIn_le_self K1 hgQ1
  set u1 : G := h * x1 * h⁻¹ with hu1def
  set u2 : G := h * x2 * h⁻¹ with hu2def
  have hu1order : orderOf u1 = orderOf x1 := by
    have hu1eq : u1 = (MulAut.conj h) x1 := by rw [hu1def, MulAut.conj_apply]
    rw [hu1eq]
    exact (MulAut.conj h).orderOf_eq x1
  have hu2order : orderOf u2 = orderOf x2 := by
    have hu2eq : u2 = (MulAut.conj h) x2 := by rw [hu2def, MulAut.conj_apply]
    rw [hu2eq]
    exact (MulAut.conj h).orderOf_eq x2
  have hu1_comm_t : u1 * t = t * u1 := by
    rw [hu1def, ← hst]
    calc (h * x1 * h⁻¹) * (h * s * h⁻¹)
        = h * (x1 * s) * h⁻¹ := by group
      _ = h * (s * x1) * h⁻¹ := by rw [hx1s]
      _ = (h * s * h⁻¹) * (h * x1 * h⁻¹) := by group
  have hu2_comm_t : u2 * t = t * u2 := by
    rw [hu2def, ← hst]
    calc (h * x2 * h⁻¹) * (h * s * h⁻¹)
        = h * (x2 * s) * h⁻¹ := by group
      _ = h * (s * x2) * h⁻¹ := by rw [hx2s]
      _ = (h * s * h⁻¹) * (h * x2 * h⁻¹) := by group
  have hu1_comm_z : u1 * z = z * u1 := by
    rw [hu1def]
    exact ((hhz.mul_left hx1z).mul_left hhz.inv_left).eq
  have hu2_comm_z : u2 * z = z * u2 := by
    rw [hu2def]
    exact ((hhz.mul_left hx2z).mul_left hhz.inv_left).eq
  have hu1K0 : u1 ∈ secK0 t z :=
    sec10T_mem_secK0_of_mem_inf_of_odd
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hu1_comm_t,
        Subgroup.mem_centralizer_singleton_iff.mpr hu1_comm_z⟩
      (by rw [hu1order]; exact hx1odd)
  have hu2K0 : u2 ∈ secK0 t z :=
    sec10T_mem_secK0_of_mem_inf_of_odd
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hu2_comm_t,
        Subgroup.mem_centralizer_singleton_iff.mpr hu2_comm_z⟩
      (by rw [hu2order]; exact hx2odd)
  have hzK0 : z ∈ secK0 t z := by
    rw [(hK0 G t L S z K1 K2 hctx).1]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hctx.pocket1.1)
  have hzK0_le : zpowers z ≤ secK0 t z := Subgroup.zpowers_le.mpr hzK0
  have heK0 : e ∈ secK0 t z := hzK0_le heZ
  have heh : Commute e h := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp heZ
    rw [← hn]
    exact (hhz.zpow_right n).symm
  have hce : h * e * h⁻¹ = e := by
    rw [heh.eq.symm, mul_assoc, mul_inv_cancel, mul_one]
  set c : G := (s * g * s⁻¹)⁻¹ * g with hcdef
  set q : G := h * c * h⁻¹ with hqdef
  have hq_eq : q = u2 * u1⁻¹ * e := by
    calc q = h * c * h⁻¹ := hqdef
      _ = h * (x2 * x1⁻¹ * e) * h⁻¹ := by rw [hfinal]
      _ = (h * x2 * h⁻¹) * (h * x1 * h⁻¹)⁻¹ * (h * e * h⁻¹) := by group
      _ = (h * x2 * h⁻¹) * (h * x1 * h⁻¹)⁻¹ * e := by rw [hce]
      _ = u2 * u1⁻¹ * e := by rw [hu2def, hu1def]
  have hqK0 : q ∈ secK0 t z := by
    rw [hq_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hu2K0 (Subgroup.inv_mem _ hu1K0)) heK0
  have hgQ : g ∈ secQ K1 K2 := by
    rw [sec10KS_twoCore_sup hP5 hC5 hpsp hctx]
    exact Subgroup.mem_sup_left hgQ1
  have hsgQ : s * g * s⁻¹ ∈ secQ K1 K2 := sec10J_Q_normal hP5 hb hctx s hs g hgQ
  have hcQ : c ∈ secQ K1 K2 := by
    rw [hcdef]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsgQ) hgQ
  have hcS : c ∈ S := (sec10J_Q_le hP5 hb hctx hcQ).1
  obtain ⟨m, hm⟩ := hctx.sylow.2.1 ⟨c, hcS⟩
  have hm' : c ^ (2 ^ m) = 1 := by
    have := congrArg (fun x : ↥S => (x : G)) hm
    simpa using this
  have hcq2 : q ^ (2 ^ m) = 1 := by
    have hconjpow : (h * c * h⁻¹) ^ (2 ^ m) = h * c ^ (2 ^ m) * h⁻¹ := by
      rw [show h * c * h⁻¹ = (MulAut.conj h) c by rw [MulAut.conj_apply], ← map_pow,
        MulAut.conj_apply]
    rw [hqdef, hconjpow, hm']
    group
  have hqQ : q ∈ secQ K1 K2 :=
    sec10T_two_elem_K0 hK0 h36 hP5 hC5 hb hctx hqK0 ⟨m, hcq2⟩
  have hgz : Commute g z := Subgroup.mem_centralizer_singleton_iff.mp (hctx.pocket1.2.1 hgK1).2
  set y : G := h * g * h⁻¹ with hydef
  have hy : y ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (by
        rw [hydef]
        exact ((hhz.mul_left hgz).mul_left hhz.inv_left).eq)
  have hcineq : g⁻¹ * s * g = s * c := by
    rw [hcdef]
    rw [show s * ((s * g * s⁻¹)⁻¹ * g) = (s * s) * g⁻¹ * s⁻¹ * g by group]
    rw [hs2, one_mul, inv_eq_of_mul_eq_one_right hs2]
  have hy_eq : y⁻¹ * t * y = h * (g⁻¹ * s * g) * h⁻¹ := by
    rw [hydef, ← hst]
    group
  have hyty : y⁻¹ * t * y = t * q := by
    rw [hy_eq, hcineq]
    rw [show h * (s * c) * h⁻¹ = (h * s * h⁻¹) * (h * c * h⁻¹) by group, ← hst, ← hqdef]
  have hmem : y⁻¹ * t * y ∈ secW t K1 K2 ⊔ zpowers z := by
    rw [hyty]
    exact Subgroup.mem_sup_left
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
        (Subgroup.mem_sup_left hqQ))
  have hq1z : q = 1 ∨ q = z := by
    have hres := hC G t L S z K1 K2 hctx hneg y hy hmem
    rw [hyty] at hres
    rcases hres with hres | hres
    · left; exact mul_left_cancel (a := t) (by simpa using hres)
    · right; exact mul_left_cancel (a := t) hres
  have hc1z : c = 1 ∨ c = z := by
    rcases hq1z with hq1 | hqz
    · left
      have h1 : h * c * h⁻¹ = 1 := by rw [← hqdef]; exact hq1
      have hcong := congrArg (fun x => h⁻¹ * x * h) h1
      rw [show h⁻¹ * (h * c * h⁻¹) * h = c by group,
        show h⁻¹ * (1 : G) * h = 1 by group] at hcong
      exact hcong
    · right
      have hz1 : h * c * h⁻¹ = z := by rw [← hqdef]; exact hqz
      have hc_eq : c = h⁻¹ * z * h := by
        have hcong := congrArg (fun x => h⁻¹ * x * h) hz1
        rw [show h⁻¹ * (h * c * h⁻¹) * h = c by group] at hcong
        exact hcong
      rw [hc_eq, hhzi, mul_assoc, inv_mul_cancel, mul_one]
  have hcZ : c ∈ zpowers z := by
    rcases hc1z with hc1 | hcz
    · rw [hc1]; exact Subgroup.one_mem _
    · rw [hcz]; exact Subgroup.mem_zpowers z
  have hgK2 : g ∈ K2 := by
    have hg_eq : g = (s * g * s⁻¹) * c := by rw [hcdef]; group
    rw [hg_eq]
    exact Subgroup.mul_mem K2 hsgK2 (Subgroup.zpowers_le.mpr hctx.pocket2.1 hcZ)
  have hgZ : g ∈ zpowers z := by
    rw [← (sec10KS_main hP5 hC5 hpsp hctx).2.2]
    exact ⟨hgK1, hgK2⟩
  exact hgnotZ hgZ

end CFSG.OddStandard.SmallF3.Omega
