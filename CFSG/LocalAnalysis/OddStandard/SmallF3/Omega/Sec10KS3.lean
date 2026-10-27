module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sl23_invol_eq_of_ne_one (x y : SL23) (hx : x * x = 1) (hy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y :=
  (by decide : ∀ x y : SL23, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y) x y hx hy hx1 hy1

private theorem sl23_exists_conj_not_comm (x : SL23) (hx : x ^ 4 = 1) (hx2 : x * x ≠ 1) :
    ∃ g : SL23, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) :=
  (by decide : ∀ x : SL23, x ^ 4 = 1 → x * x ≠ 1 →
    ∃ g : SL23, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹)) x hx hx2

private theorem twoCoreIn_le' (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

theorem sec10KS_Qi_center [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ a ∈ twoCoreIn K1, (∀ b ∈ twoCoreIn K1, a * b = b * a) → a ∈ zpowers z := by
  obtain ⟨e⟩ := (sec10KS_equiv hP5 hC5 hpsp hctx).1
  intro a ha hacentral
  obtain ⟨n, hn, hnval⟩ := Subgroup.mem_map.mp ha
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hzK1 : z ∈ K1 := hctx.pocket1.1
  let eps : ↥K1 := ⟨z, hzK1⟩
  have hzsq : eps * eps = 1 := by
    apply Subtype.ext
    change z * z = 1
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have heps : e eps * e eps = 1 := by rw [← map_mul, hzsq, map_one]
  have heps_ne : e eps ≠ 1 := by
    intro h
    have h1 : eps = 1 := e.injective (by rw [h, map_one])
    have hz1 : z = 1 := congrArg Subtype.val h1
    rw [hz1, orderOf_one] at hz2
    norm_num at hz2
  have hxn_mem : e n ∈ CFSG.pCore 2 SL23 := by
    rw [← CFSG.pCore_map_iso 2 e]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hn
  have hn4 : (e n) ^ 4 = 1 := by
    have h := hxn_mem
    rwa [sl23_pCore_eq_Q8, mem_sl23Q8] at h
  have hxcentral : ∀ y ∈ CFSG.pCore 2 SL23, (e n) * y = y * (e n) := by
    intro y hy
    rw [← CFSG.pCore_map_iso 2 e] at hy
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    have hmy' : e m = y := hmy
    have hm_two : K1.subtype m ∈ twoCoreIn K1 := Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
    have hcomm := hacentral (K1.subtype m) hm_two
    rw [← hnval] at hcomm
    have hnm : n * m = m * n :=
      K1.subtype_injective (by simpa only [map_mul] using hcomm)
    calc (e n) * y = (e n) * (e m) := by rw [hmy']
      _ = e (n * m) := (map_mul e n m).symm
      _ = e (m * n) := by rw [hnm]
      _ = (e m) * (e n) := map_mul e m n
      _ = y * (e n) := by rw [hmy']
  have hcases : n = 1 ∨ n = eps := by
    by_cases hxinv : (e n) * (e n) = 1
    · by_cases hx1 : e n = 1
      · left
        exact e.injective (by rw [hx1, map_one])
      · right
        exact e.injective (sl23_invol_eq_of_ne_one (e n) (e eps) hxinv heps hx1 heps_ne)
    · exfalso
      obtain ⟨g, hg⟩ := sl23_exists_conj_not_comm (e n) hn4 hxinv
      have hgmem : g * e n * g⁻¹ ∈ CFSG.pCore 2 SL23 :=
        (CFSG.pCore_normal (p := 2) (G := SL23)).conj_mem (e n) hxn_mem g
      exact hg (hxcentral (g * e n * g⁻¹) hgmem).symm
  rcases hcases with h1 | he
  · rw [← hnval, h1, map_one]
    exact Subgroup.one_mem _
  · rw [← hnval, he]
    change z ∈ zpowers z
    exact Subgroup.mem_zpowers z

theorem sec10KS_Q_center [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G} (hpsp : IsPSp43 L)
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ c ∈ secQ K1 K2, (∀ q ∈ secQ K1 K2, c * q = q * c) → c ∈ zpowers z := by
  intro c hc hcentralc
  have hsup := sec10KS_twoCore_sup hP5 hC5 hpsp hctx
  have hcomm : ∀ a ∈ twoCoreIn K1, ∀ b ∈ twoCoreIn K2, a * b = b * a := by
    intro a ha b hb
    exact sec10Z_comm hP5 hpsp hctx a (twoCoreIn_le' K1 ha) b (twoCoreIn_le' K2 hb)
  have hc' : c ∈ twoCoreIn K1 ⊔ twoCoreIn K2 := by rwa [← hsup]
  obtain ⟨a1, ha1, a2, ha2, hc_eq⟩ := exists_mul_of_mem_sup_of_commute hcomm hc'
  have hq1 : a1 ∈ zpowers z := by
    refine sec10KS_Qi_center hP5 hC5 hpsp hctx a1 ha1 ?_
    intro b hb
    have hbQ : b ∈ secQ K1 K2 := by rw [hsup]; exact Subgroup.mem_sup_left hb
    have hcb : c * b = b * c := hcentralc b hbQ
    have hba2 : b * a2 = a2 * b :=
      sec10Z_comm hP5 hpsp hctx b (twoCoreIn_le' K1 hb) a2 (twoCoreIn_le' K2 ha2)
    have key : a1 * b * a2 = b * a1 * a2 := by
      calc a1 * b * a2 = a1 * (b * a2) := by group
        _ = a1 * (a2 * b) := by rw [hba2]
        _ = (a1 * a2) * b := by group
        _ = c * b := by rw [← hc_eq]
        _ = b * c := hcb
        _ = b * (a1 * a2) := by rw [hc_eq]
        _ = (b * a1) * a2 := by group
    exact mul_right_cancel key
  have hq2 : a2 ∈ zpowers z := by
    refine sec10KS_Qi_center hP5 hC5 hpsp hctx.swap a2 ha2 ?_
    intro b hb
    have hbQ : b ∈ secQ K1 K2 := by rw [hsup]; exact Subgroup.mem_sup_right hb
    have hcb : c * b = b * c := hcentralc b hbQ
    have hba1 : b * a1 = a1 * b :=
      (sec10Z_comm hP5 hpsp hctx a1 (twoCoreIn_le' K1 ha1) b (twoCoreIn_le' K2 hb)).symm
    have key : a1 * (a2 * b) = a1 * (b * a2) := by
      calc a1 * (a2 * b) = (a1 * a2) * b := by group
        _ = c * b := by rw [← hc_eq]
        _ = b * c := hcb
        _ = b * (a1 * a2) := by rw [hc_eq]
        _ = (b * a1) * a2 := by group
        _ = (a1 * b) * a2 := by rw [hba1]
        _ = a1 * (b * a2) := by group
    exact mul_left_cancel key
  rw [hc_eq]
  exact Subgroup.mul_mem _ hq1 hq2

theorem sec10J_W_center [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    ∀ c ∈ secW t K1 K2, (∀ w ∈ secW t K1 K2, c * w = w * c) → c ∈ zpowers t ⊔ zpowers z := by
  intro c hc hcentral
  obtain ⟨hpsp, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have hQle : secQ K1 K2 ≤ S ⊓ L := sec10J_Q_le hP5 hb hctx
  have ht_comm : ∀ q ∈ secQ K1 K2, t * q = q * t := by
    intro q hq
    exact (Subgroup.mem_centralizer_iff.mp htC q (hQle hq).2).symm
  obtain ⟨q, hq, hcq | hcq⟩ := sec10J_mem_W hP5 hb hctx c hc
  · have hqZ : q ∈ zpowers z := by
      refine sec10KS_Q_center hP5 hC5 hpsp hctx q hq ?_
      intro q' hq'
      have hq'W : q' ∈ secW t K1 K2 := by
        change q' ∈ secQ K1 K2 ⊔ zpowers t
        exact Subgroup.mem_sup_left hq'
      simpa [hcq] using hcentral q' hq'W
    rw [hcq]
    exact Subgroup.mem_sup_right hqZ
  · have hqZ : q ∈ zpowers z := by
      refine sec10KS_Q_center hP5 hC5 hpsp hctx q hq ?_
      intro q' hq'
      have hq'W : q' ∈ secW t K1 K2 := by
        change q' ∈ secQ K1 K2 ⊔ zpowers t
        exact Subgroup.mem_sup_left hq'
      have hq'c : (q * t) * q' = q' * (q * t) := by
        simpa [hcq] using hcentral q' hq'W
      have htq' : t * q' = q' * t := ht_comm q' hq'
      have key : q * q' * t = q' * q * t := by
        calc q * q' * t = q * (q' * t) := by group
          _ = q * (t * q') := by rw [← htq']
          _ = (q * t) * q' := by group
          _ = q' * (q * t) := hq'c
          _ = (q' * q) * t := by group
      exact mul_right_cancel key
    rw [hcq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqZ)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))

end CFSG.OddStandard.SmallF3.Omega
