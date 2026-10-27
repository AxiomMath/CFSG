module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4g

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5op6_exists_fix {t h : G} {N : Subgroup G} (ht : t * t = 1) (hN : Odd (Nat.card N))
    (hc : h * t * h⁻¹ * t⁻¹ ∈ N) : ∃ m ∈ N, t * (m * h) * t⁻¹ = m * h := by
  set n : G := h * t * h⁻¹ * t⁻¹ with hn
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hnt : t * n * t⁻¹ = n⁻¹ := by
    have h1 : t * n * t⁻¹ = t * h * t * h⁻¹ * (t * t) := by
      rw [hn, hti]
      group
    have h2 : n⁻¹ = t * h * t * h⁻¹ := by
      have h2' : n⁻¹ = t * h * t⁻¹ * h⁻¹ := by
        rw [hn]
        group
      rw [h2', hti]
    rw [h1, h2, ht, mul_one]
  have hth : t * h * t⁻¹ = n⁻¹ * h := by
    rw [hn]
    group
  obtain ⟨k, hk⟩ : Odd (orderOf n) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hc)
  have hpow : n ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one n
  refine ⟨n ^ k, N.pow_mem hc k, ?_⟩
  have hconj : t * n ^ k * t⁻¹ = n⁻¹ ^ k := by
    rw [← conj_pow, hnt]
  calc t * (n ^ k * h) * t⁻¹ = (t * n ^ k * t⁻¹) * (t * h * t⁻¹) := by group
    _ = n⁻¹ ^ k * (n⁻¹ * h) := by rw [hconj, hth]
    _ = n ^ k * h := by
      have h3 : n ^ (k + 1) * n ^ k = 1 := by
        rw [← pow_add]
        convert hpow using 2
        ring
      have h4 : (n ^ (k + 1))⁻¹ = n ^ k := inv_eq_of_mul_eq_one_right h3
      rw [← mul_assoc, ← pow_succ, inv_pow, h4]

private def sec5op6_cent (H Y N : Subgroup G) (hN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    Subgroup G where
  carrier := {h | h ∈ H ∧ ∀ y ∈ Y, h * y * h⁻¹ * y⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
    refine ⟨H.mul_mem haH hbH, fun y hy => ?_⟩
    have h1 : a * b * y * (a * b)⁻¹ * y⁻¹ =
        (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * (a * y * a⁻¹ * y⁻¹) := by group
    rw [h1]
    exact N.mul_mem (hN a haH _ (hb y hy)) (ha y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simpa using N.one_mem⟩
  inv_mem' := by
    rintro a ⟨haH, ha⟩
    refine ⟨H.inv_mem haH, fun y hy => ?_⟩
    have h1 : a⁻¹ * y * a⁻¹⁻¹ * y⁻¹ = a⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [h1]
    exact hN a⁻¹ (H.inv_mem haH) _ (N.inv_mem (ha y hy))

private theorem sec5op6_restrict {K M E : Subgroup G} (hEM : E ≤ M)
    (h : (K.subgroupOf M).IsSubnormal) : (K.subgroupOf E).IsSubnormal := by
  have hEq : (K.subgroupOf M).comap (Subgroup.inclusion hEM) = K.subgroupOf E := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← hEq]
  exact h.comap _

private theorem sec5op6_trans_normal {K A B : Subgroup G} (hKA : K ≤ A) (hAB : A ≤ B)
    (hK : (K.subgroupOf A).IsSubnormal) (hA : (A.subgroupOf B).Normal) :
    (K.subgroupOf B).IsSubnormal :=
  Subgroup.IsSubnormal.trans (fun x hx => hKA hx) (aor_subnormal_subgroupOf_subgroupOf hAB hKA hK)
    hA.isSubnormal

theorem sec5op6_isSubnormal_sup {t z : G} {K Y N : Subgroup G} (ht : t * t = 1)
    (hK : Sl23PocketIn (centralizer ({t} : Set G)) z K)
    (hY : Y ≤ centralizer ({z} : Set G))
    (hYn : ∀ h ∈ centralizer ({z} : Set G), ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) (htY : t ∈ Y)
    (hN : N ≤ centralizer ({z} : Set G))
    (hNn : ∀ h ∈ centralizer ({z} : Set G), ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) (hKY : ⁅K, Y⁆ ≤ N) :
    ((K ⊔ N).subgroupOf (centralizer ({z} : Set G))).IsSubnormal := by
  obtain ⟨-, hKle, hKsub, -⟩ := hK
  set H : Subgroup G := centralizer ({z} : Set G) with hH
  let D : Subgroup G := sec5op6_cent H Y N hNn
  have hDH : D ≤ H := fun h hh => hh.1
  have hKt : K ≤ centralizer ({t} : Set G) := hKle.trans inf_le_left
  have hKH : K ≤ H := hKle.trans inf_le_right
  have hKD : K ≤ D := fun k hk =>
    ⟨hKH hk, fun y hy => hKY (Subgroup.commutator_mem_commutator hk hy)⟩
  have hND : N ≤ D := fun n hn => ⟨hN hn, fun y hy => by
    have h1 := N.mul_mem hn (hNn y (hY hy) n⁻¹ (N.inv_mem hn))
    simpa only [mul_assoc] using h1⟩
  have hDn : (D.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hDH]
    intro d h hd hh
    refine ⟨H.mul_mem (H.mul_mem hh (hDH hd)) (H.inv_mem hh), fun y hy => ?_⟩
    have hy' : h⁻¹ * y * h ∈ Y := by
      have h1 := hYn h⁻¹ (H.inv_mem hh) y hy
      rwa [inv_inv] at h1
    have h1 : h * d * h⁻¹ * y * (h * d * h⁻¹)⁻¹ * y⁻¹ =
        h * (d * (h⁻¹ * y * h) * d⁻¹ * (h⁻¹ * y * h)⁻¹) * h⁻¹ := by group
    rw [h1]
    exact hNn h hh _ (hd.2 _ hy')
  have hdec : ∀ h ∈ D, ∃ m ∈ N, m * h ∈ D ⊓ centralizer ({t} : Set G) := by
    intro h hh
    obtain ⟨m, hm, hfix⟩ := sec5op6_exists_fix ht hNodd (hh.2 t htY)
    refine ⟨m, hm, Subgroup.mem_inf.mpr ⟨D.mul_mem (hND hm) hh, ?_⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  let C : Subgroup G := D ⊓ centralizer ({t} : Set G)
  have hCD : C ≤ D := inf_le_left
  have hKC : K ≤ C := le_inf hKD hKt
  have hCle : C ≤ centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hDH)
  have hA : ((K.subgroupOf D).subgroupOf (C.subgroupOf D)).IsSubnormal :=
    aor_subnormal_subgroupOf_subgroupOf hCD hKC (sec5op6_restrict hCle hKsub)
  haveI hNnorm : (N.subgroupOf D).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hND]
    intro n d hn hd
    exact hNn d (hDH hd) n hn
  have hsup : C.subgroupOf D ⊔ N.subgroupOf D = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨h, hh⟩ -
    obtain ⟨m, hm, hmh⟩ := hdec h hh
    have h1 : (⟨h, hh⟩ : ↥D) = ⟨m, hND hm⟩⁻¹ * ⟨m * h, hmh.1⟩ := by
      apply Subtype.ext
      simp
    rw [h1, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr (N.inv_mem hm))
      (Subgroup.mem_subgroupOf.mpr hmh)
  have hsn := isSubnormal_sup_of_sup_eq_top (X := ↥D) (N' := C.subgroupOf D)
    (Nn := N.subgroupOf D) (A := K.subgroupOf D) hsup (fun x hx => hKC hx) hA
  rw [← Subgroup.subgroupOf_sup hKD hND] at hsn
  exact sec5op6_trans_normal (sup_le hKD hND) hDH hsn hDn
