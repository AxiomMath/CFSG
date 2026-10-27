module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10JW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sq_mul_t {t q : G} (ht : t * t = 1) (h : t * q = q * t) :
    (q * t) * (q * t) = q * q := by
  calc (q * t) * (q * t)
      = q * (t * q) * t := by group
    _ = q * (q * t) * t := by rw [h]
    _ = q * q * (t * t) := by group
    _ = q * q := by rw [ht, mul_one]

private lemma comm_t1 {t q1 q2 : G} (ht : t * t = 1) (h1 : t * q1 = q1 * t)
    (h2 : t * q2 = q2 * t) :
    q1 * (q2 * t) * q1⁻¹ * (q2 * t)⁻¹ = q1 * q2 * q1⁻¹ * q2⁻¹ := by
  have h1inv : t * q1⁻¹ = q1⁻¹ * t := (Commute.inv_right (show Commute t q1 from h1)).eq
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ht]
  calc q1 * (q2 * t) * q1⁻¹ * (t * q2⁻¹)
      = q1 * q2 * (t * q1⁻¹) * (t * q2⁻¹) := by group
    _ = q1 * q2 * (q1⁻¹ * t) * (t * q2⁻¹) := by rw [h1inv]
    _ = q1 * q2 * q1⁻¹ * (t * t) * q2⁻¹ := by group
    _ = q1 * q2 * q1⁻¹ * q2⁻¹ := by rw [ht, mul_one]

private lemma comm_1t {t q1 q2 : G} (ht : t * t = 1) (h1 : t * q1 = q1 * t)
    (h2 : t * q2 = q2 * t) :
    (q1 * t) * q2 * (q1 * t)⁻¹ * q2⁻¹ = q1 * q2 * q1⁻¹ * q2⁻¹ := by
  have h1inv : t * q1⁻¹ = q1⁻¹ * t := (Commute.inv_right (show Commute t q1 from h1)).eq
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_left ht]
  calc (q1 * t) * q2 * (t * q1⁻¹) * q2⁻¹
      = q1 * (t * q2) * (t * q1⁻¹) * q2⁻¹ := by group
    _ = q1 * (q2 * t) * (t * q1⁻¹) * q2⁻¹ := by rw [h2]
    _ = q1 * q2 * (t * t) * q1⁻¹ * q2⁻¹ := by group
    _ = q1 * q2 * q1⁻¹ * q2⁻¹ := by rw [ht, mul_one]

private lemma comm_tt {t q1 q2 : G} (ht : t * t = 1) (h1 : t * q1 = q1 * t)
    (h2 : t * q2 = q2 * t) :
    (q1 * t) * (q2 * t) * (q1 * t)⁻¹ * (q2 * t)⁻¹ = q1 * q2 * q1⁻¹ * q2⁻¹ := by
  have h1inv : t * q1⁻¹ = q1⁻¹ * t := (Commute.inv_right (show Commute t q1 from h1)).eq
  simp only [mul_inv_rev, inv_eq_of_mul_eq_one_left ht]
  calc (q1 * t) * (q2 * t) * (t * q1⁻¹) * (t * q2⁻¹)
      = q1 * (t * q2) * t * (t * q1⁻¹) * (t * q2⁻¹) := by group
    _ = q1 * (q2 * t) * t * (t * q1⁻¹) * (t * q2⁻¹) := by rw [h2]
    _ = q1 * q2 * (t * t) * (t * q1⁻¹) * (t * q2⁻¹) := by group
    _ = q1 * q2 * (t * q1⁻¹) * (t * q2⁻¹) := by rw [ht, mul_one]
    _ = q1 * q2 * (q1⁻¹ * t) * (t * q2⁻¹) := by rw [h1inv]
    _ = q1 * q2 * q1⁻¹ * (t * t) * q2⁻¹ := by group
    _ = q1 * q2 * q1⁻¹ * q2⁻¹ := by rw [ht, mul_one]

theorem sec10J_W_elem [Finite G] (hP5 : Asc82FactPockets5) (hC5 : Asc82FactCentZ5)
    (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) :
    z ∈ secW t K1 K2 ∧ IsElemAbelianMod z (secW t K1 K2) := by
  obtain ⟨hpsp, -, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [hctx.involution] at h
    simpa [pow_two] using h
  have hQ := sec10KS_Q_elem hP5 hC5 hpsp hctx
  have hQleS : secQ K1 K2 ≤ S := (sec10J_Q_le hP5 hb hctx).trans inf_le_left
  have hcent : S ≤ centralizer ({t} : Set G) := hctx.sylow.1
  have hcomm : ∀ q ∈ secQ K1 K2, t * q = q * t := fun q hq =>
    mem_centralizer_iff.mp (hcent (hQleS hq)) t (by simp)
  constructor
  · show z ∈ secQ K1 K2 ⊔ zpowers t
    exact Subgroup.mem_sup_left hQ.1
  · intro a ha b hbW
    obtain ⟨q1, hq1Q, ha'⟩ := sec10J_mem_W hP5 hb hctx a ha
    obtain ⟨q2, hq2Q, hb'⟩ := sec10J_mem_W hP5 hb hctx b hbW
    have h1 : t * q1 = q1 * t := hcomm q1 hq1Q
    have h2 : t * q2 = q2 * t := hcomm q2 hq2Q
    have hQab := hQ.2 q1 hq1Q q2 hq2Q
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact hQab
    · exact ⟨by rw [comm_t1 ht2 h1 h2]; exact hQab.1, hQab.2⟩
    · exact ⟨by rw [comm_1t ht2 h1 h2]; exact hQab.1,
        by rw [sq_mul_t ht2 h1]; exact hQab.2⟩
    · exact ⟨by rw [comm_tt ht2 h1 h2]; exact hQab.1,
        by rw [sq_mul_t ht2 h1]; exact hQab.2⟩

end CFSG.OddStandard.SmallF3.Omega
