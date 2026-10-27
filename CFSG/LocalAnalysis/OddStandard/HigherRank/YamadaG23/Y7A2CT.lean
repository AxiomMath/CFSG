module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1ModC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_t_commutator_inv {t m : G} (ht : t * t = 1) :
    t * ⁅m, t⁆ * t⁻¹ = ⁅m, t⁆⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * ⁅m, t⁆ * t⁻¹ = t * m * t * m⁻¹ := by
    calc t * ⁅m, t⁆ * t⁻¹
        = t * (m * t * m⁻¹ * t⁻¹) * t⁻¹ := by rw [commutatorElement_def]
      _ = t * (m * t * m⁻¹ * t) * t := by rw [htinv]
      _ = t * m * t * m⁻¹ := by
            calc t * (m * t * m⁻¹ * t) * t
                = t * m * t * m⁻¹ * (t * t) := by group
              _ = t * m * t * m⁻¹ := by rw [ht, mul_one]
  rw [h1]
  calc t * m * t * m⁻¹ = t⁻¹ * m * t⁻¹ * m⁻¹ := by rw [htinv]
    _ = (m * t * m⁻¹ * t)⁻¹ := by group
    _ = ⁅m, t⁆⁻¹ := by rw [commutatorElement_def, htinv]

theorem y7a_comm_t_mem (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {X Y : Subgroup G} (hXA : X ≤ c.s.fr.A)
    (hY : ∀ a ∈ c.s.fr.A, (∀ x ∈ X, a * x = x * a) → a ∈ Y)
    (hYsq : ∀ y ∈ Y, y * y = 1) (hzY : c.s.fr.z ∈ Y) {m : G} (hm : m ∈ M6 c.e)
    (hmX : ∀ x ∈ X, m * x = x * m) : ⁅m, c.s.t⁆ ∈ Y := by
  have h := c.y7acfg hH
  have hwAV : ⁅m, c.s.t⁆ ∈ c.s.fr.A ⊔ V1 c.e := by
    simpa only [AV1] using
      y7a_comm_t_AV c hH m (y7a_C6_le_X c hH hF (y7a_M6_le_C6 c hm))
  obtain ⟨a, ha, v, hv, haw⟩ := y7a_AV_elems h ⁅m, c.s.t⁆ hwAV
  have hcomm_w : ∀ x ∈ X, Commute x ⁅m, c.s.t⁆ := by
    intro x hx
    have hxA : x ∈ c.s.fr.A := hXA hx
    have hmx : Commute m x := hmX x hx
    have htx : Commute c.s.t x := (s3_comm_t_of_mem_A c.s hxA).symm
    have hconj : Commute (m * c.s.t * m⁻¹ * c.s.t⁻¹) x :=
      ((hmx.mul_left htx).mul_left hmx.inv_left).mul_left htx.inv_left
    have heq : m * c.s.t * m⁻¹ * c.s.t⁻¹ = ⁅m, c.s.t⁆ := by
      rw [commutatorElement_def]
    rw [← heq]
    exact hconj.symm
  have hcomm_v : ∀ x ∈ X, Commute x v :=
    fun x hx => y6_C0_comm h.cfg x (hXA hx) v (y7a_V_le_C0 h hv)
  have haY : a ∈ Y := hY a ha (fun x hx => by
    have hxw : Commute x ⁅m, c.s.t⁆ := hcomm_w x hx
    have hxv : Commute x v := hcomm_v x hx
    have haeq' : a = ⁅m, c.s.t⁆ * v⁻¹ := by rw [haw]; group
    rw [haeq']
    exact (hxw.mul_right hxv.inv_right).symm.eq)
  have htw : c.s.t * ⁅m, c.s.t⁆ * c.s.t⁻¹ = ⁅m, c.s.t⁆⁻¹ :=
    y7a_t_commutator_inv (y7a_t_sq h)
  have hta : c.s.t * a * c.s.t⁻¹ = a := by
    have hcomm := s3_comm_t_of_mem_A c.s ha
    rw [← hcomm]
    group
  have hL : c.s.t * ⁅m, c.s.t⁆ * c.s.t⁻¹ = a * (c.s.t * v * c.s.t⁻¹) := by
    rw [haw]
    calc c.s.t * (a * v) * c.s.t⁻¹
        = (c.s.t * a * c.s.t⁻¹) * (c.s.t * v * c.s.t⁻¹) := by group
      _ = a * (c.s.t * v * c.s.t⁻¹) := by rw [hta]
  have hav : Commute a v := y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hR : (a * v)⁻¹ = a⁻¹ * v⁻¹ := hav.inv
  have hE : a * (c.s.t * v * c.s.t⁻¹) = a⁻¹ * v⁻¹ := by
    rw [← hL, ← hR, ← haw]
    exact htw
  have haeq : a * a = v⁻¹ * (c.s.t * v * c.s.t⁻¹)⁻¹ := by
    calc a * a = (a * (a * (c.s.t * v * c.s.t⁻¹))) * (c.s.t * v * c.s.t⁻¹)⁻¹ := by group
      _ = (a * (a⁻¹ * v⁻¹)) * (c.s.t * v * c.s.t⁻¹)⁻¹ := by rw [hE]
      _ = v⁻¹ * (c.s.t * v * c.s.t⁻¹)⁻¹ := by group
  have hzinv : c.s.fr.z⁻¹ = c.s.fr.z := inv_eq_of_mul_eq_one_right (y7a_z_sq h)
  have hdinv : c.d⁻¹ = c.d := inv_eq_of_mul_eq_one_right (y7a_d_sq h)
  rcases y7a_V_elems h v hv with hv1 | hvz | hvd | hvzd
  · rw [haw, hv1, mul_one]
    exact haY
  · rw [haw, hvz]
    exact Y.mul_mem haY hzY
  · exfalso
    have haeq_d : a * a = c.d⁻¹ * (c.s.t * c.d * c.s.t⁻¹)⁻¹ := by simpa [hvd] using haeq
    have hdval : c.d⁻¹ * (c.s.t * c.d * c.s.t⁻¹)⁻¹ = c.s.fr.z := by
      rw [y7a_tdt h, mul_inv_rev, hzinv, hdinv]
      rw [← mul_assoc, y7a_d_sq h, one_mul]
    have hz1 : c.s.fr.z = 1 := by
      rw [← hdval, ← haeq_d, hYsq a haY]
    exact h.cfg.z_ne hz1
  · exfalso
    have haeq_zd : a * a = (c.s.fr.z * c.d)⁻¹ *
        (c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹)⁻¹ := by simpa [hvzd] using haeq
    have htz : c.s.t * c.s.fr.z * c.s.t⁻¹ = c.s.fr.z := by
      have hcomm := s3_comm_t_of_mem_A c.s (y7a_z_mem_A h)
      rw [← hcomm]
      group
    have hconj : c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ = c.d := by
      rw [show c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹ =
            (c.s.t * c.s.fr.z * c.s.t⁻¹) * (c.s.t * c.d * c.s.t⁻¹) by group,
          htz, y7a_tdt h, ← mul_assoc, y7a_z_sq h, one_mul]
    have hzdval : (c.s.fr.z * c.d)⁻¹ * (c.s.t * (c.s.fr.z * c.d) * c.s.t⁻¹)⁻¹ =
        c.s.fr.z := by
      rw [hconj, mul_inv_rev, hzinv, hdinv, mul_assoc]
      rw [y7a_d_cent h c.s.fr.z (y7a_z_mem_A h)]
      rw [← mul_assoc, y7a_d_sq h, one_mul]
    have hz1 : c.s.fr.z = 1 := by
      rw [← hzdval, ← haeq_zd, hYsq a haY]
    exact h.cfg.z_ne hz1

end CFSG.OddStandard.HigherRank.YamadaG23
