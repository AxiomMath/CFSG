module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Cfg

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem inf_cent_mul_eq {a c : G} :
    centralizer ({a} : Set G) ⊓ centralizer ({c * a} : Set G) =
      centralizer ({a} : Set G) ⊓ centralizer ({c} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hz, htz⟩
    refine ⟨hz, ?_⟩
    have h1 : g * (c * a) = (c * a) * g := htz
    calc g * c = g * (c * a) * a⁻¹ := by group
      _ = (c * a) * g * a⁻¹ := by rw [h1]
      _ = c * (a * g) * a⁻¹ := by group
      _ = c * (g * a) * a⁻¹ := by rw [← hz]
      _ = c * g := by group
  · rintro ⟨hz, ht⟩
    refine ⟨hz, ?_⟩
    calc g * (c * a) = (g * c) * a := by group
      _ = (c * g) * a := by rw [ht]
      _ = c * (g * a) := by group
      _ = c * (a * g) := by rw [hz]
      _ = (c * a) * g := by group

namespace Cfg65

variable (h : Cfg65 G z S K₁ K₂ t)

include h

theorem tz_ne_one : t * z ≠ 1 := by
  intro h1
  apply h.t_ne
  have : t = z⁻¹ := mul_eq_one_iff_eq_inv.1 h1
  rw [this]
  exact inv_eq_of_mul_eq_one_right h.z_sq

theorem orderOf_tz (hII : II4_4_4_center) : orderOf (t * z) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.tz_sq hII) h.tz_ne_one

theorem comm_zt (hII : II4_4_4_center) : Commute z t := (h.t_comm hII).symm

theorem t_mem_cent (hII : II4_4_4_center) : t ∈ centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.2 (h.t_comm hII)

theorem z_mem_cent_tz (hII : II4_4_4_center) : z ∈ centralizer ({t * z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc z * (t * z) = (z * t) * z := by group
    _ = (t * z) * z := by rw [(h.t_comm hII).symm]

theorem t_not_normalizer : t ∉ normalizer (K₁ : Set G) := by
  intro hn
  have h1 : conjugate K₁ t = K₁ := by
    rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 hn
  exact h.std.ne (h1.symm.trans h.t_swap.1)

theorem I_isPCompIn (hII : II4_4_4_center) (h327 : IG_3_27) :
    IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({t * z} : Set G)) (IDiag t K₁) := by
  have hM := h.m4 hII
  have hint : IsIntrinsic z K₁ := intrinsic_of_comp hM h.std (Or.inl rfl)
  have := (h327 G h.std.simple z t h.std.orderOf_z h.orderOf_t (h.comm_zt hII) K₁ hint
    h.t_not_normalizer).1
  rw [inf_cent_mul_eq]
  exact this

end Cfg65

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
